import Lean
import ImportGraph.Lean.Environment
import ImportGraph.Imports.Redundant

/-
  LeanDeclReport / Basic.lean
  ============================
  各宣言について
    (1) 入力構造（明示引数・暗黙引数・型クラス制約）
    (2) 直接依存する定数
    (3) 推移的に依存する公理集合
    (4) 下方閉集合 ↓d の極小元 min(↓d)（＝最小の仮定）
    (5) 依存先が定義されているモジュール集合
  を計算する。

  既存 API を使う方針:
    - 公理収集       : `Lean.collectAxioms`（core `Lean.Util.CollectAxioms`）
                       [Monad m] [MonadEnv m] (constName : Name) : m (Array Name)
                       lean4#8842 以降、公理の型が参照する公理も辿る。
    - 内部宣言の判定 : `Name.isInternalDetail`（core、Lean 4.10.0 の #4454 で公開）
    - モジュール特定 : `Environment.getModuleFor?`（ImportGraph）
    - 冗長 import    : `Environment.findRedundantImports`（ImportGraph）
  推移的な依存は自前の BFS（`downwardClosure`）で辿る。型と値の両方を
  `allowOpaque := true` で辿るので、定理の証明項にしか現れない依存も落とさない。
  必要モジュールもその閉包から集める（ImportGraph の推移閉包は使わない）。
-/

open Lean Lean.Meta

namespace LeanDeclReport

/-! ## 型シグネチャの分解

`(α : Type u) → (E : EPred β) → EBiEntails β E F → EBiEntails α X Y` のような型は、
引数・仮定・結論が同じ `→` で並ぶので、文字列のまま渡すと読み手が三つを
区別できない。ここで分解し、結論は頭部まで取り出して渡す。

pretty print は必ず `forallTelescope` の内側で行う。外で行うと束縛変数が
局所文脈を失い、`_uniq.1234` のような表示になって意味を成さない。 -/

/-- 一つの束縛。`kind` は明示 / 暗黙 / strict 暗黙 / インスタンス。
    `prop` が真なら、それは引数ではなく **仮定**（証明を要求している）。
    この区別が無いと「無条件に与えられる定義」と「条件付きの定義」を
    機械的に分けられない。 -/
structure BinderView where
  name : Name
  kind : String
  type : String
  prop : Bool := false
  deriving Inhabited

/-- 定数 `n` の型の先頭 `k` 個の束縛情報。Π 連鎖を剥がすだけで簡約はしない。
    `Eq : {α : Sort u} → α → α → Prop` なら `#[implicit, default, default]`。 -/
private def binderInfosOf (env : Environment) (n : Name) (k : Nat) : Array BinderInfo :=
  match env.find? n with
  | none    => #[]
  | some ci => go ci.type k #[]
where
  go : Expr → Nat → Array BinderInfo → Array BinderInfo
    | .forallE _ _ b bi, k+1, acc => go b k (acc.push bi)
    | _,                 _,   acc => acc

/-- `R … a b` の形を (R, a, b) に分ける。二項の適用を読むための入口で、
    関係にも二項演算にも使う。`mdata` は先に剥がす。

    末尾二つの引数が **明示引数** であることを、頭部定数の束縛情報で確かめる。
    単に末尾二つを取ると、`Nat.cast {R} [NatCast R] n` のような単項の写像が
    「インスタンスと n の二項演算」に見え、`↑(n + m) = ↑n + ↑m` を分配律
    f x (g p q) = g (f x p) (f x q) の x にインスタンスを入れた形として誤認する
    （フィクスチャの導出図で `Int.natCast_add` に実測）。法則の担い手は元で
    なければならない。束縛情報が引数の数まで取れない（型が Π 連鎖で書かれて
    いない）ときは「誤って付けない」向きに倒し、二項とは見なさない。 -/
def asBinApp (env : Environment) (e0 : Expr) : Option (Name × Expr × Expr) :=
  let e := e0.consumeMData
  match e.getAppFn with
  | .const r _ =>
    let args := e.getAppArgs
    let k := args.size
    if k ≥ 2 then
      let infos := binderInfosOf env r k
      if infos.size == k && infos[k - 2]! == .default && infos[k - 1]! == .default then
        some (r, args[k - 2]!, args[k - 1]!)
      else none
    else none
  | _ => none

/-- 比較は reducible 透明度の defeq で行う。

    構造的等価だけで比べると、暗黙引数の与え方や `mdata` の差で同じものを
    別物と見なし、成り立っている性質を取り逃す。一方で無制限の defeq は
    高価な上に、意図していない同一視まで通してしまう。その中間を取る。 -/
private def eqv (a b : Expr) : MetaM Bool := do
  if a == b then return true   -- 構造等価の高速路。defeq(heartbeat 消費源)を避ける
  try Meta.withReducible (Meta.isDefEq a b) catch _ => pure false

/-- 担い手の型の頭部定数。`join m n` なら `m : Nat` の `Nat`、`instLENat.le a b` も `Nat`。
    変数や Sort（多相な主張、命題同士の同値）のときは anonymous。
    法則の在庫表で「どの型の上の関係か」を行の鍵に加えるために使う。
    頭部定数だけを鍵にすると、`Nat` の反射と `Int` の推移が同じ行に合流する。 -/
private def carrierOf (x : Expr) : MetaM Name := do
  try
    let t ← Meta.inferType x
    pure (match t.consumeMData.getAppFn with | .const n _ => n | _ => Name.anonymous)
  catch _ => pure Name.anonymous

/-- `f xs` と `f ys` が同じ写像 `f` による `x` と `y` の像か。
    ある位置 `i` で `xs[i] ≡ x` かつ `ys[i] ≡ y`、他の位置では `xs[j] ≡ ys[j]`。
    `k + m` と `k + n` は `(m, n)` の像（`HAdd.hAdd Nat Nat Nat inst k ·`）だが、
    `a = a'` と `b = b'` は（頭部は共に `Eq` でも）どの `(x, y)` の像でもない。 -/
private def isImagePair (xs ys : Array Expr) (x y : Expr) : MetaM Bool := do
  if xs.size != ys.size then return false
  for i in [:xs.size] do
    if (← eqv xs[i]! x) && (← eqv ys[i]! y) then
      let mut others := true
      for j in [:xs.size] do
        if j != i && others then
          unless (← eqv xs[j]! ys[j]!) do others := false
      if others then return true
  return false

/-- 主張の形を判定する。

    順序・同値・代数法則が実際に取れているかは、この計画で繰り返し問われる。
    宣言名に頼らず、仮定と結論の形から機械的に見る。判定は「誤って付けない」
    向きに倒してあり、取り逃しはあり得る。

      refl / irrefl      R a a  ／  ¬ R a a
      symm               R a b  ⟹  R b a
      trans              R a m, R m b  ⟹  R a b
      antisymm           R a b, R b a  ⟹  a = b （または a ↔ b）
      total              R a b ∨ R b a （全域性。枠が ∨ のときのチャージ先）
      comm / assoc / idem  二項演算の可換・結合・冪等（枠は = / ↔ に限る）
      absorb / distrib   二演算の吸収・分配。第二の担い手も返す
      mono               R x y  ⟹  R (f x) (f y)。仮定と結論が同じ関係 R で、
                         結論の両辺が同じ f による x, y の像（isImagePair）。
                         担い手は f、第三成分にその関係 R を入れる

    各判定は主張を (枠, 担い手, 法則) へ写すチャージであり、枠(外側の結合子)を
    検査してから担い手を確定する。反対称律は結論が `Eq` / `Iff` で対象の関係が
    仮定側にあり、全域性は枠が `∨`。枠を見ずにチャージすると、全域性を可換と
    誤認するような取り違えが起きる（検証フィクスチャで実測済み）。

    返り値は (形, 担い手, 相方, 担い手の型)。相方は吸収・分配では第二の演算、
    単調では関係、それ以外は anonymous。担い手の型は `carrierOf`。 -/
def relShape (hyps : Array Expr) (body0 : Expr) : MetaM (String × Name × Name × Name) := do
  let env ← getEnv
  let body := body0.consumeMData
  let none : String × Name × Name × Name := ("", Name.anonymous, Name.anonymous, Name.anonymous)
  -- 非反射律は否定の内側を見る。`Not p` は適用であって裸の定数ではないので、
  -- core の認識子 `not?`（`isAppOfArity Not 1` で剥がす）を使う。
  if let some inner := body.not? then
    if let some (r0, a0, b0) := asBinApp env inner then
      if ← eqv a0 b0 then return ("irrefl", r0, Name.anonymous, ← carrierOf a0)
  let some (r, a, b) := asBinApp env body | return none
  if ← eqv a b then return ("refl", r, Name.anonymous, ← carrierOf a)
  let rels := hyps.map (·.consumeMData) |>.filterMap (asBinApp env)

  if r == ``Eq || r == ``Iff then
    for p in rels do
      for q in rels do
        if p.1 == q.1 then
          if (← eqv p.2.1 a) && (← eqv p.2.2 b) && (← eqv q.2.1 b) && (← eqv q.2.2 a) then
            return ("antisymm", p.1, Name.anonymous, ← carrierOf a)   -- 対象の関係は仮定側にある
  for p in rels do
    if p.1 == r then
      if (← eqv p.2.1 b) && (← eqv p.2.2 a) then return ("symm", r, Name.anonymous, ← carrierOf a)
  for p in rels do
    for q in rels do
      if p.1 == r && q.1 == r then
        if (← eqv p.2.1 a) && (← eqv q.2.2 b) && (← eqv p.2.2 q.2.1) then
          return ("trans", r, Name.anonymous, ← carrierOf a)

  -- 全域性: R x y ∨ R y x。引数の入替は可換と同形だが、枠が ∨ のときは
  -- 演算の可換ではなく関係の全域性(線形性)としてチャージする。
  if r == ``Or then
    if let some (r1, x1, y1) := asBinApp env a then
      if let some (r2, x2, y2) := asBinApp env b then
        if r1 == r2 then
          if (← eqv x1 y2) && (← eqv y1 x2) then return ("total", r1, Name.anonymous, ← carrierOf x1)

  -- 二項演算の法則(可換・結合・冪等・吸収・分配)は、結論が等式・同値の
  -- 形の場合に限る。外側の枠を制限しないと、全域性 `R a b ∨ R b a` のような
  -- 主張まで「可換」と誤判定する(検証フィクスチャで実測)。
  -- 判定は「誤って付けない」向きに倒す、という原則の適用である。
  if r == ``Eq || r == ``Iff then
    if let some (f, x, y) := asBinApp env a then
      if let some (g, u, v) := asBinApp env b then
        if f == g then
          if (← eqv x v) && (← eqv y u) then return ("comm", f, Name.anonymous, ← carrierOf x)
          if let some (f', x', y') := asBinApp env x then
            if let some (g', u', v') := asBinApp env v then
              if f' == f && g' == f then
                if (← eqv x' u) && (← eqv y' u') && (← eqv y v') then
                  return ("assoc", f, Name.anonymous, ← carrierOf x)
        else
          -- 分配律: f x (g p q) = g (f x p) (f x q)。担い手は対 (f, g)。
          if let some (g', p, q) := asBinApp env y then
            if g' == g then
              if let some (fl, xl, pl) := asBinApp env u then
                if let some (fr, xr, qr) := asBinApp env v then
                  if fl == f && fr == f then
                    if (← eqv xl x) && (← eqv xr x) && (← eqv pl p) && (← eqv qr q) then
                      return ("distrib", f, g, ← carrierOf x)
      -- 吸収律: f x (g x w) = x。担い手は対 (f, g)。
      -- 二つの半束 (⊔, ⊓) を一つの束へ融合する、対をまたぐ法則。
      if let some (g2, u2, _) := asBinApp env y then
        if g2 != f then
          if (← eqv u2 x) && (← eqv b x) then return ("absorb", f, g2, ← carrierOf x)
      if (← eqv x y) && (← eqv b x) then return ("idem", f, Name.anonymous, ← carrierOf x)

  -- 単調: 仮定 R x y があり、結論が同じ関係 R の下で f x と f y について述べている。
  -- 枠 r（例: le'）が「どの関係について単調か」なので、相方の位置に入れる。
  -- 「結論の両辺の頭部が同じ」だけでは、単射性 `mk a b = mk a' b' → a = a' ∧ b = b'`
  -- （両辺の頭部は共に Eq、仮定の関係は Eq で枠は And）まで単調と誤認する
  -- （自己解析の `DirectDeps.mk.inj` で実測）。像であることまで確かめる。
  match a.getAppFn, b.getAppFn with
  | .const f _, .const g _ =>
    if f == g then
      let xs := a.getAppArgs
      let ys := b.getAppArgs
      for p in rels do
        if p.1 == r then
          if ← isImagePair xs ys p.2.1 p.2.2 then
            return ("mono", f, r, ← carrierOf a)
  | _, _ => pure ()
  return none

/-- 明示引数・暗黙引数・型クラス制約を区別した入力構造。 -/
structure ArgClassification where
  binders      : Array BinderView := #[]
  numExplicit  : Nat := 0
  numImplicit  : Nat := 0
  numInst      : Nat := 0
  /-- `Prop` 値の束縛の数。すなわち要求している仮定の数。 -/
  numHyp       : Nat := 0
  /-- 結論を pretty print したもの。 -/
  conclusion   : String := ""
  /-- 結論の頭部定数。`Eq` のような論理結合子まで剥がして「何についての主張か」を返す。 -/
  subject      : Name := Name.anonymous
  /-- 結論の頭部定数（剥がす前）。 -/
  head         : Name := Name.anonymous
  /-- 結論の各引数の頭部定数。述語の含意関係を二層目のグラフとして取り出す材料。 -/
  conclArgs    : Array Name := #[]
  /-- 主張の形。refl / symm / trans / antisymm / total / comm / assoc / idem /
      absorb / distrib / mono、判定できなければ空。 -/
  shape        : String := ""
  /-- その形が「どの関係・演算についてのものか」。法則の在庫表の行になる。 -/
  shapeRel     : Name := Name.anonymous
  /-- 二演算法則(吸収・分配)の相方。単調では関係。単独法則では anonymous。 -/
  shapeRel2    : Name := Name.anonymous
  /-- 担い手の型の頭部（`Nat` など）。多相な主張では anonymous。 -/
  shapeType    : Name := Name.anonymous

/-- 結論の頭部が論理的な包み（`Eq` など）なら、その中身の頭部まで降りる。
    「この定理は何についての主張か」を一語で言うための鍵になる。 -/
private def wrapperHeads : NameSet :=
  [``Eq, ``Iff, ``HEq, ``And, ``Or, ``Not, ``Exists, ``Ne].foldl (·.insert ·) {}

/-- 主題。頭部が包みなら、その包みの **明示引数** のうち最初に主題を持つものへ降りる。
    `Eq {α} a b` の `α` は型であって主題ではないので飛ばす（飛ばさないと、`Nat` 上の
    等式が全て主題 `Nat` になり、主題での束ねが型での束ねに退化する。実測）。
    明示・暗黙は包みの定数の型の束縛情報で判定する。λ・∀ の本体へは透過する
    （`Exists fun x => R x x` の主題は `R`）。 -/
partial def subjectOf (env : Environment) : Expr → Name
  | .mdata _ e       => subjectOf env e
  | .lam _ _ b _     => subjectOf env b
  | .forallE _ _ b _ => subjectOf env b
  | e =>
    match e.getAppFn with
    | .const n _ =>
      if wrapperHeads.contains n then
        let args := e.getAppArgs
        let infos := binderInfosOf env n args.size
        let rec pick (i : Nat) : Name :=
          if h : i < args.size then
            let explicit := (infos[i]?.map (· == .default)).getD true
            let s := if explicit then subjectOf env args[i] else Name.anonymous
            if s != Name.anonymous && s != n then s else pick (i + 1)
          else n
        pick 0
      else n
    | _ => Name.anonymous

/-- 型 `e` を Π 型の連鎖として展開し、各引数を `BinderInfo` に応じて分類する。

    `withShapes := false` で法則の形の判定(`relShape`)だけを外せる。
    形の判定は唯一の defeq 消費源であり、heartbeat 上限による実行時例外の
    源にもなる。その場合も本体(束縛・結論・頭部)は失わない、という
    段階的縮退のための旗。形は元々「判定できなければ空」が定義済みの意味論。 -/
def classifyArgs (e : Expr) (withShapes : Bool := true) : MetaM ArgClassification :=
  Meta.forallTelescope e fun fvars body => do
    let env ← getEnv
    let mut binders : Array BinderView := #[]
    let mut hyps : Array Expr := #[]
    let mut nE := 0; let mut nI := 0; let mut nC := 0; let mut nH := 0
    for fvar in fvars do
      let ldecl ← fvar.fvarId!.getDecl
      let kind := match ldecl.binderInfo with
        | .default        => "explicit"
        | .implicit       => "implicit"
        | .strictImplicit => "strictImplicit"
        | .instImplicit   => "inst"
      match ldecl.binderInfo with
      | .default        => nE := nE + 1
      | .implicit       => nI := nI + 1
      | .strictImplicit => nI := nI + 1
      | .instImplicit   => nC := nC + 1
      let isP ← try Meta.isProp ldecl.type catch _ => pure false
      if isP then nH := nH + 1; hyps := hyps.push ldecl.type
      let ty ← try pure (toString (← Meta.ppExpr ldecl.type)) catch _ => pure ""
      /- 束縛名は衛生化（macro scope）を剥がす。`[Field F]` のように名前を書かないインスタンス束縛は
         elaborator が `inst✝` の衛生名を付け、生の `userName` は
         `inst._@.Cslib….1395594095._hygCtx._hyg.4` になる（cslib で束縛 2731 件中 640 件を実測）。
         pretty printer は `inst_1` と番号を振るが、それは表示上の便宜であって原文には無い名前。
         衛生名の束縛は **無名**（空文字）として渡し、表示側が `[Field F]`・`(_ : T)`・`P →` と書く
         （`→` で書かれた仮定も `a✝` の衛生名を持つ。`a` に剥がして出すと、書かれていない名前を
         原文に加えることになる）。 -/
      let name := if ldecl.userName.hasMacroScopes then Name.anonymous else ldecl.userName
      binders := binders.push { name, kind, type := ty, prop := isP }
    let concl ← try pure (toString (← Meta.ppExpr body)) catch _ => pure ""
    let head := match body.getAppFn with
      | .const n _ => n
      | _          => Name.anonymous
    let conclArgs := body.getAppArgs.map fun a =>
      match a.getAppFn with
      | .const n _ => n
      | _          => Name.anonymous
    /- 形の判定は命題にだけ行う。型クラスのインスタンス `C α α` は構文上は反射の
       形を持つがデータであって証明ではない（自己解析で `instHAdd` 等に実測）。
       Π 型が命題であることと本体が命題であることは同値なので、本体で判定する。 -/
    let bodyIsProp ← try Meta.isProp body catch _ => pure false
    let noShape := ("", Name.anonymous, Name.anonymous, Name.anonymous)
    let (shape, shapeRel, shapeRel2, shapeType) ←
      if withShapes && bodyIsProp then
        try relShape hyps body catch _ => pure noShape
      else
        pure noShape
    return {
      binders, numExplicit := nE, numImplicit := nI, numInst := nC, numHyp := nH,
      conclusion := concl, subject := subjectOf env body, head, conclArgs,
      shape, shapeRel, shapeRel2, shapeType
    }

/-! ## 直接依存する定数

`Lean.Expr.foldConsts (e) (init) (f : Name → α → α)` で型と値の両方から集める。
ここで欲しいのは 1 段だけの直接依存で、推移閉包は下方閉集合の構築時に
層ごとに辿る形で得る（`downwardClosure`）。 -/

def collectConsts (e : Expr) : NameSet :=
  e.foldConsts ({} : NameSet) fun n acc => acc.insert n

/--
直接依存を **型依存** と **値依存** に分ける。

- 型依存 : 宣言の *主張* に現れる。定理なら「何を述べているか」を決めるので、
           意味論的なレビュー対象として必ず保持しなければならない。
- 値依存 : 証明項・実装にのみ現れる。定理の場合、その依存先の証明の中身は
           カーネルの型検査で保証済みなので (証明無関係性)、
           上流の意味論的正しさを問う際には刈り込んでよい。
           一方 **定義** の実装に現れる値依存は意味論的に本質的なので刈り込めない。

型にも値にも現れる定数は型依存側に入れる（型依存のほうが強い制約なので）。
-/
structure DirectDeps where
  typeDeps  : NameSet := {}
  valueDeps : NameSet := {}
  deriving Inhabited

/-- 型依存と値依存を合わせた全体。 -/
def DirectDeps.all (d : DirectDeps) : NameSet := d.typeDeps.union d.valueDeps

/-- `n` が型と値から直接参照する定数集合（自己参照を除く）を分けて返す。

    `allowOpaque := true` が要る。`ConstantInfo.value?` は既定では
    **定理と opaque に対して `none` を返す**（Lean/Declaration.lean）。
    これを既定のまま使うと、定理の証明項を一度も辿らないまま
    「値依存なし・公理なし」という空虚な結果が出る。
    core の `collectAxioms` が `.thmInfo v => collectExpr v.value` と
    直接取り出しているのと意味を揃える。 -/
def directDepsOfCore (env : Environment) (n : Name) : DirectDeps :=
  match env.find? n with
  | none    => {}
  | some ci =>
    let fromType  := collectConsts ci.type
    let fromValue := match ci.value? (allowOpaque := true) with
      | some v => collectConsts v
      | none   => {}
    let tD := fromType.foldl (init := ({} : NameSet)) fun acc m =>
      if m == n then acc else acc.insert m
    let vD := fromValue.foldl (init := ({} : NameSet)) fun acc m =>
      if m == n || fromType.contains m then acc else acc.insert m
    { typeDeps := tD, valueDeps := vD }

/-! ## 共有キャッシュ

直接依存だけを解析全体で共有する。

公理集合は自前で数えず、core の `Lean.collectAxioms` をそのまま使う。
以前はここにもメモ化版を置いていたが、二重実装は必ず本家と乖離する。
実際、こちらは `ConstantInfo.value?` を既定引数のまま呼んでいたために
**定理の証明項を一度も辿らず、全ての定理を「公理非依存」と報告していた**。
core 側は imported な宣言について事前計算した公理表を持っているので
（`exportedAxiomsExt`）、素直に呼んでも十分に速い。
`#print axioms` と必ず一致することの方が価値が高い。 -/

structure Caches where
  directDeps : Std.HashMap Name DirectDeps := {}
  deriving Inhabited

abbrev CacheM := StateRefT Caches MetaM

def directDepsOf (env : Environment) (n : Name) : CacheM DirectDeps := do
  if let some cached := (← get).directDeps[n]? then
    return cached
  let deps := directDepsOfCore env n
  modify fun s => { s with directDeps := s.directDeps.insert n deps }
  return deps

/-- 型依存・値依存を合わせた集合（従来の `directDepsOf` 相当）。 -/
def allDepsOf (env : Environment) (n : Name) : CacheM NameSet :=
  return (← directDepsOf env n).all

/-! ## 補助的な観測量 -/

/-- 式の節点数。共有された部分項も展開して数えるので、燃料を切って止める。
    証明項の複雑さの目安として使う（項そのものを出さずに大きさだけ知りたい）。 -/
partial def exprSizeAux : Nat → List Expr → Nat → Nat
  | 0,      _,         acc => acc
  | _,      [],        acc => acc
  | fuel+1, e :: rest, acc =>
    match e with
    | .app f a         => exprSizeAux fuel (f :: a :: rest) (acc + 1)
    | .lam _ t b _     => exprSizeAux fuel (t :: b :: rest) (acc + 1)
    | .forallE _ t b _ => exprSizeAux fuel (t :: b :: rest) (acc + 1)
    | .letE _ t v b _  => exprSizeAux fuel (t :: v :: b :: rest) (acc + 1)
    | .mdata _ x       => exprSizeAux fuel (x :: rest) (acc + 1)
    | .proj _ _ x      => exprSizeAux fuel (x :: rest) (acc + 1)
    | _                => exprSizeAux fuel rest (acc + 1)

def exprSize (e : Expr) (fuel : Nat := 400000) : Nat := exprSizeAux fuel [e] 0

/-! ## 由来（成員・派生・断片）

`structure Pair` を書くと、Lean は利用者が書いていない宣言を追加する（`casesOn` / `rec` /
`ctorIdx` / `noConfusion*` / `mk.inj` / `mk.injEq` / `mk.sizeOf_spec` / `_sizeOf_*`）。`omega` は
`_proof_<i>` を、`match` は `match_<i>` を切り出す。各宣言について「どの宣言から作られたか」
（由来 origin）、「何か」（kind）、「元の定義とどう関係するか」（rel）を **環境の事実** から決める。
名前で推測するのは `noConfusionType` だけ（命名関数 `mkNoConfusionTypeName` が core で非公開）。

    rel = member  構成子・射影。定義の一部として利用者が書いたもの
    rel = facet   由来から機械的に導かれる **別の宣言**（単射性・互いに素・再帰子・等式補題…）
    rel = part    由来の証明・本体の **一部** を切り出したもの（`_proof_<i>` / `match_<i>` …）

由来の写像 π は手書きの宣言の上で恒等（レトラクション）。facet の由来は手書きの宣言または
成員で、facet の facet は作らない（`Pair.mk.inj` の由来は構成子 `Pair.mk`）。

`findDeclarationRanges?` は補助再帰子・noConfusion・再帰子に対して **親の範囲を返す**
（core `DeclarationRange.lean`）ので、「範囲が無い＝生成物」という判定はしない。
`deriving` のインスタンスは範囲を持ち、core に由来の記録が無いので手書きと区別しない（限界）。 -/

structure OriginInfo where
  origin : Name := Name.anonymous
  kind   : String := ""
  rel    : String := ""
  deriving Inhabited

/-- 最も近い接頭辞で、帰納型または構成子であるもの。補助再帰子・noConfusion の由来。 -/
private partial def nearestIndOrCtor (env : Environment) (n : Name) : Option Name :=
  match n with
  | .anonymous => none
  | .str p _ | .num p _ =>
    match env.find? p with
    | some (.inductInfo _) => some p
    | some (.ctorInfo _)   => some p
    | _                    => nearestIndOrCtor env p

/-- 内部名か。private 宣言（`_private.<Module>.0.<Decl>`）は `_` 始まりの成分を持つが、利用者が
    書いた宣言なので、private 接頭辞を外した利用者名で判定する（cslib の `private theorem` 8 件が
    内部扱いで対象から外れていた。実測）。 -/
def isInternalName (n : Name) : Bool :=
  ((privateToUserName? n).getD n).isInternalDetail

/-- 最も近い接頭辞で、環境に存在し内部名でない宣言。断片（`foo._proof_1_1` → `foo`）の由来。
    補助定理は private 名（`_private.<Module>.0.<Decl>._proof_1`）で作られることがある
    （cslib の `ofPure._proof_1` で実測）。接頭辞 `p` が private 名そのものなら（private 宣言の
    断片）その名で、断片だけが private 名なら利用者名（`<Decl>`）で環境を引く。 -/
private partial def nearestUserDecl (env : Environment) (n : Name) : Option Name :=
  match n with
  | .anonymous => none
  | .str p _ | .num p _ =>
    let ok (c : Name) : Bool := env.contains c && !isInternalName c
    if ok p then some p
    else
      match privateToUserName? p with
      | some u => if ok u then some u else nearestUserDecl env p
      | none   => nearestUserDecl env p

/-- 宣言 `n` の由来。判定は具体的なものから順に、core の判定子で行う。 -/
def originOf (n : Name) : MetaM OriginInfo := do
  let env ← getEnv
  let mk (o : Name) (k r : String) : OriginInfo := { origin := o, kind := k, rel := r }
  let isInd (m : Name) : Bool := env.find? m matches some (.inductInfo _)
  let isCtor (m : Name) : Bool := env.find? m matches some (.ctorInfo _)
  -- 構成子・再帰子はカーネルの宣言そのもの
  match env.find? n with
  | some (.ctorInfo v) => return mk v.induct "constructor" "member"
  | some (.recInfo _)  => if isInd n.getPrefix then return mk n.getPrefix "rec" "facet"
  | _ => pure ()
  -- 補助再帰子（casesOn / recOn / brecOn / ctorElim / ctor.elim）。拡張のタグで判定
  if isAuxRecursor env n then
    let k := if isCasesOnRecursor env n then "casesOn"
             else if isRecOnRecursor env n then "recOn"
             else if isBRecOnRecursor env n then "brecOn"
             else "auxRec"
    if let some o := nearestIndOrCtor env n then return mk o k "facet"
  if isNoConfusion env n then
    if let some o := nearestIndOrCtor env n then return mk o "noConfusion" "facet"
  if (isCtorIdxCore? env n).isSome then return mk n.getPrefix "ctorIdx" "facet"
  if let .str p "noConfusionType" := n then
    if isInd p then return mk p "noConfusionType" "facet"
  -- 構造体の射影は、利用者が書いたフィールドに対応する成員
  if env.isProjectionFn n then
    if let some s := env.getProjectionStructureName? n then return mk s "projection" "member"
  if let .str p s := n then
    if isCtor p then
      if n == mkInjectiveTheoremNameFor p then return mk p "inj" "facet"
      if n == mkInjectiveEqTheoremNameFor p then return mk p "injEq" "facet"
      if n == mkHInjectiveTheoremNameFor p then return mk p "hinj" "facet"
      if n == mkSizeOfSpecLemmaName p then return mk p "sizeOf_spec" "facet"
    if isInd p then
      if s == "_sizeOf_inst" then return mk p "sizeOf_inst" "facet"
      if s.startsWith "_sizeOf_" then return mk p "sizeOf" "facet"
  -- 断片: match の補助、証明の切り出し
  if isMatcherCore env n then
    if let some o := nearestUserDecl env n then return mk o "matcher" "part"
  -- 等式補題（遅延生成。登録表に無ければ予約名から）
  if let some d ← isEqnThm? n then return mk d "eqn" "facet"
  if let some (d, _) := declFromEqLikeName env n then return mk d "eqn" "facet"
  if let .str _ s := n then
    if ["_proof", "proof_", "_sparseCasesOn", "_unary", "_mutual"].any (s.startsWith ·) then
      if let some o := nearestUserDecl env n then return mk o "proof" "part"
  if isInternalName n then
    if let some o := nearestUserDecl env n then return mk o "internal" "part"
  return {}

/-- 宣言が書かれている行。`Lean.findDeclarationRanges?`（core）で取る。
    これが無いと「実装順」を再現できず、名前順で代用するしかなくなる。

    生成物（`.ctorIdx` / `.noConfusionType` / `.injEq` 等）は自前の range を持たない
    （自己解析で 33 件を実測。補助再帰子・noConfusion・再帰子は core が親の範囲を返す）。
    その場合は **由来** の行へ落とし（由来が無ければ接頭辞）、実装順の再現を派生にも及ぼす。 -/
def declLine (n : Name) (origin : Name := Name.anonymous) : MetaM Nat := do
  match ← Lean.findDeclarationRanges? n with
  | some r => return r.range.pos.line
  | none   =>
    let p := if origin.isAnonymous then n.getPrefix else origin
    if p.isAnonymous then return 0
    match ← Lean.findDeclarationRanges? p with
    | some r => return r.range.pos.line
    | none   => return 0

/-! ## 原文（ソースの切り出し）

整形済みの型（`typeString`）は Lean の **表示** であって原文ではない（∀ の連鎖・完全修飾名・`inst_1`）。
読み手が確認したいのは書かれたとおりの宣言なので、宣言範囲（`findDeclarationRanges?`）の行を
ソースファイルから切り出して添える。ファイルはモジュール名からソースの検索パスで解決する
（`getSrcSearchPath` = `LEAN_SRC_PATH`（`lake env` が各パッケージのソースディレクトリを置く）＋
実行ファイル基準の `src/lean`。実行ファイルは `.lake/build/bin` にあるので後者は当たらず、core の
ソースは toolchain の `src/lean` を `findSysroot` から明示的に足す）。言語サーバの定義ジャンプと
同じ機構。読めなければ空（黙って別物を出さない）。 -/

/-- モジュール → ソースの行（読めなければ none）。解析全体で共有する。 -/
initialize sourceLinesRef : IO.Ref (Std.HashMap Name (Option (Array String))) ← IO.mkRef {}
initialize srcSearchPathRef : IO.Ref (Option SearchPath) ← IO.mkRef none

def srcSearchPath : IO SearchPath := do
  if let some sp ← srcSearchPathRef.get then return sp
  let sp ← getSrcSearchPath
  let sp ← try
      let sys ← findSysroot
      pure (sp ++ [sys / "src" / "lean" / "lake", sys / "src" / "lean"])
    catch _ => pure sp
  srcSearchPathRef.set (some sp)
  return sp

def sourceLinesOf (m : Name) : IO (Option (Array String)) := do
  if let some v := (← sourceLinesRef.get)[m]? then return v
  let v ← try
      let sp ← srcSearchPath
      match ← sp.findWithExt "lean" m with
      | some p =>
        if ← p.pathExists then
          pure (some ((← IO.FS.readFile p).splitOn "\n").toArray)
        else pure none
      | none => pure none
    catch _ => pure none
  sourceLinesRef.modify (·.insert m v)
  return v

/-- 宣言 `n`（モジュール `m`）の原文と終了行。範囲は `findDeclarationRanges?`（1 始まりの行、両端含む）。
    派生（`casesOn` 等）は core が親の範囲を返すので、親（帰納型）の原文になる。自前の範囲を持たない
    派生（`ctorIdx` / `noConfusionType` / `mk.inj` / `mk.injEq` / `mk.sizeOf_spec`。フィクスチャで実測）は
    `declLine` と同じく由来の範囲へ落とす（由来の原文＝その派生を生んだ定義）。
    原文は範囲の行をそのまま全て出す。打ち切らない（切った原文は原文ではない）。 -/
def sourceOf (n : Name) (m : Name) (origin : Name := Name.anonymous) : MetaM (String × Nat) := do
  let r? ← match ← Lean.findDeclarationRanges? n with
    | some r => pure (some r)
    | none   => if origin.isAnonymous then pure none else Lean.findDeclarationRanges? origin
  let some r := r? | return ("", 0)
  let some lines ← sourceLinesOf m | return ("", r.range.endPos.line)
  let a := r.range.pos.line
  let b := min r.range.endPos.line lines.size
  if a == 0 || a > lines.size || b < a then return ("", r.range.endPos.line)
  return ("\n".intercalate (lines.extract (a - 1) b).toList, r.range.endPos.line)

/-- 帰納型なら構成子、構造体ならフィールド。「この宣言が属する型」を辿る手掛かり。 -/
def membersOf (env : Environment) (ci : ConstantInfo) : Array Name :=
  match ci with
  | .inductInfo iv =>
    if Lean.isStructure env iv.name then Lean.getStructureFields env iv.name
    else iv.ctors.toArray
  | _ => #[]

/-! ## 宣言レポート -/

def kindString (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

/-- 宣言が定義されているモジュール名。
    `Environment.getModuleFor?` は ImportGraph が提供する
    （`env.getModuleIdxFor?` + `env.allImportedModuleNames` のラッパ）。 -/
def moduleOf (env : Environment) (n : Name) : Name :=
  (env.getModuleFor? n).getD env.header.mainModule

structure DeclReport where
  name        : Name
  kind        : String
  module      : Name
  isProp      : Bool
  numExplicit : Nat
  numImplicit : Nat
  numInst     : Nat
  usesSorry   : Bool
  axioms      : Array Name
  /-- 主張（型）に現れる依存。意味論的なレビュー対象。 -/
  typeDeps    : Array Name
  /-- 証明項・実装にのみ現れる依存。定理ならカーネル検査済みなので刈り込める。 -/
  valueDeps   : Array Name
  /-- 直接依存する定数が定義されているモジュールの集合。 -/
  depModules  : Array Name
  typeString  : String
  docString   : String
  /-- 束縛を分解したもの。引数・仮定・結論を読み手が区別できるようにする。 -/
  binders     : Array BinderView
  /-- 結論を pretty print したもの。 -/
  conclusion  : String
  /-- `Prop` 値の束縛の数。すなわち要求している仮定の数。 -/
  numHyp      : Nat
  /-- 結論の頭部定数。 -/
  head        : Name
  /-- 「何についての主張か」。`Eq` などの包みを剥がした頭部。部分グラフの束ね方に使う。 -/
  subject     : Name
  /-- 結論の各引数の頭部定数。述語の含意関係を取り出す材料。 -/
  conclArgs   : Array Name
  /-- 主張の形。refl / symm / trans / antisymm / total / comm / assoc / idem /
      absorb / distrib / mono。 -/
  shape       : String
  /-- その形がどの関係・演算についてのものか。 -/
  shapeRel    : Name
  /-- 二演算法則(吸収・分配)の相方。単調では関係。単独法則では anonymous。 -/
  shapeRel2   : Name
  /-- 担い手の型の頭部（`Nat` など）。多相な主張では anonymous。在庫表の行の鍵に使う。 -/
  shapeType   : Name
  /-- `[reducible]` などの可簡約性。`abbrev` と `def` の区別がここに出る。 -/
  reducibility : String
  /-- 宣言が書かれている行。0 は不明。 -/
  line        : Nat
  /-- 宣言の終了行。0 は不明。 -/
  lineEnd     : Nat
  /-- 原文。宣言範囲の行をソースから切り出したもの（上限付き）。読めなければ空。 -/
  source      : String
  /-- 宇宙変数の個数。 -/
  numUniverse : Nat
  /-- インスタンスとして登録されているか。 -/
  isInstance  : Bool
  /-- 型の節点数。主張の構文的な大きさ。 -/
  typeSize    : Nat
  /-- 証明項・実装の節点数。項そのものを出さずに複雑さだけを測る。 -/
  valueSize   : Nat
  /-- 帰納型の構成子、または構造体のフィールド。 -/
  members     : Array Name
  /-- 証明項・実装の pretty print。`--values` を付けたときだけ入る（上限付き）。 -/
  valueString : String
  /-- 由来: この宣言を作った元の宣言（手書きなら anonymous）。`originOf` 参照。 -/
  origin      : Name
  /-- 由来の種類: constructor / projection / rec / casesOn / recOn / brecOn / auxRec / noConfusion /
      noConfusionType / ctorIdx / inj / injEq / hinj / sizeOf_spec / sizeOf_inst / sizeOf / matcher /
      eqn / proof / internal。手書きなら空。 -/
  originKind  : String
  /-- 由来との関係: member（成員）/ facet（派生）/ part（断片）。手書きなら空。 -/
  originRel   : String

instance : ToString DeclReport where
  toString r :=
    s!"{r.name} : {r.kind}\n" ++
    s!"  module     := {r.module}\n" ++
    s!"  isProp     := {r.isProp}\n" ++
    s!"  args       := 明示 {r.numExplicit} / 暗黙 {r.numImplicit} / インスタンス {r.numInst}\n" ++
    s!"  usesSorry  := {r.usesSorry}\n" ++
    s!"  axioms     := {r.axioms.toList}\n" ++
    s!"  typeDeps   := ({r.typeDeps.size} 件) {r.typeDeps.toList}\n" ++
    s!"  valueDeps  := ({r.valueDeps.size} 件) {r.valueDeps.toList}\n" ++
    s!"  depModules := {r.depModules.toList}\n" ++
    s!"  line       := {r.line}–{r.lineEnd}  universe := {r.numUniverse}  instance := {r.isInstance}\n" ++
    s!"  source     := {if r.source.isEmpty then "(読めず)" else s!"{r.source.length} 文字"}\n" ++
    s!"  size       := 型 {r.typeSize} / 値 {r.valueSize}\n" ++
    s!"  reducible  := {r.reducibility}  hyps := {r.numHyp}  members := {r.members.toList}\n" ++
    s!"  shape      := {if r.shape.isEmpty then "(なし)" else r.shape}  rel := {r.shapeRel}  rel2 := {r.shapeRel2}  on := {r.shapeType}\n" ++
    s!"  origin     := {if r.originRel.isEmpty then "(手書き)" else s!"{r.origin}  kind := {r.originKind}  rel := {r.originRel}"}\n" ++
    s!"  subject    := {r.subject}  (結論の頭部 {r.head})\n" ++
    String.join (r.binders.toList.map fun b => s!"  引数 [{b.kind}] {b.name} : {b.type}\n") ++
    s!"  結論       := {r.conclusion}\n" ++
    s!"  type       := {r.typeString}"

def nameArray (s : NameSet) : Array Name :=
  (s.foldl (init := (#[] : Array Name)) fun acc n => acc.push n).qsort Name.lt

/-- 型と値に共通する観測をまとめる。バッチ用と単一用で同じものを見せるため、
    依存と公理の取り方だけを引数で受け取り、残りはここで揃える。 -/
def buildReport (env : Environment) (ci : ConstantInfo)
    (deps : DirectDeps) (ax : Array Name) (valueChars : Nat)
    (withShapes : Bool := true) : MetaM DeclReport := do
  let name := ci.name
  let type := ci.type
  let isProp ← try Meta.isProp type catch _ => pure false
  let cls ← try classifyArgs type withShapes catch _ => pure {}
  let typeStr ← try pure (toString (← Meta.ppExpr type)) catch _ => pure (toString name)
  let doc ← (do pure ((← Lean.findDocString? env name).getD "")) <|> pure ""
  let depMods := deps.all.foldl (init := ({} : NameSet)) fun acc d =>
    match env.getModuleFor? d with
    | some m => acc.insert m
    | none   => acc
  let orig ← try originOf name catch _ => pure {}
  let line ← try declLine name orig.origin catch _ => pure 0
  let module := moduleOf env name
  let (source, lineEnd) ← try sourceOf name module orig.origin catch _ => pure ("", 0)
  let isInst ← try Lean.Meta.isInstance name catch _ => pure false
  -- `ReducibilityStatus` の構成子は版により増える(〜v4.28: 3 つ / v4.29 で
  -- `implicitReducible` 追加(#12247)/ v4.33 で `instanceReducible` に分割
  -- されて 5 つ(#13637))。構成子の全列挙は版を跨ぐと「不足」か「冗長」の
  -- どちらかで壊れるため、構成子名を参照せず `Repr`(core が導出済み)で
  -- 名前を写す。どの版でも情報を落とさない。
  -- 例: "Lean.ReducibilityStatus.instanceReducible" → "instanceReducible"
  let red ← try
      let st ← Lean.getReducibilityStatus name
      let s := toString (repr st)
      pure (((s.splitOn ".").getLast?).getD s)
    catch _ => pure ""
  let valSize := match ci.value? (allowOpaque := true) with
    | some v => exprSize v
    | none   => 0
  -- 証明項は既定では出さない。定理一つで数万節点になり得るので、
  -- 出すときも上限を切る（読むための抜粋であって、再検査用ではない）。
  let valStr ← if valueChars == 0 then pure "" else
    match ci.value? (allowOpaque := true) with
    | none   => pure ""
    | some v => do
      let s ← try pure (toString (← Meta.ppExpr v)) catch _ => pure ""
      pure (if s.length ≤ valueChars then s else String.ofList (s.toList.take valueChars) ++ " …")
  return {
    name
    kind        := kindString ci
    module
    isProp
    numExplicit := cls.numExplicit
    numImplicit := cls.numImplicit
    numInst     := cls.numInst
    usesSorry   := ax.contains `sorryAx
    axioms      := ax.qsort Name.lt
    typeDeps    := nameArray deps.typeDeps
    valueDeps   := nameArray deps.valueDeps
    depModules  := nameArray depMods
    typeString  := typeStr
    docString   := doc
    binders     := cls.binders
    conclusion  := cls.conclusion
    numHyp      := cls.numHyp
    head        := cls.head
    subject     := cls.subject
    conclArgs   := cls.conclArgs
    shape       := cls.shape
    shapeRel    := cls.shapeRel
    shapeRel2   := cls.shapeRel2
    shapeType   := cls.shapeType
    reducibility := red
    line
    lineEnd
    source
    numUniverse := ci.levelParams.length
    isInstance  := isInst
    typeSize    := exprSize type
    valueSize   := valSize
    members     := membersOf env ci
    valueString := valStr
    origin      := orig.origin
    originKind  := orig.kind
    originRel   := orig.rel
  }

/-- 1 つの `ConstantInfo` から `DeclReport` を構築する（バッチ用、キャッシュ共有）。 -/
def analyzeDecl (env : Environment) (ci : ConstantInfo) (valueChars : Nat := 0)
    (withShapes : Bool := true) : CacheM DeclReport := do
  let deps ← directDepsOf env ci.name
  let ax ← Lean.collectAxioms ci.name
  liftM (buildReport env ci deps ax valueChars withShapes)

/-- 単一宣言用。公理は core の `Lean.collectAxioms` をそのまま使う。
    対話コマンドはこちらを通すことで、`#print axioms` と必ず同じ結果になる。 -/
def analyzeDeclSingle (ci : ConstantInfo) (valueChars : Nat := 0) : MetaM DeclReport := do
  let env ← getEnv
  let deps := directDepsOfCore env ci.name
  let ax ← Lean.collectAxioms ci.name
  buildReport env ci deps ax valueChars

/-! ## 束論的な「最小の仮定」 min(↓d)

深さ上限を設けて探索すると、BFS が打ち切られただけのノードが
「依存先が閉集合の中にない」状態になり、極小元と区別できなくなる。
これを混同すると最小の仮定を誤って報告するので 2 つに分ける。

閉包作用素の言葉で言えば、↓ は宣言の冪集合上の閉包作用素
（拡大・単調・冪等）であり、

    frontier = ∅  ⟺  訪問集合が ↓ の不動点（＝依存で閉じた集合）

が成り立つ。「正直なフロンティア」とは、閉包の不動点に達したかどうかの
機械検査に他ならない。不動点の全体は完備束をなし、min(↓d) はその中の
主不動点 ↓{d} の極小元である。

深さの既定値は事実上無制限（1000000）で、そのときフロンティアは必ず空になる。
閉包は深さの有無に関わらず同じ BFS（`downwardClosure`）で辿る。

注意: ここでの min(↓d) は「型にも値にも定数を一つも含まない宣言」であり、
`Nat` や `Bool` のような **語彙の原子** である。`propext` は `Iff` と `Eq` を
参照するので極小元ではない。公理は `collectAxioms` で別に報告する。 -/

/-- 深さ付きの下方閉集合を BFS で構築する。 -/
partial def downwardClosure (env : Environment) (root : Name) (maxDepth : Nat)
    : CacheM (Std.HashMap Name Nat) := do
  let mut visited : Std.HashMap Name Nat := ({} : Std.HashMap Name Nat).insert root 0
  let mut frontier : Array Name := #[root]
  let mut depth := 0
  while !frontier.isEmpty && depth < maxDepth do
    let mut next : Array Name := #[]
    for n in frontier do
      let deps ← allDepsOf env n
      for d in deps do
        unless visited.contains d do
          visited := visited.insert d (depth + 1)
          next := next.push d
    frontier := next
    depth := depth + 1
  return visited

/--
閉集合内の「それ以上下に辿れない」ノードを 2 種類に分ける。

- `trueMinimal` : 依存先を全く持たない。これが本当の極小元 min(↓root)。
- `frontier`    : 依存先はあるが閉集合の外にある。深さ打ち切りの境界であって
                  極小元ではない。深さ無制限なら空になる。
-/
def minimalAndFrontier (env : Environment) (closure : Std.HashMap Name Nat)
    : CacheM (Array Name × Array Name) := do
  let mut trueMinimal : Array Name := #[]
  let mut frontier    : Array Name := #[]
  for (n, _) in closure do
    let deps ← allDepsOf env n
    let hasInnerDep := deps.foldl (init := false) fun acc d => acc || closure.contains d
    unless hasInnerDep do
      if deps.isEmpty then trueMinimal := trueMinimal.push n
      else frontier := frontier.push n
  return (trueMinimal.qsort Name.lt, frontier.qsort Name.lt)

structure MinimalAssumptions where
  root            : Name
  closureSize     : Nat
  trueMinimal     : Array (Name × String)
  frontier        : Array (Name × String)
  axiomsInClosure : Array Name
  /-- 推移的に必要になるモジュール。閉包 ↓root の各宣言の定義モジュールの集合から、
      root 自身のモジュールを除いたもの。 -/
  requiredModules : Array Name
  /-- 冗長を除いた極小の import 集合。推移的に必要なもの全部を並べても
      「どれが本当に要るのか」は分からない。`Environment.findRedundantImports`
      で他から含意されるものを落とした残りが、モジュール版の min(↓d) にあたる。
      root 自身のモジュール M を候補から外すのは、M が残ると M の import 閉包が
      他の候補を全て含意して、結果が M 一つに潰れるため（読解で確認）。 -/
  irredundantModules : Array Name

def analyzeMinimalAssumptions (env : Environment) (root : Name) (maxDepth : Nat := 1000000)
    : CacheM MinimalAssumptions := do
  let closure ← downwardClosure env root maxDepth
  let (trueMin, frontier) ← minimalAndFrontier env closure
  let withKind (xs : Array Name) : Array (Name × String) :=
    xs.map fun n => (n, ((env.find? n).map kindString).getD "unknown")
  let ax ← Lean.collectAxioms root
  /- 必要モジュールは、いま作った閉包の各宣言の定義モジュールから集める。
     定理の証明項にしか現れない依存も閉包に入っているので、証明でしか使わない
     モジュールも落ちない。root 自身のモジュールは「root を述べるのに要る import」
     ではないので外す。 -/
  let selfMod := moduleOf env root
  let reqMods := closure.fold (init := ({} : NameSet)) fun acc n _ =>
    match env.getModuleFor? n with
    | some m => if m == selfMod then acc else acc.insert m
    | none   => acc
  -- 冗長な import を落として極小の集合にする。ImportGraph の `#min_imports` と同じ考え方。
  let reqArr := nameArray reqMods
  let redundant := env.findRedundantImports reqArr
  let irredundant := reqArr.filter fun n => !redundant.contains n
  return {
    root
    closureSize     := closure.size
    trueMinimal     := withKind trueMin
    frontier        := withKind frontier
    axiomsInClosure := ax.qsort Name.lt
    requiredModules := reqArr
    irredundantModules := irredundant
  }

instance : ToString MinimalAssumptions where
  toString r :=
    let fmt (xs : Array (Name × String)) : String :=
      String.join (xs.toList.map fun (n, k) => s!"    - {n} : {k}\n")
    let frontierPart :=
      if r.frontier.isEmpty then ""
      else
        s!"  未展開の境界 ({r.frontier.size} 件、深さ制限で打ち切られたもの。極小元ではない):\n" ++
        fmt r.frontier
    s!"最小仮定レポート: {r.root}\n" ++
    s!"  下方閉集合 ↓{r.root} のサイズ : {r.closureSize}\n" ++
    s!"  推移的公理集合               : {r.axiomsInClosure.toList}\n" ++
    s!"  推移的に必要なモジュール     : {r.requiredModules.size} 件\n" ++
    s!"  極小の import 集合           : {r.irredundantModules.size} 件\n" ++
    String.join (r.irredundantModules.toList.map fun m => s!"    import {m}\n") ++
    s!"  真の極小元 min(↓{r.root}) ({r.trueMinimal.size} 件):\n" ++
    fmt r.trueMinimal ++
    frontierPart

end LeanDeclReport
