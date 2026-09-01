import Lean
import ImportGraph.Imports.RequiredModules
import ImportGraph.Imports.Redundant
import Std.Data.TreeSet.Basic

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
    - 推移的依存     : `Name.transitivelyUsedConstants`（ImportGraph, CoreM NameSet）
    - 必要モジュール : `Name.requiredModules` / `Name.transitivelyRequiredModules`
                       （ImportGraph）
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

/-- `R … a b` の形を (R, a, b) に分ける。二項の適用を読むための入口で、
    関係にも二項演算にも使う。`mdata` は先に剥がす。 -/
def asBinApp (e0 : Expr) : Option (Name × Expr × Expr) :=
  let e := e0.consumeMData
  match e.getAppFn with
  | .const r _ =>
    let args := e.getAppArgs
    if args.size ≥ 2 then some (r, args[args.size - 2]!, args[args.size - 1]!) else none
  | _ => none

@[inherit_doc asBinApp] abbrev asBinRel := asBinApp

/-- 比較は reducible 透明度の defeq で行う。

    構造的等価だけで比べると、暗黙引数の与え方や `mdata` の差で同じものを
    別物と見なし、成り立っている性質を取り逃す。一方で無制限の defeq は
    高価な上に、意図していない同一視まで通してしまう。その中間を取る。 -/
private def eqv (a b : Expr) : MetaM Bool :=
  try Meta.withReducible (Meta.isDefEq a b) catch _ => pure (a == b)

/-- 主張の形を判定する。

    順序・同値・代数法則が実際に取れているかは、この計画で繰り返し問われる。
    宣言名に頼らず、仮定と結論の形から機械的に見る。判定は「誤って付けない」
    向きに倒してあり、取り逃しはあり得る。

      refl / irrefl      R a a  ／  ¬ R a a
      symm               R a b  ⟹  R b a
      trans              R a m, R m b  ⟹  R a b
      antisymm           R a b, R b a  ⟹  a = b （または a ↔ b）
      comm / assoc / idem  二項演算の可換・結合・冪等
      mono               関係の仮定があり、結論の両辺が同じ頭部の像

    形とあわせて「どの関係・演算についての法則か」も返す。反対称律だけは
    結論が `Eq` / `Iff` で、対象の関係は仮定側にある。ここを取り違えると
    法則の在庫表の行がずれるので、判定した場所で確定させておく。 -/
def relShape (hyps : Array Expr) (body0 : Expr) : MetaM (String × Name) := do
  let body := body0.consumeMData
  let none : String × Name := ("", Name.anonymous)
  -- 非反射律は否定の内側を見る
  if let some (n, _) := body.const? then
    if n == ``Not then
      if let some inner := body.getAppArgs[0]? then
        if let some (r0, a0, b0) := asBinApp inner then
          if ← eqv a0 b0 then return ("irrefl", r0)
  let some (r, a, b) := asBinApp body | return none
  if ← eqv a b then return ("refl", r)
  let rels := hyps.map (·.consumeMData) |>.filterMap asBinApp

  if r == ``Eq || r == ``Iff then
    for p in rels do
      for q in rels do
        if p.1 == q.1 then
          if (← eqv p.2.1 a) && (← eqv p.2.2 b) && (← eqv q.2.1 b) && (← eqv q.2.2 a) then
            return ("antisymm", p.1)          -- 対象の関係は仮定側にある
  for p in rels do
    if p.1 == r then
      if (← eqv p.2.1 b) && (← eqv p.2.2 a) then return ("symm", r)
  for p in rels do
    for q in rels do
      if p.1 == r && q.1 == r then
        if (← eqv p.2.1 a) && (← eqv q.2.2 b) && (← eqv p.2.2 q.2.1) then return ("trans", r)

  -- 二項演算の法則。両辺が同じ演算の像になっている場合だけ見る。
  if let some (f, x, y) := asBinApp a then
    if let some (g, u, v) := asBinApp b then
      if f == g then
        if (← eqv x v) && (← eqv y u) then return ("comm", f)
        if let some (f', x', y') := asBinApp x then
          if let some (g', u', v') := asBinApp v then
            if f' == f && g' == f then
              if (← eqv x' u) && (← eqv y' u') && (← eqv y v') then return ("assoc", f)
    if (← eqv x y) && (← eqv b x) then return ("idem", f)

  if !rels.isEmpty then
    match a.getAppFn, b.getAppFn with
    | .const f _, .const g _ => if f == g then return ("mono", f)
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
  /-- 主張の形。refl / symm / trans / antisymm / mono、判定できなければ空。 -/
  shape        : String := ""
  /-- その形が「どの関係・演算についてのものか」。法則の在庫表の行になる。 -/
  shapeRel     : Name := Name.anonymous

/-- 結論の頭部が論理的な包み（`Eq` など）なら、その中身の頭部まで降りる。
    「この定理は何についての主張か」を一語で言うための鍵になる。 -/
private def wrapperHeads : NameSet :=
  [``Eq, ``Iff, ``HEq, ``And, ``Or, ``Not, ``Exists, ``Ne].foldl (·.insert ·) {}

partial def subjectOf (e : Expr) : Name :=
  let f := e.getAppFn
  match f with
  | .const n _ =>
    if wrapperHeads.contains n then
      -- 型引数を飛ばして最初の意味のある引数へ降りる
      let args := e.getAppArgs
      let rec pick (i : Nat) : Name :=
        if h : i < args.size then
          let s := subjectOf args[i]
          if s != Name.anonymous && s != n then s else pick (i + 1)
        else n
      pick 0
    else n
  | _ => Name.anonymous

/-- 型 `e` を Π 型の連鎖として展開し、各引数を `BinderInfo` に応じて分類する。 -/
def classifyArgs (e : Expr) : MetaM ArgClassification :=
  Meta.forallTelescope e fun fvars body => do
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
      binders := binders.push { name := ldecl.userName, kind, type := ty, prop := isP }
    let concl ← try pure (toString (← Meta.ppExpr body)) catch _ => pure ""
    let head := match body.getAppFn with
      | .const n _ => n
      | _          => Name.anonymous
    let conclArgs := body.getAppArgs.map fun a =>
      match a.getAppFn with
      | .const n _ => n
      | _          => Name.anonymous
    let (shape, shapeRel) ← try relShape hyps body catch _ => pure ("", Name.anonymous)
    return {
      binders, numExplicit := nE, numImplicit := nI, numInst := nC, numHyp := nH,
      conclusion := concl, subject := subjectOf body, head, conclArgs, shape, shapeRel
    }

/-! ## 直接依存する定数

`Lean.Expr.foldConsts (e) (init) (f : Name → α → α)` で型と値の両方から集める。
ImportGraph の `Name.transitivelyUsedConstants` は推移閉包を返すが、
ここでは 1 段だけの直接依存が欲しいので `foldConsts` を直接使う。
（推移閉包は下方閉集合の構築時に層ごとに辿る形で得る。） -/

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

def DirectDeps.union (a b : DirectDeps) : DirectDeps :=
  { typeDeps := a.typeDeps.union b.typeDeps, valueDeps := a.valueDeps.union b.valueDeps }

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

/-- 宣言が書かれている行。`Lean.findDeclarationRanges?`（core）で取る。
    これが無いと「実装順」を再現できず、名前順で代用するしかなくなる。 -/
def declLine (n : Name) : MetaM Nat := do
  match ← Lean.findDeclarationRanges? n with
  | some r => return r.range.pos.line
  | none   => return 0

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
  /-- 主張の形。refl / symm / trans / antisymm / mono。 -/
  shape       : String
  /-- その形がどの関係・演算についてのものか。 -/
  shapeRel    : Name
  /-- `[reducible]` などの可簡約性。`abbrev` と `def` の区別がここに出る。 -/
  reducibility : String
  /-- 宣言が書かれている行。0 は不明。 -/
  line        : Nat
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
    s!"  line       := {r.line}  universe := {r.numUniverse}  instance := {r.isInstance}\n" ++
    s!"  size       := 型 {r.typeSize} / 値 {r.valueSize}\n" ++
    s!"  subject    := {r.subject}  (結論の頭部 {r.head})\n" ++
    String.join (r.binders.toList.map fun b => s!"  引数 [{b.kind}] {b.name} : {b.type}\n") ++
    s!"  結論       := {r.conclusion}\n" ++
    s!"  type       := {r.typeString}"

def nameArray (s : NameSet) : Array Name :=
  (s.foldl (init := (#[] : Array Name)) fun acc n => acc.push n).qsort Name.lt

/-- 型と値に共通する観測をまとめる。バッチ用と単一用で同じものを見せるため、
    依存と公理の取り方だけを引数で受け取り、残りはここで揃える。 -/
def buildReport (env : Environment) (ci : ConstantInfo)
    (deps : DirectDeps) (ax : Array Name) (valueChars : Nat) : MetaM DeclReport := do
  let name := ci.name
  let type := ci.type
  let isProp ← try Meta.isProp type catch _ => pure false
  let cls ← try classifyArgs type catch _ => pure {}
  let typeStr ← try pure (toString (← Meta.ppExpr type)) catch _ => pure (toString name)
  let doc ← (do pure ((← Lean.findDocString? env name).getD "")) <|> pure ""
  let depMods := deps.all.foldl (init := ({} : NameSet)) fun acc d =>
    match env.getModuleFor? d with
    | some m => acc.insert m
    | none   => acc
  let line ← try declLine name catch _ => pure 0
  let isInst ← try Lean.Meta.isInstance name catch _ => pure false
  let red ← try
      pure (match (← Lean.getReducibilityStatus name) with
        | .reducible         => "reducible"
        | .semireducible     => "semireducible"
        | .irreducible       => "irreducible"
        | .implicitReducible => "implicitReducible"
        | .instanceReducible => "instanceReducible")
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
    module      := moduleOf env name
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
    reducibility := red
    line
    numUniverse := ci.levelParams.length
    isInstance  := isInst
    typeSize    := exprSize type
    valueSize   := valSize
    members     := membersOf env ci
    valueString := valStr
  }

/-- 1 つの `ConstantInfo` から `DeclReport` を構築する（バッチ用、キャッシュ共有）。 -/
def analyzeDecl (env : Environment) (ci : ConstantInfo) (valueChars : Nat := 0)
    : CacheM DeclReport := do
  let deps ← directDepsOf env ci.name
  let ax ← Lean.collectAxioms ci.name
  liftM (buildReport env ci deps ax valueChars)

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

深さ無制限の場合は ImportGraph の `Name.transitivelyUsedConstants` が
閉集合そのものを返すので、そちらを使う（フロンティアは必ず空になる）。 -/

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
  /-- 推移的に必要になるモジュール（ImportGraph の `transitivelyRequiredModules`）。 -/
  requiredModules : Array Name
  /-- 冗長を除いた極小の import 集合。推移的に必要なもの全部を並べても
      「どれが本当に要るのか」は分からない。`Environment.findRedundantImports`
      で他から含意されるものを落とした残りが、モジュール版の min(↓d) にあたる。 -/
  irredundantModules : Array Name

def analyzeMinimalAssumptions (env : Environment) (root : Name) (maxDepth : Nat := 1000000)
    : CacheM MinimalAssumptions := do
  let closure ← downwardClosure env root maxDepth
  let (trueMin, frontier) ← minimalAndFrontier env closure
  let withKind (xs : Array Name) : Array (Name × String) :=
    xs.map fun n => (n, ((env.find? n).map kindString).getD "unknown")
  let ax ← Lean.collectAxioms root
  -- モジュールレベルの依存は ImportGraph に任せる（CoreM なので MetaM から呼べる）
  let reqMods ← root.transitivelyRequiredModules env
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
