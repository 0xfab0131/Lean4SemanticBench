/-
  LeanDeclReport / Main.lean
  ============================
  `lake exe decl_report` の本体。

  使い方:
    lake build                                   -- 先に対象をビルドしておく
    lake exe decl_report MyProject > report.jsonl
    lake exe decl_report MyProject.Sub.Dir ...   -- 接頭辞（ディレクトリ）でもよい
    lake exe decl_report MyProject --minimal MyProject.Core.mainResult

  実装メモ:
  - 環境の構築は `Lean.importModules (loadExts := true)` を使う。
    `withImportModules` は常に `loadExts := false` で環境を作り（core の定義で確認）、
    その環境ではインスタンス表や記法の unexpander が初期値のまま空になる。
    結果として `isInstance` が全宣言で偽、pretty print が記法なしの前置形になる
    （自己解析で実測）。詳細は `mainImpl` のコメント。
  - `MetaM` の実行は `MetaM.toIO ctxCore sCore` を使う。
  - 出力は 1 行 1 宣言の JSON Lines。`jq` や pandas で後処理しやすい。
    `scope` は target / internal / external の三値（`declReportToJsonLine` 参照）。
    `origin` / `originKind` / `originRel` は由来（Basic.lean `originOf`）。
-/
import LeanDeclReport.Basic

open Lean

namespace LeanDeclReport

/-! ## JSON 出力 -/

def escapeJsonString (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c    => acc.push c

def jsonNameArray (xs : Array Name) : String :=
  let items := xs.toList.map fun n => "\"" ++ escapeJsonString (toString n) ++ "\""
  "[" ++ String.intercalate "," items ++ "]"

def jsonStr (s : String) : String :=
  "\"" ++ escapeJsonString s ++ "\""

def jsonBinders (xs : Array BinderView) : String :=
  let items := xs.toList.map fun b =>
    "{\"name\":" ++ jsonStr (toString b.name) ++
    ",\"kind\":" ++ jsonStr b.kind ++
    ",\"prop\":" ++ toString b.prop ++
    ",\"type\":" ++ jsonStr b.type ++ "}"
  "[" ++ String.intercalate "," items ++ "]"

/-- `scope` は三値。
    - "target"   対象モジュールで定義された宣言（一覧に出る）。
    - "internal" 対象モジュール内の内部補助（`_proof_*` / `match_*` 等）。一覧には
                 出さないが対象の一部なので、その依存まで辿る。
    - "external" 対象の外で定義され、参照されているだけの宣言（一段だけ）。
    外部の宣言を名前だけのスタブにすると、`Entails.trans` のような
    本当の前提が「型が分からないもの」に落ちて、補題と語彙の区別がつかなくなる。 -/
def declReportToJsonLine (r : DeclReport) (scope : String := "target") : String :=
  String.intercalate "," [
    "\"scope\":"       ++ jsonStr scope,
    "\"name\":"        ++ jsonStr (toString r.name),
    "\"kind\":"        ++ jsonStr r.kind,
    "\"module\":"      ++ jsonStr (toString r.module),
    "\"line\":"        ++ toString r.line,
    "\"lineEnd\":"     ++ toString r.lineEnd,
    "\"source\":"      ++ jsonStr r.source,
    "\"isProp\":"      ++ toString r.isProp,
    "\"isInstance\":"  ++ toString r.isInstance,
    "\"reducibility\":" ++ jsonStr r.reducibility,
    "\"numExplicit\":" ++ toString r.numExplicit,
    "\"numImplicit\":" ++ toString r.numImplicit,
    "\"numInst\":"     ++ toString r.numInst,
    "\"numHyp\":"      ++ toString r.numHyp,
    "\"numUniverse\":" ++ toString r.numUniverse,
    "\"typeSize\":"    ++ toString r.typeSize,
    "\"valueSize\":"   ++ toString r.valueSize,
    "\"usesSorry\":"   ++ toString r.usesSorry,
    "\"axioms\":"      ++ jsonNameArray r.axioms,
    "\"typeDeps\":"    ++ jsonNameArray r.typeDeps,
    "\"valueDeps\":"   ++ jsonNameArray r.valueDeps,
    "\"depModules\":"  ++ jsonNameArray r.depModules,
    "\"members\":"     ++ jsonNameArray r.members,
    "\"head\":"        ++ jsonStr (toString r.head),
    "\"subject\":"     ++ jsonStr (toString r.subject),
    "\"conclArgs\":"   ++ jsonNameArray r.conclArgs,
    "\"shape\":"       ++ jsonStr r.shape,
    "\"shapeRel\":"    ++ jsonStr (toString r.shapeRel),
    "\"shapeRel2\":"   ++ jsonStr (toString r.shapeRel2),
    "\"shapeType\":"   ++ jsonStr (toString r.shapeType),
    "\"binders\":"     ++ jsonBinders r.binders,
    "\"conclusion\":"  ++ jsonStr r.conclusion,
    "\"typeString\":"  ++ jsonStr r.typeString,
    "\"valueString\":" ++ jsonStr r.valueString,
    "\"docString\":"   ++ jsonStr r.docString,
    "\"origin\":"      ++ jsonStr (toString r.origin),
    "\"originKind\":"  ++ jsonStr r.originKind,
    "\"originRel\":"   ++ jsonStr r.originRel
  ] |> fun body => "{" ++ body ++ "}"

/-! ## 対象宣言の絞り込み -/

/-- `targets` のいずれかを接頭辞に持つモジュールで定義された宣言だけを残す。
    内部宣言の判定は core の `Name.isInternalDetail` を使う
    （Lean 4.10.0 の #4454 で公開された。名前の構成要素が `_` 始まりか数値かを見る）。
    private 宣言は接頭辞を外した利用者名で判定する（`isInternalName`。対象に含める）。 -/
def isTargetDecl (env : Environment) (targets : Array Name) (n : Name) : Bool :=
  if isInternalName n then false
  else
    let m := moduleOf env n
    targets.any fun t => t.isPrefixOf m

/-! ## 対象の指定: モジュール名と、その接頭辞（ディレクトリ）

対象は「モジュール名」でも「モジュール名の接頭辞」でもよい。`Cslib.Crypto.Protocols.Commitment`
のように根ファイル `Commitment.lean` を持たない接頭辞は、検索パスの中の対応するディレクトリ配下の
`.olean` を全て集めてモジュール名に展開し、それらを import する（`.olean.server` /
`.olean.private` はモジュールシステムの別水準なので除く）。宣言の絞り込み（`isTargetDecl`）は
元から接頭辞で判定するので、どちらで指定しても同じ集合になる。 -/

/-- 名前を検索パスのモジュール（`.olean` を持つ）か、ディレクトリとして展開する。
    どちらでもなければエラー（黙って空にしない）。 -/
def expandModulePrefix (sp : SearchPath) (n : Name) : IO (Array Name) := do
  /- `SearchPath.findWithExt` は「根のパッケージディレクトリが検索パスに在るか」で経路を返すだけで、
     ファイルの実在は見ない（core `Lean/Util/Path.lean`）。`Cslib.Crypto.Protocols.Commitment` でも
     `Cslib/` が在れば経路が返る。実在を確かめてからモジュールと見なす（実測で露見）。 -/
  if let some p ← sp.findWithExt "olean" n then
    if ← p.pathExists then return #[n]
  let rel : System.FilePath := System.mkFilePath (n.components.map toString)
  let mut acc : Array Name := #[]
  for root in sp do
    let dir := root / rel
    unless ← dir.isDir do continue
    for f in ← dir.walkDir do
      -- `X.olean` だけ。`X.olean.server` / `X.olean.private` の拡張子は server / private
      unless f.extension == some "olean" do continue
      let rootStr := root.toString
      let fStr := f.toString
      unless fStr.startsWith rootStr do continue
      -- 文字列 API は版で型が変わる（v4.33 で `String.drop` がスライスを返す）ので、
      -- `List Char` を経由して版に依らない形で相対パスを切り出す
      let relChars := fStr.toList.drop (rootStr.length + 1)
      let relStr := String.ofList (relChars.take (relChars.length - ".olean".length))
      let parts := relStr.splitOn System.FilePath.pathSeparator.toString
      let m := parts.foldl (fun (a : Name) (s : String) => Name.str a s) Name.anonymous
      acc := acc.push m
  if acc.isEmpty then
    throw <| IO.userError s!"モジュールまたは接頭辞 {n} が検索パスに見つかりません（対象をビルドしましたか？）"
  return (acc.qsort Name.lt).toList.eraseDups.toArray

/-! ## 実行本体 -/

/-- 全宣言のレポートを収集する。

    **宣言ごとに独立した `MetaM` 実行として走らせ、IO 水準で捕捉する。**
    `isDefEq` の heartbeat 上限到達などの実行時例外は、`MetaM` 内の通常の
    `try/catch` では捕まらず（catchRuntimeEx の仕様）、一宣言の暴走が
    解析器全体を殺していた（自己解析で実測）。IO 境界なら実行時例外も
    捕捉でき、heartbeat 予算も宣言ごとに仕切り直される。
    キャッシュは状態として明示的に持ち回り、飛ばした宣言は呼び出し元へ
    返す（黙って欠けさせない）。 -/
def collectAllReports (env : Environment) (names : Array Name) (valueChars : Nat)
    (coreCtx : Core.Context) (coreState : Core.State)
    : IO (Array DeclReport × Array Name × Array Name) := do
  let mut acc : Array DeclReport := #[]
  let mut shapeless : Array Name := #[]
  let mut skipped : Array Name := #[]
  let mut caches : Caches := {}
  for n in names do
    if let some ci := env.find? n then
      try
        let ((r, c), _) ← ((analyzeDecl env ci valueChars).run caches).toIO coreCtx coreState
        acc := acc.push r
        caches := c
      catch _ =>
        /- 実行時例外の唯一の源は形の判定(defeq)。宣言まるごと捨てるのは
           粒度が誤り — 形は「判定できなければ空」が定義済みの装飾層であり、
           本体(依存・公理・サイズ)は defeq 不要で必ず回収できる。
           形だけを外して再解析し、それでも失敗した場合に限り飛ばす。 -/
        try
          let ((r, c), _) ←
            ((analyzeDecl env ci valueChars (withShapes := false)).run caches).toIO coreCtx coreState
          acc := acc.push r
          caches := c
          shapeless := shapeless.push n
        catch _ =>
          skipped := skipped.push n
  /- 出力の行順を「ソースに書かれた順」に揃える。名前順で出すと、読み手が
     ファイルを読み進める順序と一致せず、"実装順" を再現できない。 -/
  let sorted := acc.qsort fun a b =>
    if a.module != b.module then Name.lt a.module b.module
    else if a.line != b.line then a.line < b.line
    else Name.lt a.name b.name
  return (sorted, shapeless, skipped)

def runMinimalReport (env : Environment) (root : Name) : MetaM String := do
  let (r, _) ← (analyzeMinimalAssumptions env root).run ({} : Caches)
  return toString r

/-- 対象モジュール群に属する宣言名を列挙する。
    `SMap.fold` を使う（`toList` は大きな環境で無駄が大きく、API も版によって異なるため）。 -/
def targetDeclNames (env : Environment) (targets : Array Name) : Array Name :=
  let acc := env.constants.fold
    (fun (acc : Array Name) (n : Name) _ => if isTargetDecl env targets n then acc.push n else acc)
    #[]
  acc.qsort Name.lt

structure Args where
  modules    : Array Name := #[]
  minimal?   : Option Name := none
  /-- 証明項を pretty print して出す文字数の上限。0 なら出さない。 -/
  valueChars : Nat := 0
  /-- モジュールシステムの対象で、証明等の非公開情報まで読む（`import all` 相当）。
      `module` ヘッダを持つモジュールは定理の証明項を import から省略するため
      （v4.20 以降の設計）、これ無しでは値依存・証明項の分析が不完全になり得る。
      `Import.importAll` は v4.30.0 / v4.33.0 の双方でフィールド名・既定値が
      一致していることを確認済み。 -/
  importAll  : Bool := false

/-- 引数を再帰で解析する（`Id.run do` 内での `while`/`break`/`return` 混在を避ける）。 -/
def parseArgsAux : List String → Args → Except String Args
  | [], acc =>
    if acc.modules.isEmpty then .error "対象モジュール名を1つ以上指定してください" else .ok acc
  | "--minimal" :: v :: tl, acc =>
    parseArgsAux tl { acc with minimal? := some v.toName }
  | ["--minimal"], _ =>
    .error "--minimal には宣言名が必要です"
  | "--values" :: v :: tl, acc =>
    match v.toNat? with
    | some n => parseArgsAux tl { acc with valueChars := n }
    | none   => parseArgsAux (v :: tl) { acc with valueChars := 2000 }
  | ["--values"], acc =>
    .ok { acc with valueChars := 2000 }
  | "--import-all" :: tl, acc =>
    parseArgsAux tl { acc with importAll := true }
  | a :: tl, acc =>
    if a.startsWith "-" then .error s!"不明なオプション: {a}"
    else parseArgsAux tl { acc with modules := acc.modules.push a.toName }

def parseArgs (args : List String) : Except String Args :=
  parseArgsAux args {}

unsafe def mainImpl (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error msg =>
    IO.eprintln msg
    IO.eprintln "使い方: decl_report <Module> [<Module>...] [--minimal <DeclName>] [--values [文字数]] [--import-all]"
    return 1
  | .ok parsed =>
    initSearchPath (← findSysroot)
    -- 対象の名前をモジュール（または接頭辞配下のモジュール群）に展開する
    let sp ← searchPathRef.get
    let mut mods : Array Name := #[]
    for m in parsed.modules do
      let ex ← expandModulePrefix sp m
      if ex.size != 1 || ex[0]! != m then
        IO.eprintln s!"接頭辞 {m} を {ex.size} モジュールに展開: {ex.toList}"
      mods := mods ++ ex
    -- モジュールシステムの対象では、素の import だと定理の証明項が省略される。
    -- --import-all で非公開情報（証明・private 宣言）まで読み込む。
    let imports : Array Import := mods.map fun m =>
      { module := m, importAll := parsed.importAll }
    /- 環境は拡張まで読み込む（`loadExts := true`）。
       `withImportModules` は常に `loadExts := false` で環境を作る（core の定義で確認）。
       その環境では `finalizePersistentExtensions` が走らず、インスタンス表や記法の
       unexpander が初期値のまま空になる。結果として `isInstance` が全宣言で偽、
       pretty print が記法なしの前置形（`Eq (…) (…)`、`instHMul.hMul a b`）になった
       （自己解析で実測）。docString・行範囲・可簡約性・公理表はモジュール項目を
       直接二分探索するので影響を受けず、これが「一部だけ効く」症状の正体。
       拡張の初期化は interpreter を使い得るので、先に `enableInitializersExecution`
       を呼ぶ（実行ファイルは `supportInterpreter := true`）。その場合、圧縮領域を
       解放してはならない（core の注意書き）ので `leakEnv := true` とし、
       プロセス終了まで環境を保持する。 -/
    enableInitializersExecution
    let env ← importModules imports {} (leakEnv := true) (loadExts := true)
    let coreCtx : Core.Context := { fileName := "<decl_report>", fileMap := default }
    let coreState : Core.State := { env }
    match parsed.minimal? with
    | some root =>
      let (text, _) ← (runMinimalReport env root).toIO coreCtx coreState
      IO.println text
    | none =>
      let names := targetDeclNames env parsed.modules
      let (reports, shapeless, skipped) ← collectAllReports env names parsed.valueChars coreCtx coreState
      unless shapeless.isEmpty do
        IO.eprintln s!"注記: {shapeless.size} 件の宣言で形の判定（defeq）が heartbeat 上限に達したため、形のみ空にしました（レポート本体は完全）: {shapeless.toList.take 5}{if shapeless.size > 5 then " …" else ""}"
      unless skipped.isEmpty do
        IO.eprintln s!"警告: {skipped.size} 件の宣言を実行時例外により解析できず飛ばしました: {skipped.toList.take 5}{if skipped.size > 5 then " …" else ""}"
      /- モジュールシステムの対象を素の import で読むと、定理の証明項が省略され
         値依存・valueSize が空になる。「黙って不完全な解析結果」を出さないため、
         証明項を辿れない定理を検出したら stderr で警告する
         （非モジュールの対象では定理は必ず証明項を持つので、誤警告は出ない）。 -/
      unless parsed.importAll do
        let elided := reports.filter fun r => r.kind == "theorem" && r.valueSize == 0
        unless elided.isEmpty do
          IO.eprintln s!"警告: 証明項を辿れない定理が {elided.size} 件あります。対象がモジュールシステム（module ヘッダ）を使っている場合、値依存の分析が不完全です。--import-all を付けて再実行してください"
      for r in reports do
        IO.println (declReportToJsonLine r "target")
      /- 対象から参照される宣言を二種に分けて出す。
         - 対象モジュール内の内部補助（`_proof_*` / `match_*` 等。`isInternalDetail` で
           対象一覧からは外れる）は対象の一部なので、その依存まで辿る（internal）。
           そうしないと omega 等が生成した補助定理の中身（公理の出どころ）がスタブに
           落ち、導出図から消える（自己解析で `double_eq._proof_1_1` に実測）。
         - 対象の外の宣言は、型と種別だけは欲しいので一段だけ出す（external）。
           名前しか無いと `Entails.trans` のような本当の前提が「型の分からないもの」に
           落ち、補題と語彙の区別がつかなくなる。 -/
      let inSet := names.foldl (fun (s : NameSet) n => s.insert n) {}
      let inTargetModule (n : Name) : Bool :=
        parsed.modules.any fun t => t.isPrefixOf (moduleOf env n)
      let mut internal : NameSet := {}
      let mut external : NameSet := {}
      let mut queue : Array Name := #[]
      for r in reports do
        queue := queue ++ r.typeDeps ++ r.valueDeps
      let mut i := 0
      while i < queue.size do
        let n := queue[i]!
        i := i + 1
        if inSet.contains n || internal.contains n || external.contains n then
          continue
        if inTargetModule n then
          internal := internal.insert n
          queue := queue ++ nameArray (directDepsOfCore env n).all
        else
          external := external.insert n
          /- 外部の断片（`X._proof_i` / `X.match_i`。由来の証明・本体の一部）を対象が直接参照する
             ことがある（cslib の定理が Mathlib のインスタンスの `_proof_i` を実測）。ビューアは断片を
             参照する側へ埋め戻すので、断片の依存先は参照する側にとって一段先である。一段しか出さないと
             それらが範囲外のスタブに落ち、基盤に「種別不明」が並ぶ（実測 8 件）。断片の依存先も出す。 -/
          let (o, _) ← (originOf n).toIO coreCtx coreState
          if o.rel == "part" then
            queue := queue ++ nameArray (directDepsOfCore env n).all
      /- 外部の派生・断片（`PMF.pure._proof_1` / `Exists.rec` 等）は、その由来（`PMF.pure` / `Exists`）も
         一段だけ出す。由来がレポートに無いと、ビューアは由来に畳めず `_proof_1` が節点のまま図に残り、
         極小元にも並ぶ（cslib で実測）。由来は手書きの宣言（π はレトラクション）なので、由来の由来は要らない。 -/
      let mut originsOfExternal : NameSet := {}
      for n in nameArray external do
        let (o, _) ← (originOf n).toIO coreCtx coreState
        let p := o.origin
        unless p.isAnonymous do
          if env.contains p && !inSet.contains p && !internal.contains p && !external.contains p then
            originsOfExternal := originsOfExternal.insert p
      external := external.union originsOfExternal
      /- 公理は依存順序の正真正銘の極小元（これ以上下が無い）であって、「依存が分からない点」ではない。
         対象から見た公理は `axioms` 欄に名前で現れるだけで、二段先（`Classical.propDecidable` →
         `Classical.choice`）に在るため外部一段には入らず、ビューアでは範囲外のスタブに落ちていた
         （cslib で実測。極小元の節に公理が一つも並ばない）。`axioms` に現れる名前を外部として出し、
         kind = axiom の宣言にする。 -/
      let mut axiomsSeen : NameSet := {}
      for r in reports do
        for a in r.axioms do
          if env.contains a && !inSet.contains a && !internal.contains a then
            axiomsSeen := axiomsSeen.insert a
      external := external.union axiomsSeen
      let (intReports, intShapeless, intSkipped) ←
        collectAllReports env (nameArray internal) parsed.valueChars coreCtx coreState
      let (extReports, extShapeless, extSkipped) ←
        collectAllReports env (nameArray external) parsed.valueChars coreCtx coreState
      unless intShapeless.isEmpty && extShapeless.isEmpty do
        IO.eprintln s!"注記: 内部補助 {intShapeless.size} 件・外部参照 {extShapeless.size} 件で形の判定を諦めました（本体は完全）"
      unless intSkipped.isEmpty && extSkipped.isEmpty do
        IO.eprintln s!"警告: 内部補助 {intSkipped.size} 件・外部参照 {extSkipped.size} 件を実行時例外により解析できず飛ばしました"
      for r in intReports do
        IO.println (declReportToJsonLine r "internal")
      for r in extReports do
        IO.println (declReportToJsonLine r "external")
    return 0

end LeanDeclReport

unsafe def main (args : List String) : IO UInt32 :=
  LeanDeclReport.mainImpl args
