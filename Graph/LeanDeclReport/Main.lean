/-
  LeanDeclReport / Main.lean
  ============================
  `lake exe decl_report` の本体。

  使い方:
    lake build                                   -- 先に対象をビルドしておく
    lake exe decl_report MyProject > report.jsonl
    lake exe decl_report MyProject --minimal MyProject.Core.mainResult

  実装メモ:
  - 環境の構築は `Lean.withImportModules`（`unsafe`）を使う。
    これは lean4checker が採用しているのと同じイディオムで、
    `importModules` を直接呼ぶよりシグネチャ変更に強い。
  - `MetaM` の実行は `MetaM.toIO ctxCore sCore` を使う。
  - 出力は 1 行 1 宣言の JSON Lines。`jq` や pandas で後処理しやすい。
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

/-- `scope` は "target"（対象モジュールで定義された宣言）か
    "external"（対象から参照されているだけの外部宣言）。
    外部の宣言を名前だけのスタブにすると、`Entails.trans` のような
    本当の前提が「型が分からないもの」に落ちて、補題と語彙の区別がつかなくなる。 -/
def declReportToJsonLine (r : DeclReport) (scope : String := "target") : String :=
  String.intercalate "," [
    "\"scope\":"       ++ jsonStr scope,
    "\"name\":"        ++ jsonStr (toString r.name),
    "\"kind\":"        ++ jsonStr r.kind,
    "\"module\":"      ++ jsonStr (toString r.module),
    "\"line\":"        ++ toString r.line,
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
    "\"binders\":"     ++ jsonBinders r.binders,
    "\"conclusion\":"  ++ jsonStr r.conclusion,
    "\"typeString\":"  ++ jsonStr r.typeString,
    "\"valueString\":" ++ jsonStr r.valueString,
    "\"docString\":"   ++ jsonStr r.docString
  ] |> fun body => "{" ++ body ++ "}"

/-! ## 対象宣言の絞り込み -/

/-- `targets` のいずれかを接頭辞に持つモジュールで定義された宣言だけを残す。
    内部宣言の判定は core の `Name.isInternalDetail` を使う
    （Lean 4.10.0 の #4454 で公開された。名前の構成要素が `_` 始まりか数値かを見る）。 -/
def isTargetDecl (env : Environment) (targets : Array Name) (n : Name) : Bool :=
  if n.isInternalDetail then false
  else
    let m := moduleOf env n
    targets.any fun t => t.isPrefixOf m

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
    -- モジュールシステムの対象では、素の import だと定理の証明項が省略される。
    -- --import-all で非公開情報（証明・private 宣言）まで読み込む。
    let imports : Array Import := parsed.modules.map fun m =>
      { module := m, importAll := parsed.importAll }
    withImportModules imports {} fun env => do
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
        /- 対象から直接参照されている外部の宣言も、型と種別だけは出す。
           名前しか無いと `Entails.trans` のような本当の前提が
           「型の分からないもの」に落ち、補題と語彙の区別がつかなくなる。
           出すのは直接参照の一段だけなので件数は多くない。 -/
        let inSet := names.foldl (fun (s : NameSet) n => s.insert n) {}
        let extNames := reports.foldl (init := ({} : NameSet)) fun s r =>
          let s := r.typeDeps.foldl (fun s d => if inSet.contains d then s else s.insert d) s
          r.valueDeps.foldl (fun s d => if inSet.contains d then s else s.insert d) s
        let extArr := nameArray extNames
        let (extReports, extShapeless, extSkipped) ← collectAllReports env extArr parsed.valueChars coreCtx coreState
        unless extShapeless.isEmpty do
          IO.eprintln s!"注記: 外部参照 {extShapeless.size} 件で形の判定を諦めました（本体は完全）"
        unless extSkipped.isEmpty do
          IO.eprintln s!"警告: 外部参照 {extSkipped.size} 件を実行時例外により解析できず飛ばしました"
        for r in extReports do
          IO.println (declReportToJsonLine r "external")
      return 0

end LeanDeclReport

unsafe def main (args : List String) : IO UInt32 :=
  LeanDeclReport.mainImpl args
