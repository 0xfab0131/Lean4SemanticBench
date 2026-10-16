import LeanDeclReport.Basic

/-
  LeanDeclReport / Commands.lean
  ================================
    #decl_report myTheorem          入出力メタデータを表示（公理は Lean.collectAxioms）
    #minimal_deps myTheorem         最小の仮定 min(↓d) を列挙
    #minimal_deps myTheorem 3       深さ 3 までに制限
    #decl_report_batch [foo, bar]   キャッシュ共有で一括処理し Markdown 表を出力
-/

open Lean Lean.Elab Lean.Elab.Command

namespace LeanDeclReport

/-- `#decl_report foo` : 単一宣言の入出力メタデータ。
    公理は core の `Lean.collectAxioms` を直接使うので `#print axioms` と一致する。 -/
elab "#decl_report " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  match env.find? name with
  | none => throwError s!"宣言 {name} が環境に見つかりません"
  | some ci => logInfo (toString (← liftTermElabM (analyzeDeclSingle ci)))

/-- `#decl_axioms foo` : `#print axioms` と同じ内容を `Lean.collectAxioms` で直接取る。
    `#decl_report` の結果と突き合わせて確認したいときに使う。 -/
elab "#decl_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let ax ← liftCoreM (Lean.collectAxioms name)
  if ax.isEmpty then
    logInfo s!"{name} は公理に依存していません"
  else
    logInfo s!"{name} が依存する公理: {ax.toList}"

/-- `#minimal_deps foo` / `#minimal_deps foo 3` :
    下方閉集合の極小元（最小の仮定）を列挙する。
    第2引数を与えると探索深さを制限する。 -/
elab "#minimal_deps " id:ident d:(num)? : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let maxDepth := match d with
    | some n => n.getNat
    | none   => 1000000
  let report ← liftTermElabM do
    let (r, _) ← (analyzeMinimalAssumptions env name maxDepth).run ({} : Caches)
    pure r
  logInfo (toString report)

/-- 複数宣言をキャッシュ共有のまま処理する（`MetaM` 上の本体）。
    解析できなかった宣言は黙って落とさず、第二成分で呼び出し元へ返す
    （Main.collectAllReports と同じ方針）。 -/
def batchReports (env : Environment) (names : Array Name) : MetaM (Array DeclReport × Array Name) := do
  -- 明示的な `CacheM` 注釈は Main.collectAllReports と同じ理由
  -- (無名 do ブロックはモナド推論が elaborator の版に依存する)。
  let collect : CacheM (Array DeclReport × Array Name) := do
    let mut acc : Array DeclReport := #[]
    let mut skipped : Array Name := #[]
    for n in names do
      match env.find? n with
      | none    => skipped := skipped.push n
      | some ci =>
        try acc := acc.push (← analyzeDecl env ci) catch _ => skipped := skipped.push n
    return (acc, skipped)
  let ((out, skipped), _) ← collect.run ({} : Caches)
  return (out, skipped)

/-- `#decl_report_batch [foo, bar, baz]` : Markdown 表で一覧出力。 -/
elab "#decl_report_batch " "[" ids:ident,* "]" : command => do
  let env ← getEnv
  let names ← ids.getElems.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let (reports, skipped) ← liftTermElabM (batchReports env names)
  unless skipped.isEmpty do
    logWarning m!"解析できず飛ばした宣言: {skipped.toList}"
  let header :=
    "| name | kind | isProp | 明示/暗黙/inst | sorry | 公理数 | 型依存 | 値依存 |\n" ++
    "|---|---|---|---|---|---|---|---|\n"
  let rows := reports.toList.map fun r =>
    let sorryMark := if r.usesSorry then "YES" else "no"
    s!"| `{r.name}` | {r.kind} | {r.isProp} | {r.numExplicit}/{r.numImplicit}/{r.numInst} " ++
    s!"| {sorryMark} | {r.axioms.size} | {r.typeDeps.size} | {r.valueDeps.size} |\n"
  logInfo (header ++ String.join rows)

end LeanDeclReport
