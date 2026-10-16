/-
  LeanDeclReport
  ==============
  ライブラリのルートモジュール。

  Basic    : 解析の本体（入出力構造・直接依存・公理集合・下方閉集合の極小元）
  Commands : 対話コマンド `#decl_report` / `#decl_axioms` / `#minimal_deps` /
             `#decl_report_batch`

  `LeanDeclReport.Main` はこのライブラリには入れない。あれは実行ファイル
  `decl_report` のルートであって、ライブラリとして import される対象ではない
  （`unsafe def main` を持ち、`Lean.importModules (loadExts := true)` で別環境を立ち上げる）。
-/
import LeanDeclReport.Basic
import LeanDeclReport.Commands
