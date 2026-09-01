import Lake
open Lake DSL

/-
  lean-decl-report
  ================
  宣言解析器 `decl_report` と対話コマンド群 `LeanDeclReport` の開発用ワークスペース。

  役割の分離:
    - **解析の実行**は、通常ここでは行わない。`Commands/Scripts/l4sb.sh` が
      解析対象プロジェクトの内側に衛星ワークスペースを生成し、対象の toolchain と
      依存の実体そのもので decl_report をビルド・実行する(環境同一性)。
    - この lakefile は LeanDeclReport 自体を**開発・単体ビルド**するためのもの
      (IDE の補完、コンパイルの確認、対話コマンドの試用)。

  依存:
    importGraph のみ(mathlib には依存しない)。提供 API は
      Lean.Environment.getModuleFor?         宣言 → 定義モジュール
      Lean.Name.transitivelyRequiredModules  推移的に必要なモジュール
      Lean.Environment.findRedundantImports  冗長な import の検出
    の三つ。リビジョンは lean-toolchain と**同名の公式タグ**で固定する
    (import-graph は toolchain ごとに同名タグを発行しており、タグの指す
    コミットの lean-toolchain はタグ名と一致する)。

  [規約] lean-toolchain を更新するときは、下の importGraph のタグも同じ版名に
    揃えること。lake-manifest.json は `lake update` が生成するロックであり、
    手で編集しない(意図はこのファイル、記録は manifest、という分離を守る)。
-/

package «lean-decl-report» where

require importGraph from git
  "https://github.com/leanprover-community/import-graph" @ "v4.33.0-rc1"

@[default_target]
lean_lib «LeanDeclReport» where

lean_exe «decl_report» where
  root := `LeanDeclReport.Main
  supportInterpreter := true
