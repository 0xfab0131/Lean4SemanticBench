# l4sb.sh — 任意の Lean4 プロジェクトへの展開コマンド

`Graph/`(宣言解析器 `decl_report` + 依存エクスプローラ)を、任意の Lake
プロジェクトに対して安全に適用するためのコマンド群。

```
必要なもの: bash / node (v16+) / elan (lake)
```

## 最短の使い方

```sh
Commands/Scripts/l4sb.sh all /path/to/YourProject YourModule
```

これで `init → report → check → ビューア埋め込み` まで一括で行い、
最後に表示される `Graph/Web/index.html` をブラウザで開くだけ(サーバ不要)。

個別には:

```sh
l4sb.sh init   <target-dir>                 # 衛星ワークスペース <target>/.l4sb/ を生成
l4sb.sh report <target-dir> <Module>...     # 解析して report.jsonl + report.meta.json を生成
l4sb.sh check  <target-dir>                 # ldr_check.js で不変条件を検査
l4sb.sh web    <target-dir>                 # レポートをビューアへ埋め込み(file:// で開くだけ)
l4sb.sh clean  <target-dir>                 # 衛星を完全削除(対象には何も残らない)
```

`report` の追加指定:

```sh
l4sb.sh report <target> <Module>... -o out.jsonl   # レポートを複写
l4sb.sh report <target> <Module>... --no-build     # 対象のビルドを省略(危険: olean が古いと結果も古い)
l4sb.sh report <target> -- --minimal My.Theorem    # -- 以降は decl_report へ透過(最小仮定レポート等)
l4sb.sh report <target> -- --values 2000           # 証明項の抜粋を含める
```

出力の契約: 進捗や lake の出力は全て **stderr**。`report` の **stdout は
レポートのパスただ一行**なので、`rep=$(l4sb.sh report <dir> <Mod>)` がそのまま使える。

## 設計原理: 環境同一性

`decl_report` は対象の **olean** を `Lean.withImportModules` で読む。したがって

- 解析器を作った toolchain = 対象をビルドした toolchain
- 解析器が読む依存(mathlib 等)の実体 = 対象が検査されたその実体

でなければならない。これを規約でなく**構成**で保証するのが衛星ワークスペースである:

```
<target>/.l4sb/            ← init が生成(全て再生成可能・.gitignore 済み)
├── lean-toolchain         対象から複写
├── lakefile.toml          生成(対象をパス require、packagesDir を対象側へ共有)
├── lake-manifest.json     公式の lake update が生成
├── LeanDeclReport/        解析器ソースの複写(対象の toolchain でその場でコンパイル)
└── report.jsonl / report.meta.json
```

衛星の依存は三種で、全てピン留めされている:

| 依存 | 固定機構 |
|---|---|
| 対象パッケージ | パス依存(リビジョン概念なし) |
| 継承依存(mathlib 等) | 対象の lake-manifest.json のロック |
| importGraph(対象の依存木に無い場合のみ) | 対象 toolchain と同名の公式タグ |

### 禁止ではなく検証

manifest は公式の `lake update` に書かせ、その直後に**事後検証**を必ず行う:
衛星と対象の両 manifest に現れる同名パッケージの rev が完全一致すること。
不一致が出た場合は対象側のロックへの復元を試みた上で**必ず停止**する。
黙って間違った環境を解析することはない。

## 検証状態の申告

本ツールの前提のうち、一次情報・実機で確認済みのものと仮説に留まるものを区別して記す。

**検証済み**

- 解析器のコードは Lean core + Std + ImportGraph の 3 API のみに依存(Mathlib への import ゼロ)
- import-graph は vX.Y.0 と rc の公式タグを発行し、タグの指すコミットの
  lean-toolchain はタグ名と一致する(v4.33.0-rc1 / v4.30.0 で実確認)。
  **パッチ版(v4.32.1 / v4.33.1 等)のタグは発行されない**(2026-09 実確認)ため、
  タグ解決は「完全一致 → rc 落とし → パッチ落とし(vX.Y.Z → vX.Y.0)」の
  退避を実装している(パッチ版 toolchain とはソース互換)
- Lake の TOML 設定は `packagesDir`・パス `[[require]]` を公式サポート。
  TOML は v4.8.0 導入の**後発の既定形式**であり、宣言的設定の公式推奨
  (lean4#4106)。探索順は **lakefile.lean 優先、無ければ lakefile.toml**
  (内省 target_info.js もこの順に合わせてある)
- **互換窓の両端で実測済み**:
  - **v4.33.1**(現行最新安定版): 開発ワークスペース(Graph/)でライブラリ・
    実行ファイル・対話コマンドの全ビルド成功
  - **v4.30.0**: 衛星での e2e 完走(init → 対象ビルド → 解析器ビルド →
    decl_report 実行 → report.jsonl + meta 生成 → ビューア埋め込み)
- **TOML の `supportInterpreter` は v4.30.0 の衛星で実働を確認**
  (decl_report が `withImportModules` で環境を読み JSONL を生成した。
  反証条項〔無効なら lakefile.lean 生成へ切替〕は発動しなかった)
- 公式タグの解決 rev は旧構成(mathlib 経由の継承)の rev と一致/
  依存 manifest のロック継承(Cli の `inherited: true`)を実確認

**仮説(破れても検出されて停止する。「黙って間違う」ことはない)**

- 衛星での `lake update` が、対象(パス依存)の manifest ロックを継承し、
  共有 packagesDir のリビジョンを動かさないこと。根拠は Lake 解決器
  `addDependencyEntries` の読解と上記の実測、および lean4#13084
  (`lake update` は推移依存のピンを再解決しない)— この「再解決しない」性質は
  我々の構成では望む方向に働く。破れは事後検証(rev 完全一致)が検出する

**意味論上の下限**

- **対応下限は v4.23.0 とする。** それ未満の toolchain では `Lean.collectAxioms` が
  「公理の型が参照する公理」(`native_decide` 由来の `Lean.trustCompiler` 等)を
  取り逃す既知バグがあり(lean4#8840、v4.23.0 の #8842 で修正)、
  **公理監査が静かに不完全になる**。本ツールの中核は公理の正直な報告なので、
  コンパイルの可否に関わらずこの版を下限とする

**未確定(利用の中で実測する)**

- v4.23.0〜v4.29 の範囲でのコンパイル可否(未実測)。
  対応外の場合は `report` の解析器ビルドで停止する

## 制限と注意

- **モジュール名の自動検出は既定値の提供に過ぎない。** lakefile の `lean_lib` 名を
  使うが、lib 名と import 可能なモジュール名が一致しない構成(root 指定・glob)では
  明示指定が必要。
- **`--no-build` は自己責任。** decl_report が読むのは olean であり、ソース編集後に
  ビルドせず解析すると「古い環境の解析結果」が出る。
- **mathlib 依存の対象**では、ビルド前に `lake exe cache get` を試みる
  (fresh clone でのソースフルビルドを避ける標準作法)。毎回ネットワークを
  叩かないよう自動実行は**衛星ごとに一度だけ**で、以後は
  `report --fetch-cache` で明示する。取得に失敗しても続行し、
  直後の `lake build` が常に正となる。
- 対象の toolchain が古く importGraph の同名タグが無い場合は
  `l4sb.sh init <target> --import-graph-rev <rev>` で明示指定できる
  (採用された rev は衛星に記録され、以後の `report` の自動 init が
  黙って上書きすることはない)。
- 衛星は解析器ソースの複写を持つ。`Graph/LeanDeclReport/` を編集した場合、
  次の `report` がハッシュ比較で検出して自動的に再複写・再ビルドする。
- **信頼境界**: `lake update` / `lake build` は対象の lakefile を実行する
  (lakefile.lean は Lean プログラム)。解析は対象のビルドを伴うため、
  **信頼できる対象にのみ**使用すること。
- **モジュールシステム化された対象**(v4.20 以降の `module` ヘッダ採用、
  v4.27 で安定化)では、定理の証明項が import から省略されるため、
  import 越しの宣言の**値依存・証明項サイズが欠け得る**
  (公理は core の exported 公理表で保たれる)。`import all` 相当での
  完全な値解析への対応は今後の課題(未実測)。

## ファイル構成

```
Commands/Scripts/
├── l4sb.sh                 本体(bash)
├── lib/target_info.js      対象の内省(名前・toolchain・lean_lib・依存の有無)
├── lib/verify_manifest.js  環境同一性の事後検証
└── README.md               この文書
```
