# Lean4SemanticBench

Lean 4 プロジェクトの宣言を**意味論の水準**で監査・探索するツール群。

各宣言について次を抽出し、ブラウザで探索できる形にする:

- **型シグネチャの分解** — 引数・仮定・結論を機械的に区別
- **型依存と値依存の分割** — 主張を決める依存と、証明にのみ現れる依存
  (カーネル検査済みで刈り込める側)の排他的分割
- **推移的公理集合** — core の `Lean.collectAxioms` を直接使い、
  `#print axioms` と必ず一致。sorry 検出を含む
- **最小の仮定** $\min(\downarrow d)$ — 依存の下方閉集合の極小元
  (深さ打ち切りとの混同を排した正直な版)
- **主張の形** — 反射・対称・推移・反対称・全域・可換・結合・冪等・
  吸収・分配・単調を構文から判定し、**法則の在庫表**として集計
  (前順序 → 半順序 → 全順序/同値/半束 → 束 → 分配束 の判断つき)

## 最短の使い方

必要なもの: bash / node (v16+) / [elan](https://leanprover-community.github.io/get_started.html)

```sh
make all TARGET=path/to/YourProject [MODULES="ModuleA ModuleB"]
```

完了後に表示される `Graph/Web/index.html` をブラウザで開くだけ(サーバ不要)。

## 構成

| パス | 内容 |
|---|---|
| [Graph/LeanDeclReport/](Graph/LeanDeclReport/) | 解析器(Lean)。`decl_report` が JSONL レポートを生成 |
| [Graph/Web/](Graph/Web/) | L4SB ビューア(静的 Web。ビルド不要・file:// で動作) |
| [Graph/ldr_check.js](Graph/ldr_check.js) | 算法層の自己検査(Node。不変条件を実データで検査) |
| [Commands/Scripts/](Commands/Scripts/) | 任意プロジェクトへの展開コマンド `l4sb.sh` |
| [Makefile](Makefile) / [Makefile.dev](Makefile.dev) | 利用者向けの入口 / 開発用 |
| [Debug/Examples/](Debug/Examples/) | 検証用フィクスチャ(全ての判定を発火させる小理論) |

## 設計の要点

- **環境同一性** — 解析は対象の内側に生成する衛星ワークスペースで行い、
  対象と同一の toolchain・同一の依存実体(mathlib 等)を用いる。
  「検査された環境」と「解析器が読む環境」が構成によって一致する。
- **禁止でなく検証** — 依存は全てピン留めし、`lake update` 直後に
  リビジョンの完全一致を機械検査する。黙って間違った環境を解析することはない。
- **検証状態の申告** — 検証済み/仮説/未確定を文書で区別して明記する
  ([Commands/Scripts/README.md](Commands/Scripts/README.md) 参照)。
- **対応下限 v4.23.0** — それ未満は `collectAxioms` の既知バグにより
  公理監査が不完全になり得るため。実測済みの互換窓: v4.30.0 / v4.33.1。

## ドキュメント

- 展開コマンドの使い方と設計原理: [Commands/Scripts/README.md](Commands/Scripts/README.md)
- ビューアの操作・可視化の設計・算法: [Graph/README.md](Graph/README.md)

## License

[MIT](LICENSE)
