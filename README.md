# Lean4SemanticBench

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

## License

[MIT](LICENSE)
