/* 検証用フィクスチャの実レポートから Web/js/sample.js を再生成する。

     node Graph/make_sample.js                    # 既定: Debug/Examples/.l4sb/report.jsonl
     node Graph/make_sample.js path/to/report.jsonl

   sample.js は「初回起動・レポート未読込」時の動作確認用フォールバック。
   スキーマが古いままだと、新規 clone の自己検査(ldr_check)がデータ形式
   起因で赤くなる。手で保守せず、実レポートから機械的に作り直す。 */
const fs = require("fs");
const path = require("path");

const src = process.argv[2]
  ? path.resolve(process.cwd(), process.argv[2])
  : path.join(__dirname, "..", "Debug", "Examples", ".l4sb", "report.jsonl");
const out = path.join(__dirname, "Web", "js", "sample.js");

if (!fs.existsSync(src) || fs.statSync(src).size === 0) {
  console.error(`レポートがありません: ${src}`);
  console.error("  先に `make all` で検証用フィクスチャの解析を実行してください");
  process.exit(1);
}

const text = fs.readFileSync(src, "utf8");
const lines = text.split("\n").filter((l) => l.trim()).length;

const body =
  "/* ============================================================\n" +
  "   js/sample.js — 動作確認用のサンプル\n" +
  "   `lake exe decl_report <Module> > report.jsonl` の出力と同じ形式。\n" +
  `   検証用フィクスチャ(Debug/Examples)の実レポートから生成(${lines} 宣言)。\n` +
  "   手で編集しない。作り直す: make all && node Graph/make_sample.js\n" +
  "   ============================================================ */\n" +
  "(function (LDR) {\n" +
  "  \"use strict\";\n" +
  "  LDR.SAMPLE = " + JSON.stringify(text) + ";\n" +
  "})(window.LDR = window.LDR || {});\n";

fs.writeFileSync(out, body);
console.log(`書き出しました: ${path.relative(process.cwd(), out)} (${lines} 宣言)`);
