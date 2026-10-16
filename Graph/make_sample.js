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

/* sample.js はフィクスチャ（Examples）の小さなレポートでなければならない。
   `make all TARGET=Debug/Examples MODULES="Cslib.…"` のように同じ衛星で別の対象を解析すると、
   既定の入力（.l4sb/report.jsonl）がその対象で上書きされる（cslib の 603 行・1 MB で実際に起きた）。
   来歴（report.meta.json）の対象モジュールが Examples で始まらなければ止める。
   意図してそうしたい場合だけ --force。 */
const force = process.argv.includes("--force");
const metaPath = src.replace(/\.jsonl$/, ".meta.json");
if (!force && fs.existsSync(metaPath)) {
  try {
    const meta = JSON.parse(fs.readFileSync(metaPath, "utf8"));
    const mods = Array.isArray(meta.modules) ? meta.modules : [];
    if (mods.length && !mods.every((m) => String(m).startsWith("Examples"))) {
      console.error(`来歴の対象 ${mods.join(" ")} はフィクスチャ（Examples）ではありません。sample.js を上書きしません`);
      console.error("  フィクスチャを解析し直す: make all TARGET=Debug/Examples   （意図的に上書きするなら --force）");
      process.exit(1);
    }
  } catch (e) { /* 来歴が読めなければ検査できない。レポートの中身で続ける */ }
}

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
