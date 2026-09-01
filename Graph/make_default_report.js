/* report.jsonl を Web から既定で読める形に埋め込む。

     node Graph/make_default_report.js                    # Graph/report.jsonl を使う
     node Graph/make_default_report.js path/to/other.jsonl

   なぜ埋め込むのか:
   index.html は file:// で開く前提なので、隣の report.jsonl を fetch すると
   opaque origin として拒否される。http で配信すれば取りに行けるが、
   そのために毎回サーバを立てるのは道具として重い。
   そこで JS ファイルとして置き、<script> で読ませる。
   （http 配信時は index.js が fetch も試すので、生成しなくても動く。）

   出力先 Web/js/default-report.js は .gitignore 済み。
   レポートと同じく、生成物であって版に載せるものではない。 */
const fs = require("fs");
const path = require("path");

const src = process.argv[2]
  ? path.resolve(process.cwd(), process.argv[2])
  : path.join(__dirname, "report.jsonl");
const out = path.join(__dirname, "Web", "js", "default-report.js");

if (!fs.existsSync(src) || fs.statSync(src).size === 0) {
  console.error(`レポートがありません: ${src}`);
  console.error(`  cd Graph && lake exe decl_report <Module> > report.jsonl`);
  process.exit(1);
}

const text = fs.readFileSync(src, "utf8");
const lines = text.split("\n").filter((l) => l.trim()).length;

const body =
  "/* 自動生成。編集しない。\n" +
  `   生成元: ${path.basename(src)}  (${lines} 宣言)\n` +
  `   作り直す: node Graph/make_default_report.js */\n` +
  "window.LDR = window.LDR || {};\n" +
  "window.LDR.DEFAULT_REPORT = " + JSON.stringify(text) + ";\n";

fs.mkdirSync(path.dirname(out), { recursive: true });
fs.writeFileSync(out, body);

const mb = (n) => (n / 1048576).toFixed(2) + " MB";
console.log(`書き出しました: ${path.relative(process.cwd(), out)}`);
console.log(`  ${lines} 宣言 / 元 ${mb(Buffer.byteLength(text))} → 埋め込み ${mb(Buffer.byteLength(body))}`);
