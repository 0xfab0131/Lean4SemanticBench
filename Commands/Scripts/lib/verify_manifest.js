/* 環境同一性の事後検証。

     node verify_manifest.js <target-dir> <satellite-dir>

   不変条件: 衛星と対象の両 manifest に現れる同名の git パッケージは、
   rev が完全一致しなければならない。ここが食い違うと「対象が検査された実体」と
   「解析器が読む実体」が別物になり、解析結果が静かに嘘になる。

   出力(1 行 1 判定。呼び出し側の bash が読む):
     OK <name> <rev>                       一致
     MISMATCH <name> <targetRev> <satRev>  不一致(終了コード 1)
     EXTRA <name> <rev>                    衛星のみに居る依存(importGraph 等)。情報のみ
     PATHDEP <name>                        対象自身のパス依存を確認

   対象に manifest が無い(依存ゼロの)場合、比較対象が無いので
   衛星側の git 依存は全て EXTRA になり、検証は自明に通る。 */
"use strict";
const fs = require("fs");
const path = require("path");

const [targetDir, satDir] = process.argv.slice(2);
if (!targetDir || !satDir) {
  console.error("usage: verify_manifest.js <target-dir> <satellite-dir>");
  process.exit(2);
}

const load = (dir, required) => {
  const f = path.join(dir, "lake-manifest.json");
  try {
    return JSON.parse(fs.readFileSync(f, "utf8"));
  } catch (e) {
    if (required) {
      console.error(`verify_manifest: ${f} を読めません: ${e.message}`);
      process.exit(2);
    }
    return { packages: [] };
  }
};
const strip = (s) => String(s || "").replace(/[«»]/g, "");

const target = load(targetDir, false);   // 依存ゼロの対象には manifest が無くてよい
const sat = load(satDir, true);          // 衛星には必ずある(lake update 直後に呼ぶ)

const targetRev = new Map();
for (const p of target.packages || []) {
  if (p.type === "git") targetRev.set(strip(p.name), p.rev);
}

let bad = 0;
for (const p of sat.packages || []) {
  const n = strip(p.name);
  if (p.type === "path") {
    console.log(`PATHDEP ${n}`);
    continue;
  }
  if (p.type !== "git") continue;
  if (targetRev.has(n)) {
    if (targetRev.get(n) === p.rev) console.log(`OK ${n} ${p.rev}`);
    else { console.log(`MISMATCH ${n} ${targetRev.get(n)} ${p.rev}`); bad = 1; }
  } else {
    console.log(`EXTRA ${n} ${p.rev}`);
  }
}
process.exit(bad);
