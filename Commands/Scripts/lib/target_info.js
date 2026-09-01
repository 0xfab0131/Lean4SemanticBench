/* 対象 Lake プロジェクトの内省。bash が eval できる形(L4SB_* の代入行)で出力する。

     node target_info.js <target-dir>

   検出するもの:
     L4SB_NAME             パッケージ名(require に使う。«» は剥がす)
     L4SB_CONFIG           lakefile.toml | lakefile.lean
     L4SB_TOOLCHAIN        lean-toolchain の内容
     L4SB_TOOLCHAIN_TAG    その版部分(例 v4.33.0-rc1)。importGraph の公式タグ解決に使う
     L4SB_LIBS             lean_lib 名の空白区切り(report の既定モジュール)
     L4SB_HAS_MANIFEST     lake-manifest.json の有無 (0/1)
     L4SB_GIT_DEPS         manifest 中の git 依存の数
     L4SB_HAS_IMPORTGRAPH  依存木に importGraph が居るか (0/1)
     L4SB_PKGDIR           manifest の packagesDir(無ければ .lake/packages)

   TOML の解釈は「値が一行の文字列リテラルである name キー」だけを見る簡易なもの。
   これで足りない特殊な lakefile の場合は、モジュール名を明示指定すればよい
   (検出は既定値の提供であって、正は常に明示指定)。 */
"use strict";
const fs = require("fs");
const path = require("path");

const dir = process.argv[2];
if (!dir) {
  console.error("usage: target_info.js <target-dir>");
  process.exit(2);
}

const read = (f) => {
  try { return fs.readFileSync(path.join(dir, f), "utf8"); } catch { return null; }
};
const stripGuillemets = (s) => String(s || "").replace(/[«»]/g, "");

const toolchain = (read("lean-toolchain") || "").trim();
const tag = (toolchain.split(":")[1] || "").trim();

let config = "";
let name = "";
const libs = [];
const requires = [];

// Lake の探索順に合わせる: lakefile.lean が存在すればそれが使われ、
// lakefile.toml は lean が無い場合の代替(v4.8.0 リリースノート)。
// 両方あるプロジェクトで .toml 側を読むと、Lake が実際に使う設定と食い違う。
const leanf = read("lakefile.lean");
const toml = leanf == null ? read("lakefile.toml") : null;

if (leanf != null) {
  config = "lakefile.lean";
  // lakefile.lean はプログラムなので、静的に読めるのは標準的な宣言だけ。
  // 計算で組み立てる lakefile は manifest とモジュール名の明示指定に委ねる。
  const pm = leanf.match(/package\s+(?:"([^"]+)"|«?([A-Za-z0-9_.\-]+)»?)/);
  if (pm) name = pm[1] || pm[2];
  for (const m of leanf.matchAll(/lean_lib\s+(?:"([^"]+)"|«?([A-Za-z0-9_.\-]+)»?)/g)) libs.push(m[1] || m[2]);
  // require は素の名前・«»・引用・scoped ("scope" / "name") の各形を拾う
  for (const m of leanf.matchAll(/require\s+(?:"[^"]*"\s*\/\s*)?(?:"([^"]+)"|«?([A-Za-z0-9_.\-]+)»?)/g)) {
    requires.push(m[1] || m[2]);
  }
} else if (toml != null) {
  config = "lakefile.toml";
  // 簡易 TOML: テーブル見出しと `name = "..."` だけを追う
  let table = "";
  for (const raw of toml.split("\n")) {
    const line = raw.trim();
    if (!line || line.startsWith("#")) continue;
    const th = line.match(/^\[\[?([^\]]+?)\]?\]$/);
    if (th) { table = th[1].trim(); continue; }
    const kv = line.match(/^name\s*=\s*"([^"]*)"/);
    if (!kv) continue;
    if (table === "") name = kv[1];
    else if (table === "lean_lib") libs.push(kv[1]);
    else if (table === "require") requires.push(kv[1]);
  }
}

let hasManifest = 0, gitDeps = 0, hasImportGraph = 0, hasMathlib = 0;
let pkgdir = ".lake/packages";
const manRaw = read("lake-manifest.json");
if (manRaw != null) {
  hasManifest = 1;
  try {
    const man = JSON.parse(manRaw);
    if (man.packagesDir) pkgdir = man.packagesDir;
    for (const p of man.packages || []) {
      if (p.type === "git") gitDeps++;
      if (stripGuillemets(p.name) === "importGraph") hasImportGraph = 1;
      if (stripGuillemets(p.name) === "mathlib") hasMathlib = 1;
    }
    if (!name && man.name) name = stripGuillemets(man.name);
  } catch (e) {
    console.error(`target_info: lake-manifest.json を JSON として読めません: ${e.message}`);
    process.exit(1);
  }
}
if (requires.some((r) => stripGuillemets(r) === "importGraph")) hasImportGraph = 1;
if (requires.some((r) => stripGuillemets(r) === "mathlib")) hasMathlib = 1;
name = stripGuillemets(name);

const esc = (s) => "'" + String(s).replace(/'/g, `'\\''`) + "'";
const out = (k, v) => console.log(`${k}=${esc(v)}`);
out("L4SB_NAME", name);
out("L4SB_CONFIG", config);
out("L4SB_TOOLCHAIN", toolchain);
out("L4SB_TOOLCHAIN_TAG", tag);
out("L4SB_LIBS", libs.join(" "));
out("L4SB_HAS_MANIFEST", hasManifest);
out("L4SB_GIT_DEPS", gitDeps);
out("L4SB_HAS_IMPORTGRAPH", hasImportGraph);
out("L4SB_HAS_MATHLIB", hasMathlib);
out("L4SB_PKGDIR", pkgdir);
