/* Web UI の算法層を Node 上で実データに当てる検査。
   ブラウザ固有 API は使っていない層（graph.js / store.js）だけを読み込む。

     node Graph/ldr_check.js                    # Graph/report.jsonl を使う
     node Graph/ldr_check.js path/to/other.jsonl

   置き場所からの相対で解決するので、どの作業ディレクトリから叩いても動く。 */
const fs = require("fs");
const nodePath = require("path");

const JS_DIR = nodePath.join(__dirname, "Web", "js");
global.window = {};
require(nodePath.join(JS_DIR, "graph.js"));
require(nodePath.join(JS_DIR, "sig.js"));
require(nodePath.join(JS_DIR, "pkg.js"));
require(nodePath.join(JS_DIR, "roles.js"));
require(nodePath.join(JS_DIR, "store.js"));
const LDR = global.window.LDR;
const S = LDR.store;

/* 引数の解釈。`--decl <名前の一部> ...` を付けると、その宣言だけを
   構造化して詳しく見る検査モードになる。付けなければ全体の検査。 */
const argv = process.argv.slice(2);
const declAt = argv.indexOf("--decl");
const declQueries = [];
if (declAt >= 0) {
  // 次の `--` オプションが来たら宣言名の並びは終わり
  for (let i = declAt + 1; i < argv.length && !argv[i].startsWith("--"); i++) declQueries.push(argv[i]);
}
const positional = (declAt >= 0 ? argv.slice(0, declAt) : argv).filter((a) => !a.startsWith("--"));

const reportPath = positional[0]
  ? nodePath.resolve(process.cwd(), positional[0])
  : nodePath.join(__dirname, "report.jsonl");

let text;
if (fs.existsSync(reportPath) && fs.statSync(reportPath).size > 0) {
  text = fs.readFileSync(reportPath, "utf8");
  console.log(`対象: ${nodePath.relative(process.cwd(), reportPath) || reportPath}\n`);
} else {
  // レポートが無い環境でも検査自体は成立させる。サンプルは Web と同じものを使う。
  require(nodePath.join(JS_DIR, "sample.js"));
  text = LDR.SAMPLE;
  console.log(`対象: ${reportPath} が無いのでサンプルを使う`);
  console.log(`      実データで見るには  cd Graph && lake exe decl_report <Module> > report.jsonl\n`);
}
const ms = (f) => { const t = process.hrtime.bigint(); const v = f(); return [Number(process.hrtime.bigint() - t) / 1e6, v]; };
const short = (n) => String(n).split(".").slice(-1)[0].slice(0, 46);

let fail = 0;
const ok = (cond, label, extra) => {
  if (!cond) fail++;
  console.log(`${cond ? "  ok  " : " FAIL "} ${label}${extra !== undefined ? "  → " + extra : ""}`);
};
/* ツールの不変条件(どんなデータでも成り立つべき)と、データの特性
   (十分な規模・内容が要る)を混同しない。前提を満たさないデータでは
   FAIL ではなく skip として報告する。 */
const skip = (label, why) => console.log(`  skip  ${label}  → ${why}`);

/* ============================================================
   宣言の検査モード

     node Graph/ldr_check.js --decl <名前の一部> [<名前の一部> ...]

   Lean 側が分解して渡してくる束縛（prop 旗つき）と結論をそのまま使い、
   引数 / 仮定 / 結論（左辺・右辺）に置き直して見せる。加えて、
   依存の尺度と極小仮定 min(↓d)、証明ツリーを添える。
   ============================================================ */
function inspectDecls(queries) {
  const G = LDR.graph, sig = LDR.sig;
  S.actions.loadText(text, { silent: true });
  const idx = S.derived.declIdx;
  const met = S.metrics();
  const names = S.state.order;

  const pad = (s, n) => String(s) + " ".repeat(Math.max(0, n - String(s).length));
  /* 折り返しは行うが、切り詰めは一切しない。名前も完全修飾のまま出す。
     読みやすさのために情報を落とすと、それはもう検査ではない。 */
  const WIDTH = 132;
  const wrap = (s, indent) => {
    /* Lean の pretty print には元の整形による改行と字下げが入っている。
       それを残したまま折り返すと名前の途中で折れる。空白を一旦均してから
       こちらの幅で折り直す。落ちる情報は空白だけ。 */
    const words = String(s).replace(/\s+/g, " ").trim().split(/(?<=[\s,()])/);
    const out = []; let line = "";
    for (const w of words) {
      if (line.length + w.length > WIDTH && line.trim()) { out.push(line); line = " ".repeat(indent); }
      line += w;
    }
    if (line.trim()) out.push(line);
    return out.join("\n");
  };
  const depthAt = argv.indexOf("--depth");
  const TREE_DEPTH = depthAt >= 0 ? Number(argv[depthAt + 1]) || 2 : 2;

  let found = 0;
  for (const q of queries) {
    const ql = q.toLowerCase();
    const hits = names.filter((n) => n.toLowerCase().includes(ql));
    if (!hits.length) { console.log(`\n■ ${q}\n   該当なし`); continue; }
    if (hits.length > 1) console.log(`\n（"${q}" に ${hits.length} 件該当。全て表示します）`);
    for (const n of hits) {
      found++;
      const nd = S.state.nodes[n];
      console.log("\n" + "─".repeat(100));
      console.log(`■ ${n}`);
      const badges = [
        (LDR.panels && "") || nd.kind,
        `${String(nd.module).split(".").slice(-1)[0]}:${nd.line}`,
        (nd.numHyp === 0 && nd.numInst === 0) ? "無条件" : `条件 ${nd.numHyp + nd.numInst}`,
        nd.shape ? `形 ${sig.SHAPE[nd.shape] ? sig.SHAPE[nd.shape].ja : nd.shape}` : "形 判定なし",
        nd.isInstance ? "instance" : null,
        nd.reducibility === "reducible" ? "reducible" : null,
      ].filter(Boolean);
      console.log("  " + badges.join(" · "));
      if (nd.docString) console.log("  " + wrap(nd.docString, 2));

      const args = (nd.binders || []).filter((b) => !b.prop);
      const hyps = (nd.binders || []).filter((b) => b.prop);
      if (args.length) {
        console.log("\n  引数");
        for (const b of args) console.log("    " + pad(b.name, 10) + ": " + wrap(b.type, 16) + `   [${b.kind}]`);
      }
      if (hyps.length) {
        console.log("\n  仮定");
        for (const b of hyps) console.log("    " + wrap(b.type, 4));
      }
      const d = sig.decompose(nd.conclusion || "");
      console.log("\n  結論");
      if (d.lhs !== null && d.rhs !== null) {
        console.log("    関係 " + d.rel + (d.ctx.length ? "   文脈 " + d.ctx.join(" ") : ""));
        console.log("    左辺 " + wrap(d.lhs, 9));
        console.log("    右辺 " + wrap(d.rhs, 9));
      } else {
        console.log("    " + wrap(d.whole, 4));
      }
      console.log("    主題 " + nd.subject + "   （結論の頭部 " + nd.head + "）");

      console.log("\n  公理     " + (nd.axioms.length ? nd.axioms.join(", ") : "なし（公理非依存）")
        + (nd.usesSorry ? "   ★ sorry を含む" : ""));
      console.log("  尺度     |↓d| " + met.closure[n] + " / 深さ " + met.depth[n]
        + " / 極小仮定 " + (met.minimal ? met.minimal[n] : "未計算")
        + " / 節点 型 " + nd.typeSize + " 証明 " + nd.valueSize);
      console.log("  直接依存 型 " + nd.typeDeps.length + " · 値 " + nd.valueDeps.length
        + "     参照 主張 " + (idx.refType[n] || []).length + " · 証明 " + (idx.refValue[n] || []).length);

      const closure = G.reachable(n, idx.dep, 64);
      const mf = G.minimalAndFrontier(Object.keys(closure), idx.dep);
      console.log("  極小仮定 min(↓d)  " + mf.trueMinimal.length + " 件");
      for (const m of mf.trueMinimal) console.log("    " + m);

      /* 導出図。項に現れた定数を並べるのではなく、役割で分けて
         「前提 ─ 規則 ─ 結論」の推論図の形に置く。前提は実際に呼ばれた
         補題と公理だけで、語彙（定義・型）と骨組み（論理結合子・再帰子）は
         線の外に出す。読み手が確認したいのは前提だけなので。 */
      console.log(`\n  導出図（深さ ${TREE_DEPTH}。同じ宣言は初出のみ展開）`);
      const seen = new Set([n]);
      const figure = (m, depth, ind) => {
        const p = " ".repeat(ind);
        const parts = LDR.roles.split(m, S.state.nodes);
        const premises = [...parts.axiom, ...parts.lemma].filter((x) => !seen.has(x.name));
        for (const x of premises) seen.add(x.name);
        if (premises.length) {
          for (const x of premises) {
            const cx = S.state.nodes[x.name] || {};
            const role = LDR.roles.roleOf(x.name, cx);
            console.log(p + "  " + (role === "axiom" ? "★公理 " : "") + x.name
              + (cx.shape && sig.SHAPE[cx.shape] ? `   [${sig.SHAPE[cx.shape].ja}]` : ""));
            const c = cx.conclusion || cx.typeString || "";
            if (c) console.log(p + "      ⊢ " + wrap(c, ind + 8));
            if (depth > 1) figure(x.name, depth - 1, ind + 4);
          }
        } else {
          console.log(p + "  （前提となる補題はありません。定義そのもの、または骨組みだけで閉じています）");
        }
        const cm = S.state.nodes[m] || {};
        console.log(p + "  " + "═".repeat(Math.max(20, Math.min(80, 100 - ind))) + " " + m);
        console.log(p + "      ⊢ " + wrap(cm.conclusion || cm.typeString || "—", ind + 8));
        if (parts.vocab.length) console.log(p + "  語彙   " + wrap(parts.vocab.map((v) => v.name).join(", "), ind + 9));
        if (parts.frame.length) console.log(p + "  骨組み " + parts.frame.length + " 件: "
          + wrap(parts.frame.map((v) => v.name).join(", "), ind + 9));
      };
      figure(n, TREE_DEPTH, 4);
    }
  }
  console.log("\n" + "─".repeat(100));
  console.log(`${found} 件を表示しました。`);
  process.exit(0);
}

if (declQueries.length) inspectDecls(declQueries);

console.log("=== 読み込み ===");
const [tLoad] = ms(() => S.actions.loadText(text, { silent: true }));
console.log(`  loadText (解析 + 索引 + 既定中心 + 配置): ${tLoad.toFixed(1)} ms`);
{
  const all = Object.values(S.state.nodes);
  const internal = all.filter((n) => n.internal).length, external = all.filter((n) => n.external).length;
  console.log(`  対象の宣言 ${S.state.order.length} 件 / 内部補助 ${internal} 件 / 外部（一段＋範囲外の補完） ${external} 件 / ノード ${all.length} 件`);
}
ok(S.state.errors.length === 0, "JSONL に読めない行が無い");
console.log(`  既定中心: ${short(S.derived.center)}`);
ok(!!S.derived.center && !S.state.nodes[S.derived.center].external && !S.state.nodes[S.derived.center].internal,
   "既定中心が対象の宣言（外部でも内部補助でもない）");
ok((S.derived.declIdx.ref[S.derived.center] || []).length === 0, "既定中心が極大元（＝ライブラリの最終結果）");

console.log("\n=== 逆向き二分割の排他性 ===");
const idx = S.derived.declIdx;
let both = 0, refT = 0, refV = 0;
for (const n of Object.keys(S.state.nodes)) {
  const a = new Set(idx.refType[n] || []), b = idx.refValue[n] || [];
  refT += a.size; refV += b.length;
  for (const x of b) if (a.has(x)) both++;
}
console.log(`  refType の辺 ${refT} 本 / refValue の辺 ${refV} 本`);
ok(both === 0, "refType と refValue が交わらない", `重複 ${both} 件`);
let unionBad = 0;
for (const n of Object.keys(S.state.nodes)) {
  const a = (idx.refType[n] || []).length + (idx.refValue[n] || []).length;
  if (a !== (idx.refAll[n] || []).length) unionBad++;
}
ok(unionBad === 0, "refAll が二つの直和になっている", `ずれ ${unionBad} 件`);

/* 三つの錐が全て埋まる中心を選ぶ。極大元だと下側が空になり幾何の検査にならない。 */
let hub = null, hubScore = -1;
for (const n of S.state.order) {
  const t = (idx.refType[n] || []).length, v = (idx.refValue[n] || []).length;
  const d = (idx.dep[n] || []).length;
  if (t && v && d) { const s = Math.min(t, 40) + Math.min(v, 40) + Math.min(d, 40); if (s > hubScore) { hubScore = s; hub = n; } }
}
if (!hub) hub = S.derived.center;   // 三方向が揃う宣言が無いデータでも検査は続ける
console.log(`\n=== 二つの錐（中心 = ${short(hub)}）===`);
console.log(`  依存 ${(idx.dep[hub] || []).length} / 主張で参照 ${(idx.refType[hub] || []).length} / 証明で参照 ${(idx.refValue[hub] || []).length}`);
S.actions.navigate(hub);
S.actions.setRefFilter("all");

function geometry(label) {
  const d = S.derived;
  const yOf = (id) => Object.values(d.posAll).filter((p) => p.cone === id).map((p) => p.y);
  const min = (a) => a.reduce((x, y) => Math.min(x, y), Infinity);
  const max = (a) => a.reduce((x, y) => Math.max(x, y), -Infinity);
  const dep = yOf("dep"), rf = yOf("ref");
  console.log(`  [${label}] ノード ${Object.keys(d.posAll).length} / 辺 ${d.edges.length} / ` +
    d.cones.map((c) => `${c.id}:${Object.keys(c.pos).length}層${c.rings.length}`).join(" ") +
    " / 辺種 " + [...new Set(d.edges.map((e) => e.cone + "|" + e.kind))].sort().join(" "));
  ok(dep.length === 0 || max(dep) < 0, `[${label}] 依存錐が中心より上`, max(dep).toFixed(0));
  ok(rf.length === 0 || min(rf) > 0, `[${label}] 参照錐が中心より下`, min(rf).toFixed(0));
  const w = Object.values(d.posAll).filter((p) => p.cone !== "center").map((p) => p.w);
  ok(w.length === 0 || Math.max(...w) > 120, `[${label}] 薄い層のノードが潰れていない`, `最大幅 ${Math.max(...w, 0).toFixed(0)}`);

  const NH = S.NODE_H;
  const boxes = Object.entries(d.posAll).map(([n, p]) =>
    ({ n, c: p.cone, x0: p.x - p.w / 2, x1: p.x + p.w / 2, y0: p.y - NH / 2, y1: p.y + NH / 2 }));
  let hits = 0, sample = null;
  for (let i = 0; i < boxes.length; i++)
    for (let j = i + 1; j < boxes.length; j++) {
      const a = boxes[i], b = boxes[j];
      if (a.x0 < b.x1 && b.x0 < a.x1 && a.y0 < b.y1 && b.y0 < a.y1) {
        hits++; if (!sample) sample = `${a.c}/${short(a.n)} × ${b.c}/${short(b.n)}`;
      }
    }
  ok(hits === 0, `[${label}] ノード矩形が一つも重ならない`, hits ? `${hits} 組 例 ${sample}` : `${boxes.length} 個`);

  let bad = 0, cross = 0;
  for (const e of d.edges) {
    const a = d.posAll[e.u], b = d.posAll[e.v];
    if (!a || !b) { bad++; continue; }
    if (a.cone !== "center" && a.cone !== b.cone) cross++;
  }
  ok(bad === 0, `[${label}] 全ての辺の両端に座標がある`, bad);
  ok(cross === 0, `[${label}] 錐をまたぐ辺が無い`, cross);

  /* 浮いた節点が無いこと。置かれた節点（中心以外）は必ずどれかの辺の終点である。
     層上限で親が溢れた子、親が別の錐に取られた子は layoutCone が置かずに溢れへ数える。 */
  const heads = new Set(d.edges.map((e) => e.v));
  const floating = Object.keys(d.posAll).filter((n) => n !== d.center && !heads.has(n));
  ok(floating.length === 0, `[${label}] 親の無い節点（辺の終点でない節点）が無い`,
     floating.length ? `${floating.length} 件 例 ${floating.slice(0, 3).map(short).join(", ")}` : `${Object.keys(d.posAll).length - 1} 個`);
  const over = d.cones.map((c) => Object.values(c.overflow).reduce((a, b) => a + b, 0)).reduce((a, b) => a + b, 0);
  if (over) console.log(`  [${label}] 溢れ（層上限・親無しで置かなかった節点） ${over} 件`);

  /* 辺交差数(弦近似)。ベジエの実形状でなく P0→P3 の弦で数える参考値。
     README の交差削減の主張を測定可能にし、反復掃引(未実装)の導入判断の
     材料にする。端点を共有する辺同士は交差と数えない。合否は付けない。 */
  const segs = d.edges.map((e) => {
    const a = e.u === d.center ? { x: 0, y: 0 } : d.posAll[e.u];
    const b = d.posAll[e.v];
    return a && b ? { u: e.u, v: e.v, ax: a.x, ay: a.y, bx: b.x, by: b.y } : null;
  }).filter(Boolean);
  const ccw = (ax, ay, bx, by, cx, cy) => (by - ay) * (cx - ax) - (bx - ax) * (cy - ay);
  let crossings = 0;
  for (let i = 0; i < segs.length; i++)
    for (let j = i + 1; j < segs.length; j++) {
      const p = segs[i], q = segs[j];
      if (p.u === q.u || p.u === q.v || p.v === q.u || p.v === q.v) continue;
      const d1 = ccw(p.ax, p.ay, p.bx, p.by, q.ax, q.ay);
      const d2 = ccw(p.ax, p.ay, p.bx, p.by, q.bx, q.by);
      const d3 = ccw(q.ax, q.ay, q.bx, q.by, p.ax, p.ay);
      const d4 = ccw(q.ax, q.ay, q.bx, q.by, p.bx, p.by);
      if (d1 * d2 < 0 && d3 * d4 < 0) crossings++;
    }
  console.log(`  [${label}] 辺交差(弦近似) ${crossings} 組`);
}

for (const d of [1, 2, 3]) {
  const [t] = ms(() => S.actions.setBaseDepth(d));
  geometry(`深さ${d} ${t.toFixed(1)}ms`);
}

/* 右パネルの依存一覧は closure の昇順で並ぶ。その並びが線形拡大である
   （c が d の依存先なら m(c) < m(d)）ことを、定義からではなく実データの
   全辺で確かめる。破れる尺度で並べると、前提より先に結論が並ぶ。 */
console.log("\n=== 依存尺度の単調性 ===");
S.actions.setBaseDepth(1);
const met = S.metrics();
console.log(`  |↓d| は厳密に数えた: ${met.exact ? "はい（ビット集合）" : "いいえ（深さで代用）"}`);
{
  /* mono な尺度は狭義（m(依存先) < m(自分)）を要求し、破れ 0 を合否にする。
     minimal は広義（≤）までしか言えないので、破れの本数を参考として出すだけ。 */
  const idx = S.derived.declIdx;
  const keys = Object.keys(S.METRICS).filter((k) => met[k]);
  const violations = Object.fromEntries(keys.map((k) => [k, 0]));
  let edges = 0;
  for (const u of Object.keys(S.state.nodes)) {
    for (const v of idx.dep[u] || []) {
      edges++;
      for (const key of keys) {
        const mu = met[key][u], mv = met[key][v];
        const fine = S.METRICS[key].mono ? mv < mu : mv <= mu;
        if (!fine) violations[key]++;
      }
    }
  }
  console.log(`  辺 ${edges} 本について検査（狭義 < / 広義 ≤）`);
  for (const key of keys) {
    const { ja, mono } = S.METRICS[key];
    const v = violations[key];
    console.log(`    ${ja.padEnd(14)} 破れ ${String(v).padStart(6)} 本${mono ? "  ← 線形拡大（狭義）" : "  （広義・参考）"}`);
    if (mono) ok(v === 0, `${ja} は依存順序と両立する`, `破れ ${v}`);
  }
}

console.log("\n=== Lean 側から来た構造化データ ===");
{
  // 対象の宣言について。内部補助（_proof_* 等）は対象の証明の一部で、独立した宣言として数えない
  const rows = Object.values(S.state.nodes).filter((n) => !n.external && !n.internal);
  const withBinders = rows.filter((n) => n.binders && n.binders.length).length;
  const withConcl = rows.filter((n) => n.conclusion).length;
  const withLine = rows.filter((n) => n.line > 0).length;
  const withProof = rows.filter((n) => n.valueSize > 0).length;
  const thm = rows.filter((n) => n.kind === "theorem");
  console.log(`  束縛あり ${withBinders} / 結論あり ${withConcl} / 行あり ${withLine} / 証明項あり ${withProof}`);
  // 派生・断片(.ctorIdx / .noConfusionType / _proof_<i> 等)は自前の range を持たないことがある。
  // Lean 側は由来の行へ落とすが、旧形式のレポートも読めるよう、
  // 検査対象は「由来を持つものを除く全宣言」とする。
  const lineless = rows.filter((n) => n.line === 0);
  const linelessReal = lineless.filter((n) => !n.originRel);
  ok(linelessReal.length === 0, "派生・断片を除く全宣言に位置情報がある（実装順を再現できる）",
     linelessReal.length ? linelessReal.slice(0, 3).map((n) => short(n.name)).join(", ")
                         : `位置なしの派生・断片 ${lineless.length} 件は許容`);
  ok(thm.every((n) => n.valueSize > 0), "全定理の証明項を辿れている",
     `辿れていない定理 ${thm.filter((n) => n.valueSize === 0).length} 件`);
  const axCarrier = rows.filter((n) => n.axioms.length > 0).length;
  console.log(`  公理に依存する宣言 ${axCarrier} 件（証明項を辿った上での結果）`);
  const shapes = {};
  for (const n of rows) if (n.shape) shapes[n.shape] = (shapes[n.shape] || 0) + 1;
  console.log("  判定された主張の形:", Object.entries(shapes).map(([k, v]) => `${k} ${v}`).join(" / ") || "なし");
  const uncond = rows.filter((n) => n.numHyp === 0 && n.numInst === 0).length;
  const hered = rows.filter((n) => met.hered && met.hered[n.name]).length;
  console.log(`  無条件（仮定 0・インスタンス 0）      : ${uncond} / ${rows.length}`);
  console.log(`  無条件で閉じる（依存先も全て無条件）: ${hered} / ${rows.length}`);
  ok(hered <= uncond, "遺伝的無条件は無条件の部分集合になっている");
}

/* 法則の在庫。行が関係、列が法則。反射と推移が揃えば前順序、
   さらに反対称で半順序、反射・対称・推移で同値関係と読める。 */
console.log("\n=== 法則の在庫 ===");
{
  const inv = S.lawInventory();
  const JA = { refl: "反射", irrefl: "非反射", symm: "対称", trans: "推移", antisymm: "反対称",
               total: "全域", mono: "単調", comm: "可換", assoc: "結合", idem: "冪等",
               absorb: "吸収", distrib: "分配" };
  const cols = inv.LAWS;
  // 行は 関係 × 担い手の型。型が空なら多相な主張の行
  const label = (r) => short(r.rel) + (r.type ? " @ " + short(r.type) : "");
  const head = "  " + "関係 @ 担い手の型".padEnd(46) + cols.map((c) => JA[c].padStart(5)).join("") + "   判断";
  console.log(head);
  console.log("  " + "─".repeat(head.length - 2));
  let verdicts = 0;
  for (const r of inv.list) {
    const has = (l) => (r.laws[l] || []).length;
    // 判断は store.lawInventory が一元的に計算したものを読む(重複実装は乖離する)
    const v = r.verdict ? r.verdict.t : "";
    if (v) verdicts++;
    const cells = cols.map((c) => (has(c) ? String(has(c)) : "·").padStart(5)).join("");
    console.log("  " + label(r).padEnd(46) + cells + "   " + v);
  }
  console.log(`\n  ${inv.list.length} 個の関係・演算 / 法則 ${inv.list.reduce((a, r) => a + r.total, 0)} 件 / 構造が読めたもの ${verdicts} 件`);
  /* 在庫に入る条件は store.lawInventory と同じ（shape あり・命題・sorry 無し・対象の宣言）。
     条件を満たす宣言が一つも無いデータでは在庫が空になるのが正しい。 */
  const eligible = Object.values(S.state.nodes).filter(
    (n) => n.shape && n.shapeRel && n.isProp && !n.usesSorry && !n.external && !n.internal
        && n.originRel !== "facet" && n.originRel !== "part");
  if (eligible.length) ok(inv.list.length > 0, "法則の在庫を集計できた", `該当 ${eligible.length} 件`);
  else skip("法則の在庫を集計できた", "在庫に入る条件を満たす宣言が無いデータ(判定対象なし)");
  ok(inv.list.reduce((a, r) => a + r.total, 0) === eligible.length, "在庫の件数が条件を満たす宣言の数と一致する",
     `在庫 ${inv.list.reduce((a, r) => a + r.total, 0)} / 該当 ${eligible.length}`);
  const bad = inv.list.filter((r) => !r.rel || r.rel === "[anonymous]").length;
  ok(bad === 0, "全ての行に関係名が付いている", `名前なし ${bad} 件`);
  const keyDup = inv.list.length - new Set(inv.list.map((r) => r.key)).size;
  ok(keyDup === 0, "行の鍵（関係 @ 型）が一意", `重複 ${keyDup}`);
}

console.log("\n=== 操作の応答 ===");
S.actions.setBaseDepth(1);
const names = S.state.order;
const [tNav] = ms(() => S.actions.navigate(names[Math.floor(names.length / 2)]));
console.log(`  navigate: ${tNav.toFixed(1)} ms`);
const [tEdge] = ms(() => S.actions.setEdgeMode("type"));
console.log(`  型のみへ切替 (索引を組み直す): ${tEdge.toFixed(1)} ms`);
const [tEdge2] = ms(() => S.actions.setEdgeMode("all"));
console.log(`  型+値へ戻す (キャッシュ命中): ${tEdge2.toFixed(1)} ms`);
const [tGran] = ms(() => S.actions.setGranularity("module"));
console.log(`  モジュール粒度へ: ${tGran.toFixed(1)} ms / ノード ${Object.keys(S.derived.posAll).length}`);
S.actions.setGranularity("decl");
ok(tNav < 300 && tEdge < 400, "主要操作が即応の範囲");

/* 由来（成員・派生・断片）。Lean 側 originOf が環境の事実から決めた欄を、Web 側がどう使うかの検査。
   π: 由来の写像。手書きの宣言の上で恒等（レトラクション）。
     断片 part  → 由来に埋め戻す（到達可能性を保つ）
     派生 facet → 由来が閉じていれば、u → g を u → π(g) に畳み、経由 g を控える */
console.log("\n=== 由来（成員・派生・断片）===");
{
  const G = LDR.graph;
  const nodes = S.state.nodes;
  const own = Object.values(nodes).filter((n) => !n.external);
  const withOrigin = own.filter((n) => n.originRel);
  // 種類名に "constructor" があるので、prototype を持たない辞書で数える
  const byRel = Object.create(null);
  for (const n of withOrigin) byRel[n.originRel] = (byRel[n.originRel] || 0) + 1;
  const byKind = Object.create(null);
  for (const n of withOrigin) byKind[n.originKind] = (byKind[n.originKind] || 0) + 1;
  console.log(`  成員 ${byRel.member || 0} / 派生 ${byRel.facet || 0} / 断片 ${byRel.part || 0}`
    + (withOrigin.length ? ` / 種類: ${Object.entries(byKind).map(([k, v]) => `${k} ${v}`).join(" ")}` : ""));
  if (!withOrigin.length) {
    skip("由来の検査", "由来を持つ宣言が無いデータ（旧形式で推定も付かない、または構造体の無い対象）");
  } else {
    let missing = 0, notRetract = 0, modMismatch = 0;
    for (const n of withOrigin) {
      const o = nodes[n.origin];
      if (!o) { missing++; continue; }
      if (o.originRel === "facet" || o.originRel === "part") notRetract++;
      if (o.module !== n.module) modMismatch++;
    }
    ok(missing === 0, "由来はレポート内に存在する", `欠け ${missing}`);
    ok(notRetract === 0, "由来は派生・断片ではない（π はレトラクション）", `違反 ${notRetract}`);
    ok(modMismatch === 0, "由来と同じモジュールにある", `不一致 ${modMismatch}`);

    // 断片の埋め戻しが到達可能性を保つ（全由来を開いた有効グラフ = 断片だけを埋め戻したもの）
    const rawDep = S.derived.declIdx.dep;
    const effOpen = G.effectiveNodes(nodes, () => true);
    const effOpenDep = G.buildIndices(effOpen.nodes, "all").dep;
    const isPart = (n) => nodes[n] && nodes[n].originRel === "part" && nodes[n].origin && nodes[nodes[n].origin];
    const sampleU = S.state.order.filter((n) => !isPart(n)).slice(0, 120);
    let reachDiff = 0;
    for (const u of sampleU) {
      const a = new Set(Object.keys(G.reachable(u, rawDep, 64)).filter((x) => !isPart(x)));
      const b = new Set(Object.keys(G.reachable(u, effOpenDep, 64)));
      if (a.size !== b.size || [...a].some((x) => !b.has(x))) reachDiff++;
    }
    ok(reachDiff === 0, "断片の埋め戻しは到達可能性を保つ", `標本 ${sampleU.length} 件中 相違 ${reachDiff}`);

    // 畳み込みの健全性（全由来を閉じた有効グラフ）
    const effClosed = G.effectiveNodes(nodes, () => false);
    const effClosedDep = G.buildIndices(effClosed.nodes, "all").dep;
    const isFacet = (n) => nodes[n] && nodes[n].originRel === "facet" && nodes[n].origin && nodes[nodes[n].origin];
    /* 断片を通って届く依存（埋め戻し）。自分の断片には経由の札が付かない設計なので、
       検査では「内部が断片だけの経路で v に届く」ことを根拠と見なす（断片の由来は問わない。
       match の補助関数は別の宣言でも再利用されるため）。閉じた派生に届いたら由来へ。 */
    const ownPartReach = (u) => {
      const acc = new Set(), seen = new Set([u]), stack = [u];
      while (stack.length) {
        const x = stack.pop();
        for (const d of rawDep[x] || []) {
          if (seen.has(d)) continue;
          seen.add(d);
          if (isPart(d)) stack.push(d);
          else if (x !== u) acc.add(isFacet(d) ? nodes[d].origin : d);
        }
      }
      return acc;
    };
    let lostFold = 0, fakeEdge = 0, folded = 0;
    for (const u of Object.keys(effClosedDep)) {
      for (const g of rawDep[u] || []) {
        if (!isFacet(g)) continue;
        const o = nodes[g].origin;
        if (o === u) continue;
        folded++;
        const via = effClosed.via[u + " " + o] || [];
        if (!(effClosedDep[u] || []).includes(o) || !via.includes(g)) lostFold++;
      }
      let inlined = null;
      for (const v of effClosedDep[u] || []) {
        const direct = (rawDep[u] || []).includes(v);
        const via = effClosed.via[u + " " + v];
        if (direct || (via && via.length)) continue;
        if (!inlined) inlined = ownPartReach(u);
        if (!inlined.has(v)) fakeEdge++;
      }
    }
    ok(lostFold === 0, "派生への辺は由来への辺に畳まれ、経由が控えられる", `畳んだ辺 ${folded} / 欠け ${lostFold}`);
    ok(fakeEdge === 0, "畳んだグラフの辺は、元の辺・経由付きの辺・自分の断片を埋め戻した辺のいずれか", `根拠の無い辺 ${fakeEdge}`);
    ok(Object.keys(effClosedDep).every((n) => !isFacet(n)), "閉じた派生は節点として現れない");

    // 件数の整合
    const facetTotal = Object.values(S.derived.facetCount || {}).reduce((a, b) => a + b, 0);
    const facetNodes = Object.keys(nodes).filter(isFacet).length;
    ok(facetTotal === facetNodes, "由来ごとの派生の数の総和が派生の宣言数と一致する", `${facetTotal} / ${facetNodes}`);

    // 派生を中心にすると、その由来が強制的に開き、中心が描かれる。固定中は押しても閉じない（理由が返る）
    const facetCenter = Object.keys(nodes).find((n) => isFacet(n) && !nodes[n].external && (rawDep[n] || []).length > 0);
    if (facetCenter) {
      S.actions.navigate(facetCenter);
      const o = nodes[facetCenter].origin;
      ok(S.isClusterOpen(o) && S.isClusterForced(o), "派生を中心にすると由来が強制的に開く", short(facetCenter));
      ok(S.derived.center === facetCenter && Object.keys(S.derived.posAll).length > 1,
         "派生を中心にしても依存が描かれる", `${Object.keys(S.derived.posAll).length - 1} 節点`);
      const r = S.actions.toggleCluster(o);
      ok(r && r.ok === false && !!r.msg && S.isClusterOpen(o), "固定で開いている由来は押しても閉じず、理由が返る", r && r.msg);
      S.actions.navigate(S.derived.defaultCenter);
      ok(!S.isClusterForced(o) && !S.state.openClusters.has(o), "中心を移すと強制開放は解け、利用者の集合には残らない");
    } else {
      skip("派生を中心にすると由来が開く", "依存を持つ派生が無いデータ");
    }

    /* 「全て開く」は集合の全入れ／全消し。旗ではないので個別の開閉と干渉しない。
       全開 → 一つ閉じる → ☑ が外れる（以前は旗が勝って見た目が変わらなかった）。 */
    const origins = [...new Set(Object.keys(nodes).filter(isFacet).map((n) => nodes[n].origin))];
    S.actions.setOpenAll(true);
    ok(S.allFacetsOpen() && origins.every((o) => S.state.openClusters.has(o)), "全て開く = 派生を持つ全ての由来が集合に入る", `${origins.length} 由来`);
    S.actions.toggleCluster(origins[0]);
    ok(!S.allFacetsOpen() && !S.state.openClusters.has(origins[0]) && origins.slice(1).every((o) => S.isClusterOpen(o)),
       "全開中に一つ閉じると、その由来だけ閉じて ☑ が外れる", short(origins[0]));
    S.actions.setOpenAll(false);
    ok(!S.allFacetsOpen() && S.state.openClusters.size === 0, "全て畳む = 集合が空になる");

    // 中心から見える派生の数 k は、由来の派生の総数 n を超えない。札 +k はこれを出す
    const reach = S.derived.facetReach || {}, count = S.derived.facetCount || {};
    const over = Object.keys(reach).filter((o) => reach[o] > (count[o] || 0));
    ok(over.length === 0, "中心から見える派生の数は由来の派生の総数を超えない", over.length ? over.slice(0, 3).map(short).join(", ") : `${Object.keys(reach).length} 由来`);
  }
}

/* 経路が閉じた派生の中だけを通る場合。区間 [t, c] を表示用の商で取ると空になり、極小元を押しても
   何も起きなかった（`pair_inj` の `id` は `mk.inj` の証明の中にだけある。実測）。区間は元のグラフで
   取り、区間に含まれる派生の由来を強制的に開く。そのような (中心, 極小元) を探して検査する。 */
console.log("\n=== 経路表示と派生（閉じた派生の中だけを通る経路）===");
{
  const G = LDR.graph;
  const nodes = S.state.nodes;
  const rawDep = S.derived.declIdx.dep, rawRef = S.derived.declIdx.ref;
  const closed = G.buildIndices(G.effectiveNodes(nodes, () => false).nodes, "all");
  const isFacet = (n) => nodes[n] && nodes[n].originRel === "facet" && nodes[n].origin && nodes[nodes[n].origin];
  let found = null;
  outer: for (const c of S.state.order) {
    if (isFacet(c)) continue;                       // 中心が派生なら由来は既に開く。別の機構
    const down = Object.keys(G.reachable(c, rawDep, 64));
    const mf = G.minimalAndFrontier(down, rawDep);
    for (const t of mf.trueMinimal) {
      const raw = G.orderInterval(c, t, rawDep, rawRef, 64);
      const viaClosed = closed.dep[c] ? G.orderInterval(c, t, closed.dep, closed.ref, 64) : new Set();
      if (raw.size > 1 && viaClosed.size === 0 && [...raw].some(isFacet)) { found = { c, t, raw }; break outer; }
    }
  }
  if (!found) {
    skip("閉じた派生の中だけを通る経路でも強調が掛かる", "そのような (中心, 極小元) の組が無いデータ");
  } else {
    const { c, t, raw } = found;
    S.actions.navigate(c);
    S.actions.setTrace(t);
    const d = S.derived;
    console.log(`  中心 ${short(c)} → 極小元 ${short(t)}: 元のグラフの区間 ${raw.size} 節点（うち派生 ${[...raw].filter(isFacet).length}）`);
    ok(!!d.highlight && d.highlight.size === raw.size && d.traceUnreachable === null, "区間は元のグラフで取られ、空にならない");
    const facetOrigins = [...new Set([...raw].filter(isFacet).map((n) => nodes[n].origin))];
    ok(facetOrigins.every((o) => S.isClusterOpen(o) && S.isClusterForced(o)), "区間に含まれる派生の由来が強制的に開く", facetOrigins.map(short).join(", "));
    const isPart = (n) => nodes[n] && nodes[n].originRel === "part" && nodes[n].origin && nodes[nodes[n].origin];
    const want = [...raw].filter((n) => LDR.roles.roleOf(n, nodes[n]) !== "frame" && !isPart(n));
    const missing = want.filter((n) => !d.posAll[n] && n !== c);
    ok(missing.length === 0, "区間の節点（骨組み・断片を除く）が全て描画対象になる",
       missing.length ? `欠け ${missing.map(short).join(", ")}` : `${want.length} 節点`);
    const r = S.actions.toggleCluster(facetOrigins[0]);
    ok(r && r.ok === false && S.isClusterOpen(facetOrigins[0]), "経路表示中は区間の由来を閉じられない（理由が返る）");
    S.actions.setTrace(t);     // 解除
    ok(!S.isClusterForced(facetOrigins[0]) && S.state.openClusters.size === 0, "経路表示を解除すると強制開放も解け、集合には残らない");
    S.actions.navigate(S.derived.defaultCenter);
  }
}

console.log("\n=== 結論の分割（主結合子）とパッケージ ===");
{
  const sig = LDR.sig, P = LDR.pkg;
  const d1 = sig.decompose("a = a' ∧ b = b'");
  ok(d1.rel === "∧" && d1.lhs === "a = a'" && d1.rhs === "b = b'", "a = a' ∧ b = b' は ∧ で割る（= ではない）", `${d1.rel} | ${d1.lhs} | ${d1.rhs}`);
  const d2 = sig.decompose("(x = y) = (p ∧ q)");
  ok(d2.rel === "=" && d2.lhs === "x = y" && d2.rhs === "p ∧ q", "括弧で包まれた両辺は外側の = で割る", `${d2.rel} | ${d2.lhs} | ${d2.rhs}`);
  const d3 = sig.decompose("p ∨ q ↔ r");
  ok(d3.rel === "↔" && d3.lhs === "p ∨ q", "↔ は ∨ より弱い（主結合子）", `${d3.rel} | ${d3.lhs}`);
  const d4 = sig.decompose("¬a = b");
  ok(d4.rel === "¬" && d4.lhs === null, "¬a = b は ¬(a = b) なので中置では割らない");
  const d5 = sig.decompose("∃ x, f x = 0");
  ok(d5.lhs === null, "束縛で始まる結論は中置では割らない");
  ok(P.packageOf("Mathlib.Order.Defs") === "Mathlib" && P.packageOf("Init.Core") === "core" && P.packageOf("Lean.Meta.Basic") === "core"
     && P.packageOf("Cslib.Crypto.X") === "Cslib" && P.packageOf("(範囲外)") === "", "パッケージはモジュール名の先頭成分（core は一つ）");
  const u = P.docsUrl({ module: "Cslib.Crypto.Protocols.Commitment.Scheme" }, "Cslib.Crypto.Protocols.Commitment.Scheme.commitmentDist");
  ok(u === "https://api.cslib.io/docs/Cslib/Crypto/Protocols/Commitment/Scheme.html#Cslib.Crypto.Protocols.Commitment.Scheme.commitmentDist",
     "cslib の docs は doc-gen4 の規則で宣言ページへ直接", u);
  const u2 = P.docsUrl({ module: "Init.Core" }, "propext");
  ok(u2 === "https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext", "core の docs は mathlib4_docs", u2);
  ok(P.docsUrl({ module: "MyPkg.Foo" }, "MyPkg.Foo.bar") === null, "文書の無いパッケージには docs を出さない");
  const pk = {};
  for (const nd of Object.values(S.state.nodes)) { const p = P.packageOf(nd.module); if (p) pk[p] = (pk[p] || 0) + 1; }
  console.log("  パッケージ別の宣言数:", Object.entries(pk).map(([k, v]) => `${P.labelOf(k)} ${v}`).join(" / "));
}

console.log("\n=== 経路表示（順序区間 [t,d] = ↑t ∩ ↓d）===");
S.actions.navigate(S.derived.defaultCenter);
const tm = S.derived.trueMinimal || [];
console.log(`  極小元 ${tm.length} 件 / 下方閉集合 ${S.derived.fullDownSize} 件`);
if (tm.length) {
  /* 最も遠い極小元を選ぶ。深さ 1 の区間では「開いて見せる」機構が試されない。 */
  const far = tm.slice().sort((a, b) => (met.depth[b] || 0) - (met.depth[a] || 0))[0];
  const [tTrace] = ms(() => S.actions.setTrace(far));
  const hl = S.derived.highlight;
  console.log(`  ${short(far)} への経路: ${hl ? hl.size : 0} ノード / ${tTrace.toFixed(1)} ms`);
  ok(hl && hl.has(S.derived.center) && hl.has(far), "経路の両端が区間に入っている");
  /* 区間の節点は全て描画対象になる（開くだけでなく、層上限より優先して置く）。
     骨組みは既定で潰して通り抜け、断片は由来に埋め戻されるので、どちらも除いて検査する。 */
  const shown = Object.keys(S.derived.posAll);
  const isPartN = (n) => { const x = S.state.nodes[n]; return x && x.originRel === "part" && x.origin && S.state.nodes[x.origin]; };
  const want = hl ? [...hl].filter((n) => LDR.roles.roleOf(n, S.state.nodes[n]) !== "frame" && !isPartN(n)) : [];
  const missing = want.filter((n) => !S.derived.posAll[n]);
  ok(hl && missing.length === 0, "経路上の全節点（骨組み・断片を除く）が描画対象になる",
     missing.length ? `欠け ${missing.length} 例 ${missing.slice(0, 3).map(short).join(", ")}` : `${want.length} / 描画 ${shown.length}`);
  ok(S.derived.traceUnreachable === null, "到達可能な公理の経路表示が「到達不能」にならない");
  S.actions.setTrace(far);
}
/* 読み込んだ範囲に無い名前を求めたときは、全てを暗くせず「到達不能」として表に出す。 */
S.actions.setTrace("__ldr_no_such_decl__");
ok(S.derived.highlight === null && S.derived.traceUnreachable === "__ldr_no_such_decl__",
   "経路の無い対象では強調を掛けず traceUnreachable に名前が入る");
S.actions.setTrace("__ldr_no_such_decl__");

console.log("\n=== 探索履歴ツリー ===");
S.actions.clearHist();
for (const n of names.slice(0, 8)) S.actions.navigate(n);
S.actions.back(); S.actions.back();
ok(S.state.hist.order.length > 0, "履歴が記録される", S.state.hist.order.length);
// 分岐と系譜の検査には移動先が 2 件以上要る(宣言 1 件のデータでは作れない)
if (names.length >= 2) {
  const before = S.state.hist.order.length;
  S.actions.navigate(names[names.length - 1]);
  ok(S.state.hist.order.length === before + 1, "戻った先から分岐しても既存の枝が消えない");
} else {
  skip("戻った先から分岐しても既存の枝が消えない", "宣言 1 件のデータでは分岐を作れない");
}
for (let i = 0; i < 120; i++) S.actions.navigate(names[i % names.length]);
ok(S.state.hist.order.length <= 50, "履歴が 50 件で頭打ち", S.state.hist.order.length);
ok(!!S.histCur(), "頭打ち後も現在地が残る", S.histCur() && short(S.histCur().name));
if (names.length >= 2) {
  let depth = 0;
  for (let p = S.state.hist.curId; p; p = S.state.hist.nodes[p].parent) depth++;
  ok(depth > 1, "現在地の系譜が残っている", `深さ ${depth}`);
} else {
  skip("現在地の系譜が残っている", "宣言 1 件のデータでは系譜が長さ 1 になる");
}

console.log("\n=== ピン留め ===");
S.actions.setRefFilter("value");
const pin = S.actions.addPin("検査");
S.actions.setBaseDepth(3);
S.actions.setRefFilter("all");
S.actions.navigate(names[0]);
S.actions.applyPin(pin.id);
ok(S.centerName() === pin.snap.center && S.state.baseDepth === pin.snap.baseDepth
   && S.state.refFilter === "value", "ピンが中心・深さ・下錐の設定を復元する");
const round = S.actions.exportPins();
S.actions.setPins([]);
const r = S.actions.importPins(round);
ok(r.ok && S.state.pins.length === 1, "JSON 往復で復元できる", r.msg);

console.log(`\n${fail === 0 ? "全て通過" : fail + " 件が失敗"}`);
process.exit(fail === 0 ? 0 : 1);
