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
        + " / 極小仮定 " + met.minimal[n] + " / 節点 型 " + nd.typeSize + " 証明 " + nd.valueSize);
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
console.log(`  宣言 ${S.state.order.length} 件 / ノード ${Object.keys(S.state.nodes).length} 件（範囲外を含む）`);
ok(S.state.errors.length === 0, "JSONL に読めない行が無い");
console.log(`  既定中心: ${short(S.derived.center)}`);
ok(!!S.derived.center && !S.state.nodes[S.derived.center].external, "既定中心がレポート内の宣言");
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

/* 依存の尺度が「依存の少ない順」として使えるかを、定義から確かめる。
   c が d の依存先なら m(c) < m(d) が要る。これが破れる尺度で並べると、
   前提より先に結論が並ぶので、読む順序として機能しない。 */
console.log("\n=== 依存尺度の単調性 ===");
S.actions.setBaseDepth(1);
const met = S.metrics();
console.log(`  |↓d| は厳密に数えた: ${met.exact ? "はい（ビット集合）" : "いいえ（深さで代用）"}`);
{
  const idx = S.derived.declIdx;
  const violations = {};
  for (const key of ["closure", "depth", "minimal", "direct", "refs", "size"]) violations[key] = 0;
  let edges = 0;
  for (const u of Object.keys(S.state.nodes)) {
    for (const v of idx.dep[u] || []) {
      edges++;
      for (const key of Object.keys(violations)) {
        const mu = met[key][u], mv = met[key][v];
        if (!(mv < mu)) violations[key]++;
      }
    }
  }
  console.log(`  辺 ${edges} 本について m(依存先) < m(自分) を検査`);
  for (const [key, v] of Object.entries(violations)) {
    const mono = S.METRICS[key].mono;
    const pct = ((v / edges) * 100).toFixed(1);
    console.log(`    ${S.METRICS[key].ja.padEnd(14)} 破れ ${String(v).padStart(6)} 本 (${pct}%)${mono ? "  ← 線形拡大" : ""}`);
    if (mono) ok(v === 0, `${S.METRICS[key].ja} は依存順序と両立する`, `破れ ${v}`);
  }
  // 負の対照実験: 十分な辺があれば破れが必ず観測されるはず。
  // 小規模データでは破れ自体が作れないので判定しない。
  if (edges >= 30) {
    ok(violations.direct > 0, "直接依存数は依存順序と両立しない（従来の並び順の欠陥）", `破れ ${violations.direct} 本`);
  } else {
    skip("直接依存数は依存順序と両立しない（負の対照）", `辺 ${edges} 本の小規模データでは判定不能`);
  }
}

console.log("\n=== Lean 側から来た構造化データ ===");
{
  const rows = Object.values(S.state.nodes).filter((n) => !n.external);
  const withBinders = rows.filter((n) => n.binders && n.binders.length).length;
  const withConcl = rows.filter((n) => n.conclusion).length;
  const withLine = rows.filter((n) => n.line > 0).length;
  const withProof = rows.filter((n) => n.valueSize > 0).length;
  const thm = rows.filter((n) => n.kind === "theorem");
  console.log(`  束縛あり ${withBinders} / 結論あり ${withConcl} / 行あり ${withLine} / 証明項あり ${withProof}`);
  // 生成宣言(.ctorIdx / .noConfusionType 等)は自前の range を持たないことがある。
  // Lean 側は親の行へフォールバックするが、旧形式のレポートも読めるよう、
  // 検査対象は「生成物(骨組み)を除く全宣言」とする。
  const lineless = rows.filter((n) => n.line === 0);
  const linelessReal = lineless.filter((n) => !LDR.roles.isFrameName(n.name));
  ok(linelessReal.length === 0, "生成物を除く全宣言に位置情報がある（実装順を再現できる）",
     linelessReal.length ? linelessReal.slice(0, 3).map((n) => short(n.name)).join(", ")
                         : `位置なしの生成物 ${lineless.length} 件は許容`);
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
  const head = "  " + "関係".padEnd(46) + cols.map((c) => JA[c].padStart(5)).join("") + "   判断";
  console.log(head);
  console.log("  " + "─".repeat(head.length - 2));
  let verdicts = 0;
  for (const r of inv.list) {
    const has = (l) => (r.laws[l] || []).length;
    // 判断は store.lawInventory が一元的に計算したものを読む(重複実装は乖離する)
    const v = r.verdict ? r.verdict.t : "";
    if (v) verdicts++;
    const cells = cols.map((c) => (has(c) ? String(has(c)) : "·").padStart(5)).join("");
    console.log("  " + short(r.rel).padEnd(46) + cells + "   " + v);
  }
  console.log(`\n  ${inv.list.length} 個の関係・演算 / 法則 ${inv.list.reduce((a, r) => a + r.total, 0)} 件 / 構造が読めたもの ${verdicts} 件`);
  // shape 付きの宣言が一つも無いデータ(法則の形の定理を含まない対象)では
  // 在庫が空になるのが正しい。集計機構の検査は shape があるときだけ意味を持つ。
  const anyShape = Object.values(S.state.nodes).some((n) => n.shape);
  if (anyShape) ok(inv.list.length > 0, "法則の在庫を集計できた");
  else skip("法則の在庫を集計できた", "shape 付き宣言が無いデータ(判定対象なし)");
  const bad = inv.list.filter((r) => !r.rel || r.rel === "[anonymous]").length;
  ok(bad === 0, "全ての行に関係名が付いている", `名前なし ${bad} 件`);
}

/* 球面モード。部分グラフごとに扇をまるごと与えるので、
   同じ扇を共有していたときより一区画あたりのノードが大きく取れるはず。 */
console.log("\n=== 球面モード（部分グラフごとの扇）===");
{
  /* 区画分割(可視ノードが PIN_MAX を超える錐)を実測するため、
     深さ 2 の依存錐が最大の中心を選ぶ。三方向の均衡で選んだ hub は
     小さくなりがちで、分割が発火しないままになる。 */
  let bigHub = hub, bigN = 0;
  for (const n of S.state.order) {
    const size = Object.keys(LDR.graph.reachable(n, S.derived.declIdx.dep, 2)).length;
    if (size > bigN) { bigN = size; bigHub = n; }
  }
  console.log(`  中心 = ${short(bigHub)}（深さ 2 の依存錐 ${bigN} ノード）`);
  S.actions.navigate(bigHub);
  S.actions.setBaseDepth(2);
  const flatW = Object.values(S.derived.posAll).filter((p) => p.cone !== "center").map((p) => p.w);
  const flatAvg = flatW.length ? flatW.reduce((a, b) => a + b, 0) / flatW.length : 0;
  const [t3] = ms(() => S.actions.toggleView3d());
  const d = S.derived;
  const w3 = [];
  for (const s of d.sectors) for (const pt of s.parts) for (const p of Object.values(pt.pos)) w3.push(p.w);
  const avg3 = w3.length ? w3.reduce((a, b) => a + b, 0) / w3.length : 0;
  const pinnedCount = (d.pinned || []).reduce((a, pt) => a + Object.keys(pt.pos).length, 0);
  console.log(`  回す錐 ${d.rotatingCone} / 区画 ${d.sectors.length} / ノード ${w3.length}`
    + ` / 固定側 ${pinnedCount} 件 / 再計算 ${t3.toFixed(1)} ms`);
  console.log(`  ノードの平均幅  平面 ${flatAvg.toFixed(0)} px → 球面 ${avg3.toFixed(0)} px`);
  for (const s of d.sectors) {
    const per = s.parts.map((pt) => `${pt.coneId}:${Object.keys(pt.pos).length}`).join(" ");
    console.log(`    ${String(s.index + 1).padStart(2)}/${s.of}  `
      + short(s.key).padEnd(34) + ` 重さ ${String(s.weight).padStart(4)}  ${per}`);
  }
  if (d.sectors.length === 0) {
    // 分割する規模が無い(全ての錐が PIN_MAX 以下)ときは、
    // 「回す錐なし・全ノードが固定表示」が仕様上の正しい挙動。
    ok(d.rotatingCone === null, "小規模データでは回す錐が無い（固定表示のみ）");
    ok(pinnedCount > 0, "全ノードが固定側に表示されている", `固定 ${pinnedCount} 件`);
    skip("区画分割の幾何（等分・総和 2π・跨ぎ辺なし 等）", "分割が発生しない規模のデータ");
  } else {
    ok(d.sectors.length <= 11, "区画が増えすぎない（小さい群は「その他」に束ねる）", d.sectors.length);
    ok(avg3 >= flatAvg, "一区画あたりの表示幅が平面モード以上になっている");
    ok(d.sectors.every((s) => s.parts.length > 0), "空の区画が無い");
    // 経度は等分。回す角度が均等でないと、狙った区画に止められない。
    const spans = [...new Set(d.sectors.map((s) => s.span.toFixed(9)))];
    ok(spans.length === 1, "経度が等分になっている", spans.join(" / "));
    const lonSum = d.sectors.reduce((a, s) => a + s.span, 0);
    ok(Math.abs(lonSum - 2 * Math.PI) < 1e-9, "経度の総和が 2π ちょうど", lonSum.toFixed(6));
    // 薄い錐は分割せず常に出す。片側が空になる区画を作らない。
    ok(pinnedCount > 0 || d.sectors.every((s) => s.parts.length),
       "薄い側の錐は固定表示になっている", `固定 ${pinnedCount} 件`);
    ok(d.sectors.every((s) => s.coneId === d.rotatingCone), "区画は回す側の錐だけから作られている");
    // 送りが一周して戻ること
    const i0 = S.frontSectorIndex();
    for (let i = 0; i < d.sectors.length; i++) S.actions.spinStep(1);
    ok(S.frontSectorIndex() === i0, "一周すると元の区画に戻る", `${i0} → ${S.frontSectorIndex()}`);
    let cross = 0;
    for (const s of d.sectors) {
      for (const pt of s.parts) {
        const own = new Set(Object.keys(pt.pos));
        for (const e of pt.edges) if (e.u !== d.center && (!own.has(e.u) || !own.has(e.v))) cross++;
      }
    }
    ok(cross === 0, "区画をまたぐ辺が無い", cross);
    /* clopen 欠損: 区画が「外と依存し合わない部分理論」(↓ と ↑ の両方で閉じた
       clopen 集合)からどれだけ離れているか。表示は跨ぎ辺を張らないが、
       分割の真の商品質は元グラフでの区画間依存辺(境界辺)の本数で測れる。
       0 なら各区画は clopen(=連結成分の和)。情報のみで合否は付けない。 */
    const sectorOf = {};
    for (const s of d.sectors)
      for (const pt of s.parts)
        for (const n2 of Object.keys(pt.pos)) sectorOf[n2] = s.id;
    let clopenDefect = 0;
    for (const u of Object.keys(sectorOf))
      for (const v2 of idx.dep[u] || [])
        if (sectorOf[v2] && sectorOf[v2] !== sectorOf[u]) clopenDefect++;
    console.log(`  clopen 欠損（区画間の依存辺） ${clopenDefect} 本`);
  }
  S.actions.toggleView3d();
  S.actions.setBaseDepth(1);
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

console.log("\n=== 経路表示（順序区間 [t,d] = ↑t ∩ ↓d）===");
S.actions.navigate(S.derived.defaultCenter);
const tm = S.derived.trueMinimal || [];
console.log(`  極小元 ${tm.length} 件 / 下方閉集合 ${S.derived.fullDownSize} 件`);
if (tm.length) {
  const [tTrace] = ms(() => S.actions.setTrace(tm[0]));
  const hl = S.derived.highlight;
  console.log(`  ${short(tm[0])} への経路: ${hl ? hl.size : 0} ノード / ${tTrace.toFixed(1)} ms`);
  ok(hl && hl.has(S.derived.center) && hl.has(tm[0]), "経路の両端が区間に入っている");
  ok(Object.keys(S.derived.posAll).some((n) => hl.has(n)), "経路が実際に開かれて描画対象になる");
  S.actions.setTrace(tm[0]);
}

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
