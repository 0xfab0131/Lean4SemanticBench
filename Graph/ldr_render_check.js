/* Node 上で DOM の代役を立て、panels.renderAll を実データで一周させる煙試験。
   目的: 右パネル（主語の統一・プレビューの再構成・docs 直接リンク）、中央の見出し（中心に固定）、
   一覧（固定の札）、絞り込み（全て開く）が例外なく組み立ち、期待する文言を含むこと。 */
const fs = require("fs"), path = require("path");
const JS = path.join(__dirname, "Web", "js");

function el(id) {
  const e = {
    id, innerHTML: "", textContent: "", value: "", disabled: false, open: false, scrollTop: 0, clientHeight: 400,
    dataset: {}, style: {}, _cls: new Set(),
    classList: { toggle(c, on) { if (on === undefined) on = !e._cls.has(c); on ? e._cls.add(c) : e._cls.delete(c); return on; },
                 add(c) { e._cls.add(c); }, remove(c) { e._cls.delete(c); }, contains(c) { return e._cls.has(c); } },
    addEventListener() {}, _q: {},
    querySelector(sel) { return e._q[sel] || (e._q[sel] = el(id + ":" + sel)); },
    querySelectorAll() { return []; },
  };
  return e;
}
const els = {};
global.window = {};
global.document = {
  getElementById: (id) => els[id] || (els[id] = el(id)),
  documentElement: el("html"),
  createElement: (t) => el("new:" + t),
};
global.requestAnimationFrame = (f) => { f(); return 0; };
for (const f of ["graph.js", "sig.js", "pkg.js", "roles.js", "store.js", "canvas.js", "panels.js", "report.js"]) require(path.join(JS, f));
const LDR = global.window.LDR, S = LDR.store, P = LDR.panels;

const src = process.argv[2] ? path.resolve(process.cwd(), process.argv[2]) : path.join(__dirname, "report.jsonl");
const text = fs.readFileSync(src, "utf8");
let fail = 0;
const ok = (c, label, extra) => { if (!c) fail++; console.log(`${c ? "  ok  " : " FAIL "} ${label}${extra !== undefined ? "  → " + extra : ""}`); };
const render = () => P.renderAll(S.state, S.derived);
const html = (id) => document.getElementById(id).innerHTML;

console.log(`対象: ${src}`);
S.actions.loadText(text, { silent: true });
document.getElementById("depTabs").dataset.tab = "prev";
S.refresh(true); render();
const cen = S.derived.center;
ok(html("inspector").includes("中心") && html("inspector").includes(cen), "中央の見出しは中心を名乗る", cen.split(".").slice(-1)[0]);
ok(html("depBody").includes("見ている宣言") && html("depBody").includes("導出図") && html("depBody").includes("依存先"), "プレビューに主語・導出図・依存先（パッケージ）がある");
ok(/data-keep="deriv"[^>]*>/.test(html("depBody")) && !/data-keep="deriv"[^>]*\sopen/.test(html("depBody")), "導出図は既定で畳まれている");

// 選択を変えると右パネルの主語が変わり、中央の見出しは中心のまま
const other = S.state.order.find((n) => n !== cen && !S.state.nodes[n].originRel);
S.actions.select(other); render();
ok(html("depBody").includes("選択") && html("depBody").includes(other) && html("inspector").includes(cen) && !html("inspector").includes(`>${other}<`),
   "選択を変えると右パネルの主語が変わり、中央の見出しは中心のまま", other.split(".").slice(-1)[0]);
document.getElementById("depTabs").dataset.tab = "type"; P.invalidate(); render();
ok(html("depBody").includes("見ている宣言") && html("depBody").includes(other), "依存タブも選択中の宣言について出す");
document.getElementById("depTabs").dataset.tab = "prev"; P.invalidate();
S.actions.setPreviewFollow(false); render();
ok(html("depBody").includes(cen) && html("depBody").includes("中心"), "中心固定なら中心を出す");
S.actions.setPreviewFollow(true);

// プレビューの履歴: 戻る／進むで見ている宣言が変わり、選択（グラフの経路）も追従する
S.actions.select(other);
const third = S.state.order.find((n) => n !== cen && n !== other && !S.state.nodes[n].originRel);
S.actions.select(third);
ok(S.state.previewHist.length >= 3 && S.state.previewHist[0] === cen && S.previewName() === third,
   "履歴は既定中心から始まり、見た宣言が順に積まれる", S.state.previewHist.map((x) => x.split(".").slice(-1)[0]).join(" › "));
S.actions.previewBack();
ok(S.previewName() === other && S.state.selected === other && S.state.pathFrom === other, "‹ で前に見た宣言へ戻り、選択も追従する");
S.actions.previewForward();
ok(S.previewName() === third && S.state.selected === third, "› で進む");
S.actions.preview(cen);
ok(S.previewName() === cen && S.state.selected === cen && S.state.previewFollow, "チップを押すとその宣言を見て選択にする（固定中でも追従へ）");
render();
ok(html("depBody").includes("data-pback") && html("depBody").includes("data-pfwd") && /\d+\/\d+/.test(html("depBody")), "頭に ‹ › と位置が出る");

// 原文・束縛の記法
const withSrc = S.state.order.map((n) => S.state.nodes[n]).find((n) => n.source);
if (withSrc) {
  S.actions.select(withSrc.name); render();
  // 原文は色付けの span を挟んで出すので、タグを剥がした文字列で先頭行を比べる（行番号の列も付く）
  const txt = html("depBody").replace(/<[^>]+>/g, "").replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&").replace(/&quot;/g, "\"");
  const first = withSrc.source.split("\n")[0].trim().slice(0, 24);
  ok(html("depBody").includes("原文") && txt.includes(first) && html("depBody").includes(`class="no">${withSrc.line}<`),
     "原文はソースの行そのものを、開始行からの行番号付きで出す", `${withSrc.line}: ${first}`);
} else console.log("  skip  原文（この形式のレポートには原文が無い）");
const withInst = S.state.order.map((n) => S.state.nodes[n]).find((n) => (n.binders || []).some((b) => b.kind === "inst"));
if (withInst) {
  S.actions.select(withInst.name); render();
  ok(!/_hyg|_@\./.test(html("depBody").split("導出図")[0]), "束縛に衛生名が出ない");
  ok(html("depBody").includes("[</span>"), "インスタンス束縛は [C α] の記法");
}
S.actions.select(other);

// 外部の宣言: docs は宣言ページへ直接、パッケージの札
const ext = Object.values(S.state.nodes).find((n) => n.external && LDR.pkg.docsUrl(n, n.name) && !LDR.pkg.docsUrl(n, n.name).includes("search"));
if (ext) {
  S.actions.select(ext.name); render();
  const b = html("depBody");
  const pkgLabel = LDR.pkg.labelOf(LDR.pkg.packageOf(ext.module));
  ok(b.includes(LDR.pkg.docsUrl(ext, ext.name).replace(/&/g, "&amp;")) && b.includes(`📘 ${pkgLabel} docs`),
     "外部の宣言の docs は宣言ページへ直接、文言にパッケージ名", `${pkgLabel}: ${LDR.pkg.docsUrl(ext, ext.name)}`);
  ok(b.includes(LDR.pkg.labelOf(LDR.pkg.packageOf(ext.module))), "外部の宣言にパッケージの札が付く", LDR.pkg.packageOf(ext.module));
} else console.log("  skip  外部の宣言の docs（文書を持つ外部の宣言が無い）");
const tgtDocs = S.state.order.map((n) => S.state.nodes[n]).find((n) => LDR.pkg.docsUrl(n, n.name));
if (tgtDocs) {
  S.actions.select(tgtDocs.name); render();
  ok(html("depBody").includes(LDR.pkg.docsUrl(tgtDocs, tgtDocs.name)), "対象の宣言でも文書があれば直接リンク", LDR.pkg.docsUrl(tgtDocs, tgtDocs.name));
}

// 一覧: 全て開く → 固定の札・件数
S.actions.navigate(cen); P.invalidate(); render();
const lc = document.getElementById("listCount").textContent;
const filters = html("listFilters");
ok(/\d+ 件/.test(lc), "一覧の件数", lc);
if (filters.includes("openall")) {
  S.actions.toggleOpenAll(); render();
  ok(html("listFilters").includes("☑"), "全て開くと ☑ になる");
  S.actions.toggleOpenAll(); render();
  ok(html("listFilters").includes("☐"), "全て畳むと ☐ に戻る");
}
// 派生を中心に: 一覧の小枝に「固定」
const facet = Object.keys(S.state.nodes).find((n) => { const x = S.state.nodes[n]; return x.originRel === "facet" && !x.external && S.state.nodes[x.origin] && !S.state.nodes[x.origin].internal; });
if (facet) {
  S.actions.navigate(facet); render();
  ok(html("inspector").includes("固定") || html("depBody").includes("固定"), "派生を中心にすると「固定」の表示が出る", facet.split(".").slice(-2).join("."));
}
// 極小元: 到達不能なら details が開く
S.actions.navigate(cen); S.actions.setTrace("__no_such__"); render();
ok(document.getElementById("minimalWrap").open === true && html("minimalBox").includes("ありません"), "到達不能の通知で極小元の区画が開く");
S.actions.setTrace("__no_such__");
// 束ね: パッケージ
S.actions.setGroupBy("package"); render();
ok(Object.keys(S.derived.posAll).length > 1, "束ね=パッケージでも配置できる", Object.keys(S.derived.posAll).length + " 節点");

// レポート（Markdown）。中心・選択・極小元の三種が組み立ち、章が揃う
{
  const R = LDR.report;
  S.actions.navigate(cen);
  const rc = R.build("center", { sections: R.ALL, depth: 2 });
  const isPropCen = !!S.state.nodes[cen].isProp;
  ok(rc.ok && rc.text.startsWith("# ") && [isPropCen ? "## 主張" : "## 定義", "## 型依存", "## 値依存", "## 公理の由来", isPropCen ? "## 導出図" : "## 構成図", "## 極小元", "## 主張で参照", "## 計量", "## 来歴"].every((h) => rc.text.includes(h)),
     "中心のレポートに全ての章がある（命題なら導出図、定義なら構成図）", `${rc.text.split("\n").length} 行`);
  ok(!rc.text.includes("## 経路") && !rc.text.includes("## 注記"), "中心のレポートに経路の章は無く、注記は選ばない限り入らない");
  const rn = R.build("center", { sections: ["claim", "notes"], fullNames: false });
  ok(rn.text.includes("## 注記") && !rn.text.includes("## 型依存"), "注記は選んだときだけ末尾に入る");
  const endsWithNote = (t) => t.trimEnd().endsWith("整理する為の材料を提供します。");
  ok(endsWithNote(rc.text) && endsWithNote(rn.text) && rn.text.indexOf("※上記は") > rn.text.indexOf("## 注記"), "但し書きは章の選択に関わらず最後に置かれる");
  const cenNd = S.state.nodes[cen];
  if (cenNd.axioms.length) {
    ok(rc.text.includes(`### \`${cenNd.axioms[0]}\``) && /主張（型）の依存|証明（値）にだけ入っている/.test(rc.text), "公理ごとに主張か証明かの判定が出る", cenNd.axioms.join(", "));
  }
  const srcOk = !S.state.nodes[cen].source || rc.text.includes("```lean");
  ok(srcOk, "原文があれば lean ブロックで入る");
  /* Mermaid の図。既定で付き、記法は一度だけ、辺の端点は宣言済みの節点、ラベルの中に生の " < > # が無い
     （Mermaid の構文に反する図は描画で落ちるので、文章版と同じ事実を持たない）。外せば一つも出ない。 */
  const blocks = (t) => { const r = []; const re = /```mermaid\n([\s\S]*?)```/g; let m; while ((m = re.exec(t))) r.push(m[1]); return r; };
  const checkBlocks = (t) => {
    const bs = blocks(t); const bad = [];
    for (const b of bs) {
      const lines = b.split("\n");
      if (lines[0] !== "flowchart BT") bad.push("向き: " + lines[0]);
      const declared = new Set();
      for (const l of lines) { const m = l.match(/^\s*(n\d+)(\{\{|\[\[|\[\/|\(\[|\[)"/); if (m) declared.add(m[1]); }
      for (const l of lines) {
        const m = l.match(/^\s*(n\d+) (?:-->|-\.->|==>|-- "[^"]*" -->|-\. "[^"]*" \.->|== "[^"]*" ==>) (n\d+)$/);
        if (m && !(declared.has(m[1]) && declared.has(m[2]))) bad.push("未宣言の端点: " + l.trim());
      }
      for (const q of b.matchAll(/"([^"]*)"/g)) if (/[<>]|#(?!(35|quot|lt|gt);)/.test(q[1])) bad.push("生の記号: " + q[1]);
    }
    return { n: bs.length, bad };
  };
  const mb = checkBlocks(rc.text);
  ok(mb.n >= 2 && !mb.bad.length, "中心のレポートの付録に Mermaid の図（公理の流入・境界…）が付き、構文の約束を守る", `${mb.n} 図${mb.bad.length ? " / " + mb.bad.slice(0, 3).join("; ") : ""}`);
  const iApp = rc.text.indexOf("## 付録: 図");
  ok((rc.text.match(/## 付録: 図/g) || []).length === 1 && iApp > rc.text.indexOf("## 来歴") && rc.text.indexOf("### 記法") > iApp && rc.text.indexOf("### 記法") < rc.text.indexOf("```mermaid"),
     "図は本文に挟まず末尾の付録に集め、記法は付録の頭に一度だけ");
  ok(!rc.text.slice(0, iApp).includes("```mermaid"), "本文（付録より前）に Mermaid は一つも無い");
  if (cenNd.axioms.length) ok(rc.text.includes("公理の流入（") && (rc.text.match(/### 図 \d+: 公理の流入/g) || []).length === 1 && /\[[PCQ!S ]+\]"/.test(rc.text),
     "公理の流入は公理ごとに分けず一つの図で、節点の札に持つ公理を書く", cenNd.axioms.map((a) => a.split(".").pop()).join(" "));
  const rcNo = R.build("center", { sections: R.ALL.filter((s) => s !== "figures"), depth: 2 });
  ok(!rcNo.text.includes("```mermaid") && !rcNo.text.includes("付録: 図"), "章「付録: 図」を外せば Mermaid も記法も出ない");
  if (process.env.LDR_DUMP) { fs.mkdirSync(process.env.LDR_DUMP, { recursive: true }); fs.writeFileSync(path.join(process.env.LDR_DUMP, "center.md"), rc.text); }
  const rs0 = R.build("selected", { sections: R.ALL, depth: 1 });
  ok(!rs0.ok && !!rs0.msg, "選択が無ければ理由を返す", rs0.msg);
  const dep1 = S.derived.declIdx.dep[cen][0];
  S.actions.select(dep1);
  const rs = R.build("selected", { sections: ["claim", "path", "type", "figures"], depth: 1 });
  ok(rs.ok && rs.text.includes("## 経路") && rs.text.includes("一本の道筋") && rs.text.includes("## 型依存") && !rs.text.includes("## 値依存"),
     "選択のレポートに経路（区間・一本の道筋）が入り、選んだ章だけが出る", LDR.sig.shortName(dep1));
  const mp = checkBlocks(rs.text);
  ok(mp.n === 1 && !mp.bad.length && ((rs.text.includes("subgraph") && rs.text.includes("Hasse 図")) || rs.text.includes("最短の道筋だけ")) && rs.text.includes("==>"),
     "経路の図は層の囲みの Hasse 図（または大きければ道筋だけ）で、最短の道筋は太線", mp.bad.slice(0, 3).join("; "));
  if (process.env.LDR_DUMP) fs.writeFileSync(path.join(process.env.LDR_DUMP, "selected.md"), rs.text);
  const tm = S.derived.trueMinimal[0];
  const rm0 = R.build("minimal", { sections: R.ALL });
  ok(!rm0.ok, "極小元が選ばれていなければ理由を返す");
  if (tm) {
    S.actions.setTrace(tm);
    const rm = R.build("minimal", { sections: ["claim", "path", "refs", "figures"], depth: 1 });
    ok(rm.ok && rm.text.includes("## 経路") && rm.text.includes("## 主張で参照"), "極小元のレポートに経路と参照が入る", LDR.sig.shortName(tm));
    const mm = checkBlocks(rm.text);
    ok(mm.n === 1 && !mm.bad.length, "極小元のレポートの経路にも図が付く", mm.bad.slice(0, 3).join("; "));
    if (process.env.LDR_DUMP) fs.writeFileSync(path.join(process.env.LDR_DUMP, "minimal.md"), rm.text);
    S.actions.setTrace(tm);
  }
}
console.log(fail ? `${fail} 件が失敗` : "全て通過");
process.exit(fail ? 1 : 0);
