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
for (const f of ["graph.js", "sig.js", "pkg.js", "roles.js", "store.js", "canvas.js", "panels.js"]) require(path.join(JS, f));
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
console.log(fail ? `${fail} 件が失敗` : "全て通過");
process.exit(fail ? 1 : 0);
