/* ============================================================
   js/panels.js — DOM 側の UI
   グラフは大域的な形を、リストは精密な走査と監査を担当する。
   両者は競合ではなく補完関係にある。

   描画は全て「鍵が変わったときだけ」に落としてある。ホバーのたびに
   数千行を組み直すと、探索が重くて比較にならない。
   宣言一覧は仮想化してあり、DOM に載るのは見えている 40 行前後だけ。
   ============================================================ */
(function (LDR) {
  "use strict";
  const S = LDR.store;

  const KIND = {
    axiom:       { c: "#EA580C", ja: "公理" },
    theorem:     { c: "#6366F1", ja: "定理" },
    def:         { c: "#0D9488", ja: "定義" },
    inductive:   { c: "#CA8A04", ja: "帰納型" },
    constructor: { c: "#CA8A04", ja: "構成子" },
    recursor:    { c: "#DB2777", ja: "再帰子" },
    opaque:      { c: "#78716C", ja: "opaque" },
    quot:        { c: "#78716C", ja: "quot" },
    external:    { c: "#A8A29E", ja: "範囲外" },
    unknown:     { c: "#A8A29E", ja: "不明" },
  };
  const kinfo = (k) => KIND[k] || KIND.unknown;

  const $ = (id) => document.getElementById(id);
  const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
  const dot = (kind, size) =>
    `<span class="inline-block rounded-full shrink-0" style="width:${size || 7}px;height:${size || 7}px;background:${kinfo(kind).c}"></span>`;

  /* 鍵が同じなら組み直さない */
  const memo = {};
  const once = (id, k, fn) => { if (memo[id] === k) return; memo[id] = k; fn(); };

  /* ================= 宣言一覧（仮想化） =================

     見えている約 40 行だけを絶対配置で描く。行の高さは固定 ROW_H。

     入れ子はガイド線で示す。字下げだけでは三段の深さが同じ位置に見える。
     線は「行ごとの部品」として描く（行をまたぐ DOM 要素は仮想化と両立しない）。
     行の高さが固定なので、隣り合う行の縦線は隙間なく連なって見える。
       列 k の x は colX(k)。深さ D の行は、列 0..D-2 に祖先の縦線（その枝に兄弟が
       続くときだけ）、列 D-1 に肘（兄弟が続けば ├、最後なら └）を描く。
     名前空間の枝には名前から決めた色相のレールを付け、その枝の線も同じ色相にする。
     中心または選択中の宣言を含む枝の線は藍にする（畳んだ枝の藍の点と同じ意味）。

     先頭に見えている行の祖先（枝の見出し）は、一覧の上端に固定して重ねる。
     長い枝の途中で「いまどの枝の中か」を文字でも示す。 */
  const ROW_H = 29;
  const UNIT = 14;                              // 一段の字下げ
  const colX = (k) => 8 + k * UNIT;             // 列 k のガイド線の x（見出しの ▾ の中央）
  const V = { host: null, win: null, spacer: null, sticky: null, rows: [], top: 0, raf: 0 };

  function vmount() {
    const host = $("declList");
    if (V.host === host) return;
    V.host = host;
    host.innerHTML = '<div data-vsticky style="position:sticky;top:0;height:0;z-index:5">'
                   +   '<div data-vstickyin style="position:absolute;left:0;right:0;top:0;padding:0 6px"></div></div>'
                   + '<div data-vspacer style="width:1px"></div>'
                   + '<div data-vwin style="position:absolute;left:0;right:0;top:0;padding:0 6px"></div>';
    V.spacer = host.querySelector("[data-vspacer]");
    V.win = host.querySelector("[data-vwin]");
    V.sticky = host.querySelector("[data-vstickyin]");
    host.addEventListener("scroll", () => {
      if (V.raf) return;
      V.raf = requestAnimationFrame(() => { V.raf = 0; vpaint(); });
    }, { passive: true });
    // 固定した見出しを押すと、その見出しの行まで戻る
    host.addEventListener("click", (e) => {
      const j = e.target.closest("[data-jump]");
      if (!j || e.target.closest("[data-tree]") || e.target.closest("[data-cluster]")) return;
      V.host.scrollTop = (+j.dataset.jump) * ROW_H;
      vpaint();
    });
  }

  function vsetRows(rows) {
    vmount();
    V.rows = rows;
    V.spacer.style.height = rows.length * ROW_H + "px";
    if (V.host.scrollTop > rows.length * ROW_H) V.host.scrollTop = 0;
    vpaint();
  }

  function vpaint() {
    if (!V.win) return;
    const h = V.host.clientHeight || 400;
    const first = Math.min(V.rows.length - 1, Math.max(0, Math.floor(V.host.scrollTop / ROW_H)));
    const start = Math.max(0, first - 6);
    const end = Math.min(V.rows.length, Math.ceil((V.host.scrollTop + h) / ROW_H) + 6);
    V.win.style.transform = `translateY(${start * ROW_H}px)`;
    V.win.innerHTML = V.rows.slice(start, end).map((r) => r.html).join("");
    // 先頭行の祖先の見出しを上端に固定する（先頭行が見出し自身なら、その祖先だけ）
    const anc = (first >= 0 && V.rows[first] && V.rows[first].anc) || [];
    V.sticky.innerHTML = anc.map((i) => stickyRow(V.rows[i].sticky)).join("");
  }

  /* ガイド線。g = { cols: [{more, hue, hot}], last }。cols[k] は列 k を持つ祖先の枝。 */
  function guides(g) {
    if (!g || !g.cols || !g.cols.length) return "";
    const n = g.cols.length;
    let out = "";
    for (let k = 0; k < n; k++) {
      const c = g.cols[k];
      const x = colX(k);
      const col = c.hot ? "border-color:#6366f1;" : (c.hue != null ? `border-color:hsla(${c.hue},55%,50%,.6);` : "");
      if (k < n - 1) {
        if (c.more) out += `<span class="gl" style="${col}left:${x}px;top:0;bottom:0;border-left-width:1px"></span>`;
      } else {
        out += `<span class="gl" style="${col}left:${x}px;top:0;${g.last ? "height:50%" : "bottom:0"};border-left-width:1px"></span>`;
        out += `<span class="gl" style="${col}left:${x}px;top:50%;width:${UNIT - 4}px;border-top-width:1px"></span>`;
      }
    }
    return out;
  }

  /* 名前空間の枝のレール。見出しの左に 3px、枝の色相で。 */
  const rail = (hue, pad) => hue == null ? "" :
    `<span class="gl" style="left:${pad - 4}px;top:5px;bottom:5px;border-left-width:3px;border-radius:2px;border-color:hsl(${hue},55%,55%)"></span>`;

  /* 上端に固定する見出し。押すとその見出しまで戻る。▾ はその場で畳む。 */
  function stickyRow(s) {
    const pad = 4 + s.depth * UNIT;
    return `<div data-jump="${s.idx}" title="この見出しまで戻る" style="height:${ROW_H}px;padding-left:${pad}px;position:relative"
      class="flex items-center gap-1.5 cursor-pointer rounded-b-md bg-white/95 dark:bg-stone-900/95 backdrop-blur-sm
             border-b border-stone-200 dark:border-stone-700 shadow-sm">
      ${rail(s.hue, pad)}
      <span ${s.cluster ? `data-cluster="${esc(s.cluster)}"` : `data-tree="${esc(s.key)}"`} class="text-[9.5px] text-stone-400 w-2 cursor-pointer" title="この枝を畳む">▾</span>
      <span class="font-mono text-[10.5px] text-stone-500 dark:text-stone-400 truncate flex-1">${esc(s.label)}</span>
      <span class="text-[10px] text-stone-400 pr-2">${s.count}</span>
    </div>`;
  }

  /* 指定の行が窓の外にあるときだけ、窓の中央に来るよう送って描き直す。
     既に見えている行には触らない。 */
  function revealRow(i) {
    if (i < 0 || !V.host) return;
    const h = V.host.clientHeight || 400;
    const top = i * ROW_H;
    if (top >= V.host.scrollTop && top + ROW_H <= V.host.scrollTop + h) return;
    V.host.scrollTop = Math.max(0, top - h / 2 + ROW_H / 2);
    vpaint();
  }

  /* ---- 並び順 ----
     ツリー     モジュールの階層。枝は名前順、モジュール内はレポートの行順
                （＝ファイル内で宣言された順）。
     名前空間   namespace の階層。名前空間は初出順（＝ファイル内の上から）で、
                入れ子の名前空間は木として畳める。
     どちらも同じ木の組み立て（buildTree）で、違いは経路の取り方と枝の並べ方だけ。 */
  /* 一覧に出す宣言。木は **成員と手書きの宣言** で組み、派生（originRel = facet）は由来ごとに
     集めて由来の行の下の小枝に出す。断片（part）は一覧に出さない（由来の証明の一部）。
     外部（参照だけ）は出さない。内部名でも派生なら小枝には出す（`_sizeOf_inst` 等）。
     検索は、派生の名前が一致すればその由来も残す。 */
  function visibleNames(st) {
    const nodes = st.nodes;
    const base = st.order.length ? st.order : Object.keys(nodes);
    const q = st.query.trim().toLowerCase();
    const hit = (n) => !q || n.toLowerCase().includes(q);
    // 派生を由来ごとに集める（順序は行・名前）
    const facetsOf = new Map();
    for (const [n, nd] of Object.entries(nodes)) {
      if (nd.external || nd.originRel !== "facet" || !nd.origin || !nodes[nd.origin]) continue;
      if (!hit(n)) continue;
      (facetsOf.get(nd.origin) || facetsOf.set(nd.origin, []).get(nd.origin)).push(n);
    }
    for (const fs of facetsOf.values()) fs.sort((a, b) => ((nodes[a].line || 0) - (nodes[b].line || 0)) || (a < b ? -1 : 1));
    let names = base.filter((n) => {
      const nd = nodes[n];
      return nd && !nd.external && !nd.internal && nd.originRel !== "facet" && nd.originRel !== "part";
    });
    if (q) names = names.filter((n) => hit(n) || facetsOf.has(n));
    if (st.onlySorry) names = names.filter((n) => nodes[n].usesSorry);
    if (st.kindFilter.size) names = names.filter((n) => st.kindFilter.has(nodes[n].kind));
    return { names, facetsOf };
  }

  /* 名前の描画。接頭辞（名前空間）は薄く、末尾成分は濃く。幅が足りないときは
     接頭辞側を省略し、末尾成分は必ず見せる（`Examples.Pair.mk.inj` が
     `Examples.Pair.m…` になって肝心の `inj` が消えることはない）。
     行ごとに見せ方が変わると、同じ名前空間かどうかが読めない。全行で同じ規則にする。 */
  const splitName = (s) => {
    const i = String(s).lastIndexOf(".");
    return i < 0 ? { prefix: "", last: String(s) } : { prefix: String(s).slice(0, i), last: String(s).slice(i + 1) };
  };
  const nameHtml = (shown) => {
    const { prefix, last } = splitName(shown);
    return `<span class="font-mono text-[11px] min-w-0 flex-1 flex items-baseline">
      ${prefix ? `<span class="truncate text-stone-400 dark:text-stone-500">${esc(prefix)}.</span>` : ""}
      <span class="shrink-0">${esc(last)}</span></span>`;
  };
  const SORRY_BADGE = '<span class="text-[9.5px] px-1 rounded-sm bg-rose-100 text-rose-700 dark:bg-rose-950 dark:text-rose-300 shrink-0">sorry</span>';
  const MARK_DOT = '<span class="inline-block w-1.5 h-1.5 rounded-full bg-indigo-500 shrink-0" title="畳んだ中に中心または選択中の宣言がある"></span>';
  const rowCls = (n, st, cen) =>
    n === cen ? "bg-indigo-50 dark:bg-indigo-950/60 ring-1 ring-indigo-300 dark:ring-indigo-700 text-indigo-900 dark:text-indigo-200"
    : n === st.selected ? "bg-stone-100 dark:bg-stone-800" : "hover:bg-stone-100 dark:hover:bg-stone-800";

  /* 行の title。完全名・所在（モジュール:行）・由来・断片の数。 */
  let curParts = {};      // 由来 → 断片の数（buildRows が derived から置く）
  function rowTitle(n, st) {
    const nd = st.nodes[n] || {};
    const K = LDR.sig.ORIGIN_KIND, R = LDR.sig.ORIGIN_REL;
    let t = `${n} — ${shortOf(nd.module || "")}${nd.line ? ":" + nd.line : ""}`;
    if (nd.originRel && nd.origin) {
      const k = K[nd.originKind] ? K[nd.originKind].ja : nd.originKind;
      t += `（${nd.origin} の${(R[nd.originRel] || {}).ja || nd.originRel}: ${k}）`;
    }
    if (curParts[n]) t += `（断片 ${curParts[n]}: 証明・本体から切り出された補助）`;
    return t;
  }

  /* `shown` は表示する名前。枝に対する相対名（枝 `Examples.Pair` の中の `Examples.Pair.fst` は
     `fst`）、枝が無ければ完全名。完全名と所在は title に残す。 */
  function itemRow(n, st, cen, depth, shown, g) {
    const nd = st.nodes[n];
    const pad = 6 + (depth || 0) * UNIT;
    return {
      name: n,
      html: `<button data-sel="${esc(n)}" title="${esc(rowTitle(n, st))}" style="height:${ROW_H}px;padding-left:${pad}px;position:relative"
        class="w-full text-left pr-2 rounded-md flex items-center gap-2 ${rowCls(n, st, cen)}">
        ${guides(g)}
        ${dot(nd.kind, 6)}
        ${nameHtml(shown || n)}
        ${nd.usesSorry ? SORRY_BADGE : ""}
      </button>`,
    };
  }

  /* 派生の行。由来に対する相対名と、種類の札（単射性・場合分け…）。 */
  function facetRow(n, st, cen, depth, g) {
    const nd = st.nodes[n];
    const K = LDR.sig.ORIGIN_KIND[nd.originKind];
    const pad = 6 + (depth || 0) * UNIT;
    const rel = nd.origin && n.startsWith(nd.origin + ".") ? n.slice(nd.origin.length + 1) : n;
    return {
      name: n,
      html: `<button data-sel="${esc(n)}" title="${esc(rowTitle(n, st))}" style="height:${ROW_H}px;padding-left:${pad}px;position:relative"
        class="w-full text-left pr-2 rounded-md flex items-center gap-2 ${rowCls(n, st, cen)}">
        ${guides(g)}
        ${dot(nd.kind, 6)}
        ${nameHtml(rel)}
        <span class="text-[9px] px-1 rounded-sm bg-stone-100 text-stone-500 dark:bg-stone-800 dark:text-stone-400 shrink-0"
              title="${esc(K ? K.note : nd.originKind)}">${esc(K ? K.ja : nd.originKind)}</span>
        ${nd.usesSorry ? SORRY_BADGE : ""}
      </button>`,
    };
  }

  /* 由来 `origin` の派生をまとめる小枝の見出し。▾ で開閉（グラフの +n と同じ状態）。
     強制的に開いている由来（中心が派生／経路表示の区間に派生）は「固定」と示し、押しても閉じない。 */
  function facetGroupRow(origin, fs, st, depth, open, g, marked, forced) {
    const K = LDR.sig.ORIGIN_KIND;
    const kinds = [...new Set(fs.map((f) => (K[st.nodes[f].originKind] || {}).ja || st.nodes[f].originKind))];
    const pad = 4 + (depth || 0) * UNIT;
    const title = `${shortOf(origin)} から Lean が作った宣言 ${fs.length} 件: ${kinds.join(" / ")}。`
      + (forced ? "中心または経路表示のため固定で開いています（押しても閉じません）" : "押すと開閉（グラフにも効く）");
    return {
      html: `<div data-cluster="${esc(origin)}" style="height:${ROW_H}px;padding-left:${pad}px;position:relative"
        title="${esc(title)}"
        class="w-full flex items-center gap-1.5 cursor-pointer hover:bg-stone-100 dark:hover:bg-stone-800 rounded-md">
        ${guides(g)}
        <span class="text-[9.5px] ${forced ? "text-indigo-500" : "text-stone-400"} w-2">${open ? "▾" : "▸"}</span>
        <span class="text-[10.5px] text-stone-500 dark:text-stone-400 shrink-0">派生 ${fs.length}</span>
        <span class="text-[9.5px] text-stone-400 truncate flex-1">${esc(kinds.join(" · "))}</span>
        ${forced ? '<span class="text-[9px] px-1 rounded-sm bg-indigo-50 text-indigo-600 dark:bg-indigo-950 dark:text-indigo-300 shrink-0">固定</span>' : ""}
        ${!open && marked ? MARK_DOT : ""}
      </div>`,
    };
  }

  /* 型の行が、その名前空間の枝の見出しを兼ねる行。`Examples.Pair` の行の下に
     `mk` / `fst` / `snd` が畳める。型とその名前空間を別の場所に出すと、同じものが
     二か所に見えて読めない。左の ▾ で畳み、名前を押すと選択（二度押しで中心）。 */
  function headRow(name, st, cen, depth, key, closed, marked, count, g, hue, facets) {
    const nd = st.nodes[name];
    const pad = 4 + (depth || 0) * UNIT;
    const countText = `${count}${facets ? ` + 派生 ${facets}` : ""}`;
    return {
      name,
      html: `<div style="height:${ROW_H}px;padding-left:${pad}px;position:relative"
        class="w-full flex items-center gap-1.5 rounded-md ${rowCls(name, st, cen)}">
        ${guides(g)}${rail(hue, pad)}
        <span data-tree="${esc(key)}" class="text-[9.5px] text-stone-400 w-2 cursor-pointer select-none"
              title="${closed ? "名前空間を開く" : "名前空間を畳む"}">${closed ? "▸" : "▾"}</span>
        <button data-sel="${esc(name)}" title="${esc(rowTitle(name, st))}" class="min-w-0 flex-1 flex items-center gap-2 text-left">
          ${dot(nd.kind, 6)}
          ${nameHtml(splitName(name).last)}
          ${nd.usesSorry ? SORRY_BADGE : ""}
        </button>
        ${closed && marked ? MARK_DOT : ""}
        <span class="text-[10px] text-stone-400 pr-2" title="成員（手書き）の数${facets ? "と、Lean が作った派生の数" : ""}">${countText}</span>
      </div>`,
    };
  }

  /* 枝の見出し行（宣言ではない枝: モジュール、型を持たない名前空間）。
     `marked` は「畳んだ中に中心または選択中の宣言がある」印で、畳んだときにだけ出す。
     開いていれば中の行自体が強調されるので要らない。 */
  function groupRow(label, count, depth, prefix, closed, marked, title, g, hue) {
    const pad = 4 + (depth || 0) * UNIT;
    const caret = closed ? "▸" : "▾";
    return {
      html: `<div data-tree="${esc(prefix)}" style="height:${ROW_H}px;padding-left:${pad}px;position:relative" title="${esc(title || prefix)}"
        class="w-full flex items-center gap-1.5 cursor-pointer bg-stone-50/70 dark:bg-stone-800/40 hover:bg-stone-100 dark:hover:bg-stone-800 rounded-md">
        ${guides(g)}${rail(hue, pad)}
        <span class="text-[9.5px] text-stone-400 w-2">${caret}</span>
        <span class="font-mono text-[10.5px] text-stone-500 dark:text-stone-400 truncate flex-1">${esc(label)}</span>
        ${closed && marked ? MARK_DOT : ""}
        <span class="text-[10px] text-stone-400 pr-2">${count}</span>
      </div>`,
    };
  }

  /* 名前を経路で木にする。
       pathOf(n)      枝の成分列 [{seg, kind}]。kind は "module"（ファイル）か "ns"（名前空間）。
                      末尾の節点の items に n を置く。
       isMarked(n)    印を付ける宣言（中心・選択中）。部分木に一つでもあれば枝に伝播する。
     モジュールの枝は名前順、名前空間の枝は初出順（ファイルの上から）。同じ段では
     モジュールの枝を先に置く。節点は nsName（名前空間としての完全名）を持ち、型の行が
     名前空間の見出しを兼ねる判定（attachHeads）と相対名の表示に使う。
     total は部分木の宣言数。空の枝（total 0）は描かない。 */
  function buildTree(names, pathOf, isMarked) {
    const mk = (seg, prefix, kind, nsName) =>
      ({ seg, prefix, kind, nsName, children: new Map(), items: [], total: 0, marked: false });
    const root = mk("", "", "root", "");
    for (const n of names) {
      let cur = root, prefix = "", nsName = "";
      for (const { seg, kind } of pathOf(n)) {
        prefix = prefix ? prefix + "." + seg : seg;
        if (kind === "ns") nsName = nsName ? nsName + "." + seg : seg;
        const key = kind + ":" + seg;
        if (!cur.children.has(key)) cur.children.set(key, mk(seg, prefix, kind, kind === "ns" ? nsName : ""));
        cur = cur.children.get(key);
      }
      cur.items.push(n);
    }
    (function finish(node) {
      const kids = [...node.children.values()];
      const mods = kids.filter((k) => k.kind === "module").sort((a, b) => (a.seg < b.seg ? -1 : a.seg > b.seg ? 1 : 0));
      const nss = kids.filter((k) => k.kind !== "module");
      node.children = new Map([...mods, ...nss].map((k) => [k.kind + ":" + k.seg, k]));
      node.total = node.items.length;
      node.marked = node.items.some(isMarked);
      for (const ch of node.children.values()) {
        finish(ch);
        node.total += ch.total;
        node.marked = node.marked || ch.marked;
      }
    })(root);
    return root;
  }

  /* 木を行に流す。各枝は見出し行（押すと畳める）、その直下にその枝自身の宣言、
     続いて子の枝。畳んだ枝の中身は出さない。tag は treeClosed の鍵の接頭辞。
     labelOf(n, prefix) があれば、枝の接頭辞に対する表示名を決める。
     枝に `head`（枝と同名の宣言 = 型）があれば、その宣言の行が見出しを兼ねる。 */
  /* 木を行に流す。各枝は見出し行（押すと畳める）、その直下にその枝自身の宣言、続いて子の枝、
     最後に見出しの宣言の派生の小枝。畳んだ枝の中身は出さない。tag は treeClosed の鍵の接頭辞。
     枝に `head`（枝と同名の宣言 = 型）があれば、その宣言の行が見出しを兼ねる。
     facetsOf（由来 → 派生の列）があれば、由来の行の下に「派生 n」の小枝を置く。
       cols: この深さの行が通る列（祖先の枝）。anc: 祖先の見出し行の索引（上端固定用）。 */
  function treeRows(root, st, cen, tag, facetsOf, isMarked) {
    const rows = [];
    const nsHue = LDR.canvas && LDR.canvas.hueOf ? (p) => LDR.canvas.hueOf(p) : () => null;
    const facetsFor = (n) => (facetsOf && facetsOf.get(n)) || [];

    /* 由来 n の派生の小枝。開閉は store.isClusterOpen（グラフと共有）。 */
    const pushFacets = (n, depth, cols, anc) => {
      const fs = facetsFor(n);
      if (!fs.length) return;
      const open = S.isClusterOpen(n);
      const marked = fs.some(isMarked);
      const idx = rows.length;
      const row = facetGroupRow(n, fs, st, depth, open, { cols, last: true }, marked, S.isClusterForced(n));
      row.anc = anc;
      row.sticky = { label: `派生 ${fs.length}（${splitName(n).last}）`, depth, key: "fx:" + n, cluster: n, hue: null, count: fs.length, idx };
      rows.push(row);
      if (!open) return;
      const inner = cols.concat([{ more: false, hue: null, hot: marked }]);
      fs.forEach((f, j) => {
        const r = facetRow(f, st, cen, depth + 1, { cols: inner, last: j === fs.length - 1 });
        r.anc = anc.concat([idx]);
        rows.push(r);
      });
    };

    /* trailing: この枝の子の後ろにまだ行（見出しの派生）が続くか。最後の子の肘を ├ にする */
    const walk = (node, depth, cols, anc, trailing) => {
      const kids = [...node.children.values()].filter((ch) => ch.total);
      kids.forEach((ch, i) => {
        const last = i === kids.length - 1 && !trailing;
        const key = tag + ch.prefix;
        const closed = st.treeClosed.has(key);
        const hue = ch.kind === "ns" ? nsHue(ch.nsName) : null;
        const g = { cols, last };
        const idx = rows.length;
        const headFacets = ch.head ? facetsFor(ch.head).length : 0;
        const row = ch.head
          ? headRow(ch.head, st, cen, depth, key, closed, ch.marked, ch.total, g, hue, headFacets)
          : groupRow(ch.seg, ch.total, depth, key, closed, ch.marked, ch.prefix, g, hue);
        row.anc = anc;
        row.sticky = { label: ch.head ? splitName(ch.head).last : ch.seg, depth, key, hue, count: ch.total, idx };
        rows.push(row);
        if (closed) return;
        const inner = cols.concat([{ more: !last, hue, hot: ch.marked }]);
        const innerAnc = anc.concat([idx]);
        const subKids = [...ch.children.values()].filter((c) => c.total).length;
        const hasHeadFacets = headFacets > 0;
        ch.items.forEach((n, j) => {
          const fs = facetsFor(n);
          const itemLast = j === ch.items.length - 1 && subKids === 0 && !hasHeadFacets;
          const shown = ch.kind === "ns" ? String(n).slice(ch.nsName.length + 1) : n;
          const r = itemRow(n, st, cen, depth + 1, shown, { cols: inner, last: itemLast && !fs.length });
          r.anc = innerAnc;
          rows.push(r);
          // 宣言の派生（等式補題など）は、その行の下に一段下げて置く
          if (fs.length) pushFacets(n, depth + 2, inner.concat([{ more: !itemLast, hue: null, hot: isMarked(n) }]), innerAnc);
        });
        walk(ch, depth + 1, inner, innerAnc, hasHeadFacets);
        if (ch.head) pushFacets(ch.head, depth + 1, inner, innerAnc);
      });
    };
    walk(root, 0, [], [], false);
    return rows;
  }

  /* 名前空間の枝と同名の宣言（`Examples.Pair` の枝と構造体 `Examples.Pair`）を
     結びつける。宣言は親の枝の項目から外し、枝の見出し `head` にする。
     枝の件数 total は中の宣言数のまま（型自身は数えない）。印は型にも及ぶ。 */
  function attachHeads(root, visible, isMarked) {
    (function walk(node) {
      for (const ch of node.children.values()) {
        if (ch.kind === "ns" && visible.has(ch.nsName)) {
          ch.head = ch.nsName;
          node.items = node.items.filter((x) => x !== ch.nsName);
          ch.marked = ch.marked || isMarked(ch.nsName);
        }
        walk(ch);
      }
    })(root);
  }

  /* 名前空間の成分列（名前から末尾一成分を落としたもの） */
  const nsPath = (n) => String(n).split(".").slice(0, -1).map((seg) => ({ seg, kind: "ns" }));

  function buildRows(st, dv) {
    const { names, facetsOf } = visibleNames(st);
    const cen = dv.center;
    const isMarked = (n) => n === cen || n === st.selected;
    curParts = dv.partCount || {};
    const visible = new Set(names);

    if (st.listMode === "ns") {
      // 名前空間の木（ファイルをまたぐ）。初出順を保つ。
      const root = buildTree(names, nsPath, isMarked);
      attachHeads(root, visible, isMarked);
      const rows = treeRows(root, st, cen, "ns:", facetsOf, isMarked);
      // 名前空間を持たない宣言は末尾にまとめる
      if (root.items.length) {
        const key = "ns:(名前空間なし)";
        const closed = st.treeClosed.has(key);
        const marked = root.items.some(isMarked);
        const idx = rows.length;
        const head = groupRow("(名前空間なし)", root.items.length, 0, key, closed, marked,
          "namespace の外で宣言されたもの", { cols: [], last: true }, null);
        head.anc = [];
        head.sticky = { label: "(名前空間なし)", depth: 0, key, hue: null, count: root.items.length, idx };
        rows.push(head);
        if (!closed) root.items.forEach((n, j) => {
          const r = itemRow(n, st, cen, 1, undefined,
            { cols: [{ more: false, hue: null, hot: marked }], last: j === root.items.length - 1 });
          r.anc = [idx];
          rows.push(r);
        });
      }
      return { rows, count: names.length, facets: [...facetsOf.values()].reduce((a, b) => a + b.length, 0) };
    }

    // モジュール = ファイルの階層（名前順）→ その中は名前空間の木（初出順）
    const pathOf = (n) => String(st.nodes[n].module).split(".").map((seg) => ({ seg, kind: "module" })).concat(nsPath(n));
    const root = buildTree(names, pathOf, isMarked);
    attachHeads(root, visible, isMarked);
    return { rows: treeRows(root, st, cen, "md:", facetsOf, isMarked), count: names.length,
             facets: [...facetsOf.values()].reduce((a, b) => a + b.length, 0) };
  }

  let lastCenter = null;
  function renderList(st, dv) {
    const k = [st.query, st.listMode, st.onlySorry, S.openSignature(),
      [...st.kindFilter].sort().join(","),
      [...st.treeClosed].sort().join(","), st.order.length, Object.keys(st.nodes).length,
      dv.center, st.selected].join("|");
    once("list", k, () => {
      const { rows, count, facets } = buildRows(st, dv);
      vsetRows(rows);
      $("listCount").textContent = `${count} 件` + (facets ? `（派生 ${facets}）` : "");
      /* 中心が変わったときだけ、その行まで一覧を送る。選択やフィルタのたびに
         動かすと読んでいる位置を奪う。畳んだ枝の中なら行が無いので、
         見出しの印（groupRow の marked）に任せる。 */
      if (dv.center !== lastCenter) {
        lastCenter = dv.center;
        revealRow(rows.findIndex((r) => r.name === dv.center));
      }
    });
  }

  function shortOf(n) {
    const p = String(n).split(".");
    return p.length <= 2 ? n : p.slice(-2).join(".");
  }

  /* ================= 監査サマリ =================
     ここは統計だけ。押せるものは置かない（押せるチップと押せないチップが同じ見た目で
     並ぶと、何が操作で何が数字か分からない）。一覧の絞り込みは renderFilters にある。 */
  const STD = new Set(["propext", "Classical.choice", "Quot.sound"]);

  function renderAudit(st) {
    // 「無条件で閉じる」件数は metrics(edgeMode 依存)から来る。鍵に含める。
    once("audit", Object.keys(st.nodes).length + "|" + st.edgeMode, () => {
      // 件数は対象の宣言について。内部補助は対象の証明の一部であって、独立した宣言として数えない
      const own = Object.values(st.nodes).filter((n) => !n.external && !n.internal);
      const sorry = own.filter((n) => n.usesSorry).length;
      const extra = own.filter((n) => n.axioms.some((a) => !STD.has(a) && a !== "sorryAx")).length;
      const axFree = own.filter((n) => n.axioms.length === 0).length;
      const m = S.metrics();
      const hered = own.filter((n) => m.hered && m.hered[n.name]).length;
      const cond = own.filter((n) => n.numHyp || n.numInst).length;
      $("auditBar").innerHTML = `
        <span class="px-2 py-1 rounded-md text-[12px] flex items-center gap-1.5
          ${sorry ? "bg-rose-50 text-rose-800 dark:bg-rose-950/60 dark:text-rose-200" : "bg-stone-100 text-stone-600 dark:bg-stone-800 dark:text-stone-300"}"
          title="sorry を含む宣言の数（下の「sorry のみ」で絞り込める）">
          <span class="w-1.5 h-1.5 rounded-full bg-rose-500"></span>sorry ${sorry}
        </span>
        <span class="px-2 py-1 rounded-md text-[12px] bg-stone-100 text-stone-600 dark:bg-stone-800 dark:text-stone-300"
              title="propext / Classical.choice / Quot.sound 以外の公理に依存">追加公理 ${extra}</span>
        <span class="px-2 py-1 rounded-md text-[12px] bg-emerald-50 text-emerald-700 dark:bg-emerald-950/60 dark:text-emerald-300"
              title="公理に一切依存しない宣言">公理なし ${axFree}/${own.length}</span>
        <span class="px-2 py-1 rounded-md text-[12px] bg-emerald-100 text-emerald-800 dark:bg-emerald-950 dark:text-emerald-200"
              title="自分にも依存先にも条件が無い。無条件に得たものだけから無条件に得られている">無条件で閉じる ${hered}</span>
        <span class="px-2 py-1 rounded-md text-[12px] bg-amber-50 text-amber-800 dark:bg-amber-950/60 dark:text-amber-300"
              title="仮定またはインスタンスを要求している宣言">条件付き ${cond}</span>`;
    });
  }

  /* ================= 一覧の絞り込み =================
     押せるものだけをここに置く。☑ / ☐ で「いま効いているか」が一目で分かる。
     件数は絞り込みの対象になる宣言の数（対象の宣言について）。 */
  function renderFilters(st, dv) {
    const own = Object.values(st.nodes).filter((n) => !n.external && !n.internal);
    const sorry = own.filter((n) => n.usesSorry).length;
    const facets = Object.values(dv.facetCount || {}).reduce((a, b) => a + b, 0);
    const allOpen = S.allFacetsOpen();
    once("filters", [sorry, facets, st.onlySorry, allOpen, st.openClusters.size].join("|"), () => {
      const tog = (id, on, label, title) => `<button data-filter="${id}" title="${esc(title)}"
        class="px-2 py-1 rounded-md text-[11.5px] flex items-center gap-1.5 border
          ${on ? "bg-stone-900 text-white border-stone-900 dark:bg-stone-100 dark:text-stone-900 dark:border-stone-100"
               : "bg-white text-stone-600 border-stone-300 hover:bg-stone-100 dark:bg-stone-900 dark:text-stone-300 dark:border-stone-600 dark:hover:bg-stone-800"}">
        <span class="text-[11px]">${on ? "☑" : "☐"}</span>${label}</button>`;
      $("listFilters").innerHTML =
        tog("sorry", st.onlySorry, `sorry のみ (${sorry})`, "sorry を含む宣言だけを一覧に出す")
        + (facets
          ? tog("openall", allOpen, `派生を全て開く (${facets})`,
                "派生 = 由来（構造体・帰納型・構成子・定義）から Lean が機械的に作る宣言（casesOn / rec / mk.inj / sizeOf_spec / eq_1 等）。既定では由来の行とグラフの節点に畳む。"
                + "☑ で全ての由来を開き、☐ で全て畳む（個別の開閉と同じ集合を操作する）。個別には行の ▸ やグラフの +n で開ける"
                + (st.openClusters.size && !allOpen ? `。いま ${st.openClusters.size} / ${S.facetOriginCount()} の由来を開いている` : ""))
          : "");
    });
  }

  /* ================= 詳細 =================

     型を一本の文字列で見せると、引数・仮定・結論が同じ「→」で並ぶために
     読み手が三つを区別できない。Lean 側が分解した `binders`（`prop` 旗つき）と
     `conclusion` を使って、役割ごとに置き直す。 */

  /* 公式ドキュメントへのリンク。パッケージ → 文書の根 URL の対応表は pkg.js が一か所で持ち
     （Mathlib と cslib は doc-gen4 の同じ規則 `<モジュールのパス>.html#<完全名>`）、ここでは
     宣言ページへ直接張る。無いパッケージ（自作の別パッケージ等）には出さない。
     LeanSearch は自作の宣言でも「似た定理」を探す用途があるので常に出す。 */
  const linkCls = "text-[11px] px-2 py-0.5 rounded-md border border-stone-300 dark:border-stone-600 hover:bg-stone-100 dark:hover:bg-stone-800";
  function docLinks(nd, name) {
    const url = LDR.pkg ? LDR.pkg.docsUrl(nd, name) : null;
    const pkg = LDR.pkg ? LDR.pkg.packageOf(nd && nd.module) : "";
    const leaf = encodeURIComponent(String(name).split(".").slice(-1)[0]);
    return (url ? `<a href="${esc(url)}" target="_blank" rel="noopener" class="${linkCls}"
           title="${esc(LDR.pkg.labelOf(pkg || LDR.pkg.packageOf(name)))} の公式ドキュメント（${url.includes("search.html") ? "検索" : "この宣言のページ"}）">📘 docs</a>` : "")
      + `<a href="https://leansearch.net/?q=${leaf}" target="_blank" rel="noopener" class="${linkCls}"
           title="LeanSearch で意味検索">🔎 LeanSearch</a>`;
  }

  /* パッケージの札（対象の外の宣言にだけ。対象のパッケージは出さない） */
  function pkgChip(nd) {
    const P = LDR.pkg;
    if (!P || !nd || !nd.external) return "";
    const p = P.packageOf(nd.module);
    const tp = LDR.canvas && LDR.canvas.targetPackage ? LDR.canvas.targetPackage(S.state) : "";
    if (!p || p === tp) return "";
    return `<span class="text-[10px] px-1.5 py-0.5 rounded-sm border" style="border-color:${P.colorOf(p)};color:${P.colorOf(p)}"
      title="対象の外のパッケージ ${esc(p)} の宣言（${esc(nd.module)}）">${esc(P.labelOf(p))}</span>`;
  }

  /* 依存パッケージの要約。直接依存の定義モジュール（Lean 側 depModules）をパッケージで数える。
     「この宣言は Mathlib の何に依っているか」を一目で示し、title に実際のモジュールを列挙する。 */
  function depPackages(nd) {
    const P = LDR.pkg;
    if (!P || !nd || !nd.depModules) return "";
    const sum = P.summarize(nd.depModules);
    const tp = LDR.canvas && LDR.canvas.targetPackage ? LDR.canvas.targetPackage(S.state) : "";
    const keys = Object.keys(sum).sort((a, b) => (a === tp ? -1 : b === tp ? 1 : sum[b].n - sum[a].n));
    if (!keys.length) return "";
    return `<div class="flex items-baseline gap-1 flex-wrap">
      <span class="text-[10px] text-stone-400 shrink-0" title="直接依存する宣言が定義されているモジュールを、パッケージごとに数えたもの">依存パッケージ</span>
      ${keys.map((p) => `<span class="text-[10px] px-1.5 py-0.5 rounded-sm ${p === tp ? "bg-stone-100 text-stone-600 dark:bg-stone-800 dark:text-stone-300" : "border"}"
          style="${p === tp ? "" : `border-color:${P.colorOf(p)};color:${P.colorOf(p)}`}"
          title="${esc(sum[p].modules.sort().join("\n"))}">${esc(P.labelOf(p))}${p === tp ? "（対象）" : ""} ${sum[p].n}</span>`).join("")}
    </div>`;
  }

  const KIND_BADGE = { explicit: "明示", implicit: "暗黙", strictImplicit: "暗黙", inst: "inst" };

  /* 定義の与えられ方を三つに分ける。

       無条件で閉じる  仮定もインスタンス要求も無く、依存先も全て同じ性質。
                       無条件に得たものだけから無条件に得られている。
       無条件          自分には条件が無いが、依存の先に条件付きのものを含む。
       条件 n          仮定またはインスタンスを n 個要求している。

     この区別は「最初に無条件で与えられる定義」「追加の理論や条件を要する定義」
     「条件付きだが無条件のものから無条件に得られる定義」を分けるためのもの。 */
  function condChip(name, nd) {
    const cls = (c) => `text-[10px] px-1.5 py-0.5 rounded-sm ${c}`;
    if (nd.numHyp || nd.numInst) {
      return `<span class="${cls("bg-amber-50 text-amber-800 dark:bg-amber-950/60 dark:text-amber-300")}"
        title="仮定 ${nd.numHyp} / インスタンス ${nd.numInst} を要求している">条件 ${nd.numHyp + nd.numInst}</span>`;
    }
    const m = S.metrics();
    const hered = m.hered && m.hered[name];
    return hered
      ? `<span class="${cls("bg-emerald-100 text-emerald-800 dark:bg-emerald-950 dark:text-emerald-200")}"
          title="自分に条件が無く、依存先も全て条件を持たない。無条件に得たものだけから無条件に得られている">無条件で閉じる</span>`
      : `<span class="${cls("bg-emerald-50 text-emerald-700 dark:bg-emerald-950/60 dark:text-emerald-300")}"
          title="自分には条件が無いが、依存の先に条件付きのものを含む">無条件</span>`;
  }

  /** 型・項を読める幅に畳んで出す。元の文字列は title に残す。 */
  function expr(s) {
    const full = String(s || "");
    return `<span class="font-mono" title="${esc(full)}">${esc(LDR.sig.abbrev(full))}</span>`;
  }

  /* 引数・仮定・結論を三つの区画に分ける。区画ごとに左の帯の色を変え（引数 灰 / 仮定 琥珀 /
     結論 藍）、区画の間に線を引く。同じ高さ・同じ配色の行を縦に積むだけでは三つが
     区別できない（指摘）。結論は主結合子（sig.decompose）で左辺・右辺に割る。 */
  function signatureBlock(nd) {
    const B = nd.binders || [];
    const args = B.filter((b) => !b.prop);
    const hyps = B.filter((b) => b.prop);
    const section = (label, rows, bar, tone) => rows.length ? `
      <div class="flex gap-2 py-1 border-l-[3px] pl-2 ${bar}">
        <span class="shrink-0 w-7 text-[10px] pt-[2px] ${tone}">${label}</span>
        <div class="min-w-0 flex-1 space-y-[2px]">${rows.join("")}</div>
      </div>` : "";
    const line = (body) => `<div class="text-[12px] leading-relaxed break-words">${body}</div>`;

    const argRows = args.map((b) => line(
      `<span class="font-mono text-stone-900 dark:text-stone-100">${esc(b.name)}</span>
       <span class="text-stone-400"> : </span>${expr(b.type)}
       <span class="ml-1 text-[9.5px] text-stone-400">${KIND_BADGE[b.kind] || ""}</span>`));
    const hypRows = hyps.map((b) => line(expr(b.type)));

    const d = LDR.sig.decompose(nd.conclusion || "");
    const conclRows = [];
    if (d.lhs !== null && d.rhs !== null) {
      conclRows.push(line(`<span class="font-mono text-indigo-700 dark:text-indigo-300">${esc(LDR.sig.abbrev(d.rel))}</span>`
        + (d.ctx.length ? ` <span class="text-stone-400">${esc(LDR.sig.abbrev(d.ctx.join(" ")))}</span>` : "")
        + ` <span class="text-[9.5px] text-stone-400">主結合子</span>`));
      conclRows.push(line(`<span class="text-[9.5px] text-stone-400 mr-1">左辺</span>${expr(d.lhs)}`));
      conclRows.push(line(`<span class="text-[9.5px] text-stone-400 mr-1">右辺</span>${expr(d.rhs)}`));
    } else if (d.whole) {
      conclRows.push(line(expr(d.whole)));
    }
    const parts = [
      section("引数", argRows, "border-stone-300 dark:border-stone-600", "text-stone-400"),
      section("仮定", hypRows, "border-amber-400", "text-amber-600 dark:text-amber-500"),
      section("結論", conclRows, "border-indigo-400", "text-indigo-600 dark:text-indigo-400"),
    ].filter(Boolean);
    return parts.join('<div class="border-t border-stone-200 dark:border-stone-700 my-0.5"></div>');
  }

  /* 宣言の印（由来・派生・断片・sorry・instance・reducible・形・条件）。中央の見出しと
     右のプレビューで同じものを使う（二か所で別々に組むと必ず乖離する）。 */
  function markChips(name, nd, dv) {
    const chip = (t, cls) => `<span class="text-[10px] px-1.5 py-0.5 rounded-sm ${cls}">${t}</span>`;
    // 法則の形は命題にだけ意味がある（インスタンス等のデータは構文上 refl の形を持ち得る）
    const sh = nd.isProp ? LDR.sig.SHAPE[nd.shape] : null;
    /* 由来。派生・断片なら「X の派生: 単射性」、由来を持つ側なら「派生 n」（押すと開閉）と「断片 m」 */
    const OK = LDR.sig.ORIGIN_KIND, OR = LDR.sig.ORIGIN_REL;
    const originChip = nd.originRel && nd.origin
      ? `<button data-sel="${esc(nd.origin)}" title="${esc(nd.origin)}（${esc((OK[nd.originKind] || {}).note || nd.originKind)}）"
           class="text-[10px] px-1.5 py-0.5 rounded-sm bg-stone-100 text-stone-700 hover:bg-stone-200 dark:bg-stone-800 dark:text-stone-200">
           ${esc(shortOf(nd.origin))} の${esc((OR[nd.originRel] || {}).ja || nd.originRel)}: ${esc((OK[nd.originKind] || {}).ja || nd.originKind)}</button>`
      : "";
    const fc = (dv.facetCount || {})[name] || 0, pc = (dv.partCount || {})[name] || 0;
    const open = fc && S.isClusterOpen(name), forced = fc && S.isClusterForced(name);
    const reach = dv.facetReach ? (dv.facetReach[name] || 0) : fc;
    const clusterChip = fc
      ? `<button data-cluster="${esc(name)}" title="${esc(`この宣言から Lean が作った派生 ${fc} 件。`
             + (forced ? "中心または経路表示のため固定で開いています" : `押すと一覧とグラフで開閉（この中心から見えるのは ${reach} 件）`))}"
           class="text-[10px] px-1.5 py-0.5 rounded-sm ${open
             ? "bg-stone-900 text-white dark:bg-stone-100 dark:text-stone-900"
             : "bg-stone-100 text-stone-700 hover:bg-stone-200 dark:bg-stone-800 dark:text-stone-200"}">派生 ${fc} ${forced ? "▾ 固定" : open ? "▾" : "▸"}</button>`
      : "";
    const partChip = pc ? chip(`断片 ${pc}`, "bg-stone-100 text-stone-500 dark:bg-stone-800 dark:text-stone-400") : "";
    return [
      originChip, clusterChip, partChip,
      nd.usesSorry ? chip("sorry を含む", "bg-rose-100 text-rose-700 dark:bg-rose-950 dark:text-rose-300") : "",
      nd.isInstance ? chip("instance", "bg-teal-100 text-teal-800 dark:bg-teal-950 dark:text-teal-200") : "",
      nd.reducibility === "reducible" ? chip("reducible", "bg-stone-100 text-stone-600 dark:bg-stone-800 dark:text-stone-300") : "",
      sh ? `<span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-indigo-100 text-indigo-800 dark:bg-indigo-950 dark:text-indigo-200"
              title="${esc(sh.note)}">${sh.ja}</span>` : "",
      condChip(name, nd),
    ].filter(Boolean).join(" ");
  }

  /* 公理のチップ。押すと中心からその公理に至る経路（順序区間）を表示する。 */
  function axiomChips(nd, st) {
    return nd.axioms.map((a) => {
      const bad = a === "sorryAx";
      const extra = !STD.has(a) && !bad;
      const on = st.traceTarget === a;
      const cls = bad ? "bg-rose-100 text-rose-800 dark:bg-rose-950 dark:text-rose-200"
                : extra ? "bg-amber-100 text-amber-900 dark:bg-amber-950 dark:text-amber-200"
                : "bg-stone-100 text-stone-600 dark:bg-stone-800 dark:text-stone-300";
      return `<button data-trace="${esc(a)}" class="font-mono text-[10.5px] px-1.5 py-0.5 rounded-sm ${cls}
                ${on ? "ring-2 ring-amber-500" : ""}"
                title="${on ? "経路表示を解除" : "中心からこの公理に至る経路を表示"}">${esc(a)}</button>`;
    }).join(" ") || `<span class="text-[11px] text-emerald-600 dark:text-emerald-400">なし（公理非依存）</span>`;
  }

  /* 中央の見出し。主語は **グラフの中心** に固定する。
     以前は選択中の宣言を出していたため、主語が三つ（見出し＝選択、プレビュー＝追従、依存タブ＝中心）
     になり「連携が取れていない」と見えた。グラフの真上にある見出しは、その図の中心を名乗る。
     選択した宣言は右パネル（プレビュー・依存）が引き受ける。
     一行に留める。シグネチャも原文も右パネルが持つので、ここに置くとグラフの高さが削られるだけ。 */
  function renderInspector(st, dv) {
    const name = dv.center;
    // 公理チップは経路表示中かどうかで見た目が変わるので、traceTarget も鍵に含める
    once("insp", name + "|" + st.traceTarget + "|" + Object.keys(st.nodes).length
         + "|" + (name ? S.isClusterOpen(name) + S.isClusterForced(name) : ""), () => {
      const nd = st.nodes[name];
      const el = $("inspector");
      if (!nd) {
        const modCount = (dv.modIdx && dv.modIdx.count || {})[name];
        el.innerHTML = modCount !== undefined
          ? `<div class="text-[12.5px] text-stone-500">
               <span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-indigo-600 text-white mr-1">中心</span>
               <span class="font-mono">${esc(name || "")}</span> はモジュールです（${modCount} 宣言）</div>`
          : `<div class="text-[12.5px] text-stone-500">
               <span class="font-mono">${esc(name || "")}</span> はこのデータにありません
               <span class="text-stone-400">（別のデータで選んだ宣言か、ピンの復元先が無い）</span></div>`;
        return;
      }
      el.innerHTML = `
        <div class="flex items-center gap-2 flex-wrap">
          <span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-indigo-600 text-white" title="グラフの中心。右パネルは選択中の宣言を出す（追従）か、この中心に固定できる">中心</span>
          ${dot(nd.kind, 8)}
          <span class="font-mono text-[12.5px] font-medium break-all leading-tight">${esc(name)}</span>
          <span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-stone-100 dark:bg-stone-800 text-stone-600 dark:text-stone-300">${kinfo(nd.kind).ja}</span>
          <span class="font-mono text-[9.5px] text-stone-500" title="${esc(nd.module)}">${esc(shortOf(nd.module))}${nd.line ? ":" + nd.line : ""}</span>
          ${pkgChip(nd)}
          ${markChips(name, nd, dv)}
          ${nd.axioms.length
            ? `<span class="text-[10px] text-stone-500">公理</span>${axiomChips(nd, st)}`
            : `<span class="text-[10px] text-emerald-600 dark:text-emerald-400">公理非依存</span>`}
        </div>`;
    });
  }

  /* ================= 右: 依存と参照 ================= */
  /* 依存の一覧も、名前だけでは何を言っているものか分からない。
     役割の色帯・形・結論を添えて、導出図の前提カードと同じ読み方に揃える。 */
  function depRow(n, st) {
    const nd = st.nodes[n] || { kind: "unknown", usesSorry: false };
    const role = LDR.roles.roleOf(n, nd);
    const col = (LDR.roles.ROLE[role] || LDR.roles.ROLE.vocab).c;
    const sh = nd.isProp ? LDR.sig.SHAPE[nd.shape] : null;
    const concl = LDR.sig.abbrev(nd.conclusion || nd.typeString || "");
    return `<button data-sel="${esc(n)}" title="${esc(n)}"
      class="w-full text-left pl-2 pr-2 py-1 rounded-sm border-l-2 hover:bg-stone-100 dark:hover:bg-stone-800
             ${st.selected === n ? "bg-stone-100 dark:bg-stone-800" : ""}"
      style="border-color:${col}66">
      <div class="flex items-center gap-1.5">
        ${dot(nd.kind, 6)}
        <span class="font-mono text-[10.5px] truncate flex-1">${esc(shortOf(n))}</span>
        ${role === "axiom" ? '<span class="text-[9px] px-1 rounded-sm bg-orange-100 text-orange-800 dark:bg-orange-950 dark:text-orange-200 shrink-0">公理</span>' : ""}
        ${sh ? `<span class="text-[9px] shrink-0" style="color:${col}">${sh.ja}</span>` : ""}
        ${nd.usesSorry ? '<span class="text-[9px] text-rose-600 shrink-0">sorry</span>' : ""}
      </div>
      ${concl ? `<div class="font-mono text-[9.5px] text-stone-500 dark:text-stone-400 leading-snug break-words"
        >${esc(concl)}</div>` : ""}
    </button>`;
  }

  /* ---- 導出図 ----

     証明項に現れる定数を一列に並べても、それは証明の図ではない。
     役割で三つに分け、前提を横線の上に、結論を下に置く推論図の形にする。

       前提   実際に呼ばれた補題と公理。押せばその前提の導出図が開く。
       規則   この宣言自身。横線の右に名前を置く。
       結論   この宣言が述べていること。
       語彙   主張を書くための定義・型。前提ではないので線の外に置く。
       骨組み  論理結合子・再帰子。畳んで件数だけ示す。

     読み手が確認したいのは前提だけなので、そこに視線が集まるようにする。 */
  const roleColor = (r) => (LDR.roles.ROLE[r] || LDR.roles.ROLE.vocab).c;

  function conclusionOf(nd) {
    return LDR.sig.abbrev(nd.conclusion || nd.typeString || "");
  }

  /* 前提は横並びに置く。推論図は「線の上に前提、線の下に結論」で読むものなので、
     縦に積むと図としての意味が失われる。幅が足りなければ折り返す。
     展開した前提はその場で自分の図に育つので、入れ子がそのまま導出の入れ子になる。 */
  /* via は、この前提が親の「主張（型）」に現れたか「証明（値）」にだけ現れたか。
     前者は親が何を述べているかを決め、後者は親をどう示したかを決める。
     骨組みを通り抜けた前提は初手の via を継承している（roles.split）。 */
  const VIA = {
    type:  { t: "型", title: "主張（型）に現れる。親が何を述べているかを決める" },
    value: { t: "証", title: "証明（値）にだけ現れる。親をどう示したかを決める" },
  };
  const viaTag = (via) => VIA[via]
    ? `<span class="text-[8.5px] px-1 rounded-sm bg-stone-100 dark:bg-stone-800 text-stone-500 dark:text-stone-400"
         title="${esc(VIA[via].title)}">${VIA[via].t}</span>` : "";

  function premiseCard(name, st, depth, seen, via) {
    const nd = st.nodes[name] || {};
    const role = LDR.roles.roleOf(name, nd);
    const open = st.derivOpen.has(name);
    const canOpen = depth > 0 && (((nd.typeDeps || []).length + (nd.valueDeps || []).length) > 0);
    const sh = nd.isProp ? LDR.sig.SHAPE[nd.shape] : null;
    const concl = conclusionOf(nd);
    const col = roleColor(role);

    if (open && canOpen) {
      // 開いた前提は、その場で自分の推論図になる
      return `<div class="rounded-md border px-2 py-1.5 min-w-0 flex-1 basis-full"
           style="border-color:${col}44;background:${col}08">
        <div class="flex items-baseline gap-1 mb-1">
          <button data-deriv="${esc(name)}" class="text-[9px] w-3 shrink-0 text-stone-400 hover:text-stone-700">▾</button>
          <span class="text-[9px]" style="color:${col}">${LDR.roles.ROLE[role].ja}</span>
          ${viaTag(via)}
        </div>
        ${derivation(name, st, depth - 1, seen)}
      </div>`;
    }
    return `<div class="rounded-md border px-2 py-1 min-w-[150px] max-w-[280px] flex-1"
         style="border-color:${col}44;background:${col}08">
      <div class="flex items-baseline gap-1">
        ${canOpen ? `<button data-deriv="${esc(name)}" title="この前提の導出を開く"
            class="text-[9px] w-3 shrink-0 text-stone-400 hover:text-stone-700">▸</button>`
          : `<span class="w-3 shrink-0 text-[9px] text-stone-300">·</span>`}
        <button data-sel="${esc(name)}" title="${esc(name)}"
          class="font-mono text-[10.5px] text-left hover:underline break-all leading-tight">${esc(shortOf(name))}</button>
      </div>
      <div class="flex items-baseline gap-1 pl-4">
        ${role === "axiom" ? `<span class="text-[8.5px] px-1 rounded-sm bg-orange-100 text-orange-800 dark:bg-orange-950 dark:text-orange-200">公理</span>` : ""}
        ${sh ? `<span class="text-[8.5px]" style="color:${col}" title="${esc(sh.note)}">${sh.ja}</span>` : ""}
        ${viaTag(via)}
      </div>
      ${concl ? `<div class="pl-4 font-mono text-[9.5px] text-stone-500 dark:text-stone-400 leading-snug break-words"
           title="${esc(nd.conclusion || nd.typeString || "")}">${esc(concl)}</div>` : ""}
    </div>`;
  }

  function derivation(name, st, depth, seen) {
    const nd = st.nodes[name];
    if (!nd) return "";
    const parts = LDR.roles.split(name, st.nodes);
    const premises = [...parts.axiom, ...parts.lemma].filter((p) => !seen.has(p.name));
    for (const p of premises) seen.add(p.name);

    const prem = premises.length
      ? `<div class="flex flex-wrap items-stretch gap-1.5">
           ${premises.map((p) => premiseCard(p.name, st, depth, seen, p.via)).join("")}
         </div>`
      : `<div class="text-[9.5px] text-stone-400 py-1">前提となる補題はありません
           <span class="text-stone-300 dark:text-stone-600">（定義そのもの、または骨組みだけで閉じています）</span></div>`;

    const chip = (list, label, color) => list.length
      ? `<div class="flex items-baseline gap-1 flex-wrap mt-1">
           <span class="text-[9px] shrink-0" style="color:${color}">${label}</span>
           ${list.map((v) => `<button data-sel="${esc(v.name)}" title="${esc(v.name)}"
             class="font-mono text-[9px] px-1 rounded-sm bg-stone-100 dark:bg-stone-800
                    text-stone-600 dark:text-stone-300 hover:bg-stone-200">${esc(shortOf(v.name))}</button>`).join("")}
         </div>` : "";

    return `<div>
      ${prem}
      <div class="flex items-center gap-2 mt-1.5 mb-1">
        <span class="h-[1.5px] flex-1 rounded-sm" style="background:${roleColor(LDR.roles.roleOf(name, nd))}88"></span>
        <span class="font-mono text-[9px] text-stone-500 dark:text-stone-400 truncate max-w-[60%]"
              title="${esc(name)}">${esc(shortOf(name))}</span>
      </div>
      <div class="font-mono text-[11px] text-stone-900 dark:text-stone-100 leading-snug break-words"
           title="${esc(nd.conclusion || nd.typeString || "")}">${esc(conclusionOf(nd)) || "—"}</div>
      ${chip(parts.vocab, "語彙", LDR.roles.ROLE.vocab.c)}
      ${parts.frame.length ? `<details class="mt-1"><summary class="cursor-pointer text-[9px] text-stone-400">
          骨組み ${parts.frame.length} 件（論理結合子）</summary>
        <div class="flex flex-wrap gap-1 mt-1">${parts.frame.map((v) =>
          `<span class="font-mono text-[9px] px-1 rounded-sm bg-stone-100 dark:bg-stone-800 text-stone-400"
            >${esc(shortOf(v.name))}</span>`).join("")}</div></details>` : ""}
      ${parts.part && parts.part.length ? `<details class="mt-1"><summary class="cursor-pointer text-[9px] text-stone-400">
          断片 ${parts.part.length} 件（証明・本体の切り出し。中身は前提として上に展開済み）</summary>
        <div class="flex flex-wrap gap-1 mt-1">${parts.part.map((v) =>
          `<span class="font-mono text-[9px] px-1 rounded-sm bg-stone-100 dark:bg-stone-800 text-stone-400"
            >${esc(shortOf(v.name))}</span>`).join("")}</div></details>` : ""}
    </div>`;
  }

  /* 右パネルの主語。追従なら選択中の宣言、固定なら中心。四つの依存タブもこの主語の一覧を出す。
     見出し行に「中心」「選択」の別を明示し、中心でなければ「中心にする」を置く。 */
  function subjectHeader(st, dv, name) {
    const nd = st.nodes[name];
    const chips = st.previewHist.map((h) => `<button data-preview="${esc(h)}" title="${esc(h)}"
        class="font-mono text-[10px] px-1.5 py-0.5 rounded-sm ${h === name
          ? "bg-indigo-600 text-white"
          : "bg-stone-100 text-stone-600 hover:bg-stone-200 dark:bg-stone-800 dark:text-stone-300"}"
        >${esc(shortOf(h))}</button>`).join(" ");
    const modeBtn = (v, l, t) => `<button data-follow="${v}" title="${esc(t)}"
        class="px-2 py-0.5 text-[10.5px] rounded-sm ${(!!st.previewFollow) === (v === "1")
          ? "bg-stone-900 text-white dark:bg-stone-100 dark:text-stone-900"
          : "text-stone-500 hover:bg-stone-100 dark:hover:bg-stone-800"}">${l}</button>`;
    const isCenter = name === dv.center;
    const role = isCenter
      ? `<span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-indigo-600 text-white shrink-0" title="グラフの中心と同じ宣言">中心</span>`
      : `<span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-stone-700 text-white dark:bg-stone-200 dark:text-stone-900 shrink-0" title="選択中の宣言（グラフの中心とは別）">選択</span>`;
    return `
      <div class="flex items-center gap-1 px-1 pb-1">
        <span class="text-[10px] text-stone-400">見ている宣言</span>
        <div class="flex gap-0.5 p-0.5 rounded-md bg-stone-200/70 dark:bg-stone-800">
          ${modeBtn("0", "中心固定", "グラフの中心を出し続ける")}${modeBtn("1", "追従", "一覧やグラフで選んだ宣言を出す（中心は動かない）")}
        </div>
      </div>
      ${chips ? `<div class="flex flex-wrap gap-1 px-1 pb-1.5">${chips}</div>` : ""}
      ${nd ? `<div class="px-1 pb-1.5 flex items-center gap-1.5 flex-wrap border-b border-stone-200 dark:border-stone-700">
        ${role}
        ${dot(nd.kind, 7)}
        <span class="font-mono text-[12px] font-medium break-all">${esc(name)}</span>
        <span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-stone-100 dark:bg-stone-800 text-stone-600 dark:text-stone-300">${kinfo(nd.kind).ja}</span>
        ${isCenter ? "" : `<button data-nav="${esc(name)}" class="text-[10px] px-1.5 py-0.5 rounded-sm bg-indigo-600 text-white hover:bg-indigo-500">中心にする</button>`}
      </div>` : ""}`;
  }

  /* `<details>` の開閉を組み直しの前後で保つ。開閉の状態を store に持たせるほどのものではなく、
     組み直しのたびに閉じるのは読んでいる最中の視線を奪う。 */
  function keepOpen(body) {
    const kept = new Set();
    for (const d of body.querySelectorAll("details[data-keep]")) if (d.open) kept.add(d.dataset.keep);
    return (key) => (kept.has(key) ? " open" : "");
  }

  /* プレビュー。読む順に上から:
       見出し（主語）→ 所在（モジュール:行・パッケージ・docs）→ シグネチャ → 説明 →
       印（由来・派生・形・条件）と公理 → 前提の要約（公理・補題・語彙の数、依存パッケージ）→
       導出図（既定で畳む。cslib の定理は前提が 20 を超え、開きっぱなしでは画面が埋まる）→ 原文・証明項 */
  function renderPreview(st, dv) {
    const name = S.previewName();
    const nd = st.nodes[name];
    const body = $("depBody");
    const open = keepOpen(body);
    const header = subjectHeader(st, dv, name);

    if (!nd) { body.innerHTML = header + `<p class="px-2 py-4 text-center text-[12px] text-stone-400">対象がありません</p>`; return; }
    const seen = new Set([name]);
    const parts = LDR.roles.split(name, st.nodes);
    const nPrem = parts.axiom.length + parts.lemma.length;
    const OK = LDR.sig.ORIGIN_KIND;
    body.innerHTML = header + `
      <div class="px-1 pt-1.5 space-y-1.5">
        <div class="flex items-center gap-1.5 flex-wrap text-[10px] text-stone-500">
          <span class="font-mono" title="${esc(nd.module)}">${esc(nd.module)}${nd.line ? ":" + nd.line : ""}</span>
          ${pkgChip(nd)}
          <span class="flex-1"></span>
          ${docLinks(nd, name)}
        </div>
        <div class="rounded-md border border-stone-200 dark:border-stone-700 bg-stone-50 dark:bg-stone-950 px-1.5 py-1">
          ${signatureBlock(nd) || `<span class="text-[11px] text-stone-400">シグネチャ情報なし</span>`}
        </div>
        ${nd.docString ? `<p class="text-[11px] text-stone-600 dark:text-stone-400 leading-relaxed">${esc(nd.docString)}</p>` : ""}
        <div class="flex items-center gap-1 flex-wrap">${markChips(name, nd, dv)}</div>
        <div class="flex items-baseline gap-1 flex-wrap">
          <span class="text-[10px] text-stone-400 shrink-0">公理</span>${axiomChips(nd, st)}
        </div>
        <div class="flex items-baseline gap-2 flex-wrap text-[10px] text-stone-500">
          <span title="主張と証明項の節点数">型 ${nd.typeSize || 0} / 証明 ${nd.valueSize || 0} 節点</span>
          ${nd.subject ? `<span>主題 <span class="font-mono" title="${esc(nd.subject)}">${esc(shortOf(nd.subject))}</span></span>` : ""}
          ${nd.numUniverse ? `<span>宇宙 ${nd.numUniverse}</span>` : ""}
          ${nd.originRel && nd.origin ? `<span title="${esc((OK[nd.originKind] || {}).note || "")}">
              ${esc((LDR.sig.ORIGIN_REL[nd.originRel] || {}).ja || nd.originRel)}: <button data-sel="${esc(nd.origin)}" class="font-mono hover:underline">${esc(shortOf(nd.origin))}</button></span>` : ""}
        </div>
        ${depPackages(nd)}
        <details data-keep="deriv" class="rounded-md border border-stone-200 dark:border-stone-700"${open("deriv")}>
          <summary class="cursor-pointer select-none px-2 py-1 text-[10.5px] text-stone-600 dark:text-stone-300 flex items-baseline gap-2 flex-wrap">
            <span>導出図</span>
            <span class="text-stone-400">前提 ${nPrem}（公理 ${parts.axiom.length} · 補題 ${parts.lemma.length}）· 語彙 ${parts.vocab.length}${parts.frame.length ? ` · 骨組み ${parts.frame.length}` : ""}${parts.part && parts.part.length ? ` · 断片 ${parts.part.length}` : ""}</span>
            <span class="text-[9.5px] text-stone-400">前提は横線の上、結論は下。▸ で前提の導出を開く</span>
          </summary>
          <div class="px-2 pb-2">${derivation(name, st, 3, seen)}</div>
        </details>
        ${nd.typeString ? `<details data-keep="type"${open("type")}>
          <summary class="cursor-pointer text-[10px] text-stone-400 hover:text-stone-600">原文を表示</summary>
          <pre class="mt-1 font-mono text-[10px] leading-relaxed whitespace-pre-wrap break-words
            bg-stone-50 dark:bg-stone-950 border border-stone-200 dark:border-stone-700 rounded-sm px-2 py-1
            max-h-48 overflow-y-auto">${esc(nd.typeString)}</pre></details>` : ""}
        ${nd.valueString ? `<details data-keep="value"${open("value")}><summary class="cursor-pointer text-[10.5px] text-stone-400">証明項</summary>
          <pre class="mt-1 font-mono text-[10px] whitespace-pre-wrap break-words leading-snug
            bg-stone-50 dark:bg-stone-950 border border-stone-200 dark:border-stone-700 rounded-sm px-2 py-1
            max-h-48 overflow-y-auto">${esc(nd.valueString)}</pre></details>` : ""}
      </div>`;
  }

  /* ================= 法則の在庫表 =================

     行が関係・演算、列が法則。埋まっている欄は「その法則がこの関係について
     証明されている」ことを、押せばその定理へ飛べる形で示す。

     欄が空なのは「まだ証明されていない」であって「成り立たない」ではない。
     判定は誤って付けない向きに倒してあるので、別の形で証明されているものは
     取り逃す。そのことは表の下に明記する。数学の主張として誤読されるのが
     一番まずい。

     右端に、列の組み合わせから読める判断を出す。反射と推移が揃えば前順序、
     さらに反対称が揃えば半順序、反射・対称・推移なら同値関係。
     これがこの表の本当の目的で、一覧を眺めるだけで構造が分かる。 */
  const LAW_JA = {
    refl: "反射", irrefl: "非反射", symm: "対称", trans: "推移", antisymm: "反対称",
    total: "全域", mono: "単調", comm: "可換", assoc: "結合", idem: "冪等",
    absorb: "吸収", distrib: "分配",
  };
  const LAW_HUE = {
    refl: 200, irrefl: 210, symm: 265, trans: 155, antisymm: 25,
    total: 262, mono: 235, comm: 320, assoc: 300, idem: 95,
    absorb: 281, distrib: 291,
  };

  function renderLaws(st) {
    const body = $("depBody");
    const inv = S.lawInventory();
    const laws = inv.LAWS;
    if (!inv.list.length) {
      body.innerHTML = `<p class="px-2 py-6 text-center text-[12px] text-stone-400">
        判定できた法則がありません（古い形式のレポートか、該当する形の定理がありません）</p>`;
      return;
    }
    const head = `<div class="grid gap-px sticky top-0 bg-white dark:bg-stone-900 z-10"
        style="grid-template-columns: minmax(96px,1fr) repeat(${laws.length}, 22px) 62px">
      <div class="text-[9.5px] text-stone-400 pb-1">関係・演算</div>
      ${laws.map((l) => `<div class="text-[9px] text-center pb-1 leading-none"
          style="writing-mode:vertical-rl;height:38px;color:hsl(${LAW_HUE[l]},45%,45%)"
          title="${esc(LAW_JA[l])}">${esc(LAW_JA[l])}</div>`).join("")}
      <div class="text-[9.5px] text-stone-400 pb-1 text-right">判断</div>
    </div>`;

    const rows = inv.list.map((r) => {
      /* 配色は動的なクラス名ではなく実値で持つ。CDN 版 Tailwind は DOM を
         監視して生成するが、組み立てたクラス名は取りこぼし得るので値で書く。
         判断そのものは store.lawInventory が一元的に計算する（重複実装は乖離する）。 */
      const verdict = r.verdict;
      const cells = laws.map((l) => {
        const list = r.laws[l] || [];
        if (!list.length) {
          return `<div class="h-5 flex items-center justify-center text-[9px] text-stone-300 dark:text-stone-700">·</div>`;
        }
        // 二演算法則(吸収・分配)は相方が、単調はその関係が意味の半分を担う。tooltip に対を明示する
        const partners = r.pairs && r.pairs[l]
          ? ` — ${l === "mono" ? "関係" : "相方"} ${[...r.pairs[l]].map(shortOf).join(", ")}` : "";
        return `<button data-sel="${esc(list[0])}" title="${esc(LAW_JA[l])}${esc(partners)}: ${esc(list[0])}${list.length > 1 ? ` 他 ${list.length - 1} 件` : ""}"
          class="h-5 w-full rounded-[3px] text-[9px] font-medium text-white flex items-center justify-center hover:brightness-110"
          style="background:hsl(${LAW_HUE[l]},58%,48%)">${list.length > 1 ? list.length : ""}</button>`;
      }).join("");
      return `<div class="grid gap-px items-center hover:bg-stone-50 dark:hover:bg-stone-800/50 rounded-sm"
          style="grid-template-columns: minmax(96px,1fr) repeat(${laws.length}, 22px) 62px">
        <button data-sel="${esc(r.rel)}" title="${esc(r.rel)}${r.type ? " の " + esc(r.type) + " 上の法則" : "（担い手の型は多相）"}"
          class="text-left font-mono text-[10px] truncate pr-1 hover:underline">${esc(shortOf(r.rel))}${
            r.type ? `<span class="text-stone-400"> @ ${esc(shortOf(r.type))}</span>` : ""}</button>
        ${cells}
        <div class="text-right pl-1">${verdict
          ? `<span class="text-[9px] px-1 py-0.5 rounded-sm font-medium"
               style="background:hsl(${verdict.h},70%,92%);color:hsl(${verdict.h},60%,30%)">${verdict.t}</span>`
          : `<span class="text-[9px] text-stone-300 dark:text-stone-700">—</span>`}</div>
      </div>`;
    }).join("");

    const proved = inv.list.reduce((a, r) => a + r.total, 0);
    body.innerHTML = `
      <div class="px-1 pb-1.5 text-[10px] text-stone-500 dark:text-stone-400 leading-relaxed">
        ${inv.list.length} 個の関係・演算（担い手の型ごと）について ${proved} 件の法則を検出。
        対象の宣言が証明したものだけを数え、押すとその定理を選びます。
      </div>
      <div class="px-1 overflow-x-auto">${head}<div class="space-y-px">${rows}</div></div>
      <p class="px-1 pt-2 text-[9.5px] text-stone-400 leading-relaxed">
        空欄は「まだ証明されていない」であって「成り立たない」ではありません。
        判定は仮定と結論の構文的な形から行い、誤って付けない向きに倒してあるので、
        別の言い回しで証明されているものは取り逃します。
        同じ理由から <code>sorry</code> を含む宣言は数えません
        （埋まった欄が嘘をつかないため）。
      </p>`;
  }

  /* 右パネル。主語は一つ（S.previewName：追従なら選択中、固定なら中心）。
     以前は四つの依存タブだけが中心を出していたので、選択を変えるとプレビューだけが変わり
     依存の一覧は中心のまま、という食い違いがあった（指摘）。 */
  function renderDeps(st, dv) {
    const name = S.previewName();
    const cur = $("depTabs").dataset.tab || "prev";
    once("deps", name + "|" + dv.center + "|" + cur + "|" + st.selected + "|" + st.edgeMode + "|"
      + st.previewFollow + "|" + st.previewHist.length + "|" + st.traceTarget
      + "|" + (name ? S.isClusterOpen(name) + S.isClusterForced(name) : "")
      + "|" + [...st.derivOpen].sort().join(","), () => {
      const nd = st.nodes[name];
      const tabs = $("depTabs"), body = $("depBody");
      if (!nd) {
        tabs.innerHTML = "";
        body.innerHTML = subjectHeader(st, dv, name) + `<p class="px-2 py-4 text-center text-[12px] text-stone-400">対象がありません</p>`;
        return;
      }
      const idx = dv.declIdx;
      const s = esc(shortOf(name));
      const sets = {
        type:  { list: nd.typeDeps || [], label: "↑ 型依存",
                 note: `<b>${s} の主張に現れる</b>宣言。この宣言が何を述べているかを決めるので、意味論的なレビュー対象。` },
        value: { list: nd.valueDeps || [], label: "↑ 値依存",
                 note: `<b>${s} の証明にだけ現れる</b>宣言。定理ならカーネル検査済み（証明無関係性）なので、主張の構造には効かない。` },
        refT:  { list: idx.refType[name] || [], label: "↓ 主張で参照",
                 note: `<b>${s} を主張に含む</b>宣言。つまり「${s} についての定理・性質」。ここから何が回収できたかが読める。` },
        refV:  { list: idx.refValue[name] || [], label: "↓ 証明で参照",
                 note: `<b>${s} を証明の道具としてのみ使う</b>宣言。主張には現れないので、${s} について何かを述べているわけではない。` },
      };
      const mk = (id, label) => `<button data-tab="${id}"
        class="px-2 py-1 text-[11px] rounded-md ${cur === id
          ? "bg-stone-900 text-white dark:bg-stone-100 dark:text-stone-900"
          : "text-stone-600 hover:bg-stone-100 dark:text-stone-300 dark:hover:bg-stone-800"}">${label}</button>`;
      tabs.innerHTML = mk("prev", "プレビュー") + mk("laws", "法則")
        + ["type", "value", "refT", "refV"].map((id) => mk(id, `${sets[id].label} ${sets[id].list.length}`)).join("");
      if (cur === "prev") { renderPreview(st, dv); return; }
      if (cur === "laws") { renderLaws(st); return; }
      const sel = sets[cur] || sets.type;
      /* 並びは総仮定量の昇順。原始的なものから積み上がる向きに読める。
         名前順だと、何から出来ているのかの手掛かりにならない。 */
      const met = S.metrics();
      const sorted = sel.list.slice().sort((a, b) =>
        ((met.closure[a] || 0) - (met.closure[b] || 0)) || (a < b ? -1 : 1));
      body.innerHTML = subjectHeader(st, dv, name)
        + `<p class="px-2 pb-1.5 pt-1.5 text-[11px] text-stone-500 dark:text-stone-400 leading-relaxed">${sel.note}</p>`
        + (sorted.length
          ? `<div class="space-y-0.5">${sorted.map((n) => depRow(n, st)).join("")}</div>`
          : `<p class="px-2 py-4 text-center text-[12px] text-stone-400">なし</p>`);
    });
  }

  /* ================= 探索履歴ツリー ================= */
  function renderHistory(st) {
    const h = st.hist;
    once("hist", h.seq + "|" + h.curId + "|" + h.order.length, () => {
      const el = $("histBody");
      if (!h.order.length) {
        el.innerHTML = `<p class="px-2 py-3 text-[12px] text-stone-400 text-center">まだ移動していません</p>`;
        $("histCount").textContent = "";
        return;
      }
      const path = new Set();
      for (let p = h.curId; p; p = h.nodes[p].parent) path.add(p);
      const out = [];
      const walk = (id, depth) => {
        const nd = h.nodes[id];
        if (!nd) return;
        const isCur = id === h.curId;
        const onPath = path.has(id);
        out.push(`<button data-hist="${id}" title="${esc(nd.name)}"
          style="padding-left:${4 + depth * 12}px"
          class="w-full text-left pr-2 py-1 rounded-sm flex items-center gap-1.5
                 ${isCur ? "bg-indigo-600 text-white"
                         : onPath ? "bg-indigo-50 dark:bg-indigo-950/50 text-indigo-900 dark:text-indigo-200"
                                  : "hover:bg-stone-100 dark:hover:bg-stone-800"}">
          <span class="text-[9.5px] ${isCur ? "text-indigo-200" : "text-stone-400"}">${depth ? "└" : "•"}</span>
          <span class="font-mono text-[11px] truncate flex-1">${esc(shortOf(nd.name))}</span>
        </button>`);
        for (const ch of nd.children) walk(ch, depth + 1);
      };
      for (const id of h.order) if (!h.nodes[id].parent) walk(id, 0);
      el.innerHTML = out.join("");
      $("histCount").textContent = `${h.order.length} / 50`;
    });
  }

  /* ================= ピン留め ================= */
  function renderPins(st) {
    once("pins", st.pins.map((p) => p.id).join(",") , () => {
      const el = $("pinBody");
      if (!st.pins.length) {
        el.innerHTML = `<p class="px-2 py-3 text-[12px] text-stone-400 text-center">閲覧状態を保存できます</p>`;
        $("pinCount").textContent = "";
        return;
      }
      el.innerHTML = st.pins.map((p) => {
        const d = new Date(p.ts);
        const t = `${String(d.getMonth() + 1).padStart(2, "0")}/${String(d.getDate()).padStart(2, "0")} ${String(d.getHours()).padStart(2, "0")}:${String(d.getMinutes()).padStart(2, "0")}`;
        // ピンは JSON で取り込める（外部入力）ので、埋め込む値は全て esc を通す
        const exp = Array.isArray(p.snap.expanded) ? p.snap.expanded.length : 0;
        return `<div class="flex items-center gap-1 group">
          <button data-pin="${esc(p.id)}" title="${esc(p.snap.center || "")}"
            class="flex-1 min-w-0 text-left px-2 py-1 rounded-sm hover:bg-stone-100 dark:hover:bg-stone-800">
            <span class="font-mono text-[11px] truncate block">${esc(shortOf(p.label || ""))}</span>
            <span class="text-[9.5px] text-stone-400">${t} · 深さ${esc(p.snap.baseDepth ?? 1)} · 下錐${{ all: "両方", type: "主張", value: "呼出" }[p.snap.refFilter] || "両方"}${exp ? ` · 展開${exp}` : ""}</span>
          </button>
          <button data-unpin="${esc(p.id)}" title="削除"
            class="w-6 h-6 shrink-0 rounded-sm text-stone-400 opacity-0 group-hover:opacity-100 hover:bg-stone-200 dark:hover:bg-stone-700">✕</button>
        </div>`;
      }).join("");
      $("pinCount").textContent = `${st.pins.length}`;
    });
  }

  /* ================= 最小の仮定 ================= */
  function renderMinimal(st, dv) {
    const tm = dv.trueMinimal || [];
    // チップの不透明度は「いま描画対象か(n ∈ posAll)」に依存する。
    // 可視集合の指紋を鍵に含めないと、展開・深さ変更後も古い明暗のままになる。
    // 開閉（派生）でも描画対象は変わるので、開閉の署名も鍵に入れる（描画数が同じでも中身は違い得る）
    const visSig = Object.keys(dv.posAll || {}).length + "|" + st.baseDepth + "|" + st.expanded.size + "|" + S.openSignature();
    once("min", dv.center + "|" + st.traceTarget + "|" + (dv.traceUnreachable || "") + "|" + tm.length + "|" + visSig, () => {
      const el = $("minimalBox");
      const vis = dv.posAll || {};
      $("minCount").textContent =
        `${tm.length} 件 / 上向きの全 ${dv.fullDownSize || 0} 件のうち依存先を持たないもの`;
      /* 公理チップ等から経路表示を求めたが、読み込んだ範囲に中心からの経路が無い。
         公理は Lean 側が証明項を最後まで辿って集めたもので、依存グラフは一段先までしか
         持たないので、両者の食い違いは起こり得る。黙って全てを暗くせず、ここで伝える。
         この区画は既定で畳まれている（見出しの公理チップから求めた場合は見えない）ので、開く。 */
      const unreachable = dv.traceUnreachable
        ? `<div class="mb-1 text-[10.5px] px-2 py-1 rounded-sm bg-amber-50 text-amber-900 dark:bg-amber-950/60 dark:text-amber-200">
             <span class="font-mono">${esc(shortOf(dv.traceUnreachable))}</span> への経路は読み込んだ範囲にありません
             （公理は証明項の末端まで辿った結果で、依存グラフは対象の外を一段しか持たないため）。
             <button data-trace="${esc(dv.traceUnreachable)}" class="underline">解除</button>
           </div>` : "";
      if (dv.traceUnreachable && $("minimalWrap")) $("minimalWrap").open = true;
      const chip = (n) => {
        const on = st.traceTarget === n;
        const shown = n in vis;
        return `<button data-trace="${esc(n)}" title="${esc(n)}"
          class="font-mono text-[10.5px] px-2 py-0.5 rounded-full transition
                 bg-amber-100 text-amber-900 dark:bg-amber-950/70 dark:text-amber-200
                 ${on ? "ring-2 ring-amber-500" : "hover:ring-1 hover:ring-amber-400"}
                 ${shown ? "" : "opacity-60"}">${esc(shortOf(n))}</button>`;
      };
      el.innerHTML = unreachable + `
        <div class="flex items-baseline gap-2 flex-wrap mb-1">
          <span class="text-[10.5px] text-stone-500">押すとそこへ至る経路だけを表示</span>
          ${st.traceTarget ? `<button data-trace="${esc(st.traceTarget)}"
            class="text-[10.5px] px-1.5 py-0.5 rounded-sm bg-amber-500 text-white">経路表示を解除</button>` : ""}
        </div>
        <div class="flex flex-wrap gap-1">${tm.length
          ? tm.map(chip).join("")
          : '<span class="text-[12px] text-stone-400">依存先がありません（この宣言自身が原始的）</span>'}</div>`;
    });
  }

  /* ================= ツールバー ================= */
  function renderToolbar(st, dv) {
    const cur = S.histCur();
    const canBack = !!(cur && cur.parent);
    const canFwd = !!(cur && (cur.last || cur.children.length));
    $("btnBack").disabled = !canBack; $("btnFwd").disabled = !canFwd;
    $("btnBack").classList.toggle("opacity-30", !canBack);
    $("btnFwd").classList.toggle("opacity-30", !canFwd);

    once("toolbar", [st.edgeMode, st.granularity, st.baseDepth, st.refFilter,
      st.expanded.size, [...st.kindFilter].sort().join(","), st.listMode,
      st.groupBy, st.density, st.hideFrame,
      Object.keys(st.nodes).length, dv.center].join("|"), () => {
      const seg = (id, cur2, opts) => opts.map((o) => `<button data-${id}="${o.v}" title="${esc(o.t || "")}"
        class="px-2.5 py-1 text-[12.5px] rounded-md ${cur2 === o.v
          ? "bg-white dark:bg-stone-700 shadow-sm text-stone-900 dark:text-stone-100"
          : "text-stone-500 hover:text-stone-800 dark:hover:text-stone-200"}">${o.l}</button>`).join("");
      $("segEdge").innerHTML = seg("edge", st.edgeMode, [{ v: "all", l: "型+値" }, { v: "type", l: "型のみ" }]);
      $("segGran").innerHTML = seg("gran", st.granularity, [{ v: "decl", l: "宣言" }, { v: "module", l: "モジュール" }]);
      /* 一覧の並べ方。どちらも木なので「ツリー」では区別にならない。何で枝を作るかを名前にする。 */
      $("segList").innerHTML = seg("list", st.listMode, [
        { v: "tree", l: "モジュール", t: "ファイル（モジュール）の階層で並べる。ファイルの中は定義された順" },
        { v: "ns",   l: "名前空間",   t: "namespace の階層で並べる（初出順）。型の行がその名前空間の見出しを兼ね、構成子・フィールドを畳める" }]);
      $("segGroup").innerHTML = seg("group", st.groupBy, [
        { v: "subject", l: "主題", t: "結論の主題（何についての宣言か）で束ねる" },
        { v: "module", l: "モジュール", t: "定義されているファイルで束ねる" },
        { v: "package", l: "パッケージ", t: "出どころのパッケージ（対象 / Mathlib / cslib / core …）で束ねる。上の錐が依存先のパッケージごとの扇になる" },
        { v: "kind", l: "種別", t: "定理・定義・帰納型などの種別で束ねる" },
        { v: "none", l: "なし" }]);
      $("segDensity").innerHTML = [24, 36, 48, 72].map((d) => `<button data-density="${d}"
        class="px-1.5 py-0.5 text-[10.5px] rounded-sm ${st.density === d
          ? "bg-white dark:bg-stone-700 shadow-sm text-stone-900 dark:text-stone-100"
          : "text-stone-500 hover:text-stone-800 dark:hover:text-stone-200"}">${d}</button>`).join("");
      // 下の参照錐に入れる辺。既定は「両方」で、呼び出し元も最初から下に開く。
      $("segRef").innerHTML = seg("ref", st.refFilter, [
        { v: "all", l: "両方" }, { v: "type", l: "主張のみ" }, { v: "value", l: "呼出のみ" }]);
      $("depthVal").textContent = st.baseDepth;
      $("depthRange").value = st.baseDepth;
      $("btnCollapse").classList.toggle("hidden", st.expanded.size === 0);
      $("btnCollapse").textContent = `展開を畳む (${st.expanded.size})`;

      const mark = (el, on, cls) => cls.forEach((c) => el.classList.toggle(c, on));
      mark($("btnFrame"), st.hideFrame,
        ["bg-stone-900", "text-white", "dark:bg-stone-100", "dark:text-stone-900", "border-stone-900"]);

      const kinds = [...new Set(Object.values(st.nodes).map((n) => n.kind))].sort();
      $("kindChips").innerHTML = kinds.map((k) => {
        const on = st.kindFilter.has(k);
        return `<button data-kind="${esc(k)}" class="px-1.5 py-0.5 rounded-sm text-[11px] flex items-center gap-1
          ${on ? "bg-stone-900 text-white dark:bg-stone-100 dark:text-stone-900" : "bg-stone-100 text-stone-600 dark:bg-stone-800 dark:text-stone-300"}">
          ${dot(k, 6)}${kinfo(k).ja}</button>`;
      }).join("");

      $("crumb").innerHTML = `<span class="font-mono text-[12px] text-stone-500 truncate">${esc(dv.center || "")}</span>`;
    });
  }

  function renderAll(st, dv) {
    if (!dv || !dv.posAll) return;
    renderToolbar(st, dv);
    renderAudit(st);
    renderFilters(st, dv);
    renderList(st, dv);
    renderInspector(st, dv);
    renderDeps(st, dv);
    renderHistory(st);
    renderPins(st);
    renderMinimal(st, dv);
  }

  LDR.panels = { renderAll, KIND, kinfo, invalidate: () => { for (const k of Object.keys(memo)) delete memo[k]; } };
})(window.LDR = window.LDR || {});
