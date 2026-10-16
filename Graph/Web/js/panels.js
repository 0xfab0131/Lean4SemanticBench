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
  const V = { host: null, win: null, spacer: null, sticky: null, rows: [], top: 0, raf: 0, wantReveal: -1 };

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
    /* 窓はその瞬間の高さとスクロール位置で描く。起動時の描画はレポートの読み込み（IndexedDB と
       埋め込みスクリプトを待つ非同期）の後に走り、その時点では欄の高さが確定していないことがある
       （Tailwind の実行時コンパイル・幅の復元・欄の開閉）。高さが後から変わっても scroll 事象は
       起きないので、何かに触るまで一覧が空のままだった（実測）。高さの変化そのものを監視して描き直し、
       中心の行への送り（revealRow）も高さが確定してから行う。 */
    if (typeof ResizeObserver === "function") {
      new ResizeObserver(() => {
        if (!V.host.clientHeight) return;
        vpaint();
        if (V.wantReveal >= 0) { const i = V.wantReveal; V.wantReveal = -1; revealRow(i); }
      }).observe(host);
    }
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
    // 高さが無い（まだ配置されていない・畳まれている）間は送れない。高さが付いたときに送る（vmount の監視）
    if (!V.host.clientHeight) { V.wantReveal = i; return; }
    const h = V.host.clientHeight;
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
  /* 幅が足りないときは接頭辞を先に縮め（flex-shrink を大きく）、それでも足りなければ末尾も
     切り詰める。末尾を縮まない指定にすると、深い枝で名前が件数の上に重なる（実測）。 */
  const nameHtml = (shown) => {
    const { prefix, last } = splitName(LDR.sig.userName(shown));
    return `<span class="font-mono text-[11px] min-w-0 flex-1 flex items-baseline">
      ${prefix ? `<span class="truncate text-stone-400 dark:text-stone-500" style="flex-shrink:999">${esc(prefix)}.</span>` : ""}
      <span class="min-w-0 truncate" style="flex-shrink:1">${esc(last)}</span></span>`;
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
      for (const e of pathOf(n)) {
        const { seg, kind } = e;
        prefix = prefix ? prefix + "." + seg : seg;
        // 名前空間の完全名。経路が省いた分（モジュール名と重なる接頭辞）は e.nsName が持つ
        if (kind === "ns") nsName = e.nsName || (nsName ? nsName + "." + seg : seg);
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
    /* 一本道のモジュールの枝（`Cslib › Crypto › Protocols`、宣言も分岐も無い）は一行に畳む
       （`Cslib.Crypto.Protocols`）。段ごとに一行と一段の字下げを使うと、264px の一覧で
       五段が字下げだけで埋まり、名前が件数に重なった（実測）。鍵（prefix）は末尾の枝のもの。 */
    (function compact(node) {
      const out = new Map();
      for (let ch of node.children.values()) {
        while (ch.kind === "module" && ch.items.length === 0 && ch.children.size === 1) {
          const only = [...ch.children.values()][0];
          if (only.kind !== "module") break;
          only.seg = ch.seg + "." + only.seg;
          ch = only;
        }
        compact(ch);
        out.set(ch.kind + ":" + ch.seg, ch);
      }
      node.children = out;
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
          /* 枝に対する相対名。名前空間の枝なら nsName、モジュールの枝ならモジュール名（prefix）を
             基準にする（`Cslib.Crypto.….Shamir.gen` がモジュール `….Shamir` の直下に来たとき
             完全名のまま出て、接頭辞だけで幅が埋まった。実測）。 */
          const shown = relName(n, ch.kind === "ns" ? ch.nsName : ch.prefix);
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

  /* 名前空間の成分列（利用者名から末尾一成分を落としたもの。private 名は接頭辞を外す） */
  const nsPath = (n) => LDR.sig.userName(n).split(".").slice(0, -1).map((seg) => ({ seg, kind: "ns" }));

  /* 基準（枝の名前）と共通する先頭の成分を落とした相対名。末尾の成分は必ず残す
     （`A.B.C` を基準 `A.B.C` に対して出すなら `C`）。 */
  function relName(n, base) {
    const a = LDR.sig.userName(n).split("."), b = String(base || "").split(".");
    let k = 0;
    while (k < a.length - 1 && k < b.length && a[k] === b[k]) k++;
    return a.slice(k).join(".");
  }

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

    /* モジュール = ファイルの階層（名前順）→ その中は名前空間の木（初出順）。
       Lean ではファイルと名前空間が一致するのが普通（`Cslib/…/Shamir.lean` の中が
       `namespace Cslib.….Shamir`）。名前空間のうちモジュール名と重なる先頭の成分は省き、
       同じ五段を二度並べない（実測）。省いた分の完全名は nsName で持ち、型の行を見出しに
       する判定（attachHeads）と相対名の表示に使う。 */
    const pathOf = (n) => {
      const mods = String(st.nodes[n].module).split(".");
      const ns = LDR.sig.userName(n).split(".").slice(0, -1);
      let k = 0;
      while (k < mods.length && k < ns.length && mods[k] === ns[k]) k++;
      return mods.map((seg) => ({ seg, kind: "module" }))
        .concat(ns.slice(k).map((seg, i) => ({ seg, kind: "ns", nsName: ns.slice(0, k + i + 1).join(".") })));
    };
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

  // 表示用の短い名前。private 名は利用者名（`_private.….0.` を外したもの）で
  function shortOf(n) {
    const u = LDR.sig.userName(n);
    const p = u.split(".");
    return p.length <= 2 ? u : p.slice(-2).join(".");
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
              title="自分にも依存先にも仮定（Prop の束縛）が無い。無条件に得たものだけから無条件に得られている（インスタンス束縛は引数であって仮定ではないので数えない）">無条件で閉じる ${hered}</span>
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
      // 札の内側では折り返さない（「sorry のみ／(0)」と二行に割れた。実測）。狭ければ札ごと次の行へ
      const tog = (id, on, label, title) => `<button data-filter="${id}" title="${esc(title)}"
        class="px-2 py-1 rounded-md text-[11.5px] flex items-center gap-1.5 border whitespace-nowrap
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
  /* 文字のリンクにする（枠付きのボタンが二つ並ぶと所在の行が折り返して二行になった。実測）。
     どの文書サイトへ行くかを文言と色で示す（「docs」だけでは Mathlib か cslib か分からない。指摘）。 */
  function docLinks(nd, name) {
    const P = LDR.pkg;
    const url = P ? P.docsUrl(nd, name) : null;
    const pkg = P ? (P.packageOf(nd && nd.module) || P.packageOf(name)) : "";
    const leaf = encodeURIComponent(String(name).split(".").slice(-1)[0]);
    return (url ? `<a href="${esc(url)}" target="_blank" rel="noopener" class="btn" style="color:${P.colorOf(pkg)};border-color:${P.colorOf(pkg)}88"
           title="${esc(P.labelOf(pkg))} の公式ドキュメント（${url.includes("search.html") ? "検索" : "この宣言のページ"}）: ${esc(url)}">📘 ${esc(P.labelOf(pkg))} docs ↗</a>` : "")
      + `<a href="https://leansearch.net/?q=${leaf}" target="_blank" rel="noopener" class="btn"
           title="LeanSearch で意味検索">🔎 LeanSearch ↗</a>`;
  }

  /* docString の最小限の整形。バッククォートはコード、空行は段落。それ以上の Markdown は解釈しない
     （誤った整形は原文を歪める）。 */
  function docHtml(s) {
    const paras = String(s || "").trim().split(/\n\s*\n/);
    return paras.map((p) => `<p>${esc(p.replace(/\s*\n\s*/g, " ")).replace(/`([^`]+)`/g, "<code>$1</code>")}</p>`).join("");
  }

  /* 原文の色付け。構文解析はしない（Lean の文法を再実装すると必ず乖離する）。
     行ごとに、コメント（`--` と `/- … -/`。複数行は状態で持ち越す）、文字列、属性 `@[…]`、
     先頭のキーワードと宣言名だけを色で分ける。残りは素のまま。行番号は宣言範囲の開始行から。 */
  const LEAN_KW = new Set(["theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive",
    "where", "extends", "deriving", "namespace", "section", "end", "open", "variable", "universe", "private",
    "protected", "noncomputable", "partial", "unsafe", "by", "fun", "let", "have", "show", "from", "match", "with",
    "if", "then", "else", "do", "return", "for", "in", "mut", "calc", "at", "import", "export", "opaque", "axiom",
    "example", "set_option", "attribute", "local", "scoped", "macro", "syntax", "elab", "omit", "include"]);
  function leanLine(line, st) {
    let out = "", i = 0;
    const put = (cls, t) => { out += cls ? `<span class="${cls}">${esc(t)}</span>` : esc(t); };
    while (i < line.length) {
      if (st.block > 0) {
        const close = line.indexOf("-/", i), open = line.indexOf("/-", i);
        if (open >= 0 && (close < 0 || open < close)) { put("cm", line.slice(i, open + 2)); st.block++; i = open + 2; continue; }
        if (close >= 0) { put("cm", line.slice(i, close + 2)); st.block--; i = close + 2; continue; }
        put("cm", line.slice(i)); break;
      }
      const rest = line.slice(i);
      let m;
      if (rest.startsWith("--")) { put("cm", rest); break; }
      if (rest.startsWith("/-")) { st.block++; put("cm", "/-"); i += 2; continue; }
      if ((m = rest.match(/^"(?:[^"\\]|\\.)*"/))) { put("st", m[0]); i += m[0].length; continue; }
      if ((m = rest.match(/^@\[[^\]]*\]/))) { put("at", m[0]); i += m[0].length; continue; }
      if ((m = rest.match(/^[A-Za-z_][A-Za-z0-9_'!?.₀-₉]*/))) {
        const w = m[0];
        if (LEAN_KW.has(w)) {
          put("kw", w); i += w.length;
          // 宣言キーワードの直後の識別子は宣言名
          const nm = line.slice(i).match(/^(\s+)([^\s(){}\[\]:]+)/);
          if (nm && /^(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|namespace|section|example)$/.test(w)) {
            put("", nm[1]); put("nm", nm[2]); i += nm[0].length;
          }
          continue;
        }
        put("", w); i += w.length; continue;
      }
      put("", rest[0]); i += 1;
    }
    return out;
  }
  function sourceHtml(src, firstLine) {
    const st = { block: 0 };
    return String(src).split("\n").map((l, k) =>
      `<div class="ln"><span class="no">${firstLine + k}</span><span class="tx">${leanLine(l, st) || " "}</span></div>`).join("");
  }

  /* パッケージの札（対象の外の宣言にだけ。対象のパッケージは出さない） */
  function pkgChip(nd) {
    const P = LDR.pkg;
    if (!P || !nd || !nd.external) return "";
    const p = P.packageOf(nd.module);
    const tp = LDR.canvas && LDR.canvas.targetPackage ? LDR.canvas.targetPackage(S.state) : "";
    if (!p || p === tp) return "";
    return `<span class="tag" style="color:${P.colorOf(p)};background:${P.colorOf(p)}14"
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
    return `<div class="row">
      <span class="lbl" title="直接依存する宣言が定義されているモジュールを、パッケージごとに数えたもの">依存先</span>
      ${keys.map((p) => `<span class="tag" style="${p === tp ? "" : `color:${P.colorOf(p)};background:${P.colorOf(p)}14`}"
          title="${esc(P.labelOf(p))}${p === tp ? "（対象のパッケージ）" : ""}: ${esc(sum[p].modules.sort().join("\n"))}">${esc(P.labelOf(p))}${p === tp ? "（対象）" : ""} ${sum[p].n}</span>`).join("")}
    </div>`;
  }

  /* 束縛の書き方は Lean の記法そのもの: `(x : T)` 明示 / `{x : T}` 暗黙 / `⦃x : T⦄` 強い暗黙 /
     `[C α]` インスタンス。無名の束縛（`[Field F]`、`→` で書かれた仮定）は名前を書かない。
     旧いレポートは衛生名（`inst._@.….13`、`_hyg`）を生で持つので、ここで無名として扱う。 */
  const KIND_TITLE = { explicit: "明示引数", implicit: "暗黙引数", strictImplicit: "強い暗黙引数", inst: "インスタンス引数（型クラス）" };
  const cleanBinderName = (s) => {
    const t = String(s || "");
    // 無名は Lean 側が Name.anonymous を出す（文字列化すると "[anonymous]"）。旧形式の衛生名も無名に
    return (t === "[anonymous]" || /(^|\.)_@\.|_hyg/.test(t)) ? "" : t;
  };
  function binderHtml(b) {
    const nm = cleanBinderName(b.name);
    const name = nm ? `<span class="font-mono text-stone-900 dark:text-stone-100">${esc(nm)}</span>` : "";
    const ty = expr(b.type);
    const wrap = (l, r, body) => `<span class="text-stone-400">${l}</span>${body}<span class="text-stone-400">${r}</span>`;
    const colon = `<span class="text-stone-400"> : </span>`;
    let body;
    const us = `<span class="text-stone-400">_</span>`;
    switch (b.kind) {
      case "inst":           body = nm ? wrap("[", "]", name + colon + ty) : wrap("[", "]", ty); break;
      case "implicit":       body = wrap("{", "}", (name || us) + colon + ty); break;
      case "strictImplicit": body = wrap("⦃", "⦄", (name || us) + colon + ty); break;
      // 無名の明示引数: 仮定（命題）なら `P →` のように型だけ、データなら `(_ : α)`（`α` だけでは引数と読めない）
      default:               body = nm ? wrap("(", ")", name + colon + ty) : (b.prop ? ty : wrap("(", ")", us + colon + ty)); break;
    }
    return `<span title="${esc(KIND_TITLE[b.kind] || b.kind)}">${body}</span>`;
  }

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
          title="自分に仮定が無く、依存先も全て仮定を持たない（インスタンス束縛は引数であって仮定ではないので数えない）。無条件に得たものだけから無条件に得られている">無条件で閉じる</span>`
      : `<span class="${cls("bg-emerald-50 text-emerald-700 dark:bg-emerald-950/60 dark:text-emerald-300")}"
          title="自分には条件が無いが、依存の先に仮定付きのものを含む">無条件</span>`;
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
    // 区画の札（引数・仮定・結論）は幅を固定した列。CSS は index.html の .pv .sig-sec（w-7 では縦に割れた。実測）
    // 札の幅は em（index.html の .pv .sig-sec .lbl）。px だと文字が大きく描かれる環境で本文に密着する
    const section = (label, rows, barColor, tone) => rows.length ? `
      <div class="sig-sec" style="border-left-color:${barColor}">
        <span class="lbl ${tone}">${label}</span>
        <div class="min-w-0 flex-1" style="min-width:0;flex:1 1 auto">${rows.join("")}</div>
      </div>` : "";
    const line = (body) => `<div class="sig-line">${body}</div>`;
    const sub = (t) => `<span class="text-[9.5px] text-stone-400 mr-1">${t}</span>`;

    const argRows = args.map((b) => line(binderHtml(b)));
    const hypRows = hyps.map((b) => line(binderHtml(b)));

    /* 左辺・右辺に割るのは命題だけ。定義の型 `Scheme F R Party F` を関係の適用として割ると
       「左辺 Party / 右辺 F」という誤読になる（実測）。定義は「型」として一行で出す。 */
    const conclRows = [];
    if (nd.isProp) {
      const d = LDR.sig.decompose(nd.conclusion || "");
      if (d.lhs !== null && d.rhs !== null) {
        conclRows.push(line(`${sub("主結合子")}<span class="font-mono text-indigo-700 dark:text-indigo-300">${esc(LDR.sig.abbrev(d.rel))}</span>`
          + (d.ctx.length ? ` <span class="text-stone-400">${esc(LDR.sig.abbrev(d.ctx.join(" ")))}</span>` : "")));
        conclRows.push(line(`${sub("左辺")}${expr(d.lhs)}`));
        conclRows.push(line(`${sub("右辺")}${expr(d.rhs)}`));
      } else if (d.whole) {
        conclRows.push(line(expr(d.whole)));
      }
    } else if (nd.conclusion) {
      conclRows.push(line(expr(nd.conclusion)));
    }
    return [
      section("引数", argRows, "#d6d3d1", "text-stone-400"),
      section("仮定", hypRows, "#fbbf24", "text-amber-600 dark:text-amber-500"),
      section(nd.isProp ? "結論" : "型", conclRows, "#818cf8", "text-indigo-600 dark:text-indigo-400"),
    ].filter(Boolean).join("");
  }

  /* 宣言の印（由来・派生・断片・sorry・instance・reducible・形・条件）。中央の見出しと
     右のプレビューで同じものを使う（二か所で別々に組むと必ず乖離する）。 */
  /* 押せるもの（由来へ・派生の開閉）は .btn、押せない印は .tag（index.html の .pv）。中央の見出しは
     .pv の外なので、そこでは同じ見た目を Tailwind のクラスで与える（inPv=false）。 */
  function markChips(name, nd, dv, inPv) {
    const tag = (t, cls, title) => inPv
      ? `<span class="tag ${cls || ""}" title="${esc(title || "")}">${t}</span>`
      : `<span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-stone-100 text-stone-600 dark:bg-stone-800 dark:text-stone-300 ${cls || ""}" title="${esc(title || "")}">${t}</span>`;
    const btnCls = (on) => inPv ? `btn${on ? " on" : ""}`
      : `text-[10px] px-1.5 py-0.5 rounded-sm border ${on ? "bg-stone-900 text-white border-stone-900 dark:bg-stone-100 dark:text-stone-900" : "bg-white text-stone-700 border-stone-300 hover:bg-stone-100 dark:bg-stone-900 dark:text-stone-200 dark:border-stone-600"}`;
    // 法則の形は命題にだけ意味がある（インスタンス等のデータは構文上 refl の形を持ち得る）
    const sh = nd.isProp ? LDR.sig.SHAPE[nd.shape] : null;
    /* 由来。派生・断片なら「X の派生: 単射性」（押すと由来へ）、由来を持つ側なら「派生 n」（押すと開閉）と「断片 m」 */
    const OK = LDR.sig.ORIGIN_KIND, OR = LDR.sig.ORIGIN_REL;
    const originChip = nd.originRel && nd.origin
      ? `<button data-sel="${esc(nd.origin)}" class="${btnCls(false)}" title="由来 ${esc(nd.origin)} を見る（${esc((OK[nd.originKind] || {}).note || nd.originKind)}）">
           ${esc(shortOf(nd.origin))} の${esc((OR[nd.originRel] || {}).ja || nd.originRel)}: ${esc((OK[nd.originKind] || {}).ja || nd.originKind)} ↗</button>`
      : "";
    const fc = (dv.facetCount || {})[name] || 0, pc = (dv.partCount || {})[name] || 0;
    const open = fc && S.isClusterOpen(name), forced = fc && S.isClusterForced(name);
    const reach = dv.facetReach ? (dv.facetReach[name] || 0) : fc;
    const clusterChip = fc
      ? `<button data-cluster="${esc(name)}" class="${btnCls(open)}" title="${esc(`この宣言から Lean が作った派生 ${fc} 件。`
             + (forced ? "中心または経路表示のため固定で開いています" : `押すと一覧とグラフで開閉（この中心から見えるのは ${reach} 件）`))}"
           >派生 ${fc} ${forced ? "▾ 固定" : open ? "▾" : "▸"}</button>`
      : "";
    return [
      originChip, clusterChip,
      pc ? tag(`断片 ${pc}`, "", "証明・本体から切り出された補助の数（由来に埋め戻して表示）") : "",
      LDR.sig.isPrivateName(name) ? tag("private", "", "private 宣言（モジュールの外からは見えない）") : "",
      nd.usesSorry ? tag("sorry を含む", inPv ? "" : "bg-rose-100 text-rose-700", "証明に sorry がある") : "",
      nd.isInstance ? tag("instance", "", "型クラスのインスタンスとして登録されている") : "",
      nd.reducibility === "reducible" ? tag("reducible", "", "@[reducible]（abbrev 等）") : "",
      sh ? tag(sh.ja, "", sh.note) : "",
      condChip(name, nd),
    ].filter(Boolean).join(" ");
  }

  /* 公理のチップ。押すと中心からその公理に至る経路（順序区間）を表示する。 */
  function axiomChips(nd, st, inPv) {
    return nd.axioms.map((a) => {
      const bad = a === "sorryAx";
      const extra = !STD.has(a) && !bad;
      const on = st.traceTarget === a;
      const tone = bad ? "color:#9f1239;border-color:#fda4af" : extra ? "color:#92400e;border-color:#fcd34d" : "";
      const cls = inPv ? `btn font-mono${on ? " on" : ""}`
        : `font-mono text-[10.5px] px-1.5 py-0.5 rounded-sm border ${on ? "bg-stone-900 text-white border-stone-900" : "bg-white border-stone-300 hover:bg-stone-100 dark:bg-stone-900 dark:border-stone-600"}`;
      return `<button data-trace="${esc(a)}" class="${cls}" style="${on ? "" : tone}"
                title="${on ? "経路表示を解除" : "中心からこの公理に至る経路をグラフに表示"}">${esc(a)}${on ? " ✕" : ""}</button>`;
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
      /* 二行の固定構成。一行目は名前（長ければ省略。完全名は title と上部バー・右パネルにある）と種別・所在、
         二行目は印と公理。全部を一つの折り返し行に置くと、長い名前が三行を使い、グラフの高さを奪った（実測）。 */
      el.innerHTML = `
        <div class="flex items-center gap-2 min-w-0">
          <span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-indigo-600 text-white shrink-0" title="グラフの中心。右パネルは選択中の宣言を出す（追従）か、この中心に固定できる">中心</span>
          ${dot(nd.kind, 8)}
          <span class="font-mono text-[12.5px] font-medium truncate min-w-0" title="${esc(name)}">${esc(name)}</span>
          <span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-stone-100 dark:bg-stone-800 text-stone-600 dark:text-stone-300 shrink-0">${kinfo(nd.kind).ja}</span>
          <span class="font-mono text-[9.5px] text-stone-500 shrink-0 whitespace-nowrap" title="${esc(nd.module)}">${esc(shortOf(nd.module))}${nd.line ? ":" + nd.line : ""}</span>
          ${pkgChip(nd)}
        </div>
        <div class="flex items-center gap-1.5 flex-wrap mt-1">
          ${markChips(name, nd, dv, false)}
          ${nd.axioms.length
            ? `<span class="text-[10px] text-stone-500">公理</span>${axiomChips(nd, st, false)}`
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

  /* 推論図を、狭い縦長の面で読める形にする。

       前提   一行一前提で縦に並べる。公理を先に、補題は総仮定量の昇順（原始的なものから）。
              行は「▸／★ ・ 名前 ・ 形 ・ 経由（型／証）」、その下に結論を一行（切り詰め。全文は title）。
       開く   ▸ で、その前提の図が字下げと左の縦線で入れ子になる。
       横線   前提の束の直下に一本。右に規則名（この宣言）。
       結論   横線の下に ⊢ で。
       脚注   語彙・骨組み・断片は図の外に一行。

     以前は前提を横並びのカード（150〜280px）で置いていたが、330px の面では一行に 1〜2 枚しか
     入らず、折り返しと開いたカードの全幅化で「線の上に前提」という読み方が壊れていた（指摘）。 */
  /* via は、この前提が親の「主張（型）」に現れたか「証明（値）」にだけ現れたか。
     前者は親が何を述べているかを決め、後者は親をどう示したかを決める。
     骨組みを通り抜けた前提は初手の via を継承している（roles.split）。 */
  const VIA = {
    type:  { t: "型", title: "主張（型）に現れる。親が何を述べているかを決める" },
    value: { t: "証", title: "証明（値）にだけ現れる。親をどう示したかを決める" },
  };
  const viaTag = (via) => VIA[via]
    ? `<span class="shrink-0 text-[8.5px] px-1 rounded-sm bg-stone-100 dark:bg-stone-800 text-stone-500 dark:text-stone-400"
         title="${esc(VIA[via].title)}">${VIA[via].t}</span>` : "";

  function premiseRow(name, st, depth, seen, via, met) {
    const nd = st.nodes[name] || {};
    const role = LDR.roles.roleOf(name, nd);
    const col = roleColor(role);
    const open = st.derivOpen.has(name);
    const canOpen = depth > 0 && (((nd.typeDeps || []).length + (nd.valueDeps || []).length) > 0);
    const sh = nd.isProp ? LDR.sig.SHAPE[nd.shape] : null;
    const concl = conclusionOf(nd);
    /* 一行目: ▸（開閉）／★（公理）・種別の点・名前・形・経由・↗（見る）。二行目: その前提の結論（一行、切り詰め）。
       列は CSS grid（index.html の .pv .prem）で揃える。
       名前を押すと **その場で開閉** する（以前は押すと右パネルがその宣言へ飛び、図を読んでいる途中で
       文脈を失った。指摘）。別の宣言として見たいときは行末の ↗ を押す（履歴に積まれ、‹ で戻れる）。
       開いているときは結論の一行を出さない（入れ子の図の横線の下に同じ結論が出る。重複していた）。 */
    const toggle = canOpen
      ? `<button data-deriv="${esc(name)}" title="${open ? "この前提の導出を閉じる" : "この前提の導出を開く"}"
           class="text-[10px] text-stone-400 hover:text-stone-700 text-center">${open ? "▾" : "▸"}</button>`
      : `<span class="text-[9px] text-stone-300 dark:text-stone-600 text-center">·</span>`;
    const head = `<div class="nm" ${canOpen ? `data-deriv="${esc(name)}"` : ""} title="${esc(name)}${canOpen ? "（押すと導出を開閉）" : ""}">
        ${role === "axiom" ? `<span class="shrink-0 text-[10px] leading-none" style="color:${col}" title="公理（これ以上遡れない仮定）">★</span>` : dot(nd.kind, 6)}
        <span class="t font-mono text-[11px] truncate min-w-0">${esc(shortOf(name))}</span>
        ${sh ? `<span class="shrink-0 text-[9px]" style="color:${col}" title="${esc(sh.note)}">${sh.ja}</span>` : ""}
        ${viaTag(via)}
        ${nd.usesSorry ? '<span class="shrink-0 text-[9px] text-rose-600">sorry</span>' : ""}
      </div>
      <button class="go" data-sel="${esc(name)}" title="この宣言を右パネルで見る（グラフでも選択。‹ で戻れる）">↗</button>`;
    const sub = concl && !(open && canOpen) ? `<div class="cl" title="${esc(nd.conclusion || nd.typeString || "")}">⊢ ${esc(concl)}</div>` : "";
    const nested = open && canOpen
      ? `<div class="nest" style="border-color:${col}66">${derivation(name, st, depth - 1, seen, met)}</div>` : "";
    return `<div class="prem">${toggle}${head}${sub}${nested}</div>`;
  }

  function derivation(name, st, depth, seen, met) {
    const nd = st.nodes[name];
    if (!nd) return "";
    met = met || S.metrics();
    const parts = LDR.roles.split(name, st.nodes);
    const byClosure = (a, b) => ((met.closure[a.name] || 0) - (met.closure[b.name] || 0)) || (a.name < b.name ? -1 : 1);
    const premises = [...parts.axiom.slice().sort(byClosure), ...parts.lemma.slice().sort(byClosure)]
      .filter((p) => !seen.has(p.name));
    for (const p of premises) seen.add(p.name);

    /* 脚注。語彙（定義・型）は前提ではないので図の外に、件数と名前だけを一行で。
       多い（9 件以上）ときは畳み、押して開く（cslib の定理は語彙 54 件で、チップが図を埋めた。実測）。
       語彙の名前は押しても飛ばない（図の中で飛ぶ操作は ↗ だけ）。 */
    const foot = [];
    if (parts.vocab.length) {
      // 語彙: 単クリックでグラフの経路を強調（図は読んだまま）、ダブルクリックで中心にする
      const chips = parts.vocab.map((v) => `<button class="tag hl font-mono" data-hl="${esc(v.name)}" title="${esc(v.name)}（語彙: 主張を書くための定義・型）
クリック: グラフで中心までの経路を強調 / ダブルクリック: プレビューでこの宣言を見る（中心は動かない。‹ で戻れる）">${esc(shortOf(v.name))}</button>`).join(" ");
      /* 多いときは畳む。開閉は状態（derivOpen の鍵 "vocab:<名前>"）に持つ。`<details>` に任せると、
         札を押して選択が変わるたびに右パネルが組み直され、毎回閉じた（実測）。 */
      const vk = "vocab:" + name;
      const vopen = st.derivOpen.has(vk);
      foot.push(parts.vocab.length > 8
        ? `<button data-deriv="${esc(vk)}" class="hover:underline" style="color:${LDR.roles.ROLE.vocab.c}" title="主張を書くための定義・型（前提ではない）。押すと${vopen ? "畳む" : "開く"}">語彙 ${parts.vocab.length} ${vopen ? "▾" : "▸"}</button>${vopen ? " " + chips : ""}`
        : `<span style="color:${LDR.roles.ROLE.vocab.c}" title="主張を書くための定義・型（前提ではない）">語彙 ${parts.vocab.length}</span> ${chips}`);
    }
    if (parts.plumbing && parts.plumbing.length) foot.push(`<span class="text-stone-400" title="${esc(parts.plumbing.map((v) => v.name).join(", "))}（型クラスの配管: 射影・インスタンス・構成子。前提ではない）">配管 ${parts.plumbing.length}</span>`);
    if (parts.unknown && parts.unknown.length && premises.length) foot.push(`<span class="text-stone-400" title="${esc(parts.unknown.map((v) => v.name).join(", "))}（レポートの範囲外で種別が分からない）">範囲外 ${parts.unknown.length}</span>`);
    if (parts.frame.length) foot.push(`<span class="text-stone-400" title="${esc(parts.frame.map((v) => v.name).join(", "))}">骨組み ${parts.frame.length}</span>`);
    if (parts.part && parts.part.length) foot.push(`<span class="text-stone-400" title="${esc(parts.part.map((v) => v.name).join(", "))}（証明・本体の切り出し。中身は前提として上に展開済み）">断片 ${parts.part.length}</span>`);
    const footHtml = foot.length ? `<div class="mt-1.5 text-[9px] leading-relaxed" style="word-spacing:2px">${foot.join(" · ")}</div>` : "";
    const concl = `<div class="fig-concl" title="${esc(nd.conclusion || nd.typeString || "")}">⊢ ${esc(conclusionOf(nd)) || "—"}</div>`;

    /* 前提が無いなら、図は結論一行（空の前提欄と横線を出すと、何も無いのに六行使う。実測）。
       範囲外の依存（種別不明）があれば「前提なし」とは言わず、そう書く。証明が反射律だけなら定義的等式。 */
    if (!premises.length) {
      const REFL = new Set(["rfl", "Iff.rfl", "Eq.refl", "HEq.refl", "Iff.refl", "id", "trivial", "True.intro"]);
      const definitional = nd.isProp && (nd.valueDeps || []).every((d) => REFL.has(d) || LDR.roles.isFrameName(d) || ((st.nodes[d] || {}).originRel === "part"));
      const why = parts.unknown && parts.unknown.length
        ? `前提は範囲外 ${parts.unknown.length} 件（${esc(parts.unknown.map((v) => shortOf(v.name)).join(", "))}）— レポートの範囲外で種別が分からない`
        : definitional ? "定義的等式 — 証明は反射律だけ。両辺は主張の語彙の定義を展開すると一致する（確認すべき内容はその定義にある）"
        : "前提なし — 論理の骨組みだけで閉じている";
      return `<div>
        ${concl}
        <div class="mt-1 text-[9.5px] text-stone-400">${why}</div>
        ${footHtml}
      </div>`;
    }
    return `<div>
      <div>${premises.map((p) => premiseRow(p.name, st, depth, seen, p.via, met)).join("")}</div>
      <div class="fig-rule"><i></i><b title="${esc(name)}">${esc(shortOf(name))}</b></div>
      ${concl}
      ${footHtml}
    </div>`;
  }

  /* 右パネルの主語。追従なら選択中の宣言、固定なら中心。四つの依存タブもこの主語の一覧を出す。
     見出し行に「中心」「選択」の別を明示し、中心でなければ「中心にする」を置く。 */
  /* 頭は三行に収める。
       1 行目  見ている宣言 ／ 中心固定・追従 ／ 履歴の ‹ › と位置
       2 行目  履歴のチップ（見た順。一行に収め、溢れは横に送る。押すとその宣言を見て選択にする）
       3 行目  中心／選択の別 ・ 名前 ・ 種別 ・ 中心にする
     以前はチップが折り返して五行ほど使い、押しても戻れず、グラフとも連動しなかった（指摘）。 */
  function subjectHeader(st, dv, name) {
    const nd = st.nodes[name];
    const h = st.previewHist, pos = st.previewPos;
    const chips = h.map((x, i) => `<button data-preview="${esc(x)}" title="${esc(x)}${i === pos ? "（いま見ている）" : "（押すとこの宣言を見て、グラフで選択）"}"
        class="font-mono text-[10px] px-1.5 py-0.5 rounded-md shrink-0 border ${i === pos
          ? "bg-indigo-600 text-white border-indigo-600"
          : "bg-white text-stone-600 border-stone-300 hover:bg-stone-100 dark:bg-stone-900 dark:text-stone-300 dark:border-stone-600"}"
        >${esc(shortOf(x))}</button>`).join("");
    const modeBtn = (v, l, t) => `<button data-follow="${v}" title="${esc(t)}"
        class="px-2 py-0.5 text-[10.5px] rounded-sm ${(!!st.previewFollow) === (v === "1")
          ? "bg-stone-900 text-white dark:bg-stone-100 dark:text-stone-900"
          : "text-stone-500 hover:bg-stone-100 dark:hover:bg-stone-800"}">${l}</button>`;
    const navBtn = (attr, glyph, on, t) => `<button ${attr} ${on ? "" : "disabled"} title="${esc(t)}"
        class="w-6 h-6 rounded-md text-[13px] ${on ? "text-stone-700 hover:bg-stone-100 dark:text-stone-200 dark:hover:bg-stone-800" : "text-stone-300 dark:text-stone-700"}">${glyph}</button>`;
    const isCenter = name === dv.center;
    const role = isCenter
      ? `<span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-indigo-600 text-white shrink-0" title="グラフの中心と同じ宣言">中心</span>`
      : `<span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-stone-700 text-white dark:bg-stone-200 dark:text-stone-900 shrink-0" title="選択中の宣言（グラフの中心とは別。経路が光る）">選択</span>`;
    return `
      <div class="flex items-center gap-1 px-1 pb-1">
        <span class="text-[10px] text-stone-400 shrink-0">見ている宣言</span>
        <div class="flex gap-0.5 p-0.5 rounded-md bg-stone-200/70 dark:bg-stone-800 shrink-0">
          ${modeBtn("0", "中心固定", "グラフの中心を出し続ける")}${modeBtn("1", "追従", "一覧やグラフで選んだ宣言を出す（中心は動かない）")}
        </div>
        <span class="flex-1"></span>
        ${navBtn("data-pback", "‹", pos > 0, "前に見た宣言へ（[ キー）")}
        <span class="text-[9.5px] text-stone-400 tabular-nums">${h.length ? `${pos + 1}/${h.length}` : ""}</span>
        ${navBtn("data-pfwd", "›", pos < h.length - 1, "次に見た宣言へ（] キー）")}
      </div>
      ${chips ? `<div class="flex gap-1 px-1 pb-1.5 overflow-x-auto" style="scrollbar-width:thin" title="見た順。押すとその宣言を見て、グラフで選択する">${chips}</div>` : ""}
      ${nd ? `<div class="px-1 pb-1.5 border-b border-stone-200 dark:border-stone-700">
        <div class="flex items-center gap-1.5" style="min-height:22px">
          ${role}
          ${dot(nd.kind, 7)}
          <span class="text-[10px] px-1.5 py-0.5 rounded-sm bg-stone-100 dark:bg-stone-800 text-stone-600 dark:text-stone-300">${kinfo(nd.kind).ja}</span>
          <span class="flex-1"></span>
          ${isCenter ? "" : `<button data-nav="${esc(name)}" class="text-[10px] px-1.5 py-0.5 rounded-sm bg-indigo-600 text-white hover:bg-indigo-500 shrink-0">中心にする</button>`}
        </div>
        <div class="font-mono text-[12px] font-medium leading-snug mt-0.5" style="overflow-wrap:anywhere">${esc(name)}</div>
      </div>` : ""}`;
  }

  /* `<details>` の開閉を組み直しの前後で保つ。開閉の状態を store に持たせるほどのものではなく、
     組み直しのたびに閉じるのは読んでいる最中の視線を奪う。 */
  function keepOpen(body) {
    const seen = new Set(), kept = new Set();
    for (const d of body.querySelectorAll("details[data-keep]")) { seen.add(d.dataset.keep); if (d.open) kept.add(d.dataset.keep); }
    // 初めて出す区画は既定（def）に従い、二度目からは直前の開閉を保つ
    return (key, def) => ((seen.has(key) ? kept.has(key) : !!def) ? " open" : "");
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
    /* 原文。宣言範囲の行をソースから切り出したもの（Lean 側 sourceOf）。整形済みの型は
       Lean の表示であって原文ではないので、名前を「型（Lean の表示）」に正す。
       短い原文（12 行以下）は最初から開く。 */
    const srcLines = nd.source ? nd.source.split("\n").length : 0;
    const where = `${nd.module}${nd.line ? ":" + nd.line + (nd.lineEnd && nd.lineEnd !== nd.line ? "–" + nd.lineEnd : "") : ""}`;
    const sourceBlock = nd.source
      ? `<details data-keep="src" class="sec"${open("src", srcLines <= 12)}>
          <summary title="${esc(where)}"><span>原文</span><span class="grow font-mono text-stone-400">${esc(shortOf(nd.module))}${nd.line ? ":" + nd.line : ""}</span><span class="text-stone-400">${srcLines} 行</span></summary>
          <div class="src">${sourceHtml(nd.source, nd.line || 1)}</div>
        </details>`
      : `<div class="text-[10px] text-stone-400">原文なし（古い形式のレポートか、ソースが検索パスに無い）</div>`;
    /* 区画の順: 所在と文書 → 原文 → シグネチャ → 説明 → 印 → 公理 → 数値 → 依存パッケージ → 導出図 → 型 → 証明項。
       隙間は .pv の space-y で一定（6px）。由来は印の中の一つ（「X の派生: 単射性」）にだけ出す
       （数値の行にも「成員: LE」と重ねて出していた。実測）。 */
    body.innerHTML = header + `
      <div class="pv px-1 pt-2">
        <div class="row">
          <span class="font-mono text-[10px] text-stone-500 min-w-0 truncate" style="flex:1 1 auto" title="${esc(where)}">${esc(where)}</span>
          ${pkgChip(nd)}
          <span class="flex items-center gap-2" style="flex:none;white-space:nowrap">${docLinks(nd, name)}</span>
        </div>
        ${sourceBlock}
        <div class="sec">
          ${signatureBlock(nd) || `<div class="px-2 py-1 text-[11px] text-stone-400">シグネチャ情報なし</div>`}
        </div>
        ${nd.docString ? `<div class="text-[11px] text-stone-600 dark:text-stone-400 leading-relaxed space-y-1 px-0.5">${docHtml(nd.docString)}</div>` : ""}
        <div class="row"><span class="lbl">印</span>${markChips(name, nd, dv, true)}</div>
        <div class="row"><span class="lbl">公理</span>${axiomChips(nd, st, true)}</div>
        <div class="row text-[10px] text-stone-500">
          <span class="lbl">数値</span>
          <span class="tag" title="主張（型）の節点数">型 ${nd.typeSize || 0}</span><span class="tag" title="証明項・本体の節点数">証明 ${nd.valueSize || 0}</span>
          ${nd.subject ? `<span class="tag font-mono" title="主題（何についての宣言か）: ${esc(nd.subject)}">主題 ${esc(shortOf(nd.subject))}</span>` : ""}
          ${nd.numUniverse ? `<span class="tag" title="宇宙変数の数">宇宙 ${nd.numUniverse}</span>` : ""}
        </div>
        ${depPackages(nd)}
        <details data-keep="deriv" class="sec"${open("deriv")}>
          <summary title="推論図: 前提は横線の上、結論は下。▸ で前提の導出を開く。公理は ★、前提は原始的なものから順">
            <span>導出図</span>
            <span class="text-stone-400">前提 ${nPrem}（公理 ${parts.axiom.length} · 補題 ${parts.lemma.length}）· 語彙 ${parts.vocab.length}${parts.plumbing.length ? ` · 配管 ${parts.plumbing.length}` : ""}${parts.unknown.length ? ` · 範囲外 ${parts.unknown.length}` : ""}${parts.frame.length ? ` · 骨組み ${parts.frame.length}` : ""}${parts.part && parts.part.length ? ` · 断片 ${parts.part.length}` : ""}</span>
          </summary>
          <div class="px-2 pb-2 pt-1 border-t border-stone-200 dark:border-stone-700">${derivation(name, st, 3, seen)}</div>
        </details>
        ${nd.typeString ? `<details data-keep="type" class="sec"${open("type")}>
          <summary title="Lean が整形して表示する型（∀ の連鎖・完全修飾名）。原文ではない"><span>型（Lean の表示）</span></summary>
          <pre class="font-mono text-[10px] leading-relaxed whitespace-pre-wrap break-words
            border-t border-stone-200 dark:border-stone-700 px-2 py-1 max-h-48 overflow-y-auto">${esc(nd.typeString)}</pre></details>` : ""}
        ${nd.valueString ? `<details data-keep="value" class="sec"${open("value")}><summary><span>証明項</span></summary>
          <pre class="font-mono text-[10px] whitespace-pre-wrap break-words leading-snug
            border-t border-stone-200 dark:border-stone-700 px-2 py-1 max-h-48 overflow-y-auto">${esc(nd.valueString)}</pre></details>` : ""}
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
      + st.previewFollow + "|" + st.previewHist.length + "|" + st.previewPos + "|" + st.traceTarget
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
      /* タブの札は一行に収まる長さにする（「↓ 証明で参照 0」だけが二行目に落ちていた。実測）。
         意味は title と本文の注記で補う。 */
      const sets = {
        type:  { list: nd.typeDeps || [], label: "↑型", title: "型依存: 主張に現れる宣言",
                 note: `<b>${s} の主張に現れる</b>宣言（型依存）。この宣言が何を述べているかを決めるので、意味論的なレビュー対象。` },
        value: { list: nd.valueDeps || [], label: "↑値", title: "値依存: 証明にだけ現れる宣言",
                 note: `<b>${s} の証明にだけ現れる</b>宣言（値依存）。定理ならカーネル検査済み（証明無関係性）なので、主張の構造には効かない。` },
        refT:  { list: idx.refType[name] || [], label: "↓主張", title: "主張で参照: この宣言を主張に含む宣言",
                 note: `<b>${s} を主張に含む</b>宣言。つまり「${s} についての定理・性質」。ここから何が回収できたかが読める。` },
        refV:  { list: idx.refValue[name] || [], label: "↓証明", title: "証明で参照: この宣言を証明の道具として使う宣言",
                 note: `<b>${s} を証明の道具としてのみ使う</b>宣言。主張には現れないので、${s} について何かを述べているわけではない。` },
      };
      // 六つの札が既定の幅（330px）で一行に収まる大きさ（二段に割れていた。実測）
      const mk = (id, label, title) => `<button data-tab="${id}" title="${esc(title || "")}"
        class="px-1.5 py-1 text-[10.5px] rounded-md whitespace-nowrap ${cur === id
          ? "bg-stone-900 text-white dark:bg-stone-100 dark:text-stone-900"
          : "text-stone-600 hover:bg-stone-100 dark:text-stone-300 dark:hover:bg-stone-800"}">${label}</button>`;
      tabs.innerHTML = mk("prev", "プレビュー", "見ている宣言の原文・シグネチャ・導出図") + mk("laws", "法則", "法則の在庫表（関係 × 法則）")
        + ["type", "value", "refT", "refV"].map((id) => mk(id, `${sets[id].label} ${sets[id].list.length}`, sets[id].title)).join("");
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

  /* ================= 基盤・原子・境界 =================

     キャンバス下の区画。三つのモードは同じグラフから計算できる別の数学的対象で、答える問いが違う
     （store.state.minimalMode）。チップはどのモードでも経路の強調（順序区間 [t, c]）に使える。

       基盤  ∂_T x = { z ∉ T : ∃ y ∈ ↓x ∩ T, y → z }。対象の閉包から外へ出る先。
             型・構造体／定義／補題／配管 に分け、多重度（使う対象側の宣言の数）と、主張が立脚するか
             （型依存だけの閉包から出る）証明が持ち込んだかを示す。対象の依存は全て外部一段として
             既知なので、この集合は読み込んだ範囲の切れ目に依存しない（正確）。
       原子  既知の範囲 K（対象＋内部補助＋外部一段）での min(↓x ∩ K)。依存先を持たない宣言は全環境でも
             原子（依存ゼロは環境の事実）だが、境界の先にも原子はあり得るので一覧としては不完全。公理は別の行。
       境界  ∂x = ↓x ∖ K。読み込んだ範囲の切れ目（範囲外へ依存が続く点）。極小元ではない。
             既知の構造体の成員と注釈は外して数える。 */
  const MODE = {
    foundation: { l: "基盤", t: "対象の閉包から外へ出る先 ∂_T x。この結果は対象の外の何の上に立つか（切れ目に依存しない）" },
    atoms:      { l: "原子", t: "既知の範囲での min(↓x)。依存先を持たない宣言と公理。境界の先にも原子はあり得る（一覧は不完全）" },
    frontier:   { l: "境界", t: "読み込んだ範囲の切れ目 ∂x。どこから先を辿っていないか（極小元ではない）" },
  };
  function renderMinimal(st, dv) {
    const tm = dv.trueMinimal || [];
    const mode = st.minimalMode || "foundation";
    // チップの不透明度は「いま描画対象か(n ∈ posAll)」に依存する。
    // 可視集合の指紋を鍵に含めないと、展開・深さ変更後も古い明暗のままになる。
    // 開閉（派生）でも描画対象は変わるので、開閉の署名も鍵に入れる（描画数が同じでも中身は違い得る）
    const visSig = Object.keys(dv.posAll || {}).length + "|" + st.baseDepth + "|" + st.expanded.size + "|" + S.openSignature();
    once("min", dv.center + "|" + mode + "|" + st.traceTarget + "|" + (dv.traceUnreachable || "") + "|" + tm.length + "|" + visSig, () => {
      const el = $("minimalBox");
      const vis = dv.posAll || {};
      const fc = dv.frontierClean || { rest: dv.frontier || [], annotations: [], members: new Map() };
      const fd = dv.foundation;
      const memberCount = [...fc.members.values()].reduce((a, b) => a + b.length, 0);
      const count = {
        foundation: fd ? `${fd.list.length} 件（対象側の閉包 ${fd.closureSize} 件から外へ出る先。うち主張が立脚 ${fd.list.filter((e) => e.inStatement).length}）` : "宣言粒度でだけ",
        atoms: `${tm.length} 件（既知の下方閉集合 ${dv.fullDownSize || 0} 件のうち依存先を持たないもの。境界の先は数えていない）`,
        frontier: `${fc.rest.length} 件（範囲外へ依存が続く点）` + (memberCount ? `。既知の構造体の成員 ${memberCount} 件は構造体に畳む` : "") + (fc.annotations.length ? `。注釈 ${fc.annotations.length} 件は数えない` : ""),
      };
      $("minCount").textContent = count[mode];
      if ($("minMode")) $("minMode").innerHTML = Object.keys(MODE).map((m) => `<button data-minmode="${m}" title="${esc(MODE[m].t)}"
          class="px-2 py-0.5 text-[11px] rounded-md ${mode === m
            ? "bg-white dark:bg-stone-700 shadow-sm text-stone-900 dark:text-stone-100"
            : "text-stone-500 hover:text-stone-800 dark:hover:text-stone-200"}">${MODE[m].l}</button>`).join("");
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
      /* チップ。extra は札の追記（多重度 ×k）、dim は「証明が持ち込んだ」（主張には現れない）の薄い枠 */
      const chip = (n, title, extra, dim) => {
        const on = st.traceTarget === n;
        const shown = n in vis;
        const ax = (st.nodes[n] || {}).kind === "axiom";
        return `<button data-trace="${esc(n)}" title="${esc(title || n)}"
          class="font-mono text-[10.5px] px-2 py-0.5 rounded-full transition
                 ${ax ? "bg-orange-100 text-orange-900 dark:bg-orange-950/70 dark:text-orange-200" : "bg-amber-100 text-amber-900 dark:bg-amber-950/70 dark:text-amber-200"}
                 ${dim ? "ring-1 ring-dashed ring-amber-300 dark:ring-amber-800 bg-transparent" : ""}
                 ${on ? "ring-2 ring-amber-500" : "hover:ring-1 hover:ring-amber-400"}
                 ${shown ? "" : "opacity-60"}">${esc(shortOf(n))}${extra ? `<span class="text-[9px] text-amber-700/70 dark:text-amber-300/70"> ${extra}</span>` : ""}</button>`;
      };
      const head = `
        <div class="flex items-baseline gap-2 flex-wrap mb-1">
          <span class="text-[10.5px] text-stone-500">${esc(MODE[mode].t)}。押すとそこへ至る経路だけを表示</span>
          ${st.traceTarget ? `<button data-trace="${esc(st.traceTarget)}"
            class="text-[10.5px] px-1.5 py-0.5 rounded-sm bg-amber-500 text-white">経路表示を解除</button>` : ""}
        </div>`;
      let body = "";
      if (mode === "atoms") {
        /* 中心が持つ公理を先に（橙の札。レポートに kind = axiom の宣言として在れば経路も引ける）。
           公理は依存順序の上では原子ではない（型が Eq・Iff を参照する）ので、min(↓x) とは別の行に置く。 */
        const cen = st.nodes[dv.center] || {};
        const axs = (cen.axioms || []).filter((a) => st.nodes[a]);
        const list = tm.slice().sort();
        body = (axs.length ? `<div class="flex items-start gap-2 mb-1"><span class="text-[10px] text-stone-500 shrink-0 min-w-[5.5em] whitespace-nowrap pt-0.5" title="これ以上遡れない仮定。型が Eq・Iff を参照するので依存順序の原子ではない">公理 ${axs.length}</span>
            <div class="flex flex-wrap gap-1 min-w-0">${axs.map((a) => chip(a, `${a}（公理）`)).join("")}</div></div>` : "")
          + `<div class="flex items-start gap-2"><span class="text-[10px] text-stone-500 shrink-0 min-w-[5.5em] whitespace-nowrap pt-0.5" title="依存先を持たない宣言（語彙の原子）。読み込んだ範囲の中で見つかったもの。境界の先にも原子はあり得る">原子 ${list.length}</span>
            <div class="flex flex-wrap gap-1 min-w-0">${list.length
              ? list.map((n) => chip(n, `${n}（${kinfo((st.nodes[n] || {}).kind).ja}）`)).join("")
              : '<span class="text-[12px] text-stone-400">依存先がありません（この宣言自身が原始的）</span>'}</div></div>`;
      } else if (mode === "frontier") {
        const memberLine = memberCount
          ? `<div class="text-[10px] text-stone-500 mb-1" title="${esc([...fc.members.entries()].map(([o, ls]) => `${o}: ${ls.join(", ")}`).join("\n"))}">既知の構造体の成員（射影・構成子）${memberCount} 件は構造体に畳む: ${esc([...fc.members.keys()].map(shortOf).join(", "))}</div>` : "";
        body = memberLine + `<div class="flex flex-wrap gap-1">${fc.rest.length
          ? fc.rest.map((n) => chip(n)).join("")
          : '<span class="text-[12px] text-stone-400">範囲外へ続く依存はありません（閉包が読み込んだ範囲で閉じている）</span>'}</div>`;
      } else {
        if (!fd) {
          body = '<span class="text-[12px] text-stone-400">基盤は宣言粒度でだけ計算します</span>';
        } else {
          const R = LDR.roles;
          const groups = new Map();
          for (const e of fd.list) {
            const g = R.foundationGroup(e.name, st.nodes[e.name]);
            (groups.get(g) || groups.set(g, []).get(g)).push(e);
          }
          const sections = R.GROUP_ORDER.filter((g) => groups.has(g)).map((g) => {
            const es = groups.get(g).slice().sort((a, b) => (b.users.length - a.users.length) || (a.name < b.name ? -1 : 1));
            const chips = es.map((e) => chip(e.name,
              `${e.name}（${R.GROUP[g].ja}）\n使う対象側の宣言 ${e.users.length} 件: ${e.users.slice(0, 8).map(shortOf).join(", ")}${e.users.length > 8 ? " …" : ""}\n${e.inStatement ? "主張（型依存の閉包）が立脚する" : "証明が持ち込んだ（主張には現れない）"}`,
              e.users.length > 1 ? `×${e.users.length}` : "", !e.inStatement)).join("");
            return `<div class="flex items-start gap-2 mb-1">
              <span class="text-[10px] text-stone-500 shrink-0 min-w-[5.5em] whitespace-nowrap pt-0.5" title="${esc(R.GROUP[g].note)}">${esc(R.GROUP[g].ja)} ${es.length}</span>
              <div class="flex flex-wrap gap-1 min-w-0">${chips}</div></div>`;
          });
          body = sections.join("") || '<span class="text-[12px] text-stone-400">対象の閉包は外へ出ません（対象の中で閉じている）</span>';
          body += `<div class="text-[9.5px] text-stone-400 mt-1">実線の札は主張が立脚するもの、破線の札は証明が持ち込んだもの。×k は使う対象側の宣言の数</div>`;
        }
      }
      el.innerHTML = unreachable + head + body;
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
      // 区切りボタンの内側では折り返さない（「モジュ／ール」と割れた。実測）
      const seg = (id, cur2, opts) => opts.map((o) => `<button data-${id}="${o.v}" title="${esc(o.t || "")}"
        class="px-2 py-1 text-[12px] rounded-md whitespace-nowrap ${cur2 === o.v
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
