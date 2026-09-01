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

  /* ================= 宣言一覧（仮想化） ================= */
  const ROW_H = 29;
  const V = { host: null, win: null, spacer: null, rows: [], top: 0, raf: 0 };

  function vmount() {
    const host = $("declList");
    if (V.host === host) return;
    V.host = host;
    host.innerHTML = '<div data-vspacer style="width:1px"></div>'
                   + '<div data-vwin style="position:absolute;left:0;right:0;top:0;padding:0 6px"></div>';
    V.spacer = host.querySelector("[data-vspacer]");
    V.win = host.querySelector("[data-vwin]");
    host.addEventListener("scroll", () => {
      if (V.raf) return;
      V.raf = requestAnimationFrame(() => { V.raf = 0; vpaint(); });
    }, { passive: true });
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
    const start = Math.max(0, Math.floor(V.host.scrollTop / ROW_H) - 6);
    const end = Math.min(V.rows.length, Math.ceil((V.host.scrollTop + h) / ROW_H) + 6);
    V.win.style.transform = `translateY(${start * ROW_H}px)`;
    V.win.innerHTML = V.rows.slice(start, end).map((r) => r.html).join("");
  }

  /* ---- 並び順 ----
     実装順   レポートの行順 = ファイル内で宣言された順。読み進める向き。
     依存少順 直接依存の少ない順。原始的なものから積み上がる向き。
     名前空間 namespace ごとに束ね、名前空間は初出順（＝ファイル内の上から）。
     ツリー   モジュールのディレクトリ構造。 */
  function visibleNames(st) {
    let names = st.order.length ? st.order : Object.keys(st.nodes);
    names = names.filter((n) => st.nodes[n] && !st.nodes[n].external);
    const q = st.query.trim().toLowerCase();
    if (q) names = names.filter((n) => n.toLowerCase().includes(q));
    if (st.onlySorry) names = names.filter((n) => st.nodes[n].usesSorry);
    if (st.kindFilter.size) names = names.filter((n) => st.kindFilter.has(st.nodes[n].kind));
    return names;
  }

  function itemRow(n, st, cen, depth, badge) {
    const nd = st.nodes[n];
    const on = n === cen;
    const sel = n === st.selected;
    const pad = 6 + (depth || 0) * 11;
    const cls = on ? "bg-indigo-50 dark:bg-indigo-950/60 ring-1 ring-indigo-300 dark:ring-indigo-700 text-indigo-900 dark:text-indigo-200"
              : sel ? "bg-stone-100 dark:bg-stone-800" : "hover:bg-stone-100 dark:hover:bg-stone-800";
    return {
      html: `<button data-sel="${esc(n)}" title="${esc(n)}" style="height:${ROW_H}px;padding-left:${pad}px"
        class="w-full text-left pr-2 rounded-md flex items-center gap-2 ${cls}">
        ${dot(nd.kind, 6)}
        <span class="font-mono text-[11px] truncate flex-1">${esc(shortOf(n))}</span>
        ${nd.usesSorry ? '<span class="text-[9.5px] px-1 rounded bg-rose-100 text-rose-700 dark:bg-rose-950 dark:text-rose-300 shrink-0">sorry</span>' : ""}
        ${badge !== undefined ? `<span class="text-[9.5px] text-stone-400 tabular-nums shrink-0">${badge}</span>` : ""}
      </button>`,
    };
  }

  function groupRow(label, count, depth, prefix, closed) {
    const pad = 4 + (depth || 0) * 11;
    const caret = prefix != null ? (closed ? "▸" : "▾") : "";
    const tag = prefix != null ? `data-tree="${esc(prefix)}"` : "";
    return {
      html: `<div ${tag} style="height:${ROW_H}px;padding-left:${pad}px"
        class="w-full flex items-center gap-1.5 ${prefix != null ? "cursor-pointer hover:bg-stone-100 dark:hover:bg-stone-800 rounded-md" : ""}">
        <span class="text-[9.5px] text-stone-400 w-2">${caret}</span>
        <span class="font-mono text-[10.5px] text-stone-500 dark:text-stone-400 truncate flex-1">${esc(label)}</span>
        <span class="text-[10px] text-stone-400 pr-2">${count}</span>
      </div>`,
    };
  }

  function buildRows(st, dv) {
    const names = visibleNames(st);
    const cen = dv.center;
    const mode = st.listMode;

    if (mode === "impl") return { rows: names.map((n) => itemRow(n, st, cen, 0)), count: names.length };

    if (mode === "deps") {
      /* 尺度の昇順で並べる。closure / depth は依存順序と両立するので、
         この並びは線形拡大になり、上から読めば前提が必ず先に来る。
         同値のときは深さ、それでも同じなら名前で決める（表示を安定させる）。 */
      const m = S.metrics();
      const key = m[st.sortMetric] || m.closure;
      const sorted = names.slice().sort((a, b) =>
        (key[a] - key[b]) || ((m.depth[a] || 0) - (m.depth[b] || 0)) || (a < b ? -1 : 1));
      return { rows: sorted.map((n) => itemRow(n, st, cen, 0, key[n])), count: names.length };
    }

    if (mode === "ns") {
      const groups = new Map();   // 初出順を保つ
      for (const n of names) {
        const p = String(n).split(".");
        const ns = p.length > 1 ? p.slice(0, -1).join(".") : "(名前空間なし)";
        if (!groups.has(ns)) groups.set(ns, []);
        groups.get(ns).push(n);
      }
      const rows = [];
      for (const [ns, list] of groups) {
        const closed = st.treeClosed.has("ns:" + ns);
        rows.push(groupRow(ns, list.length, 0, "ns:" + ns, closed));
        if (!closed) for (const n of list) rows.push(itemRow(n, st, cen, 1));
      }
      return { rows, count: names.length };
    }

    // mode === "tree"
    const byMod = new Map();
    for (const n of names) {
      const m = st.nodes[n].module;
      if (!byMod.has(m)) byMod.set(m, []);
      byMod.get(m).push(n);
    }
    const root = { children: new Map(), items: [], prefix: "", total: 0 };
    for (const mod of [...byMod.keys()].sort()) {
      let cur = root, prefix = "";
      for (const seg of String(mod).split(".")) {
        prefix = prefix ? prefix + "." + seg : seg;
        if (!cur.children.has(seg)) cur.children.set(seg, { seg, prefix, children: new Map(), items: [], total: 0 });
        cur = cur.children.get(seg);
      }
      cur.items = byMod.get(mod);
    }
    (function total(node) {
      node.total = node.items.length;
      for (const ch of node.children.values()) node.total += total(ch);
      return node.total;
    })(root);

    const rows = [];
    (function walk(node, depth) {
      for (const ch of node.children.values()) {
        if (!ch.total) continue;
        const closed = st.treeClosed.has("md:" + ch.prefix);
        rows.push(groupRow(ch.seg, ch.total, depth, "md:" + ch.prefix, closed));
        if (closed) continue;
        walk(ch, depth + 1);
        for (const n of ch.items) rows.push(itemRow(n, st, cen, depth + 1));
      }
    })(root, 0);
    return { rows, count: names.length };
  }

  function renderList(st, dv) {
    const k = [st.query, st.listMode, st.sortMetric, st.onlySorry, [...st.kindFilter].sort().join(","),
      [...st.treeClosed].sort().join(","), st.order.length, Object.keys(st.nodes).length,
      dv.center, st.selected].join("|");
    once("list", k, () => {
      const { rows, count } = buildRows(st, dv);
      vsetRows(rows);
      $("listCount").textContent = `${count} 件`;
    });
  }

  function shortOf(n) {
    const p = String(n).split(".");
    return p.length <= 2 ? n : p.slice(-2).join(".");
  }

  /* ================= 監査サマリ ================= */
  const STD = new Set(["propext", "Classical.choice", "Quot.sound"]);

  function renderAudit(st) {
    once("audit", Object.keys(st.nodes).length + "|" + st.onlySorry, () => {
      const own = Object.values(st.nodes).filter((n) => !n.external);
      const sorry = own.filter((n) => n.usesSorry).length;
      const extra = own.filter((n) => n.axioms.some((a) => !STD.has(a) && a !== "sorryAx")).length;
      const axFree = own.filter((n) => n.axioms.length === 0).length;
      const m = S.metrics();
      const hered = own.filter((n) => m.hered && m.hered[n.name]).length;
      const cond = own.filter((n) => n.numHyp || n.numInst).length;
      $("auditBar").innerHTML = `
        <button data-audit="sorry" class="px-2 py-1 rounded-md text-[12px] flex items-center gap-1.5
          ${st.onlySorry ? "bg-rose-100 text-rose-800 ring-1 ring-rose-300 dark:bg-rose-950 dark:text-rose-200"
                         : "bg-stone-100 text-stone-600 hover:bg-stone-200 dark:bg-stone-800 dark:text-stone-300"}">
          <span class="w-1.5 h-1.5 rounded-full bg-rose-500"></span>sorry ${sorry}
        </button>
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

  /* ================= 詳細 =================

     型を一本の文字列で見せると、引数・仮定・結論が同じ「→」で並ぶために
     読み手が三つを区別できない。Lean 側が分解した `binders`（`prop` 旗つき）と
     `conclusion` を使って、役割ごとに置き直す。 */

  /** Mathlib / Lean core 由来か。公式ドキュメントの検索が意味を持つのはこの場合だけ。 */
  const EXTERNAL_ROOT = /^(Mathlib|Init|Std|Lean|Batteries|Aesop|Qq|Plausible|LeanSearchClient|ProofWidgets)(\.|$)/;
  const isExternalDecl = (nd, name) =>
    !!nd && (nd.external || EXTERNAL_ROOT.test(String(nd.module || "")) || EXTERNAL_ROOT.test(String(name || "")));

  const KIND_BADGE = { explicit: "明示", implicit: "暗黙", strictImplicit: "暗黙", inst: "inst" };

  /* 定義の与えられ方を三つに分ける。

       無条件で閉じる  仮定もインスタンス要求も無く、依存先も全て同じ性質。
                       無条件に得たものだけから無条件に得られている。
       無条件          自分には条件が無いが、依存の先に条件付きのものを含む。
       条件 n          仮定またはインスタンスを n 個要求している。

     この区別は「最初に無条件で与えられる定義」「追加の理論や条件を要する定義」
     「条件付きだが無条件のものから無条件に得られる定義」を分けるためのもの。 */
  function condChip(name, nd) {
    const cls = (c) => `text-[10px] px-1.5 py-0.5 rounded ${c}`;
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

  function signatureBlock(nd) {
    const B = nd.binders || [];
    const args = B.filter((b) => !b.prop);
    const hyps = B.filter((b) => b.prop);
    const row = (label, body, tone) => `
      <div class="flex gap-2 items-baseline py-[3px]">
        <span class="shrink-0 w-11 text-right text-[10px] ${tone || "text-stone-400"}">${label}</span>
        <span class="min-w-0 flex-1 text-[12px] leading-relaxed break-words">${body}</span>
      </div>`;

    let out = "";
    if (args.length) {
      out += args.map((b, i) => row(
        i === 0 ? "引数" : "",
        `<span class="font-mono text-stone-900 dark:text-stone-100">${esc(b.name)}</span>
         <span class="text-stone-400"> : </span>${expr(b.type)}
         <span class="ml-1 text-[9.5px] text-stone-400">${KIND_BADGE[b.kind] || ""}</span>`)).join("");
    }
    if (hyps.length) {
      out += hyps.map((b, i) => row(
        i === 0 ? "仮定" : "",
        expr(b.type), "text-amber-600 dark:text-amber-500")).join("");
    }

    const d = LDR.sig.decompose(nd.conclusion || "");
    if (d.lhs !== null && d.rhs !== null) {
      out += row("結論", `<span class="font-mono text-indigo-700 dark:text-indigo-300">${esc(LDR.sig.abbrev(d.rel))}</span>`
        + (d.ctx.length ? ` <span class="text-stone-400">${esc(LDR.sig.abbrev(d.ctx.join(" ")))}</span>` : ""),
        "text-indigo-600 dark:text-indigo-400");
      out += row("左辺", expr(d.lhs));
      out += row("右辺", expr(d.rhs));
    } else if (d.whole) {
      out += row("結論", expr(d.whole), "text-indigo-600 dark:text-indigo-400");
    }
    return out;
  }

  function renderInspector(st, dv) {
    const name = st.selected || dv.center;
    once("insp", name + "|" + dv.center + "|" + Object.keys(st.nodes).length, () => {
      const nd = st.nodes[name];
      const el = $("inspector");
      if (!nd) {
        el.innerHTML = `<div class="text-[12.5px] text-stone-500">
          <span class="font-mono">${esc(name || "")}</span> はモジュールです（${(dv.modIdx.count || {})[name] || 0} 宣言）</div>`;
        return;
      }
      const axChips = nd.axioms.map((a) => {
        const bad = a === "sorryAx";
        const extra = !STD.has(a) && !bad;
        const cls = bad ? "bg-rose-100 text-rose-800 dark:bg-rose-950 dark:text-rose-200"
                  : extra ? "bg-amber-100 text-amber-900 dark:bg-amber-950 dark:text-amber-200"
                  : "bg-stone-100 text-stone-600 dark:bg-stone-800 dark:text-stone-300";
        return `<button data-trace="${esc(a)}" class="font-mono text-[10.5px] px-1.5 py-0.5 rounded ${cls}"
                  title="この公理に至る経路を表示">${esc(a)}</button>`;
      }).join(" ") || `<span class="text-[11px] text-emerald-600 dark:text-emerald-400">なし（公理非依存）</span>`;

      const isCenter = name === dv.center;
      const ext = isExternalDecl(nd, name);
      const q = encodeURIComponent(name);
      const leaf = encodeURIComponent(String(name).split(".").slice(-1)[0]);
      /* 公式ドキュメントは Mathlib / Lean core の宣言にしか無いので、そのときだけ出す。
         LeanSearch は自作の宣言でも「似た定理」を探す用途があるので常に出す。 */
      const links =
        (ext ? `<a href="https://leanprover-community.github.io/mathlib4_docs/search.html?q=${q}"
           target="_blank" rel="noopener" title="mathlib4 の公式ドキュメントで検索"
           class="text-[11px] px-2 py-0.5 rounded-md border border-stone-300 dark:border-stone-600
                  hover:bg-stone-100 dark:hover:bg-stone-800">📘 docs</a>` : "")
        + `<a href="https://leansearch.net/?q=${leaf}"
           target="_blank" rel="noopener" title="LeanSearch で意味検索"
           class="text-[11px] px-2 py-0.5 rounded-md border border-stone-300 dark:border-stone-600
                  hover:bg-stone-100 dark:hover:bg-stone-800">🔎 LeanSearch</a>`;

      const chip = (t, cls) => `<span class="text-[10px] px-1.5 py-0.5 rounded ${cls}">${t}</span>`;
      const sh = LDR.sig.SHAPE[nd.shape];
      const marks = [
        nd.usesSorry ? chip("sorry を含む", "bg-rose-100 text-rose-700 dark:bg-rose-950 dark:text-rose-300") : "",
        nd.isInstance ? chip("instance", "bg-teal-100 text-teal-800 dark:bg-teal-950 dark:text-teal-200") : "",
        nd.reducibility === "reducible" ? chip("reducible", "bg-stone-100 text-stone-600 dark:bg-stone-800 dark:text-stone-300") : "",
        sh ? `<span class="text-[10px] px-1.5 py-0.5 rounded bg-indigo-100 text-indigo-800 dark:bg-indigo-950 dark:text-indigo-200"
                title="${esc(sh.note)}">${sh.ja}</span>` : "",
        condChip(name, nd),
      ].filter(Boolean).join(" ");

      /* 中央は一行の見出しに留める。シグネチャも公理も原文も右パネルが持つので、
         同じものを二か所に置くと、そのぶんグラフの高さが削られるだけになる。 */
      el.innerHTML = `
        <div class="flex items-center gap-2 flex-wrap">
          ${dot(nd.kind, 8)}
          <span class="font-mono text-[12.5px] font-medium break-all leading-tight">${esc(name)}</span>
          <span class="text-[10px] px-1.5 py-0.5 rounded bg-stone-100 dark:bg-stone-800 text-stone-600 dark:text-stone-300">${kinfo(nd.kind).ja}</span>
          <span class="font-mono text-[9.5px] text-stone-500" title="${esc(nd.module)}">${esc(shortOf(nd.module))}${nd.line ? ":" + nd.line : ""}</span>
          ${marks}
          ${nd.axioms.length
            ? `<span class="text-[10px] text-stone-500">公理</span>${axChips}`
            : `<span class="text-[10px] text-emerald-600 dark:text-emerald-400">公理非依存</span>`}
          <span class="flex-1"></span>
          ${links}
          ${isCenter ? "" : `<button data-nav="${esc(name)}"
            class="text-[10.5px] px-2 py-0.5 rounded-md bg-indigo-600 text-white hover:bg-indigo-500">中心にする</button>`}
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
    const sh = LDR.sig.SHAPE[nd.shape];
    const concl = LDR.sig.abbrev(nd.conclusion || nd.typeString || "");
    return `<button data-sel="${esc(n)}" title="${esc(n)}"
      class="w-full text-left pl-2 pr-2 py-1 rounded border-l-2 hover:bg-stone-100 dark:hover:bg-stone-800
             ${st.selected === n ? "bg-stone-100 dark:bg-stone-800" : ""}"
      style="border-color:${col}66">
      <div class="flex items-center gap-1.5">
        ${dot(nd.kind, 6)}
        <span class="font-mono text-[10.5px] truncate flex-1">${esc(shortOf(n))}</span>
        ${role === "axiom" ? '<span class="text-[9px] px-1 rounded bg-orange-100 text-orange-800 dark:bg-orange-950 dark:text-orange-200 shrink-0">公理</span>' : ""}
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
  function premiseCard(name, st, depth, seen) {
    const nd = st.nodes[name] || {};
    const role = LDR.roles.roleOf(name, nd);
    const open = st.derivOpen.has(name);
    const canOpen = depth > 0 && (((nd.typeDeps || []).length + (nd.valueDeps || []).length) > 0);
    const sh = LDR.sig.SHAPE[nd.shape];
    const concl = conclusionOf(nd);
    const col = roleColor(role);

    if (open && canOpen) {
      // 開いた前提は、その場で自分の推論図になる
      return `<div class="rounded-md border px-2 py-1.5 min-w-0 flex-1 basis-full"
           style="border-color:${col}44;background:${col}08">
        <div class="flex items-baseline gap-1 mb-1">
          <button data-deriv="${esc(name)}" class="text-[9px] w-3 shrink-0 text-stone-400 hover:text-stone-700">▾</button>
          <span class="text-[9px]" style="color:${col}">${LDR.roles.ROLE[role].ja}</span>
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
        ${role === "axiom" ? `<span class="text-[8.5px] px-1 rounded bg-orange-100 text-orange-800 dark:bg-orange-950 dark:text-orange-200">公理</span>` : ""}
        ${sh ? `<span class="text-[8.5px]" style="color:${col}" title="${esc(sh.note)}">${sh.ja}</span>` : ""}
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
           ${premises.map((p) => premiseCard(p.name, st, depth, seen)).join("")}
         </div>`
      : `<div class="text-[9.5px] text-stone-400 py-1">前提となる補題はありません
           <span class="text-stone-300 dark:text-stone-600">（定義そのもの、または骨組みだけで閉じています）</span></div>`;

    const chip = (list, label, color) => list.length
      ? `<div class="flex items-baseline gap-1 flex-wrap mt-1">
           <span class="text-[9px] shrink-0" style="color:${color}">${label}</span>
           ${list.map((v) => `<button data-sel="${esc(v.name)}" title="${esc(v.name)}"
             class="font-mono text-[9px] px-1 rounded bg-stone-100 dark:bg-stone-800
                    text-stone-600 dark:text-stone-300 hover:bg-stone-200">${esc(shortOf(v.name))}</button>`).join("")}
         </div>` : "";

    return `<div>
      ${prem}
      <div class="flex items-center gap-2 mt-1.5 mb-1">
        <span class="h-[1.5px] flex-1 rounded" style="background:${roleColor(LDR.roles.roleOf(name, nd))}88"></span>
        <span class="font-mono text-[9px] text-stone-500 dark:text-stone-400 truncate max-w-[60%]"
              title="${esc(name)}">${esc(shortOf(name))}</span>
      </div>
      <div class="font-mono text-[11px] text-stone-900 dark:text-stone-100 leading-snug break-words"
           title="${esc(nd.conclusion || nd.typeString || "")}">${esc(conclusionOf(nd)) || "—"}</div>
      ${chip(parts.vocab, "語彙", LDR.roles.ROLE.vocab.c)}
      ${parts.frame.length ? `<details class="mt-1"><summary class="cursor-pointer text-[9px] text-stone-400">
          骨組み ${parts.frame.length} 件（論理結合子・再帰子）</summary>
        <div class="flex flex-wrap gap-1 mt-1">${parts.frame.map((v) =>
          `<span class="font-mono text-[9px] px-1 rounded bg-stone-100 dark:bg-stone-800 text-stone-400"
            >${esc(shortOf(v.name))}</span>`).join("")}</div></details>` : ""}
    </div>`;
  }

  function renderPreview(st, dv) {
    const name = S.previewName();
    const nd = st.nodes[name];
    const body = $("depBody");
    const chips = st.previewHist.map((h) => `<button data-preview="${esc(h)}" title="${esc(h)}"
        class="font-mono text-[10px] px-1.5 py-0.5 rounded ${h === name
          ? "bg-indigo-600 text-white"
          : "bg-stone-100 text-stone-600 hover:bg-stone-200 dark:bg-stone-800 dark:text-stone-300"}"
        >${esc(shortOf(h))}</button>`).join(" ");
    const modeBtn = (v, l) => `<button data-follow="${v}"
        class="px-2 py-0.5 text-[10.5px] rounded ${(!!st.previewFollow) === (v === "1")
          ? "bg-stone-900 text-white dark:bg-stone-100 dark:text-stone-900"
          : "text-stone-500 hover:bg-stone-100 dark:hover:bg-stone-800"}">${l}</button>`;
    const header = `
      <div class="flex items-center gap-1 px-1 pb-1.5">
        <span class="text-[10px] text-stone-400">プレビュー</span>
        <div class="flex gap-0.5 p-0.5 rounded-md bg-stone-200/70 dark:bg-stone-800">
          ${modeBtn("0", "中心固定")}${modeBtn("1", "追従")}
        </div>
      </div>
      ${chips ? `<div class="flex flex-wrap gap-1 px-1 pb-1.5">${chips}</div>` : ""}`;

    if (!nd) { body.innerHTML = header + `<p class="px-2 py-4 text-center text-[12px] text-stone-400">対象がありません</p>`; return; }
    const seen = new Set([name]);
    body.innerHTML = header + `
      <div class="px-1">
        <div class="flex items-baseline gap-1.5 flex-wrap">
          ${dot(nd.kind, 7)}
          <span class="font-mono text-[12px] font-medium break-all">${esc(name)}</span>
          <button data-nav="${esc(name)}" class="text-[10px] px-1.5 py-0.5 rounded bg-indigo-600 text-white hover:bg-indigo-500">中心にする</button>
        </div>
        <div class="mt-1 rounded-md border border-stone-200 dark:border-stone-700 bg-stone-50 dark:bg-stone-950 px-2 py-1">
          ${signatureBlock(nd) || `<span class="text-[11px] text-stone-400">シグネチャ情報なし</span>`}
        </div>
        ${nd.docString ? `<p class="mt-1.5 text-[11px] text-stone-600 dark:text-stone-400 leading-relaxed">${esc(nd.docString)}</p>` : ""}
        <div class="mt-1.5 flex items-baseline gap-2 flex-wrap text-[10px] text-stone-500">
          <span title="主張と証明項の節点数">型 ${nd.typeSize || 0} / 証明 ${nd.valueSize || 0} 節点</span>
          ${nd.subject ? `<span>主題 <span class="font-mono" title="${esc(nd.subject)}">${esc(shortOf(nd.subject))}</span></span>` : ""}
          <span>${nd.numUniverse ? `宇宙 ${nd.numUniverse}` : ""}</span>
        </div>
        ${nd.typeString ? `<details class="mt-1">
          <summary class="cursor-pointer text-[10px] text-stone-400 hover:text-stone-600">原文を表示</summary>
          <pre class="mt-1 font-mono text-[10px] leading-relaxed whitespace-pre-wrap break-words
            bg-stone-50 dark:bg-stone-950 border border-stone-200 dark:border-stone-700 rounded px-2 py-1
            max-h-48 overflow-y-auto">${esc(nd.typeString)}</pre></details>` : ""}
        ${nd.valueString ? `<details class="mt-1.5"><summary class="cursor-pointer text-[10.5px] text-stone-400">証明項</summary>
          <pre class="mt-1 font-mono text-[10px] whitespace-pre-wrap break-words leading-snug
            bg-stone-50 dark:bg-stone-950 border border-stone-200 dark:border-stone-700 rounded px-2 py-1
            max-h-48 overflow-y-auto">${esc(nd.valueString)}</pre></details>` : ""}
        <div class="mt-2.5 flex items-baseline gap-2">
          <span class="text-[10px] text-stone-400">導出図</span>
          <span class="text-[9.5px] text-stone-400">前提は横線の上、結論は下。▸ で前提の導出を開く</span>
        </div>
        <div class="mt-1 rounded-md border border-stone-200 dark:border-stone-700 px-2 py-2">
          ${derivation(name, st, 3, seen)}
        </div>
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
    mono: "単調", comm: "可換", assoc: "結合", idem: "冪等",
  };
  const LAW_HUE = {
    refl: 200, irrefl: 210, symm: 265, trans: 155, antisymm: 25,
    mono: 235, comm: 320, assoc: 300, idem: 95,
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
      const has = (l) => (r.laws[l] || []).length;
      /* 配色は動的なクラス名ではなく実値で持つ。CDN 版 Tailwind は DOM を
         監視して生成するが、組み立てたクラス名は取りこぼし得るので値で書く。 */
      const verdict =
        has("refl") && has("trans") && has("symm") ? { t: "同値", h: 152 }
        : has("refl") && has("trans") && has("antisymm") ? { t: "半順序", h: 243 }
        : has("refl") && has("trans") ? { t: "前順序", h: 199 }
        : has("comm") && has("assoc") && has("idem") ? { t: "半束", h: 271 }
        : null;
      const cells = laws.map((l) => {
        const list = r.laws[l] || [];
        if (!list.length) {
          return `<div class="h-5 flex items-center justify-center text-[9px] text-stone-300 dark:text-stone-700">·</div>`;
        }
        return `<button data-sel="${esc(list[0])}" title="${esc(LAW_JA[l])}: ${esc(list[0])}${list.length > 1 ? ` 他 ${list.length - 1} 件` : ""}"
          class="h-5 w-full rounded-[3px] text-[9px] font-medium text-white flex items-center justify-center hover:brightness-110"
          style="background:hsl(${LAW_HUE[l]},58%,48%)">${list.length > 1 ? list.length : ""}</button>`;
      }).join("");
      return `<div class="grid gap-px items-center hover:bg-stone-50 dark:hover:bg-stone-800/50 rounded"
          style="grid-template-columns: minmax(96px,1fr) repeat(${laws.length}, 22px) 62px">
        <button data-sel="${esc(r.rel)}" title="${esc(r.rel)}"
          class="text-left font-mono text-[10px] truncate pr-1 hover:underline">${esc(shortOf(r.rel))}</button>
        ${cells}
        <div class="text-right pl-1">${verdict
          ? `<span class="text-[9px] px-1 py-0.5 rounded font-medium"
               style="background:hsl(${verdict.h},70%,92%);color:hsl(${verdict.h},60%,30%)">${verdict.t}</span>`
          : `<span class="text-[9px] text-stone-300 dark:text-stone-700">—</span>`}</div>
      </div>`;
    }).join("");

    const proved = inv.list.reduce((a, r) => a + r.total, 0);
    body.innerHTML = `
      <div class="px-1 pb-1.5 text-[10px] text-stone-500 dark:text-stone-400 leading-relaxed">
        ${inv.list.length} 個の関係・演算について ${proved} 件の法則を検出。
        押すとその定理を選びます。
      </div>
      <div class="px-1 overflow-x-auto">${head}<div class="space-y-px">${rows}</div></div>
      <p class="px-1 pt-2 text-[9.5px] text-stone-400 leading-relaxed">
        空欄は「まだ証明されていない」であって「成り立たない」ではありません。
        判定は仮定と結論の構文的な形から行い、誤って付けない向きに倒してあるので、
        別の言い回しで証明されているものは取り逃します。
      </p>`;
  }

  function renderDeps(st, dv) {
    const cen = dv.center;
    const cur = $("depTabs").dataset.tab || "prev";
    once("deps", cen + "|" + cur + "|" + st.selected + "|" + st.edgeMode + "|"
      + st.previewFollow + "|" + S.previewName() + "|" + st.previewHist.length
      + "|" + [...st.derivOpen].sort().join(","), () => {
      const nd = st.nodes[cen];
      const tabs = $("depTabs"), body = $("depBody");
      if (!nd) { tabs.innerHTML = ""; body.innerHTML = ""; return; }
      const idx = dv.declIdx;
      const sets = {
        type:  { list: nd.typeDeps || [], label: "↑ 型依存",
                 note: `<b>${esc(shortOf(cen))} の主張に現れる</b>宣言。この宣言が何を述べているかを決めるので、意味論的なレビュー対象。` },
        value: { list: nd.valueDeps || [], label: "↑ 値依存",
                 note: `<b>${esc(shortOf(cen))} の証明にだけ現れる</b>宣言。定理ならカーネル検査済み（証明無関係性）なので、主張の構造には効かない。` },
        refT:  { list: idx.refType[cen] || [], label: "↓ 主張で参照",
                 note: `<b>${esc(shortOf(cen))} を主張に含む</b>宣言。つまり「${esc(shortOf(cen))} についての定理・性質」。ここから何が回収できたかが読める。` },
        refV:  { list: idx.refValue[cen] || [], label: "↓ 証明で参照",
                 note: `<b>${esc(shortOf(cen))} を証明の道具としてのみ使う</b>宣言。主張には現れないので、${esc(shortOf(cen))} について何かを述べているわけではない。` },
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
      body.innerHTML = `<p class="px-2 pb-1.5 pt-0.5 text-[11px] text-stone-500 dark:text-stone-400 leading-relaxed">${sel.note}</p>`
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
          class="w-full text-left pr-2 py-1 rounded flex items-center gap-1.5
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
        return `<div class="flex items-center gap-1 group">
          <button data-pin="${p.id}" title="${esc(p.snap.center)}"
            class="flex-1 min-w-0 text-left px-2 py-1 rounded hover:bg-stone-100 dark:hover:bg-stone-800">
            <span class="font-mono text-[11px] truncate block">${esc(shortOf(p.label))}</span>
            <span class="text-[9.5px] text-stone-400">${t} · 深さ${p.snap.baseDepth} · 下錐${{ all: "両方", type: "主張", value: "呼出" }[p.snap.refFilter] || "両方"}${p.snap.expanded.length ? ` · 展開${p.snap.expanded.length}` : ""}</span>
          </button>
          <button data-unpin="${p.id}" title="削除"
            class="w-6 h-6 shrink-0 rounded text-stone-400 opacity-0 group-hover:opacity-100 hover:bg-stone-200 dark:hover:bg-stone-700">✕</button>
        </div>`;
      }).join("");
      $("pinCount").textContent = `${st.pins.length}`;
    });
  }

  /* ================= 最小の仮定 ================= */
  function renderMinimal(st, dv) {
    const tm = dv.trueMinimal || [];
    once("min", dv.center + "|" + st.traceTarget + "|" + tm.length, () => {
      const el = $("minimalBox");
      const vis = dv.posAll || {};
      $("minCount").textContent =
        `${tm.length} 件 / 上向きの全 ${dv.fullDownSize || 0} 件のうち依存先を持たないもの`;
      const chip = (n) => {
        const on = st.traceTarget === n;
        const shown = n in vis;
        return `<button data-trace="${esc(n)}" title="${esc(n)}"
          class="font-mono text-[10.5px] px-2 py-0.5 rounded-full transition
                 bg-amber-100 text-amber-900 dark:bg-amber-950/70 dark:text-amber-200
                 ${on ? "ring-2 ring-amber-500" : "hover:ring-1 hover:ring-amber-400"}
                 ${shown ? "" : "opacity-60"}">${esc(shortOf(n))}</button>`;
      };
      el.innerHTML = `
        <div class="flex items-baseline gap-2 flex-wrap mb-1">
          <span class="text-[10.5px] text-stone-500">押すとそこへ至る経路だけを表示</span>
          ${st.traceTarget ? `<button data-trace="${esc(st.traceTarget)}"
            class="text-[10.5px] px-1.5 py-0.5 rounded bg-amber-500 text-white">経路表示を解除</button>` : ""}
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
      st.expanded.size, [...st.kindFilter].sort().join(","), st.listMode, st.sortMetric,
      st.groupBy, st.density, st.hideFrame, st.view3d,
      Object.keys(st.nodes).length, dv.center].join("|"), () => {
      const seg = (id, cur2, opts) => opts.map((o) => `<button data-${id}="${o.v}"
        class="px-2.5 py-1 text-[12.5px] rounded-md ${cur2 === o.v
          ? "bg-white dark:bg-stone-700 shadow-sm text-stone-900 dark:text-stone-100"
          : "text-stone-500 hover:text-stone-800 dark:hover:text-stone-200"}">${o.l}</button>`).join("");
      $("segEdge").innerHTML = seg("edge", st.edgeMode, [{ v: "all", l: "型+値" }, { v: "type", l: "型のみ" }]);
      $("segGran").innerHTML = seg("gran", st.granularity, [{ v: "decl", l: "宣言" }, { v: "module", l: "モジュール" }]);
      $("segList").innerHTML = seg("list", st.listMode, [
        { v: "impl", l: "実装順" }, { v: "deps", l: "依存順" }, { v: "ns", l: "名前空間" }, { v: "tree", l: "ツリー" }]);
      // 尺度の選択は「依存順」のときだけ意味を持つ
      const mw = $("metricWrap");
      mw.classList.toggle("hidden", st.listMode !== "deps");
      const m = S.metrics();
      $("segMetric").innerHTML = Object.entries(S.METRICS).map(([v, o]) => `<button data-metric="${v}"
        title="${o.mono ? "依存順序と両立する（昇順は線形拡大になる）" : "依存順序とは両立しない量"}"
        class="px-1.5 py-0.5 text-[10px] rounded ${st.sortMetric === v
          ? "bg-stone-900 text-white dark:bg-stone-100 dark:text-stone-900"
          : "text-stone-500 hover:bg-stone-100 dark:hover:bg-stone-800"}">${o.ja}${o.mono ? " ↑" : ""}</button>`).join("");
      $("metricNote").textContent = m.exact ? "" : "（規模が大きいため深さで代用）";
      $("segGroup").innerHTML = seg("group", st.groupBy, [
        { v: "subject", l: "主題" }, { v: "module", l: "モジュール" }, { v: "kind", l: "種別" }, { v: "none", l: "なし" }]);
      $("segDensity").innerHTML = [24, 36, 48, 72].map((d) => `<button data-density="${d}"
        class="px-1.5 py-0.5 text-[10.5px] rounded ${st.density === d
          ? "bg-white dark:bg-stone-700 shadow-sm text-stone-900 dark:text-stone-100"
          : "text-stone-500 hover:text-stone-800 dark:hover:text-stone-200"}">${d}</button>`).join("");
      // 下の参照錐に入れる辺。既定は「両方」で、呼び出し元も最初から下に開く。
      $("segRef").innerHTML = seg("ref", st.refFilter, [
        { v: "all", l: "両方" }, { v: "type", l: "主張のみ" }, { v: "value", l: "呼出のみ" }]);
      $("depthVal").textContent = st.baseDepth;
      $("depthRange").value = st.baseDepth;
      $("btnCollapse").classList.toggle("hidden", st.expanded.size === 0);
      $("btnCollapse").textContent = `展開を畳む (${st.expanded.size})`;
      const sb = $("spinBar");
      sb.classList.toggle("hidden", !st.view3d);
      sb.classList.toggle("flex", st.view3d);

      const mark = (el, on, cls) => cls.forEach((c) => el.classList.toggle(c, on));
      mark($("btnFrame"), st.hideFrame,
        ["bg-stone-900", "text-white", "dark:bg-stone-100", "dark:text-stone-900", "border-stone-900"]);
      mark($("btnSphere"), st.view3d,
        ["bg-indigo-600", "text-white", "border-indigo-600"]);

      const kinds = [...new Set(Object.values(st.nodes).map((n) => n.kind))].sort();
      $("kindChips").innerHTML = kinds.map((k) => {
        const on = st.kindFilter.has(k);
        return `<button data-kind="${k}" class="px-1.5 py-0.5 rounded text-[11px] flex items-center gap-1
          ${on ? "bg-stone-900 text-white dark:bg-stone-100 dark:text-stone-900" : "bg-stone-100 text-stone-600 dark:bg-stone-800 dark:text-stone-300"}">
          ${dot(k, 6)}${kinfo(k).ja}</button>`;
      }).join("");

      $("crumb").innerHTML = `<span class="font-mono text-[12px] text-stone-500 truncate">${esc(dv.center || "")}</span>`;
    });
  }

  /* 回転は毎フレーム動くので、鍵付きの再構築ではなく直接書き換える。
     いまどの区画に止まっているかが常に見えていないと、回す操作が当てずっぽうになる。 */
  function renderSpin(st, dv) {
    if (!st.view3d) return;
    const s = S.frontSector();
    $("spinLabel").textContent = s
      ? `${s.index + 1}/${s.of}  ${shortOf(s.key)}`
      : (dv.pinned && dv.pinned.length ? "分割なし" : "—");
  }

  function renderAll(st, dv) {
    if (!dv || !dv.posAll) return;
    renderToolbar(st, dv);
    renderSpin(st, dv);
    renderAudit(st);
    renderList(st, dv);
    renderInspector(st, dv);
    renderDeps(st, dv);
    renderHistory(st);
    renderPins(st);
    renderMinimal(st, dv);
  }

  LDR.panels = { renderAll, KIND, kinfo, invalidate: () => { for (const k of Object.keys(memo)) delete memo[k]; } };
})(window.LDR = window.LDR || {});
