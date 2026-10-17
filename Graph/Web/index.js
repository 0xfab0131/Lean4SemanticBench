/* ============================================================
   index.js — 配線
   ============================================================ */
(function (LDR) {
  "use strict";
  const S = LDR.store, P = LDR.panels, C = LDR.canvas, DB = LDR.persist;
  const $ = (id) => document.getElementById(id);

  /* ---------- 短い通知 ---------- */
  let toastT = 0;
  function toast(msg) {
    const el = $("toast");
    el.textContent = msg;
    el.style.opacity = "1";
    clearTimeout(toastT);
    // 長い通知（起動時の来歴など）は読み切れる時間まで残す
    toastT = setTimeout(() => { el.style.opacity = "0"; }, msg.length > 40 ? 5000 : 2000);
  }
  LDR.toast = toast;     // キャンバス側（固定で開いている由来を押したとき等）も同じ通知を使う

  /* ---------- テーマ ---------- */
  function applyTheme(dark) {
    document.documentElement.classList.toggle("dark", dark);
    localStorage.setItem("ldr-theme", dark ? "dark" : "light");
    $("themeIcon").textContent = dark ? "☾" : "☀";
    P.invalidate();          // 配色に依存した HTML を組み直す
    S.refresh();
  }

  /* ---------- 委譲イベント ---------- */
  function onClick(e) {
    const t = e.target.closest(
      "[data-nav],[data-sel],[data-trace],[data-tab],[data-kind],[data-edge],[data-gran]," +
      "[data-ref],[data-list],[data-filter],[data-tree],[data-hist],[data-pin],[data-unpin]," +
      "[data-group],[data-density],[data-preview],[data-follow],[data-deriv],[data-cluster]," +
      "[data-pback],[data-pfwd],[data-hl],[data-minmode]");
    if (!t) return;
    // 基盤／原子／境界の切替（summary の中にあるので、details の開閉には伝えない）
    if (t.dataset.minmode !== undefined) { e.preventDefault(); S.actions.setMinimalMode(t.dataset.minmode); return; }
    if (t.dataset.pback !== undefined) { S.actions.previewBack(); return; }
    if (t.dataset.pfwd !== undefined) { S.actions.previewForward(); return; }
    // 単クリック = グラフで経路を強調（プレビューは動かさない）、素早い 2 回目 = プレビューだけその宣言へ
    // （中心は動かさない。履歴に積まれるので ‹ で戻れる）
    if (t.dataset.hl !== undefined) {
      const n = t.dataset.hl, now = Date.now();
      if (onClick._last === n && now - (onClick._t || 0) < 380) { S.actions.preview(n); onClick._last = null; }
      else { S.actions.highlight(n); onClick._last = n; onClick._t = now; }
      return;
    }
    // 導出図の前提の名前（data-deriv を持つ行）は、その場で開閉する。↗（data-sel）は closest で先に取れる
    if (t.dataset.deriv !== undefined && t.dataset.sel === undefined) { S.actions.toggleDeriv(t.dataset.deriv); return; }
    if (t.dataset.cluster !== undefined) {
      const r = S.actions.toggleCluster(t.dataset.cluster);
      if (r && !r.ok && r.msg) toast(r.msg);      // 固定で開いている由来は閉じない。理由を伝える
      return;
    }
    if (t.dataset.nav !== undefined) { S.actions.navigate(t.dataset.nav); return; }
    if (t.dataset.sel !== undefined) {
      // 単クリック = 選択（比較のために覗くだけ。履歴は動かない）
      // 素早い2回目 = 中心移動（履歴に記録される）。キャンバスと同じ規則。
      const n = t.dataset.sel, now = Date.now();
      if (onClick._last === n && now - (onClick._t || 0) < 380) {
        S.actions.navigate(n); onClick._last = null;
      } else { S.actions.select(n); onClick._last = n; onClick._t = now; }
      return;
    }
    if (t.dataset.trace !== undefined) { S.actions.setTrace(t.dataset.trace); return; }
    if (t.dataset.tab !== undefined) { $("depTabs").dataset.tab = t.dataset.tab; S.refresh(); return; }
    if (t.dataset.kind !== undefined) { S.actions.toggleKind(t.dataset.kind); return; }
    if (t.dataset.edge !== undefined) { S.actions.setEdgeMode(t.dataset.edge); return; }
    if (t.dataset.gran !== undefined) { S.actions.setGranularity(t.dataset.gran); return; }
    if (t.dataset.ref !== undefined) { S.actions.setRefFilter(t.dataset.ref); return; }
    if (t.dataset.list !== undefined) { S.actions.setListMode(t.dataset.list); return; }
    if (t.dataset.group !== undefined) { S.actions.setGroupBy(t.dataset.group); return; }
    if (t.dataset.density !== undefined) { S.actions.setDensity(+t.dataset.density); return; }
    if (t.dataset.preview !== undefined) { S.actions.preview(t.dataset.preview); return; }
    if (t.dataset.deriv !== undefined) { S.actions.toggleDeriv(t.dataset.deriv); return; }
    if (t.dataset.follow !== undefined) { S.actions.setPreviewFollow(t.dataset.follow === "1"); return; }
    if (t.dataset.tree !== undefined) { S.actions.toggleTreeNode(t.dataset.tree); return; }
    if (t.dataset.hist !== undefined) { S.actions.jumpHist(t.dataset.hist); return; }
    if (t.dataset.pin !== undefined) { toast(S.actions.applyPin(t.dataset.pin).msg); return; }
    if (t.dataset.unpin !== undefined) { S.actions.removePin(t.dataset.unpin); return; }
    if (t.dataset.filter === "sorry") { S.actions.toggleOnlySorry(); return; }
    if (t.dataset.filter === "openall") { S.actions.toggleOpenAll(); return; }
  }

  /* ---------- キーボード ---------- */
  function onKey(e) {
    const tag = e.target && e.target.tagName;
    if (tag === "INPUT" || tag === "TEXTAREA") {
      if (e.key === "Escape") e.target.blur();
      return;
    }
    const k = e.key.toLowerCase();
    // 探索履歴の上り下り。木なので「戻る」は親、「進む」は最後に降りた子。
    if ((e.ctrlKey || e.metaKey) && k === "z" && !e.shiftKey) { e.preventDefault(); S.actions.back(); return; }
    if ((e.ctrlKey || e.metaKey) && (k === "y" || (k === "z" && e.shiftKey))) { e.preventDefault(); S.actions.forward(); return; }
    if (e.ctrlKey || e.metaKey) return;

    if (e.key === "/") { e.preventDefault(); $("search").focus(); return; }
    if (e.key === "Backspace" || (e.altKey && e.key === "ArrowLeft")) { e.preventDefault(); S.actions.back(); return; }
    if (e.altKey && e.key === "ArrowRight") { e.preventDefault(); S.actions.forward(); return; }
    if (e.key === "0") { C.reset(); return; }
    if (e.key === "+" || e.key === "=") { C.zoomIn(); return; }
    if (e.key === "-") { C.zoomOut(); return; }
    if (e.key === "Escape") { S.actions.setTrace(null); S.actions.clearPath(); return; }
    // プレビューの履歴（見た宣言の列）を戻る／進む。中心の履歴（Ctrl+Z / Y）とは別
    if (e.key === "[") { S.actions.previewBack(); return; }
    if (e.key === "]") { S.actions.previewForward(); return; }
    if (k === "f") { toggleFocus(); return; }
    if (k === "t") { S.actions.setEdgeMode(S.state.edgeMode === "all" ? "type" : "all"); return; }
    if (k === "m") { S.actions.setGranularity(S.state.granularity === "decl" ? "module" : "decl"); return; }
    if (k === "v") { S.actions.cycleRefFilter(); return; }
    if (k === "p") { const p = S.actions.addPin(); toast(`ピン留めしました: ${p.label}`); return; }
  }

  /* ---------- マウスの戻る／進むボタン ----------
     ブラウザの履歴移動が既定動作なので、file:// では取り消さないとページを失う。 */
  function onMouseNav(e) {
    if (e.button !== 3 && e.button !== 4) return;
    e.preventDefault();
    if (e.type !== "mousedown") return;
    if (e.button === 3) S.actions.back(); else S.actions.forward();
  }

  /* ---------- パネルの幅 ---------- */
  function setupResizer(el) {
    const which = el.dataset.resize;
    const target = which === "left" ? $("sidebar") : $("sideR");
    let start = null;
    el.addEventListener("pointerdown", (e) => {
      start = { x: e.clientX, w: target.offsetWidth };
      el.classList.add("on");
      document.body.classList.add("noselect");
      el.setPointerCapture(e.pointerId);
    });
    el.addEventListener("pointermove", (e) => {
      if (!start) return;
      const d = which === "left" ? (e.clientX - start.x) : (start.x - e.clientX);
      target.style.width = Math.max(which === "left" ? 220 : 280, Math.min(760, start.w + d)) + "px";
      fitWidths();
    });
    const end = () => {
      if (!start) return;
      start = null;
      el.classList.remove("on");
      document.body.classList.remove("noselect");
      localStorage.setItem("ldr-w-" + which, target.style.width);
    };
    el.addEventListener("pointerup", end);
    el.addEventListener("pointercancel", end);
    el.addEventListener("dblclick", () => {
      target.style.width = which === "left" ? "280px" : "330px";
      localStorage.setItem("ldr-w-" + which, target.style.width);
    });
  }

  /* ---------- 保持 ---------- */
  const saveData = DB.debounced((text) => DB.set("report", text), 400);
  const savePins = DB.debounced((pins) => DB.set("pins", pins), 200);
  LDR.onDataLoaded = (text) => saveData(text);
  LDR.onPinsChanged = (pins) => savePins(pins);

  /* ---------- 既定の監査結果 ----------
     file:// では隣の report.jsonl を fetch できないので、
     `node Graph/make_default_report.js` が生成する埋め込み版をまず試す。
     http で配信されている場合はそのまま取りに行ける。 */
  function injectScript(src) {
    return new Promise((res) => {
      const s = document.createElement("script");
      s.src = src;
      s.onload = () => res(true);
      s.onerror = () => res(false);
      document.head.appendChild(s);
    });
  }

  let defaultTried = false;
  async function getDefaultReport() {
    if (LDR.DEFAULT_REPORT) return LDR.DEFAULT_REPORT;
    if (!defaultTried) {
      defaultTried = true;
      await injectScript("js/default-report.js");
      if (LDR.DEFAULT_REPORT) return LDR.DEFAULT_REPORT;
    }
    try {
      const r = await fetch("../report.jsonl");
      if (r.ok) { const t = await r.text(); if (t.trim()) return t; }
    } catch (e) { /* file:// では届かない。想定内 */ }
    return null;
  }

  function download(name, text, mime) {
    const blob = new Blob([text], { type: mime || "application/json" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url; a.download = name;
    document.body.appendChild(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }

  async function copyText(text) {
    try {
      await navigator.clipboard.writeText(text);
      return true;
    } catch (e) {
      // file:// で権限が下りない環境があるので退避経路を持つ
      const ta = document.createElement("textarea");
      ta.value = text; ta.style.position = "fixed"; ta.style.opacity = "0";
      document.body.appendChild(ta); ta.select();
      let ok = false;
      try { ok = document.execCommand("copy"); } catch (_) { ok = false; }
      ta.remove();
      return ok;
    }
  }

  /* ---------- 起動 ---------- */
  async function boot() {
    const saved = localStorage.getItem("ldr-theme");
    const prefersDark = typeof window.matchMedia === "function"
      && window.matchMedia("(prefers-color-scheme: dark)").matches;
    document.documentElement.classList.toggle("dark", saved ? saved === "dark" : prefersDark);
    $("themeIcon").textContent = document.documentElement.classList.contains("dark") ? "☾" : "☀";

    /* 保存された幅をそのまま復元すると、以前に広げたまま、あるいは集中表示で
       広げたままの値で中央が潰れることがある。画面幅に対する上限で抑える。 */
    for (const which of ["left", "right"]) {
      const el = which === "left" ? $("sidebar") : $("sideR");
      const saved = parseInt(localStorage.getItem("ldr-w-" + which) || "", 10);
      /* 下限は内容の自然な幅（左: 絞り込みの札、右: 依存のタブ列）。上限は画面幅に対する割合だが、
         下限より小さくはしない（190px まで縮めると札が欄からはみ出した。実測）。
         幅が足りない画面では左の一覧は重ね表示（drawer）になるので、ここでの上限は三枚並ぶ画面の話 */
      const min = which === "left" ? 220 : 280;
      const cap = Math.max(min, Math.round(window.innerWidth * (which === "left" ? 0.24 : 0.34)));
      const def = which === "left" ? 280 : 330;
      el.style.width = Math.max(min, Math.min(Number.isFinite(saved) ? saved : def, cap)) + "px";
    }

    // 右パネルは「見ている宣言」のプレビューから始める（依存の一覧はタブで切り替える）
    $("depTabs").dataset.tab = "prev";

    /* 読み込みの優先順位。
         1. 既定の監査結果が「前回起動時に見たもの」から変わっていれば、それを読む。
            解析を回し直して埋め込みが新しくなったのに、古い保持データを復元して
            見せ続けると「直したのに変わらない」という誤認を生む（実際に起きた。
            toast で伝えるだけでは足りなかった）。保持データもこれで置き換える。
         2. 変わっていなければ、前回の保持（利用者が貼り付けた別データ等）を復元する。
         3. どちらも無ければ既定の監査結果、それも無ければサンプル。
       既定の同一性は長さとハッシュの指紋で見る。文字列比較より安く、保持側が
       既定と同じ内容かどうかも同じ指紋で判定できる。 */
    const fingerprint = (t) => {
      let h = 2166136261;
      for (let i = 0; i < t.length; i++) { h ^= t.charCodeAt(i); h = Math.imul(h, 16777619); }
      return t.length + ":" + (h >>> 0).toString(16);
    };
    let initial = null, source = "";
    let persisted = null;
    try {
      const t = await DB.get("report");
      if (typeof t === "string" && t.trim()) persisted = t;
    } catch (e) { /* 保持が使えなくても動作は続ける */ }
    const def = await getDefaultReport();
    const defFp = def ? fingerprint(def) : null;
    const seenFp = localStorage.getItem("ldr-default-fp");
    if (def && defFp !== seenFp) {
      initial = def;
      source = seenFp
        ? "既定の監査結果が更新されていたので読み込みました（前回の保持データは置き換え）"
        : "既定の監査結果を読み込みました";
      localStorage.setItem("ldr-default-fp", defFp);
      saveData(def);
    } else if (persisted) {
      initial = persisted;
      source = (def && fingerprint(persisted) !== defFp)
        ? "前回のレポートを復元しました（既定の監査結果とは別の内容。データ → 既定 で切り替え）"
        : "前回のレポートを復元しました";
    } else if (def) {
      initial = def; source = "既定の監査結果を読み込みました";
    } else if (LDR.SAMPLE) {
      initial = LDR.SAMPLE; source = "サンプルを表示しています（データボタンから読み込めます）";
    } else {
      /* 配置（GitHub Pages）には生成物 js/sample.js を同梱しない。既定の監査結果も無ければ空で始める */
      initial = ""; source = "レポートがありません（データボタンから読み込めます）";
    }

    S.actions.loadText(initial, { silent: true });
    try {
      const pins = await DB.get("pins");
      if (Array.isArray(pins)) S.actions.setPins(pins);
    } catch (e) { /* 同上 */ }

    C.mount($("canvasHost"));
    S.subscribe(P.renderAll);
    S.refresh(true);
    toast(source);

    document.addEventListener("click", onClick);
    document.addEventListener("keydown", onKey);
    window.addEventListener("mousedown", onMouseNav);
    window.addEventListener("mouseup", onMouseNav);
    window.addEventListener("auxclick", onMouseNav);
    document.querySelectorAll("[data-resize]").forEach(setupResizer);
    applyResponsive();
    window.addEventListener("resize", applyResponsive, { passive: true });
    /* 浮遊パネル（「表示」と、上部バーの 履歴・ピン・レポート・凡例）。fixed で出すので、開くたびに
       summary の位置へ置く。絶対配置のままだと、祖先の overflow やスタッキング文脈で切り取られる。
       一つ開けば他は閉じ、外を押せば閉じる。 */
    const pops = [...document.querySelectorAll("details.pop"), $("dView")];
    const placePanel = (d) => {
      if (!d.open) return;
      const sum = d.querySelector("summary").getBoundingClientRect();
      const panel = d.querySelector(".popPanel") || $("dViewPanel");
      if (!panel) return;
      panel.style.top = Math.round(sum.bottom + 6) + "px";
      const w = panel.offsetWidth || 380;
      panel.style.left = Math.round(Math.max(8, Math.min(sum.left, window.innerWidth - w - 8))) + "px";
    };
    for (const d of pops) {
      d.addEventListener("toggle", () => {
        if (d.open) { for (const o of pops) if (o !== d) o.open = false; if (d.id === "dReport") renderReportPanel(); }
        placePanel(d);
      });
    }
    window.addEventListener("resize", () => pops.forEach(placePanel), { passive: true });
    document.addEventListener("click", (e) => {
      for (const d of pops) if (d.open && !d.contains(e.target) && !e.target.closest("dialog")) d.open = false;
    }, true);
    // 履歴・ピンの中身が組み直されたら位置を取り直す（高さが変わる）
    S.subscribe(() => pops.forEach(placePanel));

    /* ---------- レポート ---------- */
    setupReport();

    $("search").addEventListener("input", (e) => S.actions.setQuery(e.target.value));
    $("depthRange").addEventListener("input", (e) => S.actions.setBaseDepth(+e.target.value));
    $("btnBack").addEventListener("click", S.actions.back);
    $("btnFwd").addEventListener("click", S.actions.forward);
    $("btnCollapse").addEventListener("click", S.actions.collapseAll);
    $("btnFrame").addEventListener("click", S.actions.toggleHideFrame);
    $("btnZoomIn").addEventListener("click", C.zoomIn);
    $("btnZoomOut").addEventListener("click", C.zoomOut);
    $("btnFit").addEventListener("click", C.reset);
    $("btnClearKinds").addEventListener("click", S.actions.clearKinds);
    $("btnHistClear").addEventListener("click", () => { S.actions.clearHist(); toast("履歴を消去しました"); });
    $("themeBtn").addEventListener("click", () =>
      applyTheme(!document.documentElement.classList.contains("dark")));

    // ピン
    $("btnPinAdd").addEventListener("click", () => {
      const p = S.actions.addPin();
      toast(`ピン留めしました: ${p.label}`);
    });
    $("btnPinCopy").addEventListener("click", async () => {
      const ok = await copyText(S.actions.exportPins());
      toast(ok ? "ピンを JSON でコピーしました" : "コピーできませんでした");
    });
    $("btnPinSave").addEventListener("click", () => {
      download(`ldr-pins-${new Date().toISOString().slice(0, 10)}.json`, S.actions.exportPins());
      toast("ピンを保存しました");
    });
    $("btnPinLoad").addEventListener("click", () => $("pinFile").click());
    $("pinFile").addEventListener("change", async (e) => {
      const f = e.target.files[0];
      if (!f) return;
      toast(S.actions.importPins(await f.text()).msg);
      e.target.value = "";
    });

    // データ読み込み
    $("btnData").addEventListener("click", async () => {
      $("dataStatus").textContent = "既定の監査結果を探しています…";
      $("dataStatus").style.whiteSpace = "pre-line";
      $("dataDlg").showModal();
      const d = await getDefaultReport();
      let status = d
        ? `既定の監査結果: ${(d.length / 1048576).toFixed(1)} MB / ${d.split("\n").filter(Boolean).length} 宣言`
        : "既定の監査結果は未生成です。Graph で `node make_default_report.js` を実行すると埋め込まれます。";
      // 来歴(report.meta.json 由来)。何の・いつの・どの環境の解析かを常に同定できるようにする
      const m = LDR.DEFAULT_META;
      if (d && m && m.target) {
        const rev = (m.target.gitRev || "").slice(0, 8);
        status += `\n来歴: ${m.target.name || "?"}${rev ? " @ " + rev : ""}`
          + (m.target.dirty ? "（dirty: 未コミットの変更あり）" : "")
          + ` · ${m.target.toolchain || "?"}`
          + (m.modules ? ` · ${m.modules.join(" ")}` : "")
          + (m.generatedAt ? ` · ${m.generatedAt}` : "");
      }
      $("dataStatus").textContent = status;
      $("dataDefault").disabled = !d;
      $("dataDefault").classList.toggle("opacity-40", !d);
    });
    $("dataClose").addEventListener("click", () => $("dataDlg").close());
    $("dataDefault").addEventListener("click", async () => {
      const d = await getDefaultReport();
      if (!d) { toast("既定の監査結果がありません"); return; }
      S.actions.loadText(d);
      $("dataDlg").close();
      toast("既定の監査結果を読み込みました");
    });
    // サンプル（js/sample.js）は生成物で、配置には同梱しない。無ければボタンを出さない
    if (!LDR.SAMPLE) $("dataSample").classList.add("hidden");
    $("dataSample").addEventListener("click", () => {
      if (!LDR.SAMPLE) { toast("サンプルは同梱されていません"); return; }
      S.actions.loadText(LDR.SAMPLE);
      $("dataDlg").close();
      toast("サンプルを読み込みました");
    });
    $("dataApply").addEventListener("click", () => {
      const t = $("dataText").value;
      if (t.trim()) { S.actions.loadText(t); toast("読み込みました"); }
      $("dataDlg").close();
    });
    $("dataForget").addEventListener("click", async () => {
      await DB.del("report");
      toast("保持データを消去しました。次回は既定の監査結果に戻ります");
    });
    $("fileInput").addEventListener("change", async (e) => {
      const f = e.target.files[0];
      if (f) $("dataText").value = await f.text();
    });

    // ドロップ
    document.body.addEventListener("dragover", (e) => { e.preventDefault(); });
    document.body.addEventListener("drop", async (e) => {
      e.preventDefault();
      const f = e.dataTransfer.files[0];
      if (!f) return;
      const text = await f.text();
      if (f.name.endsWith(".json") && text.includes('"ldr-pins"')) {
        toast(S.actions.importPins(text).msg);
      } else {
        S.actions.loadText(text);
        toast(`${f.name} を読み込みました`);
      }
    });

    // パネルの開閉
    $("btnSide").addEventListener("click", () => toggleAside($("sidebar"), "left"));
    // 重ね表示の背面を押すと一覧を閉じる
    $("drawerBackdrop").addEventListener("click", () => toggleAside($("sidebar"), "left"));
    $("btnSideR").addEventListener("click", () => toggleAside($("sideR"), "right"));
    $("btnFocus").addEventListener("click", toggleFocus);
  }

  /* ---------- レポート（証明の構造を Markdown に） ----------
     主語（中心／選択／極小元）・章・導出図の深さを選び、プレビューしてから写す／保存する。
     生成は report.js（純粋関数）。ここは選択の保持と配線だけ。 */
  const reportOpts = { kind: "center", sections: new Set(LDR.report ? LDR.report.ALL : []), depth: 2,
                       style: Object.fromEntries((LDR.report ? LDR.report.STYLE : []).map((s) => [s.id, s.def])) };
  function renderReportPanel() {
    if (!LDR.report) return;
    const st = S.state, dv = S.derived;
    const short = (n) => (n ? LDR.sig.shortName(n) : "");
    const subj = [
      { k: "center", l: "中心", n: dv.center, t: "グラフの中心" },
      { k: "selected", l: "選択", n: st.selected && st.selected !== dv.center ? st.selected : null, t: "グラフや一覧で押した宣言（中心と異なるもの）" },
      { k: "minimal", l: "経路の対象", n: st.traceTarget, t: "経路表示の対象（基盤・原子・境界・公理のチップで選んだもの）" },
    ];
    $("reportSubject").innerHTML = `<span class="text-[11.5px] text-stone-500 mr-1">主語</span>` + subj.map((s) => `<button data-rsubj="${s.k}" ${s.n ? "" : "disabled"}
        title="${s.t}${s.n ? "" : "（いまは無い）"}"
        class="px-2 py-1 rounded-md text-[11.5px] border ${reportOpts.kind === s.k
          ? "bg-stone-900 text-white border-stone-900 dark:bg-stone-100 dark:text-stone-900"
          : s.n ? "bg-white text-stone-600 border-stone-300 hover:bg-stone-100 dark:bg-stone-900 dark:text-stone-300 dark:border-stone-600" : "text-stone-300 border-stone-200 dark:text-stone-600 dark:border-stone-700"}">
        ${s.l}${s.n ? ` <span class="font-mono text-[10.5px] opacity-80">${short(s.n)}</span>` : ""}</button>`).join("");
    $("reportSections").innerHTML = `<div class="text-[10.5px] text-stone-400">章</div>`
      + LDR.report.SECTIONS.map((s) => `<label class="flex items-center gap-1.5 cursor-pointer ${s.id === "path" && reportOpts.kind === "center" ? "opacity-40" : ""}">
        <input type="checkbox" data-rsec="${s.id}" ${reportOpts.sections.has(s.id) ? "checked" : ""} class="accent-indigo-600">${s.ja}${s.id === "path" && reportOpts.kind === "center" ? "（中心が主語のときは無し）" : ""}</label>`).join("")
      + `<div class="text-[10.5px] text-stone-400 pt-1">書き方</div>`
      + LDR.report.STYLE.map((s) => `<label class="flex items-center gap-1.5 cursor-pointer">
        <input type="checkbox" data-rstyle="${s.id}" ${reportOpts.style[s.id] ? "checked" : ""} class="accent-indigo-600">${s.ja}</label>`).join("");
    $("reportDepth").innerHTML = [1, 2, 3].map((d) => `<button data-rdepth="${d}"
        class="px-2 py-0.5 text-[11px] rounded-md ${reportOpts.depth === d ? "bg-white dark:bg-stone-700 shadow-sm text-stone-900 dark:text-stone-100" : "text-stone-500 hover:text-stone-800 dark:hover:text-stone-200"}">${d}</button>`).join("");
  }
  function buildReport() {
    if (!LDR.report) return { ok: false, msg: "レポートの部品が読み込まれていません" };
    return LDR.report.build(reportOpts.kind, { sections: [...reportOpts.sections], depth: reportOpts.depth, ...reportOpts.style });
  }
  function setupReport() {
    $("dReport").addEventListener("click", (e) => {
      const b = e.target.closest("[data-rsubj],[data-rdepth],[data-rsec],[data-rstyle]");
      if (!b) return;
      if (b.dataset.rsubj) { reportOpts.kind = b.dataset.rsubj; renderReportPanel(); }
      else if (b.dataset.rdepth) { reportOpts.depth = +b.dataset.rdepth; renderReportPanel(); }
      else if (b.dataset.rsec) { b.checked ? reportOpts.sections.add(b.dataset.rsec) : reportOpts.sections.delete(b.dataset.rsec); }
      else if (b.dataset.rstyle) { reportOpts.style[b.dataset.rstyle] = b.checked; }
    });
    $("reportAll").addEventListener("click", () => { reportOpts.sections = new Set(LDR.report.ALL); renderReportPanel(); });
    $("reportNone").addEventListener("click", () => { reportOpts.sections = new Set(["claim"]); renderReportPanel(); });
    const fileName = (r) => `ldr-${LDR.sig.shortName(r.subject).replace(/[^\w.-]+/g, "_")}-${new Date().toISOString().slice(0, 10)}.md`;
    $("reportPreview").addEventListener("click", () => {
      const r = buildReport();
      if (!r.ok) { toast(r.msg); return; }
      $("reportText").value = r.text;
      $("reportDlgInfo").textContent = `${LDR.sig.shortName(r.subject)} · ${r.text.split("\n").length} 行 · ${(r.text.length / 1024).toFixed(1)} KB`;
      $("reportDlg").showModal();
    });
    $("reportCopy").addEventListener("click", async () => {
      const r = buildReport();
      if (!r.ok) { toast(r.msg); return; }
      toast((await copyText(r.text)) ? `レポートをコピーしました（${r.text.split("\n").length} 行）` : "コピーできませんでした");
    });
    $("reportSave").addEventListener("click", () => {
      const r = buildReport();
      if (!r.ok) { toast(r.msg); return; }
      download(fileName(r), r.text, "text/markdown");
      toast("レポートを保存しました");
    });
    $("reportDlgCopy").addEventListener("click", async () => {
      toast((await copyText($("reportText").value)) ? "レポートをコピーしました" : "コピーできませんでした");
    });
    $("reportDlgSave").addEventListener("click", () => {
      const r = buildReport();
      download(r.ok ? fileName(r) : "ldr-report.md", $("reportText").value, "text/markdown");
      toast("レポートを保存しました");
    });
    $("reportDlgClose").addEventListener("click", () => $("reportDlg").close());
  }

  /* 幅に応じてパネルを自動で畳む。
     狭いところに三枚並べても、どれも読めない幅になるだけなので、
     優先度の低い側から外す。利用者が明示的に開いたものは尊重する。 */
  /* 幅の配分。三枚を並べるのは、左右を下限（左 220・右 280）まで縮めても中央に 480px 残る幅から
     （220 + 280 + 480 + 帯 10 = 990）。並べるときは中央を 480px 以上に保ち、足りない分は右 → 左の順に
     下限まで縮める（保存された幅はそのまま、画面幅に応じて毎回ここで詰める）。
     OS の拡大率が高い画面では CSS 上の幅が 1000px 前後になり、三枚で左 190・右 326・中央 434 に
     潰れて中央の見出しも操作列も読めなかった（実測）。 */
  const BP = { both: 990, right: 820 };
  const MIN = { left: 220, right: 280, center: 480 };
  let autoState = null, userTouched = { left: false, right: false };
  function fitWidths() {
    const w = window.innerWidth;
    const side = $("sidebar"), right = $("sideR");
    const L = !side.classList.contains("hidden") && !side.classList.contains("drawer");
    const R = !right.classList.contains("hidden");
    let l = L ? (parseInt(side.style.width, 10) || 280) : 0;
    let r = R ? (parseInt(right.style.width, 10) || 330) : 0;
    let over = l + r + MIN.center + (L ? 5 : 0) + (R ? 5 : 0) - w;
    if (over > 0 && R) { const d = Math.min(over, Math.max(0, r - MIN.right)); r -= d; over -= d; }
    if (over > 0 && L) { const d = Math.min(over, Math.max(0, l - MIN.left)); l -= d; over -= d; }
    if (L) side.style.width = l + "px";
    if (R) right.style.width = r + "px";
  }
  /* 三枚が並ばない幅（BP.both 未満）で一覧を開いたときは、中央を押し潰さずキャンバスの上に重ねる
     （drawer。CSS は index.html の #sidebar.drawer）。背面を暗くし、押せば閉じる。重ねている間は幅の帯も出さない。 */
  function syncDrawer() {
    const side = $("sidebar"), rz = document.querySelector('[data-resize="left"]'), bd = $("drawerBackdrop");
    const drawer = window.innerWidth < BP.both && !focusOn;
    side.classList.toggle("drawer", drawer);
    if (rz) rz.classList.toggle("hidden", drawer || side.classList.contains("hidden"));
    if (bd) bd.classList.toggle("hidden", !(drawer && !side.classList.contains("hidden")));
  }
  function applyResponsive() {
    if (focusOn) return;          // 集中表示は自動制御より優先する
    const w = window.innerWidth;
    syncDrawer();
    const want = w >= BP.both ? "both" : w >= BP.right ? "right" : "none";
    if (want !== autoState) {
      autoState = want;
      const setSide = (el, which, show) => {
        if (userTouched[which]) return;
        el.classList.toggle("hidden", !show);
        const rz = document.querySelector(`[data-resize="${which}"]`);
        if (rz) rz.classList.toggle("hidden", !show);
      };
      setSide($("sidebar"), "left", want === "both");
      setSide($("sideR"), "right", want !== "none");
      syncDrawer();
    }
    fitWidths();
  }

  function toggleAside(el, which) {
    userTouched[which] = true;          // 明示的に触った側は自動制御から外す
    const hidden = el.classList.toggle("hidden");
    const rz = document.querySelector(`[data-resize="${which}"]`);
    if (rz) rz.classList.toggle("hidden", hidden);
    if (which === "left") syncDrawer();
    fitWidths();
  }

  /* 集中表示。左の一覧と操作列を畳み、中央のグラフと右のプレビューだけにする。
     一つの宣言を腰を据えて読むときは、探索のための道具立てが視野を狭める。 */
  let focusOn = false, focusSaved = null;
  function toggleFocus() {
    focusOn = !focusOn;
    const side = $("sidebar"), rz = document.querySelector('[data-resize="left"]');
    const bar = document.getElementById("toolRow");
    if (focusOn) {
      focusSaved = { side: side.classList.contains("hidden"), r: $("sideR").style.width };
      side.classList.add("hidden");
      side.classList.remove("drawer");
      if (rz) rz.classList.add("hidden");
      // 操作列は消さず、キャンバスの上に浮かせて残す。詳しい制御は「表示 ▾」に畳んである
      if (bar) bar.classList.add("focus-min");
      $("inspector").classList.add("hidden");
      $("sideR").classList.remove("hidden");
      $("sideR").style.width = Math.max(420, Math.round(window.innerWidth * 0.38)) + "px";
      S.actions.setPreviewFollow(true);
      $("depTabs").dataset.tab = "prev";
      S.refresh();
    } else {
      if (bar) bar.classList.remove("focus-min");
      $("inspector").classList.remove("hidden");
      if (focusSaved && focusSaved.r) $("sideR").style.width = focusSaved.r;
      autoState = null;           // 幅に応じた自動制御をやり直させる
      applyResponsive();
    }
    $("btnFocus").classList.toggle("bg-indigo-600", focusOn);
    $("btnFocus").classList.toggle("text-white", focusOn);
    $("btnFocus").classList.toggle("border-indigo-600", focusOn);
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", boot);
  else boot();
})(window.LDR = window.LDR || {});
