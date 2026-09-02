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
    toastT = setTimeout(() => { el.style.opacity = "0"; }, 2000);
  }

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
      "[data-ref],[data-list],[data-audit],[data-tree],[data-hist],[data-pin],[data-unpin]," +
      "[data-metric],[data-group],[data-density],[data-preview],[data-follow],[data-deriv],[data-spin]");
    if (!t) return;
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
    if (t.dataset.metric !== undefined) { S.actions.setSortMetric(t.dataset.metric); return; }
    if (t.dataset.group !== undefined) { S.actions.setGroupBy(t.dataset.group); return; }
    if (t.dataset.density !== undefined) { S.actions.setDensity(+t.dataset.density); return; }
    if (t.dataset.preview !== undefined) { S.actions.preview(t.dataset.preview); return; }
    if (t.dataset.deriv !== undefined) { S.actions.toggleDeriv(t.dataset.deriv); return; }
    if (t.dataset.spin !== undefined) { S.actions.spinStep(+t.dataset.spin); return; }
    if (t.dataset.follow !== undefined) { S.actions.setPreviewFollow(t.dataset.follow === "1"); return; }
    if (t.dataset.tree !== undefined) { S.actions.toggleTreeNode(t.dataset.tree); return; }
    if (t.dataset.hist !== undefined) { S.actions.jumpHist(t.dataset.hist); return; }
    if (t.dataset.pin !== undefined) { S.actions.applyPin(t.dataset.pin); toast("ピンの状態に戻しました"); return; }
    if (t.dataset.unpin !== undefined) { S.actions.removePin(t.dataset.unpin); return; }
    if (t.dataset.audit === "sorry") { S.actions.toggleOnlySorry(); return; }
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
    if (k === "f") { toggleFocus(); return; }
    if (k === "b") { S.actions.toggleView3d(); return; }
    // 経度は等分なので、一押しで隣の区画へちょうど送れる
    if (S.state.view3d && (e.key === "[" || e.key === "]")) {
      S.actions.spinStep(e.key === "[" ? -1 : 1);
      return;
    }
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
      target.style.width = Math.max(190, Math.min(760, start.w + d)) + "px";
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
      target.style.width = which === "left" ? "264px" : "312px";
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
      const cap = Math.round(window.innerWidth * (which === "left" ? 0.24 : 0.34));
      const def = which === "left" ? 264 : 330;
      el.style.width = Math.max(190, Math.min(Number.isFinite(saved) ? saved : def, cap)) + "px";
    }

    $("depTabs").dataset.tab = "type";

    /* 読み込みの優先順位: 前回の保持 → 既定の監査結果 → サンプル。
       毎回 5 MB を投げ直させないための順序。 */
    let initial = null, source = "";
    try {
      const t = await DB.get("report");
      if (typeof t === "string" && t.trim()) { initial = t; source = "前回のレポートを復元しました"; }
    } catch (e) { /* 保持が使えなくても動作は続ける */ }
    if (!initial) {
      const d = await getDefaultReport();
      if (d) { initial = d; source = "既定の監査結果を読み込みました"; }
    }
    if (!initial) { initial = LDR.SAMPLE; source = "サンプルを表示しています（データボタンから読み込めます）"; }

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
    /* 「表示」ポップオーバー。fixed で出すので、開くたびに summary の位置へ置く。
       絶対配置のままだと、祖先の overflow やスタッキング文脈で切り取られる。 */
    const dv = $("dView");
    const placeViewPanel = () => {
      if (!dv.open) return;
      const sum = dv.querySelector("summary").getBoundingClientRect();
      const panel = $("dViewPanel");
      panel.style.top = Math.round(sum.bottom + 6) + "px";
      const w = panel.offsetWidth || 380;
      panel.style.left = Math.round(Math.max(8, Math.min(sum.left, window.innerWidth - w - 8))) + "px";
    };
    dv.addEventListener("toggle", placeViewPanel);
    window.addEventListener("resize", placeViewPanel, { passive: true });
    document.addEventListener("click", (e) => {
      if (dv.open && !dv.contains(e.target)) dv.open = false;
    }, true);

    $("search").addEventListener("input", (e) => S.actions.setQuery(e.target.value));
    $("depthRange").addEventListener("input", (e) => S.actions.setBaseDepth(+e.target.value));
    $("btnBack").addEventListener("click", S.actions.back);
    $("btnFwd").addEventListener("click", S.actions.forward);
    $("btnCollapse").addEventListener("click", S.actions.collapseAll);
    $("btnFrame").addEventListener("click", S.actions.toggleHideFrame);
    $("btnSphere").addEventListener("click", S.actions.toggleView3d);
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
    $("dataSample").addEventListener("click", () => {
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
    $("btnSideR").addEventListener("click", () => toggleAside($("sideR"), "right"));
    $("btnFocus").addEventListener("click", toggleFocus);
  }

  /* 幅に応じてパネルを自動で畳む。
     狭いところに三枚並べても、どれも読めない幅になるだけなので、
     優先度の低い側から外す。利用者が明示的に開いたものは尊重する。 */
  const BP = { both: 1180, right: 820 };
  let autoState = null, userTouched = { left: false, right: false };
  function applyResponsive() {
    if (focusOn) return;          // 集中表示は自動制御より優先する
    const w = window.innerWidth;
    const want = w >= BP.both ? "both" : w >= BP.right ? "right" : "none";
    if (want === autoState) return;
    autoState = want;
    const setSide = (el, which, show) => {
      if (userTouched[which]) return;
      el.classList.toggle("hidden", !show);
      const rz = document.querySelector(`[data-resize="${which}"]`);
      if (rz) rz.classList.toggle("hidden", !show);
    };
    setSide($("sidebar"), "left", want === "both");
    setSide($("sideR"), "right", want !== "none");
  }

  function toggleAside(el, which) {
    userTouched[which] = true;          // 明示的に触った側は自動制御から外す
    const hidden = el.classList.toggle("hidden");
    const rz = document.querySelector(`[data-resize="${which}"]`);
    if (rz) rz.classList.toggle("hidden", hidden);
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
