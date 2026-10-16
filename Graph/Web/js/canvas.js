/* ============================================================
   js/canvas.js — p5 による円錐グラフの描画

   ・中心のまわりに二つの錐を置く。上は中心が依存する側 ↓d、下は中心を使う側 ↑d。
     角度の区間が交わらないので、上下の辺は原理的に一本も交差しない。
   ・層は同心の円弧（ファイバーの底空間が角度方向）。辺は極座標のベジエで、
     中間半径まで半径方向に出てから角度方向へ移る。同じ扇の辺が束ねられる。
   ・層を跨ぐ辺は角度方向へ膨らませる。まっすぐ引くと途中の層のノードを
     突き抜けてしまい、どこから来た線なのか読めなくなる。
   ・辺は四種類あり、色・線種・矢じりの三つで区別する。色だけだと
     並んでいないと比較できず、線種だけだと細いところで潰れる。
   ・位置は store が事前に計算した表を読むだけ。毎フレームの仕事は
     可視ノード数に比例する分だけで、グラフ全体の走査は起きない。
   ・単クリック = 選択（中心は動かない）、ダブルクリック = 中心移動。
   ============================================================ */
(function (LDR) {
  "use strict";
  const S = LDR.store;

  const PAL = {
    light: {
      bg: "#FFFFFF", ring: "#E7E5E4", ringHot: "#D6D3D1",
      nodeBg: "#FFFFFF", nodeBd: "#D6D3D1", nodeTx: "#1C1917",
      dim: 0.1,
      center: "#4F46E5", centerTx: "#FFFFFF", centerRing: "#C7D2FE",
      minBg: "#FEF3C7", minBd: "#D97706", minTx: "#78350F",
      sorryBg: "#FFE4E6", sorryBd: "#E11D48", sorryTx: "#881337",
      trace: "#D97706",
      badgeBg: "#F5F5F4", badgeTx: "#57534E",
      muted: "#A8A29E", faint: "#57534E",
      panel: "rgba(255,255,255,.86)", panelBd: "#E7E5E4",
    },
    dark: {
      bg: "#0C0A09", ring: "#242020", ringHot: "#3F3B39",
      nodeBg: "#1C1917", nodeBd: "#44403C", nodeTx: "#E7E5E4",
      dim: 0.1,
      center: "#6366F1", centerTx: "#FFFFFF", centerRing: "#3730A3",
      minBg: "#451A03", minBd: "#D97706", minTx: "#FDE68A",
      sorryBg: "#4C0519", sorryBd: "#F43F5E", sorryTx: "#FECDD3",
      trace: "#F59E0B",
      badgeBg: "#292524", badgeTx: "#A8A29E",
      muted: "#78716C", faint: "#D6D3D1",
      panel: "rgba(28,25,23,.86)", panelBd: "#292524",
    },
  };

  /* 四種類の辺。色相・線種・矢じりの形を全て変えてある。 */
  const EDGE = {
    "dep|type":  { l: "#4F46E5", d: "#818CF8", dash: null,     head: "solid", ja: "型依存",   sub: "中心の主張に現れる" },
    "dep|value": { l: "#7C3AED", d: "#C4B5FD", dash: [5, 5],   head: "open",  ja: "値依存",   sub: "中心の証明にだけ現れる" },
    "ref|type":  { l: "#0F766E", d: "#2DD4BF", dash: null,     head: "solid", ja: "主張で参照", sub: "中心についての定理・性質" },
    "ref|value": { l: "#C2410C", d: "#FB923C", dash: [4.5, 4.5], head: "open", ja: "証明で参照", sub: "中心を道具に使う証明" },
  };

  const CONE = {
    dep: { wash: "#6366F1", ja: "↑ 依存", sub: "中心が証明で使うもの" },
    ref: { wash: "#0D9488", ja: "↓ 参照", sub: "中心を使っている側" },
  };

  const KIND_DOT = {
    axiom: "#EA580C", theorem: "#6366F1", def: "#0D9488",
    inductive: "#CA8A04", constructor: "#CA8A04", recursor: "#DB2777",
    opaque: "#78716C", quot: "#78716C", external: "#A8A29E", unknown: "#A8A29E",
  };

  let p, host, anim = {}, fitK = 1, hitBoxes = [], lastClick = 0, lastClickName = null;
  let drag = null;
  let legendRect = { x: 0, y: 0, w: 0, h: 0 };   // 凡例の矩形（画面座標）。指しているときだけ全体を出す

  const isDark = () => document.documentElement.classList.contains("dark");
  const pal = () => (isDark() ? PAL.dark : PAL.light);
  const edgeStyle = (cone, kind) => EDGE[cone + "|" + kind] || EDGE["dep|type"];
  const edgeCol = (st) => (isDark() ? st.d : st.l);
  const polar = (r, th) => ({ x: r * Math.cos(th), y: r * Math.sin(th) });

  /** 同じ辺には毎回同じ向きの膨らみを与える。フレームごとに揺れると読めない。 */
  function hash01(s) {
    let h = 2166136261;
    for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); }
    return ((h >>> 0) % 1000) / 1000;
  }

  /** 部分グラフの色。名前から決めるので、展開しても中心を移しても同じ群は同じ色。
      錐そのものの色（藍・青緑・橙）と衝突しない帯域へ寄せてある。 */
  function hueOf(s) {
    return Math.round(hash01("g:" + s) * 300 + 200) % 360;
  }
  const shortLabel = (n) => {
    const p = String(n || "").split(".");
    return p[p.length - 1] || String(n || "");
  };

  function nodeStyle(name, st, dv) {
    const nd = st.nodes[name];
    const c = pal();
    if (nd && nd.usesSorry) return { bg: c.sorryBg, bd: c.sorryBd, tx: c.sorryTx, pill: false };
    if (dv.minimalSet && dv.minimalSet.has(name)) return { bg: c.minBg, bd: c.minBd, tx: c.minTx, pill: true };
    return { bg: c.nodeBg, bd: c.nodeBd, tx: c.nodeTx, pill: false };
  }

  function fitScale(dv, w, h) {
    const b = dv.bbox || { x0: -300, x1: 300, y0: -200, y1: 200 };
    const cw = Math.max(b.x1 - b.x0, 1), ch = Math.max(b.y1 - b.y0, 1);
    return Math.max(0.1, Math.min(1.1, Math.min((w - 56) / cw, (h - 64) / ch)));
  }

  function worldOf(mx, my, st, w, h) {
    const k = st.view.k == null ? fitK : st.view.k;
    return { x: (mx - w / 2 - st.view.tx) / k, y: (my - h / 2 - st.view.ty) / k };
  }

  function lerpAngle(a, b, t) {
    let d = b - a;
    while (d > Math.PI) d -= 2 * Math.PI;
    while (d < -Math.PI) d += 2 * Math.PI;
    return a + d * t;
  }

  function sketch(pp) {
    p = pp;

    pp.setup = function () {
      const r = host.getBoundingClientRect();
      const cv = pp.createCanvas(r.width, r.height);
      cv.parent(host);
      pp.pixelDensity(Math.min(2, window.devicePixelRatio || 1));
      pp.textFont("ui-monospace, SFMono-Regular, Menlo, monospace");
      pp.frameRate(60);
    };

    pp.windowResized = function () {
      const r = host.getBoundingClientRect();
      pp.resizeCanvas(r.width, r.height);
    };

    pp.draw = function () {
      const st = S.state, dv = S.derived, c = pal();
      pp.clear();
      pp.background(c.bg);
      if (!dv.posAll || !dv.center) { pp.noLoop(); return; }   // 描くものが無いときも眠る

      const W = pp.width, H = pp.height;
      fitK = fitScale(dv, W, H);
      const k = st.view.k == null ? fitK : st.view.k;

      /* 目標位置へ極座標のまま補間する。x,y で補間すると、角度が変わったとき
         ノードが中心を横切って直線的に飛び、どの扇から来たのか分からなくなる。
         残差 animDelta は「もう動いていないか」の判定に使う(静止時は描画を止める)。 */
      let animDelta = 0;
      const live = {};
      for (const [n, t] of Object.entries(dv.posAll)) {
        let a = anim[n];
        if (!a) a = anim[n] = { r: t.r * 0.6, th: t.th, o: 0 };
        animDelta = Math.max(animDelta,
          Math.abs(t.r - a.r),
          Math.abs(t.th - a.th) * (a.r + 60),
          60 * (1 - a.o));
        a.r += (t.r - a.r) * 0.24;
        a.th = lerpAngle(a.th, t.th, 0.24);
        a.o += (1 - a.o) * 0.2;
        const q = polar(a.r, a.th);
        live[n] = { x: q.x, y: q.y, r: a.r, th: a.th, o: a.o, w: t.w, cone: t.cone, level: t.level };
      }
      for (const n of Object.keys(anim)) if (!(n in dv.posAll)) delete anim[n];

      const hl = dv.highlight, hov = st.hovered, cen = dv.center;
      const path = dv.pathSet;      // 選んだノードから中心までの経路
      const NH = S.NODE_H;

      pp.push();
      pp.translate(W / 2 + st.view.tx, H / 2 + st.view.ty);
      pp.scale(k);

      /* ---- 扇と層の輪郭 ---- */
      for (const cone of dv.cones) {
        if (!cone.rings.length) continue;
        const col = CONE[cone.id] || CONE.dep;
        pp.drawingContext.globalAlpha = 0.04;
        pp.noStroke(); pp.fill(col.wash);
        pp.arc(0, 0, (cone.rMax + 190) * 2, (cone.rMax + 190) * 2, cone.th0, cone.th1, pp.PIE);
        pp.drawingContext.globalAlpha = 1;

        /* 部分グラフの帯。同じ主題・名前空間・種別のノードが弧の上で連続するよう
           並べてあるので、その区間を環状の帯として描くだけで囲いになる。
           色相は群の名前から決めるので、再描画でも中心を移しても同じ群は同じ色。 */
        const NH2 = S.NODE_H / 2 + 7;
        for (const ring of cone.rings) {
          for (const run of ring.runs || []) {
            if (run.n < 2 && (ring.runs || []).length < 2) continue;
            const hue = hueOf(run.group);
            pp.noFill();
            pp.stroke(`hsla(${hue}, 62%, ${isDark() ? 62 : 42}%, 0.30)`);
            pp.strokeWeight(1.2 / k);
            pp.arc(0, 0, (ring.r - NH2) * 2, (ring.r - NH2) * 2, run.th0, run.th1);
            pp.arc(0, 0, (ring.r + NH2) * 2, (ring.r + NH2) * 2, run.th0, run.th1);
            for (const th of [run.th0, run.th1]) {
              const p1 = polar(ring.r - NH2, th), p2 = polar(ring.r + NH2, th);
              pp.line(p1.x, p1.y, p2.x, p2.y);
            }
            pp.drawingContext.globalAlpha = 0.07;
            pp.noStroke(); pp.fill(`hsl(${hue}, 62%, 50%)`);
            pp.arc(0, 0, (ring.r + NH2) * 2, (ring.r + NH2) * 2, run.th0, run.th1, pp.PIE);
            pp.drawingContext.globalAlpha = 1;
            // 群の名前は帯が十分広いときだけ。狭いところに置いても読めない。
            if ((run.th1 - run.th0) * ring.r > 150) {
              const q = polar(ring.r + NH2 + 11, (run.th0 + run.th1) / 2);
              pp.noStroke(); pp.fill(`hsl(${hue}, 45%, ${isDark() ? 70 : 38}%)`);
              pp.textSize(10.5 / k); pp.textAlign(pp.CENTER, pp.CENTER);
              pp.text(shortLabel(run.group), q.x, q.y);
            }
          }
        }

        pp.noFill(); pp.strokeWeight(1 / k);
        for (const ring of cone.rings) {
          pp.stroke(hov && dv.posAll[hov] && dv.posAll[hov].cone === cone.id
            && dv.posAll[hov].level === ring.level ? c.ringHot : c.ring);
          pp.arc(0, 0, ring.r * 2, ring.r * 2, cone.th0, cone.th1);
        }
        pp.noStroke(); pp.fill(c.muted); pp.textSize(10.5 / k);
        pp.textAlign(pp.CENTER, pp.CENTER);
        for (const ring of cone.rings) {
          const q = polar(ring.r, cone.th1 + 26 / (ring.r * k));
          const extra = cone.overflow[ring.level] ? ` +${cone.overflow[ring.level]}` : "";
          pp.text(`ℓ${ring.level}${extra}`, q.x, q.y);
        }
      }

      /* ---- 辺 ---- */
      for (const e of dv.edges) {
        const A = e.u === cen ? { r: 0, th: 0, level: 0 } : live[e.u];
        const B = live[e.v];
        if (!A || !B) continue;
        const dim = (hl && !(hl.has(e.u) && hl.has(e.v)));
        const trace = hl && !dim;
        const onPath = path && path.has(e.u) && path.has(e.v);
        const hot = (hov && (e.u === hov || e.v === hov)) || onPath;
        const style = edgeStyle(e.cone, e.kind);

        const thA = e.u === cen ? B.th : A.th;
        const rA = e.u === cen ? NH * 1.05 : A.r + NH / 2;

        /* 非外向きの辺(巡回フォールバック等で ℓ が増えない)。半径クランプの
           ベジエで描くと終点が実位置から遊離し、矢じりが空中を指す(監査で発見)。
           実座標間の直線で正直に描き、矢じりも実方向へ向ける。 */
        if (B.r - NH / 2 < rA + 6) {
          const ax = e.u === cen ? 0 : A.x, ay = e.u === cen ? 0 : A.y;
          const dx = B.x - ax, dy = B.y - ay, L = Math.hypot(dx, dy) || 1;
          const t0 = Math.min(0.45, (NH / 2 + 4) / L);
          const t1 = Math.max(t0 + 0.1, 1 - (NH / 2 + 4) / L);
          pp.noFill();
          pp.stroke(trace ? c.trace : edgeCol(style));
          pp.strokeWeight((hot || trace ? 2.3 : 1.25) / k);
          pp.drawingContext.globalAlpha = dim ? c.dim : (hot || trace ? 1 : 0.5);
          if (style.dash) pp.drawingContext.setLineDash(style.dash.map((v2) => v2 / k));
          pp.line(ax + dx * t0, ay + dy * t0, ax + dx * t1, ay + dy * t1);
          pp.drawingContext.setLineDash([]);
          const ang = Math.atan2(dy, dx);
          pp.push(); pp.translate(ax + dx * t1, ay + dy * t1); pp.rotate(ang - Math.PI / 2);
          if (style.head === "solid") {
            pp.noStroke(); pp.fill(trace ? c.trace : edgeCol(style));
            pp.triangle(0, 1.5 / k, -3.6 / k, -6.2 / k, 3.6 / k, -6.2 / k);
          } else {
            pp.noFill(); pp.stroke(trace ? c.trace : edgeCol(style));
            pp.strokeWeight(1.9 / k);
            pp.line(-3.8 / k, -6.6 / k, 0, 0.6 / k);
            pp.line(3.8 / k, -6.6 / k, 0, 0.6 / k);
          }
          pp.pop();
          if (e.via && e.via.length && !dim) drawViaLabel(pp, c, ax + dx * (t0 + t1) / 2, ay + dy * (t0 + t1) / 2, viaText(st, e.via), k);
          pp.drawingContext.globalAlpha = 1;
          continue;
        }

        const rB = Math.max(B.r - NH / 2, rA + 6);
        const rM = (rA + rB) / 2;

        /* 層を跨ぐ辺は角度方向へ逃がす。まっすぐだと中間層のノードを貫く。 */
        const gap = Math.abs((B.level || 0) - (A.level || 0));
        let bow = 0;
        if (gap >= 2) {
          const amp = 0.08 + 0.035 * Math.min(gap, 4);
          bow = (hash01(e.u + e.v) < 0.5 ? -1 : 1) * amp;
        }

        const P0 = polar(rA, thA), P3 = polar(rB, B.th);
        const C1 = polar(rM, thA + bow), C2 = polar(rM, B.th + bow);

        pp.noFill();
        pp.stroke(trace ? c.trace : edgeCol(style));
        pp.strokeWeight((hot || trace ? 2.3 : 1.25) / k);
        pp.drawingContext.globalAlpha = dim ? c.dim : (hot || trace ? 1 : 0.5);
        if (style.dash) pp.drawingContext.setLineDash(style.dash.map((v) => v / k));
        pp.bezier(P0.x, P0.y, C1.x, C1.y, C2.x, C2.y, P3.x, P3.y);
        pp.drawingContext.setLineDash([]);

        // 矢じり。実線は塗り三角、点線は開いた山形。形でも区別できるようにする。
        pp.push(); pp.translate(P3.x, P3.y); pp.rotate(B.th - Math.PI / 2);
        if (style.head === "solid") {
          pp.noStroke(); pp.fill(trace ? c.trace : edgeCol(style));
          pp.triangle(0, 1.5 / k, -3.6 / k, -6.2 / k, 3.6 / k, -6.2 / k);
        } else {
          pp.noFill(); pp.stroke(trace ? c.trace : edgeCol(style));
          pp.strokeWeight(1.9 / k);
          pp.line(-3.8 / k, -6.6 / k, 0, 0.6 / k);
          pp.line(3.8 / k, -6.6 / k, 0, 0.6 / k);
        }
        pp.pop();
        if (e.via && e.via.length && !dim) {
          const q = polar(rB - 22 / Math.max(k, 0.4), B.th);
          drawViaLabel(pp, c, q.x, q.y, viaText(st, e.via), k);
        }
        pp.drawingContext.globalAlpha = 1;
      }

      /* ---- ノード ---- */
      hitBoxes = [];
      for (const [n, a] of Object.entries(live)) {
        if (n === cen) continue;
        const stl = nodeStyle(n, st, dv);
        const dim = hl && !hl.has(n);
        const isHov = hov === n, isSel = st.selected === n;
        const w = a.w, h = NH;
        pp.drawingContext.globalAlpha = (dim ? c.dim : 1) * a.o;

        const onPath = path && path.has(n);
        const nd = st.nodes[n];
        /* 外部の宣言（対象の外で定義されたもの）とモジュール粒度の節点は、縁をパッケージの色に
           する（Mathlib / cslib / core …。pkg.colorOf）。どのパッケージに依っているかが
           図の上で読める。対象のパッケージの節点は既定の縁のまま。 */
        const pkgC = pkgColorOf(n, nd, st);
        pp.fill(stl.bg);
        pp.stroke(isSel ? c.center : onPath ? CONE[a.cone].wash : isHov ? CONE[a.cone].wash : (pkgC || stl.bd));
        pp.strokeWeight((isSel ? 2.4 : onPath ? 2.2 : isHov ? 2 : pkgC ? 1.6 : 1.1) / k);
        pp.rect(a.x - w / 2, a.y - h / 2, w, h, stl.pill ? h / 2 : 9);

        const dotC = KIND_DOT[st.granularity === "module" ? "unknown" : (nd ? nd.kind : "unknown")] || KIND_DOT.unknown;
        /* 派生の札。畳んでいれば「+k」（k = この中心から見える派生の数。facetReach）、
           開いていれば「−n」（n = 由来の派生の総数）。押すと開閉（一覧の小枝と同じ状態）。 */
        const fc = st.granularity === "decl" && dv.facetCount ? (dv.facetCount[n] || 0) : 0;
        const badgeW = fc ? 24 : 0;
        pp.noStroke(); pp.fill(dotC);
        if (w < 78) {
          pp.circle(a.x, a.y, 9);
        } else {
          pp.circle(a.x - w / 2 + 14, a.y, 8);
          pp.fill(stl.tx); pp.textSize(13);
          pp.textAlign(pp.LEFT, pp.CENTER);
          pp.text(fit(pp, (dv.labels && dv.labels[n]) || n, w - 32 - badgeW), a.x - w / 2 + 24, a.y + 0.5);
        }

        // 展開バッジは半径方向の外側。ノード幅が細っても必ず押せる。
        const more = dv.more && dv.more[n];
        const isExp = st.expanded.has(n);
        if (more || isExp) {
          const q = polar(a.r + h / 2 + 12, a.th);
          pp.fill(c.badgeBg); pp.stroke(stl.bd); pp.strokeWeight(1 / k);
          const bw = isExp ? 24 : 16 + String(more).length * 7;
          pp.rect(q.x - bw / 2, q.y - 9.5, bw, 19, 9.5);
          pp.noStroke(); pp.fill(c.badgeTx); pp.textSize(11);
          pp.textAlign(pp.CENTER, pp.CENTER);
          pp.text(isExp ? "－" : "+" + more, q.x, q.y + 0.5);
          hitBoxes.push({ kind: "expand", name: n, x: q.x - bw / 2, y: q.y - 9.5, w: bw, h: 19 });
        }
        hitBoxes.push({ kind: "node", name: n, x: a.x - w / 2, y: a.y - h / 2, w, h });
        /* 派生の札はノードの矩形の内側にあるので、当たり判定はノードの後に積む
           （後から積んだものが優先。先に積むと押してもノードの選択になる。実障害）。 */
        if (fc) drawClusterBadge(pp, c, dv, n, fc, a.x + w / 2 - 27, a.y - 8, stl.bd, k, (dim ? c.dim : 1) * a.o);
        pp.drawingContext.globalAlpha = 1;
      }

      /* ---- 中心 ---- */
      const cw = S.NODE_W + 30, ch = NH + 12;
      pp.noFill(); pp.stroke(c.centerRing); pp.strokeWeight(1.6 / k);
      pp.circle(0, 0, S.GEO.r0 * 0.62);
      pp.fill(c.center); pp.stroke(c.center); pp.strokeWeight(1 / k);
      pp.rect(-cw / 2, -ch / 2, cw, ch, 11);
      const cfc = st.granularity === "decl" && dv.facetCount ? (dv.facetCount[cen] || 0) : 0;
      pp.noStroke(); pp.fill(c.centerTx); pp.textSize(14.5);
      pp.textAlign(pp.CENTER, pp.CENTER);
      pp.text(fit(pp, (dv.labels && dv.labels[cen]) || cen, cw - 18 - (cfc ? 26 : 0)), cfc ? -13 : 0, 0.5);
      hitBoxes.push({ kind: "node", name: cen, x: -cw / 2, y: -ch / 2, w: cw, h: ch });
      if (cfc) drawClusterBadge(pp, c, dv, cen, cfc, cw / 2 - 29, -8, c.centerRing, k, 1);

      pp.pop();

      drawLegend(pp, c, dv, st, W, H);
      drawHoverCard(pp, c, dv, st, W, H);
      maybeSleep(animDelta);
    };

    /* 静止したら描画ループを止める。常時 60fps の再描画は、静止した図に対して
       純粋な CPU/バッテリーの浪費になる。入力(マウス)と状態変化(subscribe)で
       再開するので、見た目の応答は変わらない。 */
    function maybeSleep(animDelta) {
      if (animDelta < 0.5 && !drag) pp.noLoop();
    }

    /* 派生の札。記号は展開バッジ（ノードの外の `+n`: 深さの先に隠れている依存の数）と
       取り違えないよう、菱形にする（同じ `+n` が二種あると区別できない。実測）。
         ◇k   畳んでいる。k はこの中心から見える派生の数（開けば現れる）。0 なら薄く描く
              （開いても図は変わらない。一覧では由来の下に全て出る）。
         ◆n   開いている。n は由来の派生の総数。
         ◆n（藍） 強制的に開いている（中心が派生／経路表示の区間に派生）。押しても閉じない。
       押すと開閉（一覧の小枝と同じ状態）。 */
    function drawClusterBadge(pp, c, dv, name, fc, x, y, bd, k, alpha) {
      const open = S.isClusterOpen(name), forced = S.isClusterForced(name);
      const reach = dv.facetReach ? (dv.facetReach[name] || 0) : fc;
      const bw = 24, bh = 16;
      const faint = !open && reach === 0;
      pp.drawingContext.globalAlpha = alpha * (faint ? 0.45 : 1);
      pp.fill(c.badgeBg); pp.stroke(forced ? c.center : bd); pp.strokeWeight((forced ? 1.4 : 1) / k);
      pp.rect(x, y, bw, bh, 8);
      pp.noStroke(); pp.fill(forced ? c.center : c.badgeTx); pp.textSize(10);
      pp.textAlign(pp.CENTER, pp.CENTER);
      pp.text((open ? "◆" : "◇") + (open ? fc : reach), x + bw / 2, y + bh / 2 + 0.5);
      pp.drawingContext.globalAlpha = alpha;
      hitBoxes.push({ kind: "cluster", name, x, y, w: bw, h: bh });
    }

    /* パッケージの縁の色。対象のパッケージ（レポートの対象モジュールのもの）は無色。 */
    function pkgColorOf(n, nd, st) {
      const P = LDR.pkg;
      if (!P) return null;
      if (st.granularity === "module") {
        const p = P.packageOf(n);
        return p && p !== targetPackage(st) ? P.colorOf(p) : null;
      }
      if (!nd || !nd.external) return null;
      const p = P.packageOf(nd.module);
      return p && p !== targetPackage(st) ? P.colorOf(p) : null;
    }

    /* 辺が畳まれた派生・断片を経由しているとき、その種類（単射性・場合分け…）を辺の
       終点の手前に小さく書く。「pair_inj は mk を使う」ではなく「mk の単射性を使う」と読める。 */
    function viaText(st, via) {
      const K = LDR.sig.ORIGIN_KIND;
      const kinds = [...new Set(via.map((g) => {
        const nd = st.nodes[g];
        return nd && K[nd.originKind] ? K[nd.originKind].ja : "経由";
      }))];
      return kinds.join("·") + (via.length > kinds.length ? ` ×${via.length}` : "");
    }
    function drawViaLabel(pp, c, x, y, text, k) {
      pp.textSize(9.5 / k);
      const w = pp.textWidth(text) + 8 / k, h = 13 / k;
      pp.noStroke(); pp.fill(c.panel);
      pp.rect(x - w / 2, y - h / 2, w, h, 4 / k);
      pp.fill(c.faint); pp.textAlign(pp.CENTER, pp.CENTER);
      pp.text(text, x, y + 0.5 / k);
    }

    /* ホバーした宣言の中身を、その場で読めるようにする。
       密な層ではノードが細くなって名前が入りきらない。押さないと分からない、
       という状態を作らないために、指した瞬間に全属性を出す。 */
    function drawHoverCard(pp, c, dv, st, W, H) {
      const n = st.hovered;
      if (!n) return;
      const nd = st.nodes[n];
      if (!nd) return;
      const S2 = LDR.sig;
      const idx = dv.declIdx || {};
      const lines = [];
      lines.push({ t: n, s: 12.5, col: c.nodeTx, mono: true });
      const sub = [];
      sub.push(((LDR.panels && LDR.panels.kinfo(nd.kind)) || {}).ja || nd.kind);
      if (nd.module) sub.push(shortLabel(nd.module) + (nd.line ? ":" + nd.line : ""));
      if (nd.isInstance) sub.push("instance");
      if (nd.reducibility === "reducible") sub.push("reducible");
      if (nd.isProp && nd.shape && S2.SHAPE[nd.shape]) sub.push(S2.SHAPE[nd.shape].ja);   // 形は命題にだけ
      sub.push(nd.numHyp || nd.numInst ? `条件 ${(nd.numHyp || 0) + (nd.numInst || 0)}` : "無条件");
      lines.push({ t: sub.join(" · "), s: 11, col: c.muted });
      lines.push({
        t: `依存 型${(nd.typeDeps || []).length} / 値${(nd.valueDeps || []).length}`
         + `   参照 主張${(idx.refType && idx.refType[n] || []).length} / 証明${(idx.refValue && idx.refValue[n] || []).length}`
         + `   節点 型${nd.typeSize || 0}/証明${nd.valueSize || 0}`,
        s: 11, col: c.muted,
      });
      if (nd.subject) lines.push({ t: "主題 " + S2.shortName(nd.subject), s: 11, col: c.faint, mono: true });
      /* 由来。派生・断片なら「X の派生: 単射性」、由来を持つ側なら派生・断片の数。
         経由: この節点に触れる辺が畳まれた派生を通っていれば、何を使ったかを列挙する。 */
      const OK = S2.ORIGIN_KIND, OR = S2.ORIGIN_REL;
      if (nd.originRel && nd.origin) {
        lines.push({ t: `${S2.shortName(nd.origin)} の${(OR[nd.originRel] || {}).ja || nd.originRel}: ${(OK[nd.originKind] || {}).ja || nd.originKind}`, s: 11, col: c.faint });
      }
      const fc = dv.facetCount ? dv.facetCount[n] : 0, pc = dv.partCount ? dv.partCount[n] : 0;
      if (fc || pc) {
        const reach = dv.facetReach ? (dv.facetReach[n] || 0) : fc;
        const how = S.isClusterForced(n) ? "固定で開いている（中心または経路の由来）"
                  : S.isClusterOpen(n) ? "開いている。◆ で畳む"
                  : reach ? `畳んでいる。この中心から見えるのは ${reach} 件、◇${reach} で開く`
                  : "畳んでいる。この中心の依存・参照の経路上には無い（一覧の由来の行で見る）";
        lines.push({ t: (fc ? `派生 ${fc}（${how}）` : "") + (fc && pc ? "  " : "") + (pc ? `断片 ${pc}` : ""), s: 11, col: c.muted });
      }
      if (LDR.pkg && nd.external) {
        const p = LDR.pkg.packageOf(nd.module);
        if (p) lines.push({ t: `パッケージ ${LDR.pkg.labelOf(p)}（${nd.module}）`, s: 11, col: LDR.pkg.colorOf(p) });
      }
      const vias = [];
      for (const e of dv.edges || []) {
        if (!e.via || (e.u !== n && e.v !== n)) continue;
        for (const g of e.via) vias.push(`${S2.shortName(g)}（${(OK[(st.nodes[g] || {}).originKind] || {}).ja || "経由"}）`);
      }
      if (vias.length) lines.push({ t: "経由 " + [...new Set(vias)].slice(0, 4).join(", ") + (vias.length > 4 ? " …" : ""), s: 11, col: c.faint });

      const concl = S2.abbrev(nd.conclusion || nd.typeString || "");
      const w = 430, padX = 11, padY = 9;
      pp.textSize(11.5);
      const wrapH = concl ? Math.min(58, Math.ceil(pp.textWidth(concl) / (w - padX * 2)) * 15 + 4) : 0;
      const h = padY * 2 + lines.length * 17 + (wrapH ? wrapH + 6 : 0);

      let x = pp.mouseX + 18, y = pp.mouseY + 18;
      if (x + w > W - 8) x = pp.mouseX - w - 18;
      if (y + h > H - 8) y = Math.max(8, pp.mouseY - h - 18);

      pp.noStroke(); pp.fill(c.panel);
      pp.rect(x, y, w, h, 10);
      pp.noFill(); pp.stroke(c.panelBd); pp.strokeWeight(1);
      pp.rect(x, y, w, h, 10);

      pp.noStroke(); pp.textAlign(pp.LEFT, pp.TOP);
      let yy = y + padY;
      for (const l of lines) {
        pp.fill(l.col); pp.textSize(l.s);
        pp.text(fit(pp, l.t, w - padX * 2), x + padX, yy);
        yy += 17;
      }
      if (concl) {
        pp.stroke(c.panelBd); pp.strokeWeight(1);
        pp.line(x + padX, yy + 1, x + w - padX, yy + 1);
        pp.noStroke(); pp.fill(c.nodeTx); pp.textSize(11.5);
        pp.text(concl, x + padX, yy + 6, w - padX * 2, wrapH);
      }
      pp.textAlign(pp.LEFT, pp.CENTER);
    }

    /* 画面固定の凡例。四種類の辺を実物と同じ描き方で並べる。
       別の場所に文字だけで書いても、線を見比べられないと区別に使えない。 */
    function drawLegend(pp, c, dv, st, W, H) {
      const rows = [];
      const has = new Set(dv.edges.map((e) => e.cone + "|" + e.kind));
      for (const key of ["dep|type", "dep|value", "ref|type", "ref|value"]) {
        rows.push({ key, st: EDGE[key], on: has.has(key) });
      }
      /* 描かれている節点のパッケージ（対象のパッケージ以外）。縁の色の凡例。 */
      const pkgs = new Map();
      if (LDR.pkg) {
        for (const n of Object.keys(dv.posAll || {})) {
          const nd = st.nodes[n];
          const col = pkgColorOf(n, nd, st);
          if (!col) continue;
          const p = LDR.pkg.packageOf(st.granularity === "module" ? n : nd.module);
          pkgs.set(p, (pkgs.get(p) || 0) + 1);
        }
      }

      /* 凡例は既定では一行に畳み、指したときだけ全体を出す。開いたままの 268px × 150px の箱は
         左上の節点を隠していた（実測）。狭い画面でも同じ一行で足りる。 */
      const pkgRows = [...pkgs.entries()].sort((a, b) => b[1] - a[1]);
      const compactW = 4 + rows.length * 30 + 150 + (pkgRows.length ? 14 * pkgRows.length + 70 : 0);
      const hovering = pp.mouseX >= legendRect.x && pp.mouseX <= legendRect.x + legendRect.w
                    && pp.mouseY >= legendRect.y && pp.mouseY <= legendRect.y + legendRect.h;
      if (W < 760 || !hovering) {
        const y0 = 14, x0 = 12;
        pp.noStroke(); pp.fill(c.panel);
        pp.rect(x0, y0 - 4, compactW, 22, 8);
        rows.forEach((r, i) => {
          const xx = x0 + 8 + i * 30;
          pp.drawingContext.globalAlpha = r.on ? 1 : 0.28;
          pp.stroke(edgeCol(r.st)); pp.strokeWeight(2.2);
          if (r.st.dash) pp.drawingContext.setLineDash(r.st.dash);
          pp.line(xx, y0 + 7, xx + 18, y0 + 7);
          pp.drawingContext.setLineDash([]);
          pp.drawingContext.globalAlpha = 1;
        });
        pp.noStroke(); pp.fill(c.muted); pp.textSize(9.5);
        pp.textAlign(pp.LEFT, pp.CENTER);
        let tx = x0 + 12 + rows.length * 30;
        pp.text("型 / 値 / 主張 / 証明", tx, y0 + 7);
        tx += 108;
        if (pkgRows.length) {
          pp.text("縁:", tx, y0 + 7); tx += 20;
          for (const [p] of pkgRows) {
            pp.noFill(); pp.stroke(LDR.pkg.colorOf(p)); pp.strokeWeight(1.6);
            pp.rect(tx, y0 + 2, 10, 10, 3);
            tx += 14;
          }
          pp.noStroke(); pp.fill(c.muted);
          pp.text("パッケージ", tx + 4, y0 + 7); tx += 50;
        }
        pp.fill(c.muted); pp.text("▸ 指すと展開", tx + 6, y0 + 7);
        legendRect = { x: x0, y: y0 - 4, w: compactW, h: 22 };
        return;
      }

      const padX = 11, padY = 9, lh = 19, sample = 34, boxW = 268;
      const boxH = padY * 2 + lh * rows.length + 20 + (pkgRows.length ? 16 + 17 * Math.ceil(pkgRows.length / 2) : 0);
      const x = 12, y = 12;
      legendRect = { x, y, w: boxW, h: boxH };

      pp.noStroke(); pp.fill(c.panel);
      pp.rect(x, y, boxW, boxH, 10);
      pp.stroke(c.panelBd); pp.strokeWeight(1); pp.noFill();
      pp.rect(x, y, boxW, boxH, 10);

      pp.noStroke(); pp.fill(c.muted); pp.textSize(11);
      pp.textAlign(pp.LEFT, pp.TOP);
      pp.text("辺の種類（矢印は中心から外へ）", x + padX, y + padY);

      rows.forEach((r, i) => {
        const yy = y + padY + 20 + i * lh + lh / 2;
        const x0 = x + padX, x1 = x0 + sample;
        pp.drawingContext.globalAlpha = r.on ? 1 : 0.3;
        pp.stroke(edgeCol(r.st)); pp.strokeWeight(1.9);
        if (r.st.dash) pp.drawingContext.setLineDash(r.st.dash);
        pp.line(x0, yy, x1 - 7, yy);
        pp.drawingContext.setLineDash([]);
        if (r.st.head === "solid") {
          pp.noStroke(); pp.fill(edgeCol(r.st));
          pp.triangle(x1 + 1, yy, x1 - 7, yy - 4.2, x1 - 7, yy + 4.2);
        } else {
          pp.noFill(); pp.stroke(edgeCol(r.st)); pp.strokeWeight(1.9);
          pp.line(x1 - 7, yy - 4.6, x1 + 1, yy);
          pp.line(x1 - 7, yy + 4.6, x1 + 1, yy);
        }
        pp.noStroke(); pp.fill(c.faint); pp.textSize(11.5);
        pp.textAlign(pp.LEFT, pp.CENTER);
        pp.text(r.st.ja, x1 + 10, yy);
        pp.fill(c.muted); pp.textSize(10.5);
        pp.text(r.st.sub, x1 + 74, yy);
        pp.drawingContext.globalAlpha = 1;
      });

      /* 縁の色 = パッケージ（対象の外から来た宣言）。二列に並べる。 */
      if (pkgRows.length) {
        const y0 = y + padY + 20 + rows.length * lh + 4;
        pp.noStroke(); pp.fill(c.muted); pp.textSize(10.5);
        pp.textAlign(pp.LEFT, pp.CENTER);
        pp.text("縁の色 = パッケージ（対象の外）", x + padX, y0 + 6);
        pkgRows.forEach(([p, n], i) => {
          const col = i % 2, row = Math.floor(i / 2);
          const xx = x + padX + col * 124, yy = y0 + 22 + row * 17;
          pp.noFill(); pp.stroke(LDR.pkg.colorOf(p)); pp.strokeWeight(1.8);
          pp.rect(xx, yy - 5, 14, 10, 3);
          pp.noStroke(); pp.fill(c.faint); pp.textSize(11);
          pp.text(`${LDR.pkg.labelOf(p)} ${n}`, xx + 20, yy);
        });
      }

      /* 錐の見出しは上下の端に置く。どちら側が何なのかを常に示す。 */
      pp.textSize(12);
      for (const cone of dv.cones) {
        if (!cone.rings.length) continue;
        const col = CONE[cone.id];
        const top = cone.id === "dep";
        pp.noStroke(); pp.fill(col.wash);
        pp.circle(W - 16, top ? 20 : H - 20, 9);
        pp.fill(c.faint);
        pp.textAlign(pp.RIGHT, pp.CENTER);
        pp.text(`${col.ja}  ${col.sub}`, W - 28, top ? 20 : H - 20);
      }
      pp.textAlign(pp.LEFT, pp.CENTER);
    }

    pp.mouseMoved = function () {
      pp.loop();          // 眠っていたら起こす(ホバーカードの追従にも必要)
      const st = S.state;
      const w = worldOf(pp.mouseX, pp.mouseY, st, pp.width, pp.height);
      const h = pick(w.x, w.y);
      S.actions.hover(h && h.kind === "node" ? h.name : null);
      host.style.cursor = h ? "pointer" : (drag ? "grabbing" : "grab");
    };

    pp.mousePressed = function () {
      pp.loop();
      /* 副ボタンは履歴移動に使うので、左ボタンのみ扱う。
         p5 1.x の mouseButton は "left" 等の文字列、2.x は {left,right,center} の
         オブジェクト(破壊的変更)。旧比較は 2.x で常に偽になり、ドラッグと
         クリックが全滅する(実障害として発生)。両版対応で判定する。 */
      const mb = pp.mouseButton;
      const isLeft = (mb !== null && typeof mb === "object") ? !!mb.left : mb === pp.LEFT;
      if (!isLeft) return;
      if (pp.mouseX < 0 || pp.mouseY < 0 || pp.mouseX > pp.width || pp.mouseY > pp.height) return;
      drag = { x: pp.mouseX, y: pp.mouseY, tx: S.state.view.tx, ty: S.state.view.ty, moved: false };
    };

    pp.mouseDragged = function () {
      pp.loop();
      if (!drag) return;
      const dx = pp.mouseX - drag.x, dy = pp.mouseY - drag.y;
      if (Math.abs(dx) + Math.abs(dy) > 3) drag.moved = true;
      S.actions.setView({ ...S.state.view, tx: drag.tx + dx, ty: drag.ty + dy });
    };

    pp.mouseReleased = function () {
      pp.loop();
      if (!drag) return;
      const moved = drag.moved; drag = null;
      if (moved) return;
      if (pp.mouseX < 0 || pp.mouseY < 0 || pp.mouseX > pp.width || pp.mouseY > pp.height) return;
      const st = S.state;
      const w = worldOf(pp.mouseX, pp.mouseY, st, pp.width, pp.height);
      const h = pick(w.x, w.y);
      if (!h) return;
      if (h.kind === "expand") { S.actions.toggleExpand(h.name); return; }
      if (h.kind === "cluster") {
        const r = S.actions.toggleCluster(h.name);
        if (r && !r.ok && r.msg && LDR.toast) LDR.toast(r.msg);   // 固定で開いている由来を押したとき
        return;
      }
      const now = Date.now();
      if (lastClickName === h.name && now - lastClick < 380) {
        S.actions.navigate(h.name);          // ダブルクリック = 中心移動（連鎖的に降りる／登る）
        lastClick = 0; lastClickName = null;
      } else {
        S.actions.select(h.name);            // 単クリック = 選択のみ。履歴は動かない
        lastClick = now; lastClickName = h.name;
      }
    };

    pp.mouseWheel = function (e) {
      pp.loop();
      if (pp.mouseX < 0 || pp.mouseY < 0 || pp.mouseX > pp.width || pp.mouseY > pp.height) return;
      const st = S.state;
      const k0 = st.view.k == null ? fitK : st.view.k;
      const f = e.deltaY > 0 ? 0.92 : 1.08;
      const k1 = Math.min(3, Math.max(0.1, k0 * f));
      const cx = pp.mouseX - pp.width / 2, cy = pp.mouseY - pp.height / 2;
      S.actions.setView({
        tx: cx - (cx - st.view.tx) * (k1 / k0),
        ty: cy - (cy - st.view.ty) * (k1 / k0),
        k: k1,
      });
      if (e.preventDefault) e.preventDefault();     // p5 2.x では return false だけに頼らない
      return false;
    };
  }

  /** 対象のパッケージ（レポートの対象モジュールの先頭成分）。読み込んだデータごとに一度だけ決める。 */
  let tpCache = { nodes: null, pkg: "" };
  function targetPackage(st) {
    if (tpCache.nodes !== st.nodes) {
      const first = st.order[0];
      tpCache = { nodes: st.nodes, pkg: first && st.nodes[first] && LDR.pkg ? LDR.pkg.packageOf(st.nodes[first].module) : "" };
    }
    return tpCache.pkg;
  }

  /** 当たり判定。箱は world 座標で持つ。後から積んだもの（手前）を優先する。 */
  function pick(wx, wy) {
    for (let i = hitBoxes.length - 1; i >= 0; i--) {
      const b = hitBoxes[i];
      if (wx >= b.x && wx <= b.x + b.w && wy >= b.y && wy <= b.y + b.h) return b;
    }
    return null;
  }

  function fit(pp, s, maxW) {
    if (maxW <= 8) return "";
    if (pp.textWidth(s) <= maxW) return s;
    let t = s;
    while (t.length > 1 && pp.textWidth(t + "…") > maxW) t = t.slice(0, -1);
    return t + "…";
  }

  function mount(el) {
    host = el;
    new p5(sketch);
    const ro = new ResizeObserver(() => { if (p) { p.loop(); p.windowResized(); } });
    ro.observe(el);
    // 状態が変わったら描画を再開する(静止時は noLoop で眠っているため)
    S.subscribe(() => { if (p) p.loop(); });
  }

  LDR.canvas = {
    mount, EDGE, CONE,
    hueOf,                                   // 左の一覧の名前空間の色も同じ関数で決める
    targetPackage,                           // 右パネルのパッケージ表示も同じ判定を使う

    zoomIn: () => S.actions.zoomBy(1.18, fitK),
    zoomOut: () => S.actions.zoomBy(1 / 1.18, fitK),
    reset: () => S.actions.resetView(),
    get fitK() { return fitK; },
  };
})(window.LDR = window.LDR || {});
