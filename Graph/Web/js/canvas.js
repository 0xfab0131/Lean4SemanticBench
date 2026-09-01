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
  let drag = null, globeRect = null, globeDrag = null;
  /* 回転は自由に動かせるが、手を離したら最寄りの区画へ寄って止まる。
     途中の角度で止まると、どの区画も半端に傾いたまま読めなくなる。
     phiAnim が実際に描く角度で、state.phi が目標。 */
  let phiAnim = 0, snapTimer = 0;

  const wrapPi = (d) => {
    while (d > Math.PI) d -= 2 * Math.PI;
    while (d < -Math.PI) d += 2 * Math.PI;
    return d;
  };

  function snapToNearest() {
    const dv = S.derived, st = S.state;
    if (!st.view3d || !dv.sectors || !dv.sectors.length) return;
    let best = null, bestAbs = Infinity;
    for (const s of dv.sectors) {
      const d = Math.abs(wrapPi(s.lon - st.phi));
      if (d < bestAbs) { bestAbs = d; best = s; }
    }
    if (best) S.actions.spinTo(best.lon);
  }
  const scheduleSnap = (ms) => {
    clearTimeout(snapTimer);
    snapTimer = setTimeout(snapToNearest, ms);
  };

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
      if (!dv.posAll || !dv.center) return;

      const W = pp.width, H = pp.height;
      fitK = fitScale(dv, W, H);
      const k = st.view.k == null ? fitK : st.view.k;

      /* 目標位置へ極座標のまま補間する。x,y で補間すると、角度が変わったとき
         ノードが中心を横切って直線的に飛び、どの扇から来たのか分からなくなる。 */
      const live = {};
      for (const [n, t] of Object.entries(dv.posAll)) {
        let a = anim[n];
        if (!a) a = anim[n] = { r: t.r * 0.6, th: t.th, o: 0 };
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

      if (st.view3d) {
        // 目標角へ滑らかに寄せる。極小元の経路表示と同じ「押すと落ち着く」感覚に揃える
        phiAnim += wrapPi(st.phi - phiAnim) * 0.16;
        if (Math.abs(wrapPi(st.phi - phiAnim)) < 0.002) phiAnim = st.phi;
        drawSpherical(pp, st, dv, c, W, H, k, live, hl, hov, path, cen, NH);
        drawLegend(pp, c, dv, W, H);
        drawGlobe(pp, c, dv, st, W, H);
        drawHoverCard(pp, c, dv, st, W, H);
        return;
      }

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
        pp.fill(stl.bg);
        pp.stroke(isSel ? c.center : onPath ? CONE[a.cone].wash : isHov ? CONE[a.cone].wash : stl.bd);
        pp.strokeWeight((isSel ? 2.4 : onPath ? 2.2 : isHov ? 2 : 1.1) / k);
        pp.rect(a.x - w / 2, a.y - h / 2, w, h, stl.pill ? h / 2 : 9);

        const nd = st.nodes[n];
        const dotC = KIND_DOT[st.granularity === "module" ? "unknown" : (nd ? nd.kind : "unknown")] || KIND_DOT.unknown;
        pp.noStroke(); pp.fill(dotC);
        if (w < 78) {
          pp.circle(a.x, a.y, 9);
        } else {
          pp.circle(a.x - w / 2 + 14, a.y, 8);
          pp.fill(stl.tx); pp.textSize(13);
          pp.textAlign(pp.LEFT, pp.CENTER);
          pp.text(fit(pp, (dv.labels && dv.labels[n]) || n, w - 32), a.x - w / 2 + 24, a.y + 0.5);
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
        pp.drawingContext.globalAlpha = 1;
      }

      /* ---- 中心 ---- */
      const cw = S.NODE_W + 30, ch = NH + 12;
      pp.noFill(); pp.stroke(c.centerRing); pp.strokeWeight(1.6 / k);
      pp.circle(0, 0, S.GEO.r0 * 0.62);
      pp.fill(c.center); pp.stroke(c.center); pp.strokeWeight(1 / k);
      pp.rect(-cw / 2, -ch / 2, cw, ch, 11);
      pp.noStroke(); pp.fill(c.centerTx); pp.textSize(14.5);
      pp.textAlign(pp.CENTER, pp.CENTER);
      pp.text(fit(pp, (dv.labels && dv.labels[cen]) || cen, cw - 18), 0, 0.5);
      hitBoxes.push({ kind: "node", name: cen, x: -cw / 2, y: -ch / 2, w: cw, h: ch });

      pp.pop();

      drawLegend(pp, c, dv, W, H);
      drawHoverCard(pp, c, dv, st, W, H);
    };

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
      if (nd.shape && S2.SHAPE[nd.shape]) sub.push(S2.SHAPE[nd.shape].ja);
      sub.push(nd.numHyp || nd.numInst ? `条件 ${(nd.numHyp || 0) + (nd.numInst || 0)}` : "無条件");
      lines.push({ t: sub.join(" · "), s: 11, col: c.muted });
      lines.push({
        t: `依存 型${(nd.typeDeps || []).length} / 値${(nd.valueDeps || []).length}`
         + `   参照 主張${(idx.refType && idx.refType[n] || []).length} / 証明${(idx.refValue && idx.refValue[n] || []).length}`
         + `   節点 型${nd.typeSize || 0}/証明${nd.valueSize || 0}`,
        s: 11, col: c.muted,
      });
      if (nd.subject) lines.push({ t: "主題 " + S2.shortName(nd.subject), s: 11, col: c.faint, mono: true });

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

    /* ---------- 球面モード ----------

       部分グラフごとに扇をまるごと与え、経度で切り替える。正面に来た区画だけが
       読める大きさで描かれ、脇へ回った区画は水平に圧縮されて薄くなる。
       一つの扇を全部で共有すると、どれも狭くなって重なる。それを避けるための構造。

       中心は経度に依らず原点に固定する。層を行き来しても現在地を失わないため。 */
    function sectorDepth(s, phi) { return Math.cos(s.lon - phi); }

    /* `path`（選んだノードから中心までの経路）は必ず引数で受け取る。
       draw のローカル変数はここからは見えない。以前これを取りこぼしていて、
       最初の辺を描く時点で ReferenceError になり、球面モードが真っ白になっていた。 */
    function drawSpherical(pp, st, dv, c, W, H, k, live, hl, hov, path, cen, NH) {
      const phi = phiAnim;

      /* 円筒に貼って回す。奥の区画は水平に圧縮するだけでなく、
         sin で **横へ退かせる**。圧縮だけだと全部が中心線に重なって混ざる。
         正面から 65 度より外は描かない。薄く重ねても読めないので、
         そこは地球儀に任せる。 */
      const SLIDE = Math.max(W * 0.86, 460);
      const vis = dv.sectors
        .map((s) => ({ s, dl: wrapPi(s.lon - phi) }))
        .map((x) => Object.assign(x, { d: Math.cos(x.dl) }))
        .filter((x) => x.d > 0.42)
        .sort((a, b) => a.d - b.d);          // 奥から手前へ

      // 正面はただ一つ。閾値で決めると複数が「正面」になり、ラベルが重なる。
      let frontKey = null, best = Infinity;
      for (const x of vis) if (Math.abs(x.dl) < best) { best = Math.abs(x.dl); frontKey = x.s.id; }

      hitBoxes = [];

      /* 薄い方の錐は回さず常に出す。9 件しかない上錐を部分グラフに割ると、
         回すたびに片側が空になるだけで読みにくい。 */
      const groupsToDraw = [];
      for (const part of dv.pinned || []) {
        groupsToDraw.push({ parts: [part], slide: 0, sq: 1, sc: 1, alpha: 1, front: true, hue: null });
      }
      for (const { s, dl, d } of vis) {
        groupsToDraw.push({
          parts: s.parts, slide: Math.sin(dl) * SLIDE,
          sq: Math.max(0.12, d), sc: 0.72 + 0.28 * d,
          alpha: s.id === frontKey ? 1 : Math.pow(d, 2.2) * 0.75,
          front: s.id === frontKey, hue: hueOf(s.key),
        });
      }

      for (const grp of groupsToDraw) {
        const { slide, sq, sc, alpha, front } = grp;
        const hue = grp.hue;

        pp.push();
        pp.translate(W / 2 + st.view.tx + slide, H / 2 + st.view.ty);
        pp.scale(k * sc, k * sc);
        pp.scale(sq, 1);

        for (const part of grp.parts) {
          const col = CONE[part.coneId] || CONE.dep;

          pp.drawingContext.globalAlpha = alpha * 0.06;
          pp.noStroke();
          pp.fill(hue == null ? col.wash : `hsl(${hue},60%,50%)`);
          pp.arc(0, 0, (part.rMax + 190) * 2, (part.rMax + 190) * 2, part.th0, part.th1, pp.PIE);

          pp.drawingContext.globalAlpha = alpha * 0.5;
          pp.noFill(); pp.stroke(c.ring); pp.strokeWeight(1 / (k * sc));
          for (const ring of part.rings) pp.arc(0, 0, ring.r * 2, ring.r * 2, part.th0, part.th1);

          if (front) {
            pp.noStroke(); pp.fill(c.muted); pp.textSize(10.5 / (k * sc));
            pp.textAlign(pp.CENTER, pp.CENTER);
            pp.drawingContext.globalAlpha = 1;
            for (const ring of part.rings) {
              const q = polar(ring.r, part.th1 + 26 / (ring.r * k * sc));
              const extra = part.overflow[ring.level] ? ` +${part.overflow[ring.level]}` : "";
              pp.text(`ℓ${ring.level}${extra}`, q.x, q.y);
            }
          }

          // 辺。経路表示と選択した流れは平面モードと同じ規則で強調する
          for (const e of part.edges) {
            const A = e.u === cen ? { r: 0, th: 0, level: 0 } : part.pos[e.u];
            const B = part.pos[e.v];
            if (!A || !B) continue;
            const style = edgeStyle(e.cone, e.kind);
            const dim = (hl && !(hl.has(e.u) && hl.has(e.v)));
            const trace = hl && !dim;
            const onPath = path && path.has(e.u) && path.has(e.v);
            const hot = (hov && (e.u === hov || e.v === hov)) || onPath;
            const thA = e.u === cen ? B.th : A.th;
            const rA = e.u === cen ? NH * 1.05 : A.r + NH / 2;
            const rB = Math.max(B.r - NH / 2, rA + 6);
            const rM = (rA + rB) / 2;
            const P0 = polar(rA, thA), P3 = polar(rB, B.th);
            const C1 = polar(rM, thA), C2 = polar(rM, B.th);
            pp.noFill();
            pp.stroke(trace ? c.trace : edgeCol(style));
            pp.strokeWeight(((hot || trace) ? 2.2 : front ? 1.25 : 1) / (k * sc));
            pp.drawingContext.globalAlpha = dim ? alpha * c.dim
              : alpha * ((hot || trace) ? 0.95 : front ? 0.5 : 0.3);
            if (style.dash) pp.drawingContext.setLineDash(style.dash.map((v) => v / (k * sc)));
            pp.bezier(P0.x, P0.y, C1.x, C1.y, C2.x, C2.y, P3.x, P3.y);
            pp.drawingContext.setLineDash([]);
          }

          // ノード。正面の区画だけラベルを出し、押せるようにする
          for (const [n, p] of Object.entries(part.pos)) {
            const stl = nodeStyle(n, st, dv);
            const isSel = st.selected === n, isHov = hov === n;
            const onPath = path && path.has(n);
            const dim = hl && !hl.has(n);
            const w = p.w, h = NH;
            pp.drawingContext.globalAlpha = alpha * (dim ? c.dim : 1);
            pp.fill(stl.bg);
            pp.stroke(isSel ? c.center : (onPath || isHov) ? col.wash : stl.bd);
            pp.strokeWeight((isSel ? 2.4 : onPath ? 2.2 : isHov ? 2 : 1.1) / (k * sc));
            pp.rect(p.x - w / 2, p.y - h / 2, w, h, stl.pill ? h / 2 : 9);
            const nd = st.nodes[n];
            pp.noStroke();
            pp.fill(KIND_DOT[(nd && nd.kind) || "unknown"] || KIND_DOT.unknown);
            if (front && w >= 78) {
              pp.circle(p.x - w / 2 + 14, p.y, 8);
              pp.fill(stl.tx); pp.textSize(13);
              pp.textAlign(pp.LEFT, pp.CENTER);
              pp.text(fit(pp, (dv.labels && dv.labels[n]) || n, w - 32), p.x - w / 2 + 24, p.y + 0.5);
            } else {
              pp.circle(p.x, p.y, 9);
            }

            if (!front) continue;
            const toScreen = (wx, wy, ww, hh) => ({
              x: W / 2 + st.view.tx + slide + wx * k * sc * sq - (ww * k * sc * sq) / 2,
              y: H / 2 + st.view.ty + wy * k * sc - (hh * k * sc) / 2,
              w: ww * k * sc * sq, h: hh * k * sc,
            });
            const more = dv.more && dv.more[n];
            const isExp = st.expanded.has(n);
            if (more || isExp) {
              const q = polar(p.r + h / 2 + 12, p.th);
              const bw = isExp ? 24 : 16 + String(more).length * 7;
              pp.fill(c.badgeBg); pp.stroke(stl.bd); pp.strokeWeight(1 / (k * sc));
              pp.rect(q.x - bw / 2, q.y - 9.5, bw, 19, 9.5);
              pp.noStroke(); pp.fill(c.badgeTx); pp.textSize(11);
              pp.textAlign(pp.CENTER, pp.CENTER);
              pp.text(isExp ? "－" : "+" + more, q.x, q.y + 0.5);
              hitBoxes.push(Object.assign({ kind: "expand", name: n, screen: true },
                toScreen(q.x, q.y, bw, 19)));
            }
            hitBoxes.push(Object.assign({ kind: "node", name: n, screen: true },
              toScreen(p.x, p.y, w, h)));
          }
        }
        pp.drawingContext.globalAlpha = 1;
        pp.pop();
      }

      /* 正面の区画の名札。いまどこに止まっているのかが常に分かるようにする。
         回している最中にどの区画が正面なのか分からないのが一番使いにくい。 */
      const fs = vis.find((x) => x.s.id === frontKey);
      if (fs) {
        const s = fs.s;
        const hue = hueOf(s.key);
        const side = s.coneId === "dep" ? "上錐" : "下錐";
        const cnt = s.parts.reduce((a, pt) => a + Object.keys(pt.pos).length, 0);
        pp.noStroke(); pp.fill(`hsl(${hue},52%,${isDark() ? 70 : 36}%)`);
        pp.textSize(13.5); pp.textAlign(pp.CENTER, pp.TOP);
        pp.text(shortLabel(s.key), W / 2, 42);
        pp.fill(c.muted); pp.textSize(10.5);
        pp.text(`${side} ${cnt} 件   ${s.index + 1} / ${s.of} 区画`
          + (dv.pinned && dv.pinned.length ? "   （反対側は固定表示）" : ""), W / 2, 61);
        pp.textAlign(pp.LEFT, pp.CENTER);
      }

      // 中心は経度に依らず固定
      pp.push();
      pp.translate(W / 2 + st.view.tx, H / 2 + st.view.ty);
      pp.scale(k);
      const cw = S.NODE_W + 30, ch = NH + 12;
      pp.noFill(); pp.stroke(c.centerRing); pp.strokeWeight(1.6 / k);
      pp.circle(0, 0, S.GEO.r0 * 0.62);
      pp.fill(c.center); pp.stroke(c.center); pp.strokeWeight(1 / k);
      pp.rect(-cw / 2, -ch / 2, cw, ch, 11);
      pp.noStroke(); pp.fill(c.centerTx); pp.textSize(14.5);
      pp.textAlign(pp.CENTER, pp.CENTER);
      pp.text(fit(pp, (dv.labels && dv.labels[cen]) || cen, cw - 18), 0, 0.5);
      pp.pop();
      hitBoxes.push({ kind: "node", name: cen, screen: true,
        x: W / 2 + st.view.tx - (cw * k) / 2, y: H / 2 + st.view.ty - (ch * k) / 2,
        w: cw * k, h: ch * k });
      pp.textAlign(pp.LEFT, pp.CENTER);
    }

    /* 地球儀。区画の配置と大きさ、いまどこを向いているかを一目で示す。
       内側の環が上錐（依存）、外側が下錐（参照）。掴んで回すと正面が変わる。 */
    function drawGlobe(pp, c, dv, st, W, H) {
      if (!dv.sectors || !dv.sectors.length) return;
      const R = 58, cx = W - R - 22, cy = R + 22;
      const phi = phiAnim;
      globeRect = { x: cx - R - 6, y: cy - R - 6, w: (R + 6) * 2, h: (R + 6) * 2, cx, cy, R };

      pp.noStroke(); pp.fill(c.panel);
      pp.circle(cx, cy, (R + 8) * 2);
      pp.noFill(); pp.stroke(c.panelBd); pp.strokeWeight(1);
      pp.circle(cx, cy, (R + 8) * 2);

      // 球の子午線。奥行きの手掛かり
      pp.stroke(c.ring); pp.strokeWeight(1);
      for (let i = 0; i < 6; i++) {
        const t = (i / 6) * Math.PI - phi;
        pp.noFill(); pp.ellipse(cx, cy, Math.abs(Math.cos(t)) * R * 2, R * 2);
      }
      pp.stroke(c.ring); pp.line(cx - R, cy, cx + R, cy);

      /* 経度は等分なので、区画はどれも同じ角度幅の帯になる。
         部分グラフの大きさは帯の**太さ**で示す。角度で示すと回す量が
         均等でなくなり、狙った区画に止められない。 */
      let frontKey = null, best = Infinity;
      for (const s of dv.sectors) {
        const a = Math.abs(wrapPi(s.lon - phi));
        if (a < best) { best = a; frontKey = s.id; }
      }
      const maxW = dv.sectors.reduce((a, s) => Math.max(a, s.weight), 1);
      const band = (s, rr, weight, alpha) => {
        const steps = Math.max(4, Math.round(s.span * 14));
        pp.noFill();
        pp.strokeWeight(weight);
        pp.drawingContext.globalAlpha = alpha;
        pp.beginShape();
        for (let i = 0; i <= steps; i++) {
          const lam = s.lon - s.span / 2 + (s.span * i) / steps - phi;
          pp.vertex(cx + Math.sin(lam) * rr, cy - Math.cos(lam) * rr * 0.30);
        }
        pp.endShape();
        pp.drawingContext.globalAlpha = 1;
      };
      for (const s of dv.sectors) {
        const hue = hueOf(s.key);
        const d0 = sectorDepth(s, phi);
        const isFront = s.id === frontKey;
        const a = d0 > 0 ? 0.3 + 0.7 * d0 : 0.12;
        const thick = 1.6 + 5.4 * (s.weight / maxW);     // 太さ＝部分グラフの大きさ
        pp.stroke(`hsl(${hue},62%,${isDark() ? 62 : 45}%)`);
        band(s, R * 0.8, isFront ? thick + 2 : thick, a);
        // 区画の切れ目。等分なので、止まる位置が目盛りとして読める
        const edge = s.lon - s.span / 2 - phi;
        pp.stroke(c.ring); pp.strokeWeight(1);
        pp.drawingContext.globalAlpha = 0.5;
        pp.line(cx + Math.sin(edge) * R * 0.62, cy - Math.cos(edge) * R * 0.62 * 0.30,
                cx + Math.sin(edge) * R * 0.98, cy - Math.cos(edge) * R * 0.98 * 0.30);
        pp.drawingContext.globalAlpha = 1;
      }
      // 固定表示している側があることを示す環
      if (dv.pinned && dv.pinned.length) {
        for (const part of dv.pinned) {
          pp.noFill(); pp.stroke(CONE[part.coneId].wash); pp.strokeWeight(2);
          pp.drawingContext.globalAlpha = 0.75;
          pp.ellipse(cx, cy, R * 0.42 * 2, R * 0.42 * 2 * 0.30);
          pp.drawingContext.globalAlpha = 1;
        }
      }

      // 正面の印
      pp.stroke(c.center); pp.strokeWeight(1.5);
      pp.line(cx, cy - R - 4, cx, cy + R + 4);
      pp.noStroke(); pp.fill(c.muted); pp.textSize(9.5);
      pp.textAlign(pp.CENTER, pp.TOP);
      pp.text("掴んで回す / 押して正面へ", cx, cy + R + 10);
      pp.textAlign(pp.LEFT, pp.CENTER);
    }

    /* 画面固定の凡例。四種類の辺を実物と同じ描き方で並べる。
       別の場所に文字だけで書いても、線を見比べられないと区別に使えない。 */
    function drawLegend(pp, c, dv, W, H) {
      const rows = [];
      // 球面モードでは辺は区画の内側に持っているので、そちらから拾う
      const src = (dv.sectors && dv.sectors.length)
        ? dv.sectors.flatMap((s) => s.parts.flatMap((pt) => pt.edges)) : dv.edges;
      const has = new Set(src.map((e) => e.cone + "|" + e.kind));
      for (const key of ["dep|type", "dep|value", "ref|type", "ref|value"]) {
        rows.push({ key, st: EDGE[key], on: has.has(key) });
      }

      /* 幅が足りないところに 268 px の凡例を置くと、地球儀と食い合って
         グラフに残る面積が無くなる。狭いときは線見本だけの一列に畳む。 */
      if (W < 760) {
        const y0 = 14, x0 = 12;
        pp.noStroke(); pp.fill(c.panel);
        pp.rect(x0, y0 - 4, 4 + rows.length * 30, 22, 8);
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
        pp.text("型 / 値 / 主張 / 証明", x0 + 12 + rows.length * 30, y0 + 7);
        return;
      }

      const padX = 11, padY = 9, lh = 19, sample = 34, boxW = 268;
      const boxH = padY * 2 + lh * rows.length + 20;
      const x = 12, y = 12;

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

      /* 錐の見出しは上下の端に置く。どちら側が何なのかを常に示す。
         球面モードでは右上を地球儀が占めているので置かない。重ねると両方読めない。 */
      if (dv.sectors && dv.sectors.length) { pp.textAlign(pp.LEFT, pp.CENTER); return; }
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
      const st = S.state;
      const w = worldOf(pp.mouseX, pp.mouseY, st, pp.width, pp.height);
      const h = pick(w.x, w.y, pp.mouseX, pp.mouseY);
      S.actions.hover(h && h.kind === "node" ? h.name : null);
      host.style.cursor = inGlobe(pp.mouseX, pp.mouseY) ? "ew-resize"
        : h ? "pointer" : (drag ? "grabbing" : "grab");
    };

    pp.mousePressed = function () {
      if (pp.mouseButton !== pp.LEFT) return;      // 副ボタンは履歴移動に使う
      if (pp.mouseX < 0 || pp.mouseY < 0 || pp.mouseX > pp.width || pp.mouseY > pp.height) return;
      if (S.state.view3d && inGlobe(pp.mouseX, pp.mouseY)) {
        globeDrag = { x: pp.mouseX, phi: S.state.phi, moved: false };
        return;
      }
      drag = { x: pp.mouseX, y: pp.mouseY, tx: S.state.view.tx, ty: S.state.view.ty, moved: false };
    };

    pp.mouseDragged = function () {
      if (globeDrag) {
        const dx = pp.mouseX - globeDrag.x;
        if (Math.abs(dx) > 2) globeDrag.moved = true;
        S.actions.setPhi(globeDrag.phi + dx * 0.014);
        clearTimeout(snapTimer);          // 掴んでいる間は寄せない
        return;
      }
      if (!drag) return;
      const dx = pp.mouseX - drag.x, dy = pp.mouseY - drag.y;
      if (Math.abs(dx) + Math.abs(dy) > 3) drag.moved = true;
      S.actions.setView({ ...S.state.view, tx: drag.tx + dx, ty: drag.ty + dy });
    };

    pp.mouseReleased = function () {
      if (globeDrag) {
        const moved = globeDrag.moved; globeDrag = null;
        if (!moved && globeRect) {
          // 押した位置の経度へ最短回りで正面を移し、そこから最寄りの区画へ落ち着かせる
          const t = Math.max(-1, Math.min(1, (pp.mouseX - globeRect.cx) / globeRect.R));
          S.actions.spinTo(S.state.phi + Math.asin(t));
        }
        snapToNearest();
        return;
      }
      if (!drag) return;
      const moved = drag.moved; drag = null;
      if (moved) return;
      if (pp.mouseX < 0 || pp.mouseY < 0 || pp.mouseX > pp.width || pp.mouseY > pp.height) return;
      const st = S.state;
      const w = worldOf(pp.mouseX, pp.mouseY, st, pp.width, pp.height);
      const h = pick(w.x, w.y, pp.mouseX, pp.mouseY);
      if (!h) return;
      if (h.kind === "expand") { S.actions.toggleExpand(h.name); return; }
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
      if (pp.mouseX < 0 || pp.mouseY < 0 || pp.mouseX > pp.width || pp.mouseY > pp.height) return;
      const st = S.state;
      /* 球面モードでは Shift かホイール上での横方向を回転に割り当てる。
         回している間は自由に動かし、手が止まったら最寄りの区画へ寄せて止める。
         途中の角度で置き去りにすると、どの区画も半端に傾いたまま読めない。 */
      if (st.view3d && (e.shiftKey || inGlobe(pp.mouseX, pp.mouseY))) {
        S.actions.setPhi(st.phi + (e.deltaY > 0 ? 0.1 : -0.1));
        scheduleSnap(220);
        return false;
      }
      const k0 = st.view.k == null ? fitK : st.view.k;
      const f = e.deltaY > 0 ? 0.92 : 1.08;
      const k1 = Math.min(3, Math.max(0.1, k0 * f));
      const cx = pp.mouseX - pp.width / 2, cy = pp.mouseY - pp.height / 2;
      S.actions.setView({
        tx: cx - (cx - st.view.tx) * (k1 / k0),
        ty: cy - (cy - st.view.ty) * (k1 / k0),
        k: k1,
      });
      return false;
    };
  }

  /** 当たり判定。球面モードの箱は画面座標、平面モードの箱は world 座標で持つ。 */
  function pick(wx, wy, sx, sy) {
    for (let i = hitBoxes.length - 1; i >= 0; i--) {
      const b = hitBoxes[i];
      const x = b.screen ? sx : wx, y = b.screen ? sy : wy;
      if (x >= b.x && x <= b.x + b.w && y >= b.y && y <= b.y + b.h) return b;
    }
    return null;
  }

  const inGlobe = (x, y) => globeRect && x >= globeRect.x && x <= globeRect.x + globeRect.w
    && y >= globeRect.y && y <= globeRect.y + globeRect.h;

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
    const ro = new ResizeObserver(() => { if (p) p.windowResized(); });
    ro.observe(el);
  }

  LDR.canvas = {
    mount, EDGE, CONE,
    zoomIn: () => S.actions.zoomBy(1.18, fitK),
    zoomOut: () => S.actions.zoomBy(1 / 1.18, fitK),
    reset: () => S.actions.resetView(),
    get fitK() { return fitK; },
  };
})(window.LDR = window.LDR || {});
