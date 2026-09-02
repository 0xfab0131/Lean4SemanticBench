/* ============================================================
   js/store.js — 状態と派生計算
   状態を1か所に集め、変更を購読者に配る。
   派生（層化・配置）はキーが変わったときだけ再計算する。

   中心 d のまわりに二つの円錐を置く。MacNeille の極 (polarity) と同じ形で、
   上が下界作用素の側 ↓d、下が上界作用素の側 ↑d に対応する。

     上   依存錐  d が証明で使っているもの   adj = dep
     下   参照錐  d を使っている宣言         adj = refAll

   下の錐は二種類の辺を含む。Lean 側 directDepsOfCore が型にも値にも現れる
   定数を型側にのみ入れるので、この二つは交わらない。

     実線  refType   d を「主張」に含む宣言。d についての定理・性質。
     点線  refValue  d を「証明」でのみ使う宣言。d を道具にした側。

   当初これを左右二つの錐に割ったが、下半分を半々にすると両方とも狭くて読めない。
   上錐が型依存と値依存を線種で描き分けているのと同じ流儀に揃え、
   一つの錐を下半分いっぱいに開いて、種類は線種と色で分ける。
   ============================================================ */
(function (LDR) {
  "use strict";
  const G = LDR.graph;

  const NODE_H = 34, NODE_W = 186;

  /* 円錐の幾何。角度は画面座標（y が下向き、0 = 右、π/2 = 下）。 */
  /* slotMin は「1 ノードが占める弧長の下限」。ここを削ると密な層でノードが
     点に潰れ、押すまで何か分からなくなる。読める幅を下限として確保し、
     その代わりに 1 層の表示上限（density）で溢れを制御する。 */
  /* dr(隣接リングの最小間隔)の下限には導出がある。リング間の中心間距離は
     常に ≥ dr であり、軸平行矩形の重なりは距離 < √(w² + h²) を要するから、
        dr ≥ √(w_max² + h²) = √(186² + 34²) ≈ 189.1
     で任意の角度差に対して重なりが不可能になる。旧値 136 はこれを下回り、
     扇の水平寄りで原理的に重なり得た(自己解析で実測して 200 に修正)。

     [不変条件] 同リング隣接にはこの距離論法が使えない(中心間距離 ≈ slot ≥
     slotMin = 94 < 189)。成分評価では、危険角 |cosθ| ≈ NODE_H/slot での余白が
        Δx − w = slot·√(1 − (NODE_H/slot)²) − (slot − 12) ≈ 5px  (slot = slotMin)
     しかない。slotMin(94)・ノード幅の控除(w = slot − 12)・NODE_H(34)は
     この余白で互いに結合しており、どれか一つを単独で「改善」すると静かに壊れる。
     経験的ガードは ldr_check の全深さ・矩形重なり検査。 */
  const GEO = {
    r0: 196, dr: 200, slotMax: 200, slotMin: 94, slotPref: 202,
    rSoft: 1180,
    margin: 0.20,      // 水平線から空ける角度
  };

  const SECTORS = {
    dep: { th0: -Math.PI + GEO.margin, th1: -GEO.margin },   // 上半分いっぱい
    ref: { th0: GEO.margin, th1: Math.PI - GEO.margin },     // 下半分いっぱい
  };

  const HIST_CAP = 50;

  const state = {
    rawText: "",
    nodes: {}, errors: [], order: [],

    edgeMode: "all",        // "all" | "type"
    granularity: "decl",    // "decl" | "module"
    baseDepth: 1,
    expanded: new Set(),
    refFilter: "all",       // 下の参照錐に入れる辺: "all" | "type" | "value"
    density: 36,            // 1 層に描く上限。溢れは環のラベルに件数で出る
    hideFrame: true,        // 論理の骨組みを潰して補題を前面に出す

    /* 球面モード。部分グラフごとに扇をまるごと与え、経度で切り替える。
       一つの扇を全ての部分グラフで共有すると、どれも狭くなって重なる。
       前に来た区画だけを読める大きさで描き、他は奥へ退かせる。 */
    view3d: false,
    phi: 0,                 // いま正面に向いている経度
    pathFrom: null,         // ここから中心までの経路を強調する
    derivOpen: new Set(),   // 導出図で開いている前提

    hist: { nodes: {}, order: [], curId: null, seq: 0 },
    pins: [],

    selected: null,         // 詳細に出す宣言（中心とは独立）
    traceTarget: null,      // 順序区間 [t, d] の t
    hovered: null,

    query: "",
    listMode: "impl",       // "impl" | "deps" | "ns" | "tree"
    sortMetric: "closure",  // listMode="deps" のときの尺度
    groupBy: "subject",     // 部分グラフの束ね方: "subject" | "module" | "kind" | "none"
    treeClosed: new Set(),  // ツリー表示で閉じているモジュール接頭辞
    kindFilter: new Set(),
    onlySorry: false,

    /* 右パネルのプレビュー。中心に固定するか、選んだものを追うかを切り替える。
       比較しながら読むときは追従、腰を据えて読むときは固定が要る。 */
    previewFollow: true,
    previewName: null,
    previewHist: [],        // 直近に見た宣言。最大 10 件

    view: { tx: 0, ty: 0, k: null },  // k=null なら自動フィット
  };

  const subs = new Set();
  function subscribe(fn) { subs.add(fn); return () => subs.delete(fn); }
  function emit() { for (const fn of subs) fn(state, derived); }

  let derived = {};
  let lastKey = null;

  /* ---------- 索引のキャッシュ ----------
     索引と既定中心は「読み込んだデータ」だけで決まる。展開やズームのたびに
     組み直すと、宣言数に比例した仕事が操作のたびに走る。 */
  let cache = { nodesRef: null, decl: {}, mod: {}, defaultCenter: {}, metrics: {} };

  function indices() {
    if (cache.nodesRef !== state.nodes) {
      cache = { nodesRef: state.nodes, decl: {}, mod: {}, defaultCenter: {}, metrics: {}, laws: null };
    }
    const em = state.edgeMode;
    if (!cache.decl[em]) cache.decl[em] = G.buildIndices(state.nodes, em);
    if (!cache.mod[em]) cache.mod[em] = G.buildModuleIndices(state.nodes, em);
    if (!cache.defaultCenter[em]) cache.defaultCenter[em] = G.pickDefaultCenter(state.nodes, cache.decl[em]);
    return { decl: cache.decl[em], mod: cache.mod[em], defaultCenter: cache.defaultCenter[em] };
  }

  /* ---------- 依存の尺度 ----------

     直接依存の本数だけでは「依存の少ない順」にならない。c が d の依存先でも
     deg(c) > deg(d) が起こり得るので、その並びは依存順序と両立しない。
     順序と両立する量（c ≺ d ⇒ m(c) < m(d)）を揃えて、選べるようにする。

       closure  |↓d|        総仮定量。昇順は必ず線形拡大になる。
       depth    最長導出鎖   何段の導出を経ているか。これも線形拡大。
       minimal  |min(↓d)|   必要な原始要素の数。
       direct   直接依存数   従来の量。比較のために残す（線形拡大ではない）。
       refs     |↑d| の一段  どれだけ使われているか。影響範囲。
       size     証明項の節点数。証明の重さ。 */
  const METRICS = {
    closure: { ja: "総仮定量 |↓d|", mono: true },
    depth:   { ja: "導出鎖の深さ",  mono: true },
    minimal: { ja: "極小仮定の数",  mono: false },
    direct:  { ja: "直接依存数",    mono: false },
    refs:    { ja: "被参照数",      mono: false },
    size:    { ja: "証明項の大きさ", mono: false },
  };

  function metrics() {
    indices();                       // nodes が変われば cache ごと入れ替わる
    const em = state.edgeMode;
    if (!cache.metrics) cache.metrics = {};
    if (!cache.metrics[em]) {
      const idx = cache.decl[em];
      const names = Object.keys(state.nodes);
      const cs = G.closureStats(idx.dep, names);
      const depth = G.chainDepths(idx.dep, names);
      const direct = {}, refs = {}, size = {};
      for (const n of names) {
        direct[n] = (idx.dep[n] || []).length;
        refs[n] = (idx.ref[n] || []).length;
        size[n] = state.nodes[n].valueSize || 0;
      }
      /* 「無条件に得られたものだけから、無条件に得られている」か。
         自分に仮定もインスタンス要求も無く、かつ依存先すべてが同じ性質を持つ。
         利用者が語っていた def の使い分けのうち、三番目にあたる区別。 */
      const uncond = (n) => {
        const nd = state.nodes[n];
        return !!nd && (nd.numHyp || 0) === 0 && (nd.numInst || 0) === 0;
      };
      const hered = G.hereditary(idx.dep, names, uncond);
      cache.metrics[em] = {
        closure: cs ? cs.size : depth,      // 数え上げられない規模なら深さで代用
        minimal: cs ? cs.minimal : direct,
        depth, direct, refs, size, hered,
        uncond: Object.fromEntries(names.map((n) => [n, uncond(n)])),
        exact: !!cs,
      };
    }
    return cache.metrics[em];
  }

  /* ---------- 法則の在庫 ----------

     「この関係について反射律・推移律は取れているか」は、この計画で最も
     繰り返し問われることの一つ。宣言名から推し量るのではなく、Lean 側が
     仮定と結論の形から判定した `shape` と、それが「どの関係についてか」を
     示す `shapeRel` を集計する。行が関係、列が法則の表になる。

     取れていない欄は「まだ証明されていない」ことを意味するのであって、
     「成り立たない」ことではない。判定は取り逃す向きに倒してあるので、
     欄が空でも別の形で証明されている可能性は残る。そこは表に明記する。
     同じ原則から、`sorry` を含む宣言は在庫に数えない。空欄は正直でも、
     埋まった欄が sorry で嘘をつくことは許されない。 */
  const LAWS = ["refl", "irrefl", "symm", "trans", "antisymm", "total", "mono",
                "comm", "assoc", "idem", "absorb", "distrib"];

  function lawInventory() {
    indices();
    if (cache.laws) return cache.laws;
    const rows = new Map();          // 関係名 → { law → [宣言名], pairs }
    for (const [n, nd] of Object.entries(state.nodes)) {
      if (!nd.shape || !nd.shapeRel) continue;
      if (nd.usesSorry) continue;    // sorry の主張を「証明済みの法則」として数えない
      // 法則は命題である。型クラスのインスタンス(C α α 等)は構文上 refl の形を
      // 持つがデータであって証明ではない(自己解析で MonadLiftT 等の行として実測)。
      if (!nd.isProp) continue;
      const rel = nd.shapeRel;
      if (!rows.has(rel)) rows.set(rel, { rel, total: 0, laws: {}, pairs: {} });
      const row = rows.get(rel);
      (row.laws[nd.shape] || (row.laws[nd.shape] = [])).push(n);
      // 二演算法則(吸収・分配)は相方 shapeRel2 を対として控える
      if ((nd.shape === "absorb" || nd.shape === "distrib") && nd.shapeRel2) {
        (row.pairs[nd.shape] || (row.pairs[nd.shape] = new Set())).add(nd.shapeRel2);
      }
      row.total++;
    }
    // 主題としての登場回数も添える。関係の「大きさ」の目安になる。
    const weight = {};
    for (const nd of Object.values(state.nodes)) {
      if (nd.subject) weight[nd.subject] = (weight[nd.subject] || 0) + 1;
    }
    const list = [...rows.values()].map((r) => ({ ...r, weight: weight[r.rel] || 0 }));
    list.sort((a, b) => (b.total - a.total) || (b.weight - a.weight) || (a.rel < b.rel ? -1 : 1));

    /* 判断（列の組から読める構造）。計算はここに一元化し、表示側
       （panels / ldr_check）は結果を読むだけにする（重複実装は必ず乖離する）。

         反射+推移               → 前順序
           +反対称               → 半順序、さらに +全域 → 全順序
         反射+対称+推移          → 同値
         可換+結合+冪等          → 半束
           相方も半束で吸収が双方向 → 束、さらに分配があれば → 分配束 */
    const byRel = new Map(list.map((r) => [r.rel, r]));
    const hasLaw = (row, l) => (row.laws[l] || []).length > 0;
    const isSemi = (row) => hasLaw(row, "comm") && hasLaw(row, "assoc") && hasLaw(row, "idem");
    for (const r of list) {
      let verdict = null;
      if (hasLaw(r, "refl") && hasLaw(r, "trans") && hasLaw(r, "symm")) {
        verdict = { t: "同値", h: 152 };
      } else if (hasLaw(r, "refl") && hasLaw(r, "trans") && hasLaw(r, "antisymm")) {
        verdict = hasLaw(r, "total") ? { t: "全順序", h: 262 } : { t: "半順序", h: 243 };
      } else if (hasLaw(r, "refl") && hasLaw(r, "trans")) {
        verdict = { t: "前順序", h: 199 };
      } else if (isSemi(r)) {
        verdict = { t: "半束", h: 271 };
        for (const g of r.pairs.absorb ? [...r.pairs.absorb] : []) {
          const rg = byRel.get(g);
          if (rg && isSemi(rg) && rg.pairs.absorb && rg.pairs.absorb.has(r.rel)) {
            const dist = (r.pairs.distrib && r.pairs.distrib.has(g))
                      || (rg.pairs.distrib && rg.pairs.distrib.has(r.rel));
            verdict = dist ? { t: "分配束", h: 291 } : { t: "束", h: 281 };
            break;
          }
        }
      }
      r.verdict = verdict;
    }
    cache.laws = { list, LAWS };
    return cache.laws;
  }

  /** 部分グラフを束ねる鍵。主題は「何についての宣言か」を Lean 側が出したもの。 */
  function groupKeyOf(name) {
    const nd = state.nodes[name];
    if (!nd) return "";
    switch (state.groupBy) {
      case "module":  return nd.module || "";
      case "kind":    return nd.kind || "";
      case "subject": return nd.subject || nd.head || "";
      default:        return "";
    }
  }

  /* ---------- 探索履歴ツリー ----------
     直線の履歴だと、戻ってから別の枝に入った瞬間に元の枝が消える。
     探索は本来分岐するものなので、木のまま持って木のまま見せる。 */
  function histCur() { return state.hist.curId ? state.hist.nodes[state.hist.curId] : null; }

  function histPush(name) {
    const h = state.hist;
    const cur = histCur();
    if (cur && cur.name === name) return;
    const siblings = cur ? cur.children : h.order.filter((id) => !h.nodes[id].parent);
    const found = siblings.map((id) => h.nodes[id]).find((c) => c.name === name);
    if (found) { h.curId = found.id; if (cur) cur.last = found.id; return; }
    const id = "h" + (++h.seq);
    h.nodes[id] = { id, name, parent: cur ? cur.id : null, children: [], last: null, ts: Date.now() };
    if (cur) { cur.children.push(id); cur.last = id; }
    h.order.push(id);
    h.curId = id;
    histPrune();
  }

  /* 上限を超えたら、まず「現在地の系譜に無い古い葉」から捨てる。
     一本道に降り続けると全ノードが祖先になって葉が尽きるので、
     その場合は最も古い根を外して子を根に繰り上げる（＝古い側から忘れる）。
     どちらの場合も現在地とその系譜は最後まで残る。 */
  function histPrune() {
    const h = state.hist;
    let guard = HIST_CAP * 4;
    while (h.order.length > HIST_CAP && guard-- > 0) {
      const path = new Set();
      for (let p = h.curId; p; p = h.nodes[p].parent) path.add(p);
      const leaf = h.order.find((id) => h.nodes[id].children.length === 0 && !path.has(id));
      const victim = leaf !== undefined ? leaf : oldestRootOnPath(h, path);
      if (victim === undefined) break;
      const nd = h.nodes[victim];
      if (nd.parent && h.nodes[nd.parent]) {
        const par = h.nodes[nd.parent];
        par.children = par.children.filter((x) => x !== victim);
        if (par.last === victim) par.last = par.children[par.children.length - 1] || null;
      }
      for (const ch of nd.children) if (h.nodes[ch]) h.nodes[ch].parent = nd.parent || null;
      if (nd.parent && h.nodes[nd.parent]) {
        const par = h.nodes[nd.parent];
        par.children = par.children.concat(nd.children.filter((c) => h.nodes[c]));
      }
      delete h.nodes[victim];
      h.order = h.order.filter((x) => x !== victim);
    }
  }

  function oldestRootOnPath(h, path) {
    let root;
    for (let p = h.curId; p; p = h.nodes[p].parent) root = p;
    return root !== undefined && root !== h.curId ? root : undefined;
  }

  function centerName() {
    const cur = histCur();
    if (cur) return cur.name;
    return derived.defaultCenter || "";
  }

  function effCenter() {
    const c = centerName();
    if (state.granularity === "module") {
      const n = state.nodes[c];
      return n ? n.module : c;
    }
    return c;
  }

  /* ---------- 派生 ---------- */
  function recompute() {
    const nodes = state.nodes;
    const ix = indices();
    const idx = state.granularity === "module" ? ix.mod : ix.decl;
    derived.declIdx = ix.decl; derived.modIdx = ix.mod; derived.idx = idx;
    derived.defaultCenter = ix.defaultCenter;

    const c = effCenter();
    derived.center = c;
    derived.cones = [];
    derived.sectors = [];
    derived.pinned = [];
    derived.rotatingCone = null;
    derived.posAll = {};
    derived.edges = [];
    derived.labels = {};
    derived.more = {};
    derived.bbox = { x0: -200, x1: 200, y0: -120, y1: 120 };
    if (!c || !idx.dep) return;

    /* min(↓d) は宣言 d の性質であって、いま何を展開しているかとは無関係。
       可視集合から計算すると初期表示で空になり、意味も違ってしまう。 */
    const fullDep = G.reachable(c, idx.dep, 64);
    const mf = G.minimalAndFrontier(Object.keys(fullDep), idx.dep);
    derived.trueMinimal = mf.trueMinimal;
    derived.minimalSet = new Set(mf.trueMinimal);   // 描画は毎フレーム引くので集合で持つ
    derived.frontier = mf.frontier;
    derived.fullDownSize = Object.keys(fullDep).length;

    /* 経路表示中はその区間を強制的に開く。公理を押したのに畳まれたままでは意味がない。 */
    let openSet = state.expanded, interval = null;
    if (state.traceTarget) {
      interval = G.orderInterval(c, state.traceTarget, idx.dep, idx.ref, 64);
      openSet = new Set([...state.expanded, ...interval]);
    }
    derived.highlight = interval;

    /* 選んだノードから中心までの経路。上錐なら中心から下りる向き、
       下錐なら中心へ上がる向きなので、順序区間の取り方が逆になる。
       強調はするが他を暗くはしない。周りが見えなくなると比較ができない。 */
    derived.pathSet = null;
    if (state.pathFrom && state.pathFrom !== c && state.granularity === "decl") {
      const t = state.pathFrom;
      const down = G.orderInterval(c, t, idx.dep, idx.ref, 64);
      derived.pathSet = down.size > 1 ? down : G.orderInterval(t, c, idx.dep, idx.ref, 64);
      if (derived.pathSet.size <= 1) derived.pathSet = null;
    }

    let depAdj = idx.dep;
    let refAdj = state.refFilter === "type" ? idx.refType
               : state.refFilter === "value" ? idx.refValue
               : idx.refAll;
    /* 論理の骨組みを潰して、実際に使われた補題が前面に出るようにする。
       表示のためだけの縮約で、上の min(↓d) や |↓d| は元のグラフで測っている。
       縮約辺の種(型/値)は初手から継承した上書き表で引く。既存の edgeKind は
       元グラフの直接辺しか知らないため、これ無しでは縮約辺が全て既定の
       「型依存」の見た目に落ちる。 */
    derived.edgeKindOverlay = null;
    if (state.hideFrame && state.granularity === "decl" && LDR.roles) {
      const names = Object.keys(nodes);
      const hidden = (n) => LDR.roles.roleOf(n, nodes[n]) === "frame";
      if (!cache.contracted) cache.contracted = {};
      const ck = state.edgeMode + "|" + state.refFilter;
      if (!cache.contracted[ck]) {
        const kindDep = (u, v) => idx.edgeKind[u + " " + v] || "type";
        const kindRef = (u, v) => (idx.refKind && idx.refKind[u + " " + v]) || "type";
        cache.contracted[ck] = {
          dep: G.contractThrough(idx.dep, hidden, names, kindDep),
          ref: G.contractThrough(refAdj || {}, hidden, names, kindRef),
        };
      }
      depAdj = cache.contracted[ck].dep.adj;
      refAdj = cache.contracted[ck].ref.adj;
      derived.edgeKindOverlay = {
        dep: cache.contracted[ck].dep.kind,
        ref: cache.contracted[ck].ref.kind,
      };
    }
    const specs = [
      { id: "dep", adj: depAdj, sector: SECTORS.dep },
      { id: "ref", adj: refAdj || {}, sector: SECTORS.ref },
    ];

    if (state.view3d) { buildSectors(c, specs, idx, passes, openSet); return; }

    const claimed = new Set([c]);
    for (const sp of specs) {
      const vis = G.visibleClosure(c, sp.adj, state.baseDepth, openSet);
      const lv = G.longestPathLevels(c, sp.adj, vis.hop);
      // 種別フィルタと、別の錐が既に取ったノードを層から落とす。
      const layers = lv.layers.map((L, l) => (l === 0 ? L : L.filter((n) => !claimed.has(n) && passes(n))));
      const cone = G.layoutCone({
        layers, adj: sp.adj, th0: sp.sector.th0, th1: sp.sector.th1,
        groupOf: state.groupBy === "none" ? null : groupKeyOf,
        r0: GEO.r0, dr: GEO.dr, slotMax: GEO.slotMax, slotMin: GEO.slotMin,
        slotPref: GEO.slotPref, rSoft: GEO.rSoft, maxPerLayer: state.density,
      });
      cone.id = sp.id; cone.adj = sp.adj; cone.hop = vis.hop;
      cone.closedFrontier = vis.closedFrontier;
      for (const n of Object.keys(cone.pos)) claimed.add(n);
      Object.assign(derived.more, vis.closedFrontier);
      derived.cones.push(cone);
    }

    // 位置表と辺列を一度だけ作る。描画側は毎フレームこれを読むだけにする。
    const center = { x: 0, y: 0, r: 0, th: 0, level: 0, w: NODE_W, cone: "center" };
    derived.posAll[c] = center;
    for (const cone of derived.cones) {
      for (const [n, p] of Object.entries(cone.pos)) derived.posAll[n] = Object.assign({ cone: cone.id }, p);
    }
    for (const cone of derived.cones) {
      const seen = new Set();
      for (const u of [c, ...Object.keys(cone.pos)]) {
        const pu = derived.posAll[u];
        if (!pu || (u !== c && pu.cone !== cone.id)) continue;
        for (const v of cone.adj[u] || []) {
          const pv = derived.posAll[v];
          if (!pv || pv.cone !== cone.id) continue;
          const kk = u + " " + v;
          if (seen.has(kk)) continue;
          seen.add(kk);
          const ov = derived.edgeKindOverlay;
          derived.edges.push({
            u, v, cone: cone.id,
            kind: cone.id === "dep"
              ? ((ov && ov.dep[kk]) || idx.edgeKind[kk] || "type")
              : ((ov && ov.ref[kk]) || (idx.refKind && idx.refKind[kk]) || "type"),
          });
        }
      }
    }

    derived.labels = G.shortestUniqueSuffixes(Object.keys(derived.posAll));

    let x0 = -NODE_W, x1 = NODE_W, y0 = -NODE_H * 2, y1 = NODE_H * 2;
    for (const p of Object.values(derived.posAll)) {
      x0 = Math.min(x0, p.x - p.w / 2); x1 = Math.max(x1, p.x + p.w / 2);
      y0 = Math.min(y0, p.y - NODE_H); y1 = Math.max(y1, p.y + NODE_H);
    }
    derived.bbox = { x0, x1, y0, y1 };

    function passes(n) {
      if (state.granularity === "module") return true;
      if (!state.kindFilter.size) return true;
      return state.kindFilter.has(nodes[n] ? nodes[n].kind : "unknown");
    }
  }

  /* ---------- 球面モードの配置 ----------

     区画 = 部分グラフ。一つの部分グラフは上錐にも下錐にも顔を出すので、
     **一つの経度に上下両方を載せる**。上と下で別々に経度を割り当てると、
     回したときに正面へ来る区画が上下で食い違い、意味を成さない。

     経度の幅は部分グラフの重さ（上下あわせた可視ノード数）に比例する。
     ただし 1〜2 個しかない部分グラフに独立した区画を与えると、回しても
     当たらない針のような区間が並ぶだけなので、小さいものは「その他」に束ねる。

     層の番号は全体の錐で決めたものをそのまま使う。部分グラフごとに数え直すと、
     同じ ℓ が違う深さを意味してしまう。 */
  const SECTOR_MAX = 10;      // 独立した区画として立てる上限
  const SECTOR_MIN_W = 3;     // これ未満の部分グラフは「その他」へ
  const PIN_MAX = 24;         // これ以下の錐は分割せず、回さず、常に出す

  function buildSectors(c, specs, idx, passes, openSet) {
    derived.sectors = [];
    derived.pinned = [];
    const center = { x: 0, y: 0, r: 0, th: 0, level: 0, w: NODE_W, cone: "center" };
    derived.posAll[c] = center;

    /* 各錐の層を先に集める。ここではまだ分割しない。 */
    const cones = [];
    for (const sp of specs) {
      const vis = G.visibleClosure(c, sp.adj, state.baseDepth, openSet);
      Object.assign(derived.more, vis.closedFrontier);   // 区画の中でも個別に開ける
      const lv = G.longestPathLevels(c, sp.adj, vis.hop);
      const layers = lv.layers.map((L, l) =>
        l === 0 ? [c] : L.filter((n) => n !== c && passes(n)));
      const count = layers.reduce((a, L, l) => a + (l ? L.length : 0), 0);
      cones.push({ sp, layers, count });
      derived.cones.push({ id: sp.id, rings: [], overflow: {}, rMax: 0,
        th0: sp.sector.th0, th1: sp.sector.th1, adj: sp.adj });
    }

    /** 一組の層から扇を一つ作る。区画にも固定側にも同じものを使う。 */
    const makePart = (sp, layers, sectorId) => {
      const cone = G.layoutCone({
        layers, adj: sp.adj, th0: sp.sector.th0, th1: sp.sector.th1, groupOf: null,
        r0: GEO.r0, dr: GEO.dr, slotMax: GEO.slotMax, slotMin: GEO.slotMin,
        slotPref: GEO.slotPref, rSoft: GEO.rSoft, maxPerLayer: state.density,
      });
      const own = new Set(Object.keys(cone.pos));
      const edges = [];
      const ov = derived.edgeKindOverlay;
      for (const u of [c, ...own]) {
        for (const v of sp.adj[u] || []) {
          if (!own.has(v)) continue;
          const kk = u + " " + v;
          edges.push({ u, v, cone: sp.id,
            kind: sp.id === "dep"
              ? ((ov && ov.dep[kk]) || idx.edgeKind[kk] || "type")
              : ((ov && ov.ref[kk]) || (idx.refKind && idx.refKind[kk]) || "type") });
        }
      }
      for (const [n, p] of Object.entries(cone.pos)) {
        if (!derived.posAll[n]) derived.posAll[n] = Object.assign({ cone: sp.id, sector: sectorId }, p);
      }
      return { coneId: sp.id, pos: cone.pos, rings: cone.rings, overflow: cone.overflow,
        rMax: cone.rMax, th0: cone.th0, th1: cone.th1, edges };
    };

    /* 薄い錐は分割しない。9 件しかない上錐を部分グラフに割っても、
       回すたびに片側が空になるだけで読みにくくなる。常に出しておく。
       厚い錐だけを部分グラフに割って回す。 */
    const rotating = cones.filter((x) => x.count > PIN_MAX);
    const pinnedCones = cones.filter((x) => x.count <= PIN_MAX && x.count > 0);
    for (const x of pinnedCones) derived.pinned.push(makePart(x.sp, x.layers, "pinned"));
    derived.rotatingCone = rotating.length ? rotating[0].sp.id : null;

    if (!rotating.length) {
      // どちらも薄い。回す対象が無いので、そのまま両方を出す。
      finishSectors();
      return;
    }

    /* 厚い錐を部分グラフに割る。小さい群は「その他」へ束ね、上限も掛ける。
       針のような区間が並ぶと、回しても当たらず操作にならない。 */
    for (const rot of rotating) {
      const byGroup = new Map();
      rot.layers.forEach((L, l) => {
        if (l === 0) return;
        for (const n of L) {
          const key = groupKeyOf(n) || "(その他)";
          if (!byGroup.has(key)) byGroup.set(key, { key, layers: [], weight: 0 });
          const g = byGroup.get(key);
          (g.layers[l] || (g.layers[l] = [])).push(n);
          g.weight++;
        }
      });
      const sorted = [...byGroup.values()].sort((a, b) => (b.weight - a.weight) || (a.key < b.key ? -1 : 1));
      const keep = [], rest = [];
      for (const g of sorted) {
        if (keep.length < SECTOR_MAX && g.weight >= SECTOR_MIN_W) keep.push(g); else rest.push(g);
      }
      if (rest.length) {
        const merged = { key: `その他 (${rest.length} 群)`, layers: [], weight: 0, merged: true };
        for (const g of rest) {
          g.layers.forEach((L, l) => {
            if (!L) return;
            (merged.layers[l] || (merged.layers[l] = [])).push(...L);
          });
          merged.weight += g.weight;
        }
        if (merged.weight) keep.push(merged);
      }

      /* 経度は **等分**。重さに比例させると 37 % の区画と 1 % の区画が混在し、
         回す角度が全く均等にならず、狙った区画に止められない。
         重さは地球儀の帯の太さで示す。 */
      const n = keep.length || 1;
      const span = (2 * Math.PI) / n;
      keep.forEach((g, i) => {
        for (let j = 0; j < g.layers.length; j++) if (!g.layers[j]) g.layers[j] = [];
        g.layers[0] = [c];
        const id = "s|" + rot.sp.id + "|" + g.key;
        const part = makePart(rot.sp, g.layers, id);
        derived.sectors.push({ id, key: g.key, merged: !!g.merged, coneId: rot.sp.id,
          weight: g.weight, index: i, of: n, lon: span * (i + 0.5), span,
          parts: [part], rMax: part.rMax });
      });
    }
    finishSectors();

    function finishSectors() {
      derived.labels = G.shortestUniqueSuffixes(Object.keys(derived.posAll));
      let x0 = -NODE_W, x1 = NODE_W, y0 = -NODE_H * 2, y1 = NODE_H * 2;
      const eat = (part) => {
        for (const p of Object.values(part.pos)) {
          x0 = Math.min(x0, p.x - p.w / 2); x1 = Math.max(x1, p.x + p.w / 2);
          y0 = Math.min(y0, p.y - NODE_H); y1 = Math.max(y1, p.y + NODE_H);
        }
      };
      for (const part of derived.pinned) eat(part);
      for (const s of derived.sectors) for (const part of s.parts) eat(part);
      derived.bbox = { x0, x1, y0, y1 };
    }
  }

  function key() {
    return [
      Object.keys(state.nodes).length, state.edgeMode, state.granularity,
      state.baseDepth, state.refFilter, state.groupBy, state.density, state.hideFrame,
      state.view3d, state.pathFrom,
      [...state.expanded].sort().join(","),
      centerName(), state.traceTarget, [...state.kindFilter].sort().join(","),
    ].join("|");
  }

  function refresh(force) {
    const k = key();
    if (force || k !== lastKey) { lastKey = k; recompute(); }
    emit();
  }

  /* ---------- 閲覧状態のピン留め ---------- */
  function snapshot() {
    return {
      center: centerName(),
      expanded: [...state.expanded],
      edgeMode: state.edgeMode,
      granularity: state.granularity,
      baseDepth: state.baseDepth,
      refFilter: state.refFilter,
      groupBy: state.groupBy,
      sortMetric: state.sortMetric,
      previewFollow: state.previewFollow,
      previewName: state.previewName,
      traceTarget: state.traceTarget,
      selected: state.selected,
      kindFilter: [...state.kindFilter],
      view: { ...state.view },
    };
  }

  function applySnapshot(s) {
    if (!s) return;
    state.edgeMode = s.edgeMode || "all";
    state.granularity = s.granularity || "decl";
    state.baseDepth = s.baseDepth || 1;
    // 旧いピン（下錐を二つに割っていた頃）も読めるようにしておく
    state.refFilter = s.refFilter || (s.showRefValue === false ? "type" : "all");
    state.groupBy = s.groupBy || "subject";
    state.sortMetric = s.sortMetric || "closure";
    if (s.previewFollow !== undefined) state.previewFollow = !!s.previewFollow;
    state.previewName = s.previewName || null;
    state.expanded = new Set(s.expanded || []);
    state.kindFilter = new Set(s.kindFilter || []);
    state.traceTarget = s.traceTarget || null;
    state.selected = s.selected || null;
    state.view = s.view ? { ...s.view } : { tx: 0, ty: 0, k: null };
    if (s.center) histPush(s.center);
    refresh(true);
  }

  /* ---------- 操作 ---------- */
  const actions = {
    loadText(text, opts) {
      const r = G.parseJsonl(text);
      state.rawText = text;
      state.nodes = r.nodes; state.errors = r.errors; state.order = r.order;
      state.hist = { nodes: {}, order: [], curId: null, seq: 0 };
      state.expanded = new Set(); state.traceTarget = null; state.selected = null;
      state.pathFrom = null; state.treeClosed = new Set();
      state.previewName = null; state.previewHist = [];
      state.view = { tx: 0, ty: 0, k: null };
      refresh(true);
      if (!opts || !opts.silent) LDR.onDataLoaded && LDR.onDataLoaded(text);
    },
    navigate(n) {
      if (!n) return;
      histPush(n);
      state.expanded = new Set(); state.traceTarget = null;
      state.selected = n;
      state.previewName = n;
      state.previewHist = [n, ...state.previewHist.filter((x) => x !== n)].slice(0, 10);
      state.view = { tx: 0, ty: 0, k: null };
      refresh();
    },
    back() {
      const cur = histCur();
      if (!cur || !cur.parent) return;
      state.hist.curId = cur.parent;
      state.expanded = new Set(); state.traceTarget = null; state.pathFrom = null;
      state.view = { tx: 0, ty: 0, k: null };
      refresh();
    },
    forward() {
      const cur = histCur();
      if (!cur) return;
      const nx = cur.last || cur.children[cur.children.length - 1];
      if (!nx) return;
      state.hist.curId = nx;
      state.expanded = new Set(); state.traceTarget = null; state.pathFrom = null;
      state.view = { tx: 0, ty: 0, k: null };
      refresh();
    },
    jumpHist(id) {
      if (!state.hist.nodes[id]) return;
      state.hist.curId = id;
      const p = state.hist.nodes[id].parent;
      if (p) state.hist.nodes[p].last = id;
      state.expanded = new Set(); state.traceTarget = null; state.pathFrom = null;
      state.view = { tx: 0, ty: 0, k: null };
      refresh();
    },
    clearHist() {
      const cur = histCur();
      state.hist = { nodes: {}, order: [], curId: null, seq: 0 };
      if (cur) histPush(cur.name);
      refresh(true);
    },
    select(n) {
      state.selected = n;
      state.pathFrom = n;              // 中心までの流れを浮かび上がらせる
      // 追従なら、覗いた先をそのままプレビューに出す。移動はしない。
      if (state.previewFollow && n) {
        state.previewName = n;
        state.previewHist = [n, ...state.previewHist.filter((x) => x !== n)].slice(0, 10);
      }
      refresh();
    },
    /** プレビューの対象を差し替え、直近 10 件を控える。 */
    preview(n) {
      if (!n) return;
      state.previewName = n;
      state.previewHist = [n, ...state.previewHist.filter((x) => x !== n)].slice(0, 10);
      emit();
    },
    setPreviewFollow(v) {
      state.previewFollow = !!v;
      if (!state.previewFollow) state.previewName = centerName();
      else if (state.selected) state.previewName = state.selected;
      emit();
    },
    setSortMetric(m) { state.sortMetric = m; emit(); },
    setGroupBy(g) { state.groupBy = g; refresh(true); },
    setDensity(d) { state.density = d; refresh(); },
    toggleView3d() {
      state.view3d = !state.view3d;
      state.view = { tx: 0, ty: 0, k: null };
      refresh(true);
    },
    /** 正面に向ける経度。区画を押したときと、地球儀を回したときに動く。 */
    setPhi(p) { state.phi = p; emit(); },
    spinTo(lon) {
      // 最短回りで目標へ。何周も回らせない。
      let d = lon - state.phi;
      while (d > Math.PI) d -= 2 * Math.PI;
      while (d < -Math.PI) d += 2 * Math.PI;
      state.phi += d;
      emit();
    },
    /** 隣の区画へ一つ送る。経度は等分なので、送る量は常に同じ。 */
    spinStep(dir) {
      const list = derived.sectors || [];
      if (!list.length) return;
      const i = frontSectorIndex();
      const j = ((i + dir) % list.length + list.length) % list.length;
      actions.spinTo(list[j].lon);
    },
    toggleHideFrame() { state.hideFrame = !state.hideFrame; refresh(true); },
    clearPath() { state.pathFrom = null; refresh(); },
    toggleDeriv(n) {
      const s = new Set(state.derivOpen);
      s.has(n) ? s.delete(n) : s.add(n);
      state.derivOpen = s; emit();
    },
    hover(n) { if (state.hovered !== n) { state.hovered = n; emit(); } },
    toggleExpand(n) {
      const s = new Set(state.expanded);
      s.has(n) ? s.delete(n) : s.add(n);
      state.expanded = s; refresh();
    },
    collapseAll() { state.expanded = new Set(); refresh(); },
    setTrace(n) { state.traceTarget = state.traceTarget === n ? null : n; refresh(); },
    setEdgeMode(m) { state.edgeMode = m; refresh(); },
    setGranularity(g) { state.granularity = g; state.expanded = new Set(); refresh(); },
    setBaseDepth(d) { state.baseDepth = d; state.expanded = new Set(); refresh(); },
    setRefFilter(f) { state.refFilter = f; refresh(); },
    cycleRefFilter() {
      const order = ["all", "type", "value"];
      state.refFilter = order[(order.indexOf(state.refFilter) + 1) % order.length];
      refresh();
    },
    setQuery(q) { state.query = q; emit(); },
    setListMode(m) { state.listMode = m; emit(); },
    toggleTreeNode(prefix) {
      const s = new Set(state.treeClosed);
      s.has(prefix) ? s.delete(prefix) : s.add(prefix);
      state.treeClosed = s; emit();
    },
    toggleKind(k) {
      const s = new Set(state.kindFilter);
      s.has(k) ? s.delete(k) : s.add(k);
      state.kindFilter = s; refresh();
    },
    clearKinds() { state.kindFilter = new Set(); refresh(); },
    toggleOnlySorry() { state.onlySorry = !state.onlySorry; emit(); },
    setView(v) { state.view = v; emit(); },
    zoomBy(f, fit) {
      const cur = state.view.k == null ? fit : state.view.k;
      state.view = { ...state.view, k: Math.min(3, Math.max(0.12, cur * f)) };
      emit();
    },
    resetView() { state.view = { tx: 0, ty: 0, k: null }; emit(); },

    /* ピン留め */
    addPin(label) {
      const snap = snapshot();
      const p = { id: "p" + Date.now().toString(36), label: label || snap.center, ts: Date.now(), snap };
      state.pins = [p, ...state.pins].slice(0, 200);
      emit();
      LDR.onPinsChanged && LDR.onPinsChanged(state.pins);
      return p;
    },
    applyPin(id) {
      const p = state.pins.find((x) => x.id === id);
      if (p) applySnapshot(p.snap);
    },
    removePin(id) {
      state.pins = state.pins.filter((x) => x.id !== id);
      emit();
      LDR.onPinsChanged && LDR.onPinsChanged(state.pins);
    },
    setPins(pins) { state.pins = Array.isArray(pins) ? pins : []; emit(); },
    importPins(json) {
      let data;
      try { data = JSON.parse(json); } catch (e) { return { ok: false, msg: "JSON として読めません" }; }
      const arr = Array.isArray(data) ? data : data.pins;
      if (!Array.isArray(arr)) return { ok: false, msg: "pins 配列が見つかりません" };
      const seen = new Set(state.pins.map((p) => p.id));
      const add = arr.filter((p) => p && p.snap && !seen.has(p.id));
      state.pins = [...add, ...state.pins].slice(0, 200);
      emit();
      LDR.onPinsChanged && LDR.onPinsChanged(state.pins);
      return { ok: true, msg: `${add.length} 件を取り込みました` };
    },
    exportPins() {
      return JSON.stringify({ kind: "ldr-pins", version: 1, ts: Date.now(), pins: state.pins }, null, 2);
    },
  };

  /** いま正面を向いている区画の番号。経度が等分なので単純な最短距離で決まる。 */
  function frontSectorIndex() {
    const list = derived.sectors || [];
    let best = -1, bestAbs = Infinity;
    list.forEach((s, i) => {
      let d = s.lon - state.phi;
      while (d > Math.PI) d -= 2 * Math.PI;
      while (d < -Math.PI) d += 2 * Math.PI;
      if (Math.abs(d) < bestAbs) { bestAbs = Math.abs(d); best = i; }
    });
    return best;
  }
  function frontSector() {
    const i = frontSectorIndex();
    return i < 0 ? null : derived.sectors[i];
  }

  /** プレビューに出す宣言。追従なら選択中、固定なら中心。 */
  function previewName() {
    if (!state.previewFollow) return centerName();
    return state.previewName || state.selected || centerName();
  }

  LDR.store = {
    state, actions, subscribe, refresh, metrics, groupKeyOf, previewName, METRICS,
    lawInventory, frontSector, frontSectorIndex,
    get derived() { return derived; },
    centerName, effCenter, histCur, snapshot, applySnapshot,
    NODE_W, NODE_H, GEO, SECTORS,
  };
})(window.LDR = window.LDR || {});
