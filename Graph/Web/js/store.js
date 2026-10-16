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

    pathFrom: null,         // ここから中心までの経路を強調する
    derivOpen: new Set(),   // 導出図で開いている前提

    hist: { nodes: {}, order: [], curId: null, seq: 0 },
    pins: [],

    selected: null,         // 詳細に出す宣言（中心とは独立）
    traceTarget: null,      // 順序区間 [t, d] の t
    hovered: null,

    query: "",
    listMode: "tree",       // "tree" | "ns"
    groupBy: "subject",     // 部分グラフの束ね方: "subject" | "module" | "kind" | "none"
    treeClosed: new Set(),  // 一覧で畳んでいる枝の鍵（"md:…" はモジュール、"ns:…" は名前空間）
    kindFilter: new Set(),
    onlySorry: false,
    /* 派生（由来から導かれる宣言: casesOn / mk.inj / sizeOf_spec …）の開閉。
       閉じた由来の派生は、グラフでは由来の節点に畳まれ（辺に経由の札）、一覧では
       由来の行の下の小枝に畳まれる。開閉は一覧とグラフで共有する。
       状態はこの集合ただ一つ（既定は空＝全て畳む）。「全て開く」は集合を全入れにする
       操作であって、別の旗ではない（旗と集合の二重状態は、押しても効かない／勝手に
       開いているという見え方を生んだ。実測）。これとは別に、中心が派生ならその由来、
       経路表示の区間に派生が含まれればその由来を **強制的に** 開く（forcedOpen）。 */
    openClusters: new Set(),

    /* 右パネルのプレビュー。中心に固定するか、選んだものを追うかを切り替える。
       比較しながら読むときは追従、腰を据えて読むときは固定が要る。
       履歴は見た順の列と現在位置で持ち、戻る／進むができる（以前は直近を前に積むだけで、
       押しても元の位置に戻れず、グラフとも連動しなかった）。 */
    previewFollow: true,
    previewName: null,
    previewHist: [],        // 見た順（古い → 新しい）。最大 30 件
    previewPos: -1,         // previewHist の現在位置

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
  let cache = { nodesRef: null, decl: {}, mod: {}, defaultCenter: {}, metrics: {}, view: {}, contracted: {}, trace: {}, facetOrigins: null };

  /* ---------- 元の索引 ----------
     宣言の事実（直接依存・尺度・極小元・順序区間）は常にここで測る。 */
  function baseIndices() {
    if (cache.nodesRef !== state.nodes) {
      cache = { nodesRef: state.nodes, decl: {}, mod: {}, defaultCenter: {}, metrics: {}, laws: null,
                view: {}, contracted: {}, trace: {}, facetOrigins: null };
    }
    const em = state.edgeMode;
    if (!cache.decl[em]) cache.decl[em] = G.buildIndices(state.nodes, em);
    if (!cache.mod[em]) cache.mod[em] = G.buildModuleIndices(state.nodes, em);
    if (!cache.defaultCenter[em]) {
      // 既定中心は手書きの宣言から選ぶ。骨組み・派生・断片は候補にしない
      const skip = LDR.roles ? (n) => {
        const nd = state.nodes[n];
        return LDR.roles.roleOf(n, nd) === "frame" || (!!nd.originRel && nd.originRel !== "member");
      } : null;
      cache.defaultCenter[em] = G.pickDefaultCenter(state.nodes, cache.decl[em], skip);
    }
    if (!cache.facetOrigins) {
      // 派生を持つ由来の集合。「全て開く」はこれを openClusters に入れる操作
      const s = new Set();
      for (const nd of Object.values(state.nodes)) {
        if (nd.originRel === "facet" && nd.origin && state.nodes[nd.origin]) s.add(nd.origin);
      }
      cache.facetOrigins = s;
    }
    return { decl: cache.decl[em], mod: cache.mod[em], defaultCenter: cache.defaultCenter[em], facetOrigins: cache.facetOrigins };
  }

  /* ---------- 順序区間 [t, c] = ↑t ∩ ↓c ----------
     経路表示の区間は **元のグラフ** で取る。表示用の商（派生を畳んだグラフ）で取ると、
     閉じた派生の中身だけを通る経路（`pair_inj` → `mk.inj` → `id`）や、極小元そのものが
     閉じた派生（`Exists.rec`）のとき区間が空になり、極小元を押しても何も起きない
     （実測。極小元 min(↓c) は元のグラフで取っているので、両者が食い違っていた）。
     区間は中心・対象・辺の種類だけで決まるので記憶化する。 */
  function traceInterval() {
    const t = state.traceTarget;
    if (!t) return null;
    const b = baseIndices();
    const c = effCenter();
    if (!c) return null;
    const k = state.granularity + "|" + state.edgeMode + "|" + c + "|" + t;
    if (!(k in cache.trace)) {
      if (Object.keys(cache.trace).length > 32) cache.trace = {};
      const idx = state.granularity === "module" ? b.mod : b.decl;
      cache.trace[k] = G.orderInterval(c, t, idx.dep, idx.ref, 64);
    }
    return cache.trace[k];
  }

  /* ---------- 由来の強制開放 ----------
     商を取る側（表示）が、元のグラフで決めた事実（中心・区間）を必ず含むように、
     開閉集合を最小限だけ広げる。
       ・中心が派生なら、その由来（中心は必ず可視）
       ・経路表示の区間に派生 g が含まれれば、その由来 π(g)（区間の像が節点として現れる）
     利用者の開閉（openClusters）とは独立で、押しても閉じない（理由は toggleCluster が返す）。 */
  function forcedOpen() {
    const set = new Set();
    if (state.granularity !== "decl") return set;
    const nodes = state.nodes;
    const own = (n) => {
      const nd = nodes[n];
      if (nd && nd.originRel === "facet" && nd.origin && nodes[nd.origin]) set.add(nd.origin);
    };
    own(centerName());
    const iv = traceInterval();
    if (iv) for (const n of iv) own(n);
    return set;
  }
  function clusterOpen(o, forced) {
    return state.openClusters.has(o) || forced.has(o);
  }
  function openSignature(forced) {
    const f = forced || forcedOpen();
    return [...state.openClusters].sort().join(",") + "|" + [...f].sort().join(",");
  }

  function indices() {
    const b = baseIndices();
    const em = state.edgeMode;
    /* 表示用の有効グラフ（断片の埋め戻し・派生の畳み込み。graph.effectiveNodes）。
       開閉状態（利用者の集合＋強制開放）ごとに作り直す。 */
    const forced = forcedOpen();
    const vk = em + "|" + openSignature(forced);
    if (!cache.view[vk]) {
      if (Object.keys(cache.view).length > 8) { cache.view = {}; cache.contracted = {}; }
      const eff = G.effectiveNodes(state.nodes, (o) => clusterOpen(o, forced));
      cache.view[vk] = {
        key: vk, nodes: eff.nodes, idx: G.buildIndices(eff.nodes, em),
        via: eff.via, facetCount: eff.facetCount, partCount: eff.partCount,
      };
    }
    return Object.assign({}, b, { view: cache.view[vk], forced });
  }

  /* ---------- 依存の尺度 ----------

     直接依存の本数は「依存の少ない順」にならない。c が d の依存先でも
     deg(c) > deg(d) が起こり得るので、その並びは依存順序と両立しない。
     ここでは順序と両立する量だけを持つ。

       closure  |↓d|        総仮定量。c ≺ d ⇒ m(c) < m(d) なので昇順は線形拡大になる。
       depth    最長導出鎖   何段の導出を経ているか。これも狭義に単調。
       minimal  |min(↓d)|   必要な原始要素の数。c ≺ d ⇒ m(c) ≤ m(d) の広義単調に
                            留まるので、並べ替えには使わない（--decl の参考値）。

     右パネルの依存一覧は closure の昇順で並べ、ldr_check は mono な尺度について
     破れ 0 を検査する。 */
  const METRICS = {
    closure: { ja: "総仮定量 |↓d|", mono: true },
    depth:   { ja: "導出鎖の深さ",  mono: true },
    minimal: { ja: "極小仮定の数",  mono: false },
  };

  function metrics() {
    baseIndices();                   // nodes が変われば cache ごと入れ替わる
    const em = state.edgeMode;
    if (!cache.metrics) cache.metrics = {};
    if (!cache.metrics[em]) {
      const idx = cache.decl[em];
      const names = Object.keys(state.nodes);
      const cs = G.closureStats(idx.dep, names);
      const depth = G.chainDepths(idx.dep, names);
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
        minimal: cs ? cs.minimal : null,    // 代用は無い。無ければ未計算として扱う
        depth, hered,
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
    baseIndices();
    if (cache.laws) return cache.laws;
    const rows = new Map();          // 関係名 → { law → [宣言名], pairs }
    for (const [n, nd] of Object.entries(state.nodes)) {
      if (!nd.shape || !nd.shapeRel) continue;
      if (nd.usesSorry) continue;    // sorry の主張を「証明済みの法則」として数えない
      // 法則は命題である。型クラスのインスタンス(C α α 等)は構文上 refl の形を
      // 持つがデータであって証明ではない(自己解析で MonadLiftT 等の行として実測)。
      if (!nd.isProp) continue;
      // 在庫は「この対象が証明したもの」。外部（core / Mathlib）と内部補助は数えない。
      if (nd.external || nd.internal) continue;
      // 派生・断片（injEq / sizeOf_spec / _proof_<i> …）は Lean が作った定理であって、対象が証明した法則ではない
      if (nd.originRel === "facet" || nd.originRel === "part") continue;
      /* 行の鍵は 関係 × 担い手の型。頭部定数だけだと `LE.le` の反射（Nat）と
         推移（Int）が同じ行に合流し、無い構造を「全順序」と判断してしまう。
         多相な主張（shapeType が空）は型を持たない行になる。 */
      const rel = nd.shapeRel, type = nd.shapeType || "";
      const key = type ? rel + "@" + type : rel;
      if (!rows.has(key)) rows.set(key, { key, rel, type, total: 0, laws: {}, pairs: {} });
      const row = rows.get(key);
      (row.laws[nd.shape] || (row.laws[nd.shape] = [])).push(n);
      // 二演算法則(吸収・分配)は相方、単調はその関係を shapeRel2 に持つ。対として控える
      if ((nd.shape === "absorb" || nd.shape === "distrib" || nd.shape === "mono") && nd.shapeRel2) {
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
    const byKey = new Map(list.map((r) => [r.key, r]));
    const keyOf = (rel, type) => (type ? rel + "@" + type : rel);
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
          const rg = byKey.get(keyOf(g, r.type));   // 相方は同じ担い手の型の行

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

  /** 部分グラフを束ねる鍵。主題は「何についての宣言か」を Lean 側が出したもの。
      パッケージはモジュール名の先頭成分（pkg.packageOf。core は一つに束ねる）。 */
  function groupKeyOf(name) {
    const nd = state.nodes[name];
    if (!nd) return "";
    switch (state.groupBy) {
      case "module":  return nd.module || "";
      case "kind":    return nd.kind || "";
      case "subject": return nd.subject || nd.head || "";
      case "package": return LDR.pkg ? LDR.pkg.packageOf(nd.module) : "";
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
    /* 既定中心は元の索引だけで決まる。中心（centerName）が強制開放の計算に要るので、
       表示用の商（indices）を作る前に確定させる。 */
    const b = baseIndices();
    derived.defaultCenter = b.defaultCenter;
    const ix = indices();
    /* 錐は表示用の有効グラフ（view）で組む。宣言の事実（直接依存・尺度・極小元・区間）は
       元の索引 decl で測る。モジュール粒度は元の節点から。 */
    const view = ix.view;
    const idx = state.granularity === "module" ? ix.mod : view.idx;
    derived.declIdx = ix.decl; derived.modIdx = ix.mod; derived.idx = idx; derived.viewIdx = view.idx;
    derived.via = view.via; derived.facetCount = view.facetCount; derived.partCount = view.partCount;
    derived.forcedOpen = ix.forced;

    const c = effCenter();
    derived.center = c;
    derived.cones = [];
    derived.posAll = {};
    derived.edges = [];
    derived.labels = {};
    derived.more = {};
    derived.bbox = { x0: -200, x1: 200, y0: -120, y1: 120 };
    // 早期 return でも前のデータの値を残さない
    derived.trueMinimal = []; derived.minimalSet = new Set(); derived.frontier = [];
    derived.fullDownSize = 0; derived.highlight = null; derived.traceUnreachable = null;
    derived.pathSet = null; derived.edgeKindOverlay = null; derived.facetReach = {};
    if (!c || !idx.dep) return;

    /* min(↓d) は宣言 d の性質であって、いま何を展開しているかとは無関係。
       可視集合から計算すると初期表示で空になり、意味も違ってしまう。
       元のグラフで測る（断片・派生の畳み込みの影響を受けない）。 */
    const rawDep = state.granularity === "module" ? idx.dep : ix.decl.dep;
    const fullDep = G.reachable(c, rawDep, 64);
    const mf = G.minimalAndFrontier(Object.keys(fullDep), rawDep);
    derived.trueMinimal = mf.trueMinimal;
    derived.minimalSet = new Set(mf.trueMinimal);   // 描画は毎フレーム引くので集合で持つ
    derived.frontier = mf.frontier;
    derived.fullDownSize = Object.keys(fullDep).length;

    /* 由来ごとに「この中心から見える派生の数」。派生 g は中心の依存閉包 ↓c か参照閉包 ↑c に
       入っているときだけ、由来を開けば節点として現れ得る。グラフの札 `+k` はこの k を出す
       （総数 n を出すと「開けば n 件現れる」という嘘になる。`Params +8` を開いても描画が
       増えなかった実測）。一覧は由来の下に全ての派生を出すので総数 facetCount を使う。 */
    if (state.granularity === "decl") {
      const fullRef = G.reachable(c, ix.decl.refAll, 64);
      const reach = {};
      for (const [n, nd] of Object.entries(nodes)) {
        if (nd.originRel !== "facet" || !nd.origin || !nodes[nd.origin]) continue;
        if (n in fullDep || n in fullRef) reach[nd.origin] = (reach[nd.origin] || 0) + 1;
      }
      derived.facetReach = reach;
    }

    /* 経路表示中はその区間（元のグラフで取った [t, c]。traceInterval）を強制的に開く。
       区間に派生が含まれれば forcedOpen がその由来を開いているので、区間の各節点は
       商の中に像を持つ（断片は由来に埋め戻されているので、両端が区間に入る辺として現れる）。
       区間が空（= 読み込んだ範囲に経路が無い）なら強調は掛けない。空の集合をそのまま
       渡すと「区間外を暗くする」規則で全てが暗くなり、何も伝わらない（自己解析で
       `double_eq` の `propext` に実測）。空だった事実は traceUnreachable で表に出す。 */
    let openSet = state.expanded;
    if (state.traceTarget) {
      const interval = traceInterval();
      if (interval && interval.size) {
        derived.highlight = interval;
        openSet = new Set([...state.expanded, ...interval]);
      } else {
        derived.traceUnreachable = state.traceTarget;
      }
    }

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
      const kindDep = (u, v) => idx.edgeKind[u + " " + v] || "type";
      const kindRef = (u, v) => (idx.refKind && idx.refKind[u + " " + v]) || "type";
      const refAdj0 = refAdj || {};
      if (!cache.contracted) cache.contracted = {};
      // 縮約は有効グラフの上で行うので、開閉状態（view.key）も鍵に入れる
      const ck = state.edgeMode + "|" + state.refFilter + "|" + view.key;
      if (!cache.contracted[ck]) {
        cache.contracted[ck] = {
          dep: G.contractThrough(idx.dep, hidden, names, kindDep),
          ref: G.contractThrough(refAdj0, hidden, names, kindRef),
        };
      }
      const ct = cache.contracted[ck];
      depAdj = ct.dep.adj; refAdj = ct.ref.adj;
      let depKind = ct.dep.kind, refKind = ct.ref.kind;
      /* 中心そのものが骨組みの名前（`.injEq` / `.rec` / `match_*` 等）のとき、縮約は
         中心を「通り抜ける側」に置き、出辺を持たせない（両錐が空になる。フィクスチャの
         `Pair.mk.injEq` を中心にして実測）。中心は利用者が選んで見ている節点なので
         必ず可視として扱い、中心の出辺だけをその場で縮約して上書きする。縮約表の
         キャッシュは中心に依存しないまま保つ。 */
      if (hidden(c)) {
        const d = G.contractNode(idx.dep, hidden, c, kindDep);
        const r = G.contractNode(refAdj0, hidden, c, kindRef);
        depAdj = Object.assign({}, depAdj, { [c]: d.adj });
        refAdj = Object.assign({}, refAdj, { [c]: r.adj });
        depKind = Object.assign({}, depKind, d.kind);
        refKind = Object.assign({}, refKind, r.kind);
      }
      derived.edgeKindOverlay = { dep: depKind, ref: refKind };
    }
    const specs = [
      { id: "dep", adj: depAdj, sector: SECTORS.dep },
      { id: "ref", adj: refAdj || {}, sector: SECTORS.ref },
    ];

    const claimed = new Set([c]);
    for (const sp of specs) {
      const vis = G.visibleClosure(c, sp.adj, state.baseDepth, openSet);
      const lv = G.longestPathLevels(c, sp.adj, vis.hop);
      // 種別フィルタと、別の錐が既に取ったノードを層から落とす。
      const layers = lv.layers.map((L, l) => (l === 0 ? L : L.filter((n) => !claimed.has(n) && passes(n))));
      const cone = G.layoutCone({
        layers, adj: sp.adj, th0: sp.sector.th0, th1: sp.sector.th1,
        groupOf: state.groupBy === "none" ? null : groupKeyOf,
        pin: openSet,   // 経路表示の区間と手動展開は、層上限より優先して描く
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
          // 経由: 畳まれた派生・断片を通って来た辺（依存の向きは「依存する側 → 依存先」）
          const viaKey = cone.id === "dep" ? kk : v + " " + u;
          derived.edges.push({
            u, v, cone: cone.id,
            kind: cone.id === "dep"
              ? ((ov && ov.dep[kk]) || idx.edgeKind[kk] || "type")
              : ((ov && ov.ref[kk]) || (idx.refKind && idx.refKind[kk]) || "type"),
            via: (derived.via && derived.via[viaKey]) || null,
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

  function key() {
    return [
      Object.keys(state.nodes).length, state.edgeMode, state.granularity,
      state.baseDepth, state.refFilter, state.groupBy, state.density, state.hideFrame,
      state.pathFrom,
      [...state.expanded].sort().join(","),
      centerName(), state.traceTarget, [...state.kindFilter].sort().join(","),
      openSignature(),
    ].join("|");
  }

  function refresh(force) {
    const k = key();
    if (force || k !== lastKey) { lastKey = k; recompute(); }
    emit();
  }

  /* ---------- 閲覧状態のピン留め ---------- */
  /* 読み込んだデータの同一性。ピンは別のデータでは意味を持たないので、保存時に控えて
     適用時に照合する。宣言数と先頭の宣言名で、実用上は十分に区別できる。 */
  function datasetId() { return state.order.length + ":" + (state.order[0] || ""); }

  function snapshot() {
    return {
      dataset: datasetId(),
      center: centerName(),
      expanded: [...state.expanded],
      edgeMode: state.edgeMode,
      granularity: state.granularity,
      baseDepth: state.baseDepth,
      refFilter: state.refFilter,
      groupBy: state.groupBy,
      previewFollow: state.previewFollow,
      previewName: state.previewName,
      traceTarget: state.traceTarget,
      selected: state.selected,
      kindFilter: [...state.kindFilter],
      openClusters: [...state.openClusters],
      view: { ...state.view },
    };
  }

  /* 復元の結果を {ok, msg} で返す。別のデータのピン、無くなった中心は黙って
     見かけだけ戻すのではなく、何が戻せなかったかを呼び出し元（toast）に伝える。 */
  function applySnapshot(s) {
    if (!s) return { ok: false, msg: "ピンの内容がありません" };
    let msg = null;
    if (s.dataset && s.dataset !== datasetId()) msg = "別のデータで作ったピンです。戻せる範囲で戻しました";
    state.edgeMode = s.edgeMode || "all";
    state.granularity = s.granularity || "decl";
    state.baseDepth = s.baseDepth || 1;
    // 旧いピン（下錐を二つに割っていた頃）も読めるようにしておく
    state.refFilter = s.refFilter || (s.showRefValue === false ? "type" : "all");
    state.groupBy = s.groupBy || "subject";
    if (s.previewFollow !== undefined) state.previewFollow = !!s.previewFollow;
    state.previewName = s.previewName || null;
    state.expanded = new Set(s.expanded || []);
    state.kindFilter = new Set(s.kindFilter || []);
    state.traceTarget = s.traceTarget || null;
    state.selected = s.selected || null;
    state.openClusters = new Set(s.openClusters || []);
    // 旧いピン（全開を旗で持っていた頃）は、集合を全入れにして読む
    if (s.openAll) state.openClusters = new Set(baseIndices().facetOrigins);
    state.view = s.view ? { ...s.view } : { tx: 0, ty: 0, k: null };
    if (s.center) {
      if (state.nodes[s.center]) histPush(s.center);
      else msg = `中心 ${s.center} はこのデータにありません。中心以外を戻しました`;
    }
    refresh(true);
    return { ok: !msg, msg: msg || "ピンの状態に戻しました" };
  }

  /* ---------- プレビューの履歴 ----------
     見た宣言を順に積む。現在位置より先（戻った後に捨てた枝）は、新しい宣言を見た時点で切る
     （ブラウザの履歴と同じ）。同じ宣言は列に一つだけ置く。 */
  function previewPush(n) {
    if (!n) return;
    const h = state.previewHist;
    if (h[state.previewPos] === n) { state.previewName = n; return; }
    const next = h.slice(0, state.previewPos + 1).filter((x) => x !== n);
    next.push(n);
    state.previewHist = next.slice(-30);
    state.previewPos = state.previewHist.length - 1;
    state.previewName = n;
  }
  /* 履歴の位置を動かしたときの共通処理。見ている宣言を選択にもして、グラフで経路を光らせる。
     固定中でも履歴を動かしたなら見たいのはその宣言なので、追従に切り替える。 */
  function previewGoto(pos) {
    const n = state.previewHist[pos];
    if (!n) return;
    state.previewPos = pos;
    state.previewName = n;
    state.previewFollow = true;
    state.selected = n;
    state.pathFrom = n;
    refresh();
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
      state.previewName = null; state.previewHist = []; state.previewPos = -1;
      state.view = { tx: 0, ty: 0, k: null };
      refresh(true);
      // 履歴は既定中心から始める（最初に見ているのはそれ。戻る先として残す）
      if (derived.center && state.nodes[derived.center]) { previewPush(derived.center); emit(); }
      if (!opts || !opts.silent) LDR.onDataLoaded && LDR.onDataLoaded(text);
    },
    navigate(n) {
      if (!n) return;
      histPush(n);
      state.expanded = new Set(); state.traceTarget = null;
      state.selected = n;
      previewPush(n);
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
      if (state.previewFollow && n) previewPush(n);
      refresh();
    },
    /** 履歴のチップを押す。その宣言を見て、選択にもする（グラフで経路が光る）。 */
    preview(n) {
      if (!n) return;
      const i = state.previewHist.indexOf(n);
      if (i >= 0) previewGoto(i);
      else { previewPush(n); previewGoto(state.previewPos); }
    },
    previewBack() { if (state.previewPos > 0) previewGoto(state.previewPos - 1); },
    previewForward() { if (state.previewPos < state.previewHist.length - 1) previewGoto(state.previewPos + 1); },
    setPreviewFollow(v) {
      state.previewFollow = !!v;
      if (!state.previewFollow) state.previewName = centerName();
      else if (state.selected) previewPush(state.selected);
      emit();
    },
    setGroupBy(g) { state.groupBy = g; refresh(true); },
    setDensity(d) { state.density = d; refresh(); },
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
    setListMode(m) { if (m === "tree" || m === "ns") { state.listMode = m; emit(); } },
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
    /* 派生の開閉（一覧とグラフで共有）。強制開放中の由来は押しても閉じないので、
       黙って無視せず理由を返す（呼び出し元が通知に出す）。 */
    toggleCluster(o) {
      if (!o) return { ok: false, msg: "" };
      if (forcedOpen().has(o)) {
        const nd = state.nodes[centerName()];
        const why = nd && nd.originRel === "facet" && nd.origin === o
          ? "中心の由来なので、中心が派生であるあいだは開いたままにします"
          : "経路表示の区間に派生が含まれるので、経路表示のあいだは開いたままにします";
        return { ok: false, msg: `${o.split(".").slice(-1)[0]} の派生: ${why}` };
      }
      const s = new Set(state.openClusters);
      s.has(o) ? s.delete(o) : s.add(o);
      state.openClusters = s; refresh();
      return { ok: true, msg: "" };
    },
    /* 「全て開く」は集合の全入れ／全消し。旗ではないので個別の開閉と干渉しない */
    setOpenAll(v) {
      state.openClusters = v ? new Set(baseIndices().facetOrigins) : new Set();
      refresh();
    },
    toggleOpenAll() { actions.setOpenAll(!allFacetsOpen()); },
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
      if (!p) return { ok: false, msg: "ピンが見つかりません" };
      return applySnapshot(p.snap);
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

  /** プレビューに出す宣言。追従なら選択中、固定なら中心。 */
  function previewName() {
    if (!state.previewFollow) return centerName();
    return state.previewName || state.selected || centerName();
  }

  /** 由来 o の派生が開いているか（個別、または強制）。一覧とグラフが同じ判定を使う。 */
  function isClusterOpen(o) { return clusterOpen(o, forcedOpen()); }
  /** 由来 o が強制的に開いているか（中心が派生／経路表示の区間に派生）。押しても閉じない。 */
  function isClusterForced(o) { return forcedOpen().has(o); }
  /** 派生を持つ全ての由来が（利用者の集合として）開いているか。「全て開く」の ☑ の判定。 */
  function allFacetsOpen() {
    const all = baseIndices().facetOrigins;
    if (!all.size) return false;
    for (const o of all) if (!state.openClusters.has(o)) return false;
    return true;
  }
  /** 派生を持つ由来の数（「全て開く (N)」の N は派生の総数なので別。こちらは由来の数）。 */
  function facetOriginCount() { return baseIndices().facetOrigins.size; }

  LDR.store = {
    state, actions, subscribe, refresh, metrics, groupKeyOf, previewName, METRICS,
    lawInventory, isClusterOpen, isClusterForced, allFacetsOpen, facetOriginCount,
    openSignature: () => openSignature(),
    get derived() { return derived; },
    centerName, effCenter, histCur, snapshot, applySnapshot,
    NODE_W, NODE_H, GEO, SECTORS,
  };
})(window.LDR = window.LDR || {});
