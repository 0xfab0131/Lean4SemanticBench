/* ============================================================
   js/graph.js — 依存グラフの算法
   UI から独立した純関数群。global 名前空間 LDR に載せる。
   ============================================================ */
(function (LDR) {
  "use strict";

  /* ---------- JSON Lines の読み込み ---------- */
  /* Lean の Name.anonymous は文字列化すると "[anonymous]" になる。
     群の鍵や関係名として素通しすると「[anonymous]」という偽の群が生まれる
     (自己解析で 74 ノードの区画として実測)。読み込み時に空へ正規化する。 */
  const deanon = (s) => (s === "[anonymous]" ? "" : s);

  /* ---------- 由来の互換シム ----------
     新形式のレポートは Lean 側が環境の事実から決めた `origin` / `originKind` / `originRel` を
     持つ（Basic.lean `originOf`）。欄の無い旧形式だけ、名前の形から推定する。
     名前による推定はここに閉じ込め、他の場所では欄だけを見る。 */
  function legacyOrigin(name) {
    const i = name.lastIndexOf(".");
    if (i < 0) return null;
    const p = name.slice(0, i), s = name.slice(i + 1);
    let kind = null, rel = null;
    if (/^(rec|recOn|casesOn|brecOn|below|ndrec)$/.test(s)) { kind = s; rel = "facet"; }
    else if (/^(noConfusion|noConfusionType|ctorIdx|inj|injEq|hinj|sizeOf_spec)$/.test(s)) { kind = s; rel = "facet"; }
    else if (/^(eq_\d+|eq_def|eq_unfold)$/.test(s)) { kind = "eqn"; rel = "facet"; }
    else if (s === "_sizeOf_inst") { kind = "sizeOf_inst"; rel = "facet"; }
    else if (s.startsWith("_sizeOf_")) { kind = "sizeOf"; rel = "facet"; }
    else if (/^match_\d+/.test(s)) { kind = "matcher"; rel = "part"; }
    else if (/^(_proof|proof_|_sparseCasesOn|_unary|_mutual)/.test(s)) { kind = "proof"; rel = "part"; }
    else if (s.startsWith("_") || /^\d+$/.test(s)) { kind = "internal"; rel = "part"; }
    if (!rel) return null;
    // 由来 = 内部名でない最も近い接頭辞
    let o = p;
    while (o && /(^|\.)(_[^.]*|match_\d+|proof_\d+|\d+)$/.test(o)) o = o.slice(0, Math.max(0, o.lastIndexOf(".")));
    return o ? { origin: o, originKind: kind, originRel: rel } : null;
  }

  function parseJsonl(text) {
    const nodes = {};
    const errors = [];
    const order = [];
    const legacy = [];       // origin 欄を持たない行（旧形式）
    text.split("\n").map((l) => l.trim()).filter(Boolean).forEach((line, i) => {
      try {
        const o = JSON.parse(line);
        if (!o.name) throw new Error("name フィールドがありません");
        // 旧形式（dependsOn のみ）との後方互換
        const typeDeps = o.typeDeps ?? o.dependsOn ?? [];
        const valueDeps = o.valueDeps ?? [];
        nodes[o.name] = {
          name: o.name,
          kind: o.kind ?? "unknown",
          module: o.module ?? "(unknown)",
          line: o.line ?? 0,
          lineEnd: o.lineEnd ?? 0,
          // 原文（宣言範囲の行をソースから切り出したもの）。無ければ古い形式か、ソースが読めなかった
          source: o.source ?? "",
          isProp: !!o.isProp,
          isInstance: !!o.isInstance,
          reducibility: o.reducibility ?? "",
          usesSorry: !!o.usesSorry,
          axioms: o.axioms ?? [],
          typeDeps, valueDeps,
          depModules: o.depModules ?? null,
          members: o.members ?? [],
          typeString: o.typeString ?? "",
          docString: o.docString ?? "",
          // Lean 側が分解した束縛と結論。無ければ古い形式のレポート。
          binders: o.binders ?? [],
          conclusion: o.conclusion ?? "",
          head: deanon(o.head ?? ""),
          subject: deanon(o.subject ?? ""),
          conclArgs: o.conclArgs ?? [],
          shape: o.shape ?? "",
          shapeRel: deanon(o.shapeRel ?? ""),
          shapeRel2: deanon(o.shapeRel2 ?? ""),
          shapeType: deanon(o.shapeType ?? ""),
          valueString: o.valueString ?? "",
          numExplicit: o.numExplicit ?? 0,
          numImplicit: o.numImplicit ?? 0,
          numInst: o.numInst ?? 0,
          numHyp: o.numHyp ?? 0,
          numUniverse: o.numUniverse ?? 0,
          typeSize: o.typeSize ?? 0,
          valueSize: o.valueSize ?? 0,
          /* scope の三値。"target" は対象（一覧に出る）、"internal" は対象モジュール内の
             内部補助（_proof_* 等。一覧には出さないが対象の一部として依存を持つ）、
             "external" は対象の外で定義され参照だけされている宣言（一段だけ。
             型と種別は入っているので、補題か語彙かの判定はできる）。 */
          external: o.scope === "external",
          internal: o.scope === "internal",
          /* 由来（Basic.lean `originOf`）。origin = この宣言を作った元の宣言、
             originRel = member（成員）/ facet（派生）/ part（断片）/ ""（手書き）。 */
          origin: deanon(o.origin ?? ""),
          originKind: o.originKind ?? "",
          originRel: o.originRel ?? "",
        };
        if (o.originRel === undefined) legacy.push(o.name);
        if (!o.scope || o.scope === "target") order.push(o.name);
      } catch (e) {
        errors.push(`${i + 1} 行目: ${e.message}`);
      }
    });
    // 旧形式: 名前から由来を推定する（由来がレポート内に無ければ付けない）
    for (const n of legacy) {
      const l = legacyOrigin(n);
      if (l && nodes[l.origin]) Object.assign(nodes[n], l);
    }
    // レポートに含まれない参照先を外部ノードとして補う。
    // 最小の仮定はほぼこちら側に現れるので必須。
    for (const info of Object.values({ ...nodes })) {
      for (const dep of [...info.typeDeps, ...info.valueDeps]) {
        if (!nodes[dep]) {
          nodes[dep] = {
            name: dep, kind: "external", module: "(範囲外)", line: 0, lineEnd: 0, source: "",
            isProp: false, isInstance: false, reducibility: "",
            usesSorry: false, axioms: [], typeDeps: [], valueDeps: [],
            depModules: null, members: [], typeString: "", docString: "",
            binders: [], conclusion: "", head: "", subject: "", conclArgs: [],
            shape: "", shapeRel: "", shapeRel2: "", shapeType: "", valueString: "",
            numExplicit: 0, numImplicit: 0, numInst: 0, numHyp: 0, numUniverse: 0,
            typeSize: 0, valueSize: 0, external: true, internal: false,
            origin: "", originKind: "", originRel: "",
          };
        }
      }
    }
    return { nodes, errors, order };
  }

  /* ---------- 有効グラフ（由来による商） ----------

     由来の写像 π を使って、表示用の節点集合を作る。関係ごとに扱いが違う。

       断片 part（`_proof_<i>` / `match_<i>`）: 由来の証明・本体の一部。
         由来 o 自身からの参照は **埋め戻す**（断片の依存を o の値依存に合流）。
         他の節点 u からの参照は o への参照に付け替える（経由として控える）。
         断片の節点は消える。到達可能性は保たれる。
       派生 facet（`casesOn` / `inj` / `sizeOf_spec` …）: 由来から導かれる別の宣言。
         由来 o が閉じているとき、u → g を u → o に **畳み**、経由 g を控える。
         g 自身の出辺は出さない（o の依存に混ぜると「構成子が And に依存する」嘘になる）。
         o が開いていれば g は通常の節点。
       成員 member（構成子・射影）: 通常の節点。

     返り値 nodes は buildIndices にそのまま渡せる（typeDeps / valueDeps の排他性を保つ）。
     via["u v"] は u → v が経由した宣言の列。facetCount / partCount は由来ごとの件数。 */
  function effectiveNodes(nodes, isOpen) {
    const has = (n) => !!nodes[n];
    const relOf = (n) => (nodes[n] && nodes[n].originRel) || "";
    const orgOf = (n) => nodes[n].origin;
    const hasOrigin = (n) => has(n) && !!nodes[n].origin && has(nodes[n].origin);
    const isPart = (n) => relOf(n) === "part" && hasOrigin(n);
    const isClosedFacet = (n) => relOf(n) === "facet" && hasOrigin(n) && !isOpen(orgOf(n));

    const facetCount = {}, partCount = {};
    for (const [n, nd] of Object.entries(nodes)) {
      if (!hasOrigin(n)) continue;
      if (nd.originRel === "facet") facetCount[nd.origin] = (facetCount[nd.origin] || 0) + 1;
      else if (nd.originRel === "part") partCount[nd.origin] = (partCount[nd.origin] || 0) + 1;
    }

    /* 節点 owner から見た、断片 g を通り抜けた先（断片でない依存）。断片は由来にかかわらず
       辿り続ける。Lean は `match` の補助関数を同じ形の match を持つ別の宣言でも再利用する
       （自己解析で `relShape` が `asBinApp.match_1` を使うのを実測）。他人の断片をその由来へ
       付け替えると、使っていない宣言に到達して見える。中身を辿るのが正しい。
       他人の断片を通ったことは経由（via）に控える（自分の断片は控えない）。
       記憶化の鍵は owner と g。 */
    const partMemo = new Map();
    const partClosure = (g, owner) => {
      const key = owner + " " + g;
      if (partMemo.has(key)) return partMemo.get(key);
      const res = [], seen = new Set([g]);
      const stack = [[g, orgOf(g) === owner ? [] : [g]]];
      while (stack.length) {
        const [x, path] = stack.pop(), nx = nodes[x];
        if (!nx) continue;
        for (const d of [...nx.typeDeps, ...nx.valueDeps]) {
          if (seen.has(d)) continue;
          seen.add(d);
          if (!isPart(d)) res.push({ d, via: path });
          else stack.push([d, orgOf(d) === owner ? path : path.concat([d])]);
        }
      }
      partMemo.set(key, res);
      return res;
    };

    const via = {};
    const out = {};
    for (const [n, nd] of Object.entries(nodes)) {
      if (isPart(n) || isClosedFacet(n)) continue;          // 消える節点
      const t = new Set(), v = new Set();
      const put = (d, set, viaList) => {
        let target = d;
        if (isClosedFacet(d)) { target = orgOf(d); viaList = viaList.concat([d]); }
        if (target === n) return;
        set.add(target);
        if (viaList.length) { const k = n + " " + target; (via[k] || (via[k] = [])).push(...viaList); }
      };
      const add = (d, set) => {
        if (!isPart(d)) { put(d, set, []); return; }
        for (const x of partClosure(d, n)) put(x.d, v, x.via);   // 断片: 埋め戻し（値依存）
      };
      for (const d of nd.typeDeps) add(d, t);
      for (const d of nd.valueDeps) add(d, v);
      for (const x of t) v.delete(x);                           // 型依存と値依存の排他性を保つ
      out[n] = Object.assign({}, nd, { typeDeps: [...t], valueDeps: [...v] });
    }
    for (const k of Object.keys(via)) via[k] = [...new Set(via[k])];
    return { nodes: out, via, facetCount, partCount };
  }

  /* ---------- 隣接構造 ----------

     四つの関係を持つ。前二つは向きが同じで、後二つは Lean 側が
     typeDeps / valueDeps を排他的に分離していることを利用した「逆向きの二分割」。

       dep[n]    n が依存する宣言。edgeMode="type" なら型依存のみ。
                 （定理の証明項に現れる依存はカーネル検査済みなので、
                   主張の構造を見るときは刈り込んでよい。）
       ref[n]    n を使う宣言すべて。refType ∪ refValue。
       refType[n]  n を「主張（型）」に含む宣言。
                   e ∈ refType[d] は「e は d についての性質・結果」を意味する。
       refValue[n] n を「証明（値）」でのみ使う宣言。
                   e ∈ refValue[d] は「e は d を道具として呼び出しただけ」を意味する。

     Lean 側 directDepsOfCore が、型にも値にも現れる定数を型側にのみ入れるので、
     refType と refValue は交わらない。この排他性がそのまま二つの錐の独立性になる。 */
  function buildIndices(nodes, edgeMode) {
    const dep = {}, ref = {}, refType = {}, refValue = {}, refAll = {};
    const edgeKind = {}, refKind = {};
    const names = Object.keys(nodes);
    for (const n of names) { dep[n] = []; ref[n] = []; refType[n] = []; refValue[n] = []; refAll[n] = []; }
    for (const n of names) {
      const info = nodes[n];
      const seen = new Set();
      const push = (d, kind) => {
        if (d === n || !nodes[d] || seen.has(d)) return;
        seen.add(d);
        dep[n].push(d);
        ref[d].push(n);
        edgeKind[n + " " + d] = kind;
      };
      for (const d of info.typeDeps) push(d, "type");
      if (edgeMode !== "type") for (const d of info.valueDeps) push(d, "value");
      // 逆向きの二分割は edgeMode に依らない。刈り込みの根拠（証明無関係性）は
      // 「自分が何に依存するか」の側の話であって、「誰が自分を使うか」には効かない。
      for (const d of info.typeDeps) {
        if (!nodes[d] || d === n) continue;
        refType[d].push(n); refAll[d].push(n); refKind[d + " " + n] = "type";
      }
      for (const d of info.valueDeps) {
        if (!nodes[d] || d === n || refKind[d + " " + n]) continue;
        refValue[d].push(n); refAll[d].push(n); refKind[d + " " + n] = "value";
      }
    }
    return { dep, ref, refType, refValue, refAll, edgeKind, refKind };
  }

  function buildModuleIndices(nodes, edgeMode) {
    const count = {}, dep = {}, ref = {};
    for (const info of Object.values(nodes)) count[info.module] = (count[info.module] || 0) + 1;
    for (const info of Object.values(nodes)) {
      const a = info.module;
      // Lean 側が getModuleFor? で解決した depModules があればそれを使う。
      // 宣言レベルの辺から推測すると範囲外宣言のモジュールが分からず辺が落ちる。
      const targets = info.depModules
        ? info.depModules
        : [...info.typeDeps, ...(edgeMode !== "type" ? info.valueDeps : [])]
            .map((d) => nodes[d] && nodes[d].module).filter(Boolean);
      for (const b of targets) {
        if (!b || a === b) continue;
        (dep[a] || (dep[a] = new Set())).add(b);
        (ref[b] || (ref[b] = new Set())).add(a);
      }
    }
    const toArr = (m) => Object.fromEntries(Object.entries(m).map(([k, v]) => [k, [...v]]));
    const d = toArr(dep), r = toArr(ref);
    for (const m of Object.keys(count)) { d[m] = d[m] || []; r[m] = r[m] || []; }
    // モジュール粒度では depModules が型／値を区別しないので、参照側は分割しない。
    return { dep: d, ref: r, refType: r, refValue: {}, refAll: r, count, edgeKind: {}, refKind: {} };
  }

  /* ---------- 骨組みの縮約 ----------

     証明項には `And.intro` や `PSigma.mk`、再帰子といった論理の骨組みが必ず現れる。
     これを頂点として描くと、実際に使われた補題がその陰に隠れてしまう。
     そこで骨組みを潰し、そこを通り抜けた先の非骨組みへ辺を張り替える。

       adj'(u) = { 最初に出会う非骨組みの子孫 }   （u 自身は非骨組み）

     これは骨組みの集合で商を取る操作で、到達可能性を保つ。
     表示のためだけに使い、極小仮定や |↓d| の計算には使わない。
     監査の結果を歪めてはならないので、そちらは常に元のグラフで測る。

     縮約辺 u→w の**種**(型依存/値依存)は「初手 u→v₁ の種」を継承する
     (依存を*どう*使い始めたかが縮約後も意味を持つ)。複数経路で到達した
     場合は type 側へ寄せる(型依存の方が強い主張、directDepsOfCore と同じ規約)。
     これ無しでは縮約辺の種が引けず、全てが既定の「型依存」の見た目に落ちて
     視覚語彙が嘘をつく(自己解析の観察で発見)。 */
  /* 一つの節点 n について、骨組みを通り抜けた先の可視な到達先と、各到達先への
     初手の種を返す。contractThrough の中身であり、中心そのものが骨組みの名前を
     持つとき（`.injEq` / `.rec` / `match_*` へ移動したとき）に、store が中心だけを
     「可視」として個別に縮約し直すのにも使う。 */
  function contractNode(adj, isHidden, n, kindOf) {
    const put = (map, m, k) => {
      const prev = map.get(m);
      if (prev === undefined || (prev === "value" && k === "type")) map.set(m, k);
    };
    const resKind = new Map();          // 可視の到達先 → 初手の種
    for (const d of adj[n] || []) {
      const k0 = kindOf ? kindOf(n, d) : "type";
      if (!isHidden(d)) { put(resKind, d, k0); continue; }
      // 骨組みの内部を子ごとに辿り直す。到達先が継承すべき「初手の種」が
      // 子ごとに異なるため(骨組みは小集合なので重複走査は許容)。
      const seen = new Set([n, d]);
      const stack = (adj[d] || []).slice();
      while (stack.length) {
        const m = stack.pop();
        if (seen.has(m)) continue;
        seen.add(m);
        if (isHidden(m)) { for (const x of adj[m] || []) stack.push(x); }
        else put(resKind, m, k0);
      }
    }
    const kind = {};
    if (kindOf) for (const [m, k] of resKind) kind[n + " " + m] = k;
    return { adj: [...resKind.keys()], kind };
  }

  function contractThrough(adj, isHidden, names, kindOf) {
    const out = {};
    const kind = {};
    for (const n of names) {
      if (isHidden(n)) continue;
      const r = contractNode(adj, isHidden, n, kindOf);
      out[n] = r.adj;
      Object.assign(kind, r.kind);
    }
    return { adj: out, kind };
  }

  /* ---------- 可視集合（局所展開） ----------
     深さを大域スライダーで制御すると注目していない枝まで伸びて層数が二桁になる。
     「基本の深さまでは自動で開き、その先は利用者がノード単位で開く」方式。
       n が open ⟺ hop(n) < baseDepth または n ∈ expanded
     closedFrontier[n] は「n を開いたら新たに何件見えるか」。 */
  function visibleClosure(root, adj, baseDepth, expanded) {
    const hop = {}; hop[root] = 0;
    const order = [root];
    const isOpen = (n) => hop[n] < baseDepth || expanded.has(n);
    for (let i = 0; i < order.length; i++) {
      const n = order[i];
      if (!isOpen(n)) continue;
      for (const m of adj[n] || []) {
        if (!(m in hop)) { hop[m] = hop[n] + 1; order.push(m); }
      }
    }
    const closedFrontier = {};
    for (const n of order) {
      if (isOpen(n)) continue;
      const hidden = (adj[n] || []).filter((m) => !(m in hop));
      if (hidden.length) closedFrontier[n] = hidden.length;
    }
    return { hop, order, closedFrontier };
  }

  function reachable(root, adj, maxHops) {
    const hop = {}; hop[root] = 0;
    let frontier = [root], h = 0;
    while (frontier.length && h < maxHops) {
      const next = [];
      for (const n of frontier)
        for (const m of adj[n] || [])
          if (!(m in hop)) { hop[m] = h + 1; next.push(m); }
      frontier = next; h++;
    }
    return hop;
  }

  /* ---------- 最長路レベリング ----------
     BFS 深さ（最短路）で層を作ると、辺 u→v に対して ℓ(v)=ℓ(u)+1 が成り立たず、
     層をまたぐ辺が生じて描画から漏れる。最長路なら
        ℓ(root)=0,  ℓ(v)=max{ℓ(u)+1 : u→v}
     が非巡回性から well-defined で、全ての辺が厳密に外向きになる。
     ℓ(v) は「root から v への最長導出鎖の長さ」を意味し、極小元が最外層に出る。 */
  function longestPathLevels(root, adj, hop) {
    const inSet = new Set(Object.keys(hop));
    const indeg = {};
    for (const v of inSet) indeg[v] = 0;
    for (const u of inSet)
      for (const v of adj[u] || []) if (inSet.has(v)) indeg[v]++;
    const level = {}; level[root] = 0;
    const queue = [];
    for (const v of inSet) if (indeg[v] === 0) { if (v !== root) level[v] = hop[v]; queue.push(v); }
    if (!queue.includes(root)) queue.push(root);
    const settled = new Set();
    for (let qi = 0; qi < queue.length; qi++) {
      const u = queue[qi];
      if (settled.has(u)) continue;
      settled.add(u);
      for (const v of adj[u] || []) {
        if (!inSet.has(v)) continue;
        const cand = (level[u] !== undefined ? level[u] : hop[u]) + 1;
        if (level[v] === undefined || cand > level[v]) level[v] = cand;
        if (--indeg[v] <= 0) queue.push(v);
      }
    }
    // 巡回（整礎再帰の補助定義など）に巻き込まれた分は BFS ホップ数で退避
    for (const v of inSet) if (level[v] === undefined) level[v] = hop[v];
    const layers = [];
    for (const [v, l] of Object.entries(level)) (layers[l] || (layers[l] = [])).push(v);
    for (let i = 0; i < layers.length; i++) if (!layers[i]) layers[i] = [];
    return { level, layers };
  }

  /* ---------- 円錐配置 ----------

     直交格子に層を積むと、扇入り／扇出しの大きい宣言のところで辺が束になって
     互いに重なり、どれがどこへ行くのか読めなくなる。中心から放射する構造は
     本来「中心の上のファイバー束」なので、その形のまま極座標に置く。

       ・層 ℓ は半径 r(ℓ) の円弧に載る（＝ファイバーの底空間が角度方向）
       ・角度は親の角度の重心で並べる（交差削減）
       ・半径は「その層の全ノードが弧上で重ならない最小値」まで自動で開く
         → 密な層ほど円錐が大きく開く。重なりが原理的に生じない。
       ・辺は極座標のベジエ（中間半径で角度だけ移る）で描くので、
         同じ扇に属する辺が束ねられ、交差が視覚的に整理される。

     戻り値の pos は画面座標 (x, y) と極座標 (r, th) の両方を持つ。
     辺の描画は極座標側を使う。 */
  function layoutCone(spec) {
    const {
      layers, adj, th0, th1, groupOf,
      // 層上限より優先して必ず置く節点の集合（経路表示の区間・手動展開）。null なら無し
      pin = null,
      // dr の既定は √(slotMax² + ノード高²) を上回らせる(隣接リングの
      // 軸平行矩形が どの角度でも重ならないための必要条件。store.js 参照)
      r0 = 150, dr = 200, slotMax = 172, slotMin = 62, slotPref = 196,
      rSoft = 1150, maxPerLayer = 48,
    } = spec;
    const span = Math.max(0.15, th1 - th0);
    const mid = (th0 + th1) / 2;

    const levelOf = {};
    layers.forEach((L, l) => L.forEach((n) => { levelOf[n] = l; }));
    /* parents    外向き（層が増える）の親。重心法の角度決めに使う。
       anyParent  向きを問わない親。巡回の退避（longestPathLevels の hop 代用）では
                  親の層が自分以上になり得て、その辺は canvas が非外向きの直線で描く。 */
    const parents = {}, anyParent = {};
    for (const u of Object.keys(levelOf))
      for (const v of adj[u] || []) {
        if (levelOf[v] === undefined || v === u) continue;
        (anyParent[v] || (anyParent[v] = [])).push(u);
        if (levelOf[v] > levelOf[u]) (parents[v] || (parents[v] = [])).push(u);
      }

    const pos = {};
    const rings = [];
    const overflow = {};
    const angle = {};
    let r = r0 - dr;
    let rMax = 0;
    /* ここまでに置いた節点。親が一つも置かれていない節点は辺を引けず浮くので
       置かず、溢れに数える。浮く原因は二つある。
         ・層上限で親が溢れた（深さ 2 以上の子が孤立する）
         ・親が全て別の錐に取られた／種別フィルタで落ちた（この錐の層に親が無い）
       外向きの親が無いのは巡回の退避の節点で、親がこの錐に残っていれば後の層で
       置かれ、辺は非外向きとして描かれるので許す。根は中心として必ず描かれる。 */
    const placed = new Set(layers[0] || []);

    for (let l = 1; l < layers.length; l++) {
      const full = layers[l] || [];
      if (!full.length) continue;
      const layer = full.filter((n) => {
        const ps = parents[n] || [];
        if (ps.length) return ps.some((p) => placed.has(p));
        return (anyParent[n] || []).length > 0;
      });
      if (!layer.length) { overflow[l] = full.length; continue; }

      // 重心法: 親の角度の平均。親は必ず前の層にあるので既に確定している。
      const key = {};
      for (const n of layer) {
        const ps = (parents[n] || []).map((p) => angle[p]).filter((a) => a !== undefined);
        key[n] = ps.length ? ps.reduce((a, b) => a + b, 0) / ps.length : mid;
      }
      /* 同じ部分グラフ（名前空間・主題・種別）に属するものを弧の上で隣り合わせる。
         主鍵を「その群の重心の平均」にすることで、群をまとめても交差が増えない。
         群の中の順序は従来どおり重心。 */
      let ordered;
      if (groupOf) {
        const gKey = new Map(), gCnt = new Map();
        for (const n of layer) {
          const g = groupOf(n) || "";
          gKey.set(g, (gKey.get(g) || 0) + key[n]);
          gCnt.set(g, (gCnt.get(g) || 0) + 1);
        }
        for (const [g, s] of gKey) gKey.set(g, s / gCnt.get(g));
        ordered = layer.slice().sort((a, b) => {
          const ga = groupOf(a) || "", gb = groupOf(b) || "";
          if (ga !== gb) return (gKey.get(ga) - gKey.get(gb)) || (ga < gb ? -1 : 1);
          return (key[a] - key[b]) || (a < b ? -1 : 1);
        });
      } else {
        ordered = layer.slice().sort((a, b) => (key[a] - key[b]) || (a < b ? -1 : 1));
      }

      /* 表示上限。溢れた分は右パネルの一覧で全件見られるので、ここでは件数だけ伝える。
         経路表示や手動展開で「見せる」と決めた節点（pin）は上限より優先し、
         角度の順序は保ったまま、残りの枠を先頭から埋める。 */
      let shown = ordered;
      if (ordered.length > maxPerLayer) {
        const must = new Set(pin ? ordered.filter((n) => pin.has(n)) : []);
        const keep = new Set(must);
        let room = Math.max(0, maxPerLayer - must.size);
        for (const n of ordered) {
          if (room <= 0) break;
          if (!must.has(n)) { keep.add(n); room--; }
        }
        shown = ordered.filter((n) => keep.has(n));
      }
      if (full.length > shown.length) overflow[l] = full.length - shown.length;

      /* 半径の決め方。
         rNeed  これ未満だと弧上でノードが重なる、絶対の下限。
         rWant  一枚一枚を最大幅で置ける理想値。層が薄いときはこちらが効いて、
                数個しかない層が中心の近くで潰れて点になるのを防ぐ。
         rSoft  理想値の頭打ち。層が厚いときに半径が青天井になるのを止める。
                このとき slot は自動的に細くなり、ノードは小さく描かれる。 */
      const rNeed = (shown.length * slotMin) / span;
      const rWant = (shown.length * slotPref) / span;
      r = Math.max(r + dr, r0, rNeed, Math.min(rWant, rSoft));
      rMax = Math.max(rMax, r);

      const slot = Math.min(slotMax, (span * r) / Math.max(shown.length, 1));
      const usedSpan = (shown.length * slot) / r;
      const start = mid - usedSpan / 2 + slot / r / 2;
      shown.forEach((n, i) => {
        const th = start + (i * slot) / r;
        angle[n] = th;
        placed.add(n);
        pos[n] = {
          r, th, level: l, slot,
          x: r * Math.cos(th), y: r * Math.sin(th),
          w: Math.max(46, Math.min(slotMax - 14, slot - 12)),
        };
      });
      /* 同じ群が連続している区間を記録する。描画側はこれを弧の帯として描く。
         位置が確定した後で切り出すので、帯とノードが必ず一致する。 */
      let runs = [];
      if (groupOf) {
        const half = slot / r / 2;
        for (const n of shown) {
          const g = groupOf(n) || "";
          const last = runs[runs.length - 1];
          if (last && last.group === g) { last.th1 = pos[n].th + half; last.n++; }
          else runs.push({ group: g, th0: pos[n].th - half, th1: pos[n].th + half, n: 1 });
        }
        runs = runs.filter((x) => x.group);
      }
      rings.push({ level: l, r, count: full.length, shown: shown.length, th0, th1, slot, runs });
    }
    return { pos, rings, overflow, rMax, th0, th1, mid };
  }

  /* ---------- 最短識別接尾辞 ----------
     Nat.add_comm と Int.add_comm を両方 add_comm と表示すると区別できない。
     表示集合の中で一意になる最小の接尾辞を返す。Lean の open と同じ感覚。
     接尾辞の出現数を先に数えるので、名前数に対して線形。 */
  function shortestUniqueSuffixes(names) {
    const uniq = [...new Set(names)];
    const cnt = new Map();
    const parts = new Map();
    for (const n of uniq) {
      const p = String(n).split(".");
      parts.set(n, p);
      for (let j = 1; j <= p.length; j++) {
        const suf = p.slice(p.length - j).join(".");
        cnt.set(suf, (cnt.get(suf) || 0) + 1);
      }
    }
    const res = {};
    for (const n of uniq) {
      const p = parts.get(n);
      let chosen = String(n);
      for (let j = 1; j <= p.length; j++) {
        const suf = p.slice(p.length - j).join(".");
        if (cnt.get(suf) === 1) { chosen = suf; break; }
      }
      res[n] = chosen;
    }
    return res;
  }

  /* ---------- 極小元とフロンティア ----------
     深さ上限で切られただけのノードを極小元と誤認しないよう分ける。 */
  function minimalAndFrontier(closureNames, adj) {
    const set = new Set(closureNames);
    const trueMinimal = [], frontier = [];
    for (const n of closureNames) {
      const deps = adj[n] || [];
      if (deps.some((d) => set.has(d))) continue;
      (deps.length === 0 ? trueMinimal : frontier).push(n);
    }
    return { trueMinimal: trueMinimal.sort(), frontier: frontier.sort() };
  }

  /* ---------- 順序区間 [t, d] = ↑t ∩ ↓d ----------
     d から t への経路上にあるノードちょうどの集合。
     「この定理はどこで選択公理を使うのか」に正確に答える。 */
  function orderInterval(d, t, dep, ref, maxHops) {
    maxHops = maxHops || 64;
    const a = reachable(d, dep, maxHops);
    const b = reachable(t, ref, maxHops);
    const iv = new Set();
    for (const x of Object.keys(a)) if (x in b) iv.add(x);
    return iv;
  }

  /* ---------- 依存の大きさ ----------

     「依存の少ない順」に直接依存の本数を使ってはいけない。c が d の依存先でも
     deg(c) > deg(d) が普通に起こるので、その並びは依存順序と両立せず、
     前提より先に結論が来てしまう。順序と両立する量、すなわち

         c ≺ d  ⟹  m(c) < m(d)

     を満たすものを使う。非巡回性から次の二つがこれを満たす。

         size(d)    = |↓d|         下方閉集合の濃度。総仮定量。
         minimal(d) = |min(↓d)|    依存先を持たない元の数。必要な原始要素の数。

     size が狭義単調なのは、c ≺ d のとき ↓c ⊆ ↓d かつ d ∈ ↓d \ ↓c だから。
     よって size の昇順は必ず線形拡大になり、上から読めば前提が必ず先に来る。

     計算は逆位相順にビット集合を OR していくだけで O(|E|·|V|/32)。
     巡回（整礎再帰の補助定義）に触れた辺は寄与させない。閉集合がわずかに
     小さく出るが、順序が保たれれば足りる用途なので許容する。 */
  function closureStats(adj, names) {
    const N = names.length;
    const words = (N + 31) >> 5;
    if (N === 0 || N * words > 12e6) return null;   // 過大なら諦めて深さで代用する

    const idx = new Map();
    names.forEach((n, i) => idx.set(n, i));
    const bits = new Uint32Array(N * words);
    const sink = new Uint32Array(words);
    for (let i = 0; i < N; i++) {
      if (!(adj[names[i]] || []).length) sink[i >> 5] |= 1 << (i & 31);
    }

    const state = new Uint8Array(N);   // 0 未訪問 / 1 訪問中 / 2 確定
    const absorb = (i, j) => {
      const a = i * words, b = j * words;
      for (let w = 0; w < words; w++) bits[a + w] |= bits[b + w];
    };
    const stack = [];
    for (let s = 0; s < N; s++) {
      if (state[s]) continue;
      stack.push([s, 0]);
      while (stack.length) {
        const fr = stack[stack.length - 1];
        const i = fr[0];
        if (fr[1] === 0) {
          if (state[i]) { stack.pop(); continue; }
          state[i] = 1;
          bits[i * words + (i >> 5)] |= 1 << (i & 31);   // 自分自身を含める
        }
        const kids = adj[names[i]] || [];
        let descended = false;
        while (fr[1] < kids.length) {
          const j = idx.get(kids[fr[1]++]);
          if (j === undefined) continue;
          if (state[j] === 2) absorb(i, j);
          else if (state[j] === 0) { stack.push([j, 0]); descended = true; break; }
        }
        if (descended) continue;
        for (const kid of kids) {          // 降りて確定した子を取り込み直す
          const j = idx.get(kid);
          if (j !== undefined && state[j] === 2) absorb(i, j);
        }
        state[i] = 2;
        stack.pop();
      }
    }

    const popcount = (x) => {
      x -= (x >> 1) & 0x55555555;
      x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
      x = (x + (x >> 4)) & 0x0f0f0f0f;
      return (Math.imul(x, 0x01010101) >> 24) & 0x3f;
    };
    const size = {}, minimal = {};
    for (let i = 0; i < N; i++) {
      let s = 0, m = 0;
      const a = i * words;
      for (let w = 0; w < words; w++) {
        s += popcount(bits[a + w]);
        m += popcount(bits[a + w] & sink[w]);
      }
      size[names[i]] = s; minimal[names[i]] = m;
    }
    return { size, minimal };
  }

  /* ---------- 導出鎖の深さ ----------
     depth(n) = 1 + max{depth(m) : n → m}。DAG 上の一回の記憶化再帰で全ノード。
     巡回は訪問中フラグで断ち切る（整礎再帰の補助定義がここに来る）。 */
  function chainDepths(adj, names) {
    const depth = {};
    const state = {};   // 1 = 訪問中, 2 = 確定
    const stack = [];
    for (const s of names) {
      if (state[s]) continue;
      stack.push([s, 0]);
      while (stack.length) {
        const fr = stack[stack.length - 1];
        const n = fr[0];
        if (fr[1] === 0) {
          if (state[n]) { stack.pop(); continue; }
          state[n] = 1; depth[n] = 0;
        }
        const kids = adj[n] || [];
        if (fr[1] < kids.length) {
          const m = kids[fr[1]++];
          if (state[m] === 2) depth[n] = Math.max(depth[n], depth[m] + 1);
          else if (state[m] !== 1) stack.push([m, 0]);
          continue;
        }
        for (const m of kids) if (state[m] === 2) depth[n] = Math.max(depth[n], depth[m] + 1);
        state[n] = 2;
        stack.pop();
      }
    }
    return depth;
  }

  /* ---------- 性質の遺伝 ----------

     「無条件に与えられた定義だけから、無条件に得られている」かどうかは、
     自分が無条件であることに加えて、依存先すべてが同じ性質を持つことを要求する。
     不動点の言葉では F(X) = { n : pred(n) かつ deps(n) ⊆ X } の最大不動点
     （述語を満たし依存で閉じた集合のうち最大のもの）を計算している。
     DAG 上の一回の走査で全ノード分を得る。巡回に触れた場合は偽側に倒す
     （成り立つと言い切れないものを成り立つとは言わない）。 */
  function hereditary(adj, names, pred) {
    const state = {};      // 1 = 訪問中, 2 = 確定
    const res = {};
    const stack = [];
    for (const s of names) {
      if (state[s]) continue;
      stack.push([s, 0]);
      while (stack.length) {
        const fr = stack[stack.length - 1];
        const n = fr[0];
        if (fr[1] === 0) {
          if (state[n]) { stack.pop(); continue; }
          state[n] = 1; res[n] = !!pred(n);
        }
        const kids = adj[n] || [];
        let descended = false;
        while (fr[1] < kids.length) {
          const m = kids[fr[1]++];
          if (state[m] === 2) { if (!res[m]) res[n] = false; }
          else if (state[m] === 1) { res[n] = false; }        // 巡回は偽側へ
          else { stack.push([m, 0]); descended = true; break; }
        }
        if (descended) continue;
        for (const m of kids) if (state[m] === 2 && !res[m]) res[n] = false;
        state[n] = 2;
        stack.pop();
      }
    }
    return res;
  }

  /* ---------- 初期中心の選定 ----------
     名前順の先頭を取ると Classical.choice のような依存先ゼロの公理が中心になり
     グラフがほぼ空になる。半順序の極大元（他のどの宣言からも使われない
     ＝そのライブラリの最終結果）のうち、導出鎖が最も長いものを選ぶ。
     全ノードの深さは DAG 上の一回の走査で得られるので、宣言数に対して線形。 */
  function pickDefaultCenter(nodes, idx, isFrame) {
    let cands = Object.keys(nodes).filter((n) => !nodes[n].external && !nodes[n].internal);
    /* 生成物（構造体の `.injEq` / `.rec` / `match_*` 等の骨組み）は「ライブラリの
       最終結果」ではない。候補から外す（フィクスチャに構造体を足したところ、
       既定中心が `Pair.mk.injEq` に選ばれたのを実測）。手書きの宣言が無ければ戻す。 */
    if (isFrame) {
      const hand = cands.filter((n) => !isFrame(n));
      if (hand.length) cands = hand;
    }
    if (!cands.length) return Object.keys(nodes)[0] || "";
    const maximal = cands.filter((n) => (idx.ref[n] || []).length === 0);
    const pool = maximal.length ? maximal : cands;
    const depth = chainDepths(idx.dep, pool);
    let best = pool[0], bestKey = [-1, -1];
    for (const n of pool) {
      const k = [depth[n] || 0, (idx.dep[n] || []).length];
      if (k[0] > bestKey[0] || (k[0] === bestKey[0] && k[1] > bestKey[1])) { best = n; bestKey = k; }
    }
    return best;
  }

  LDR.graph = {
    parseJsonl, legacyOrigin, effectiveNodes, buildIndices, buildModuleIndices, visibleClosure, reachable,
    longestPathLevels, layoutCone, shortestUniqueSuffixes, contractThrough, contractNode,
    minimalAndFrontier, orderInterval, chainDepths, closureStats, hereditary, pickDefaultCenter,
  };
})(window.LDR = window.LDR || {});
