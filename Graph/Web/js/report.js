/* ============================================================
   js/report.js — 証明の構造を Markdown のレポートにする

   依存順序 (D, ⪯) の上で、読み手が確認したい順に章を並べる。事実は常に **元のグラフ**
   （派生の畳み込み・骨組みの縮約を行う前）で測り、表示の都合はレポートの頭に注記する。

     1. 主張（What）        名前・種別・所在・パッケージ・docs・公理・sorry・形、原文、束縛と結論
     2. 前提（On what）     直接依存を 型依存（主張に現れる）/ 値依存（証明にだけ現れる）に分け、
                            総仮定量 |↓x| の昇順（原始的なものから）
     3. 道筋（How）         導出図の文章版（前提 → 横線＋規則名 → 結論。深さ指定）
     4. 基盤（Ultimately）  極小元 min(↓x)（断片を由来に埋め戻した索引で）と公理
     5. 影響（Depends on it）主張で参照 / 証明で参照
     6. 経路（Interval）    主語と中心の順序区間 [s, c] = ↑s ∩ ↓c を層で、一本の道筋も添える
     7. 計量・来歴

   三種の主語:  中心 c / 選択 s（グラフで押した要素）/ 極小元 t（経路表示の対象）。
   章は opts.sections で選ぶ（部分出力: 型依存だけ、参照だけ、…）。
   ============================================================ */
(function (LDR) {
  "use strict";
  const S = LDR.store, G = LDR.graph, sig = LDR.sig, P = LDR.pkg, R = LDR.roles;

  const SECTIONS = [
    { id: "claim",   ja: "主張（所在・原文・束縛・結論）" },
    { id: "type",    ja: "型依存（主張に現れる宣言）" },
    { id: "value",   ja: "値依存（証明にだけ現れる宣言）" },
    { id: "axioms",  ja: "公理の由来（主張か証明か・入口・最初に現れる宣言）" },
    { id: "figure",  ja: "導出図（前提 → 規則 → 結論）" },
    { id: "foundation", ja: "基盤（対象の閉包から外へ出る先 ∂_T x）と原子 min(↓x)" },
    { id: "frontier",   ja: "境界（読み込んだ範囲の切れ目 ∂x）" },
    { id: "refs",    ja: "参照（主張で／証明で）" },
    { id: "path",    ja: "経路（中心との順序区間）" },
    { id: "metrics", ja: "計量（総仮定量・導出鎖の深さ）" },
    { id: "meta",    ja: "来歴（対象・リビジョン・toolchain）" },
    { id: "figures", ja: "付録: 図（Mermaid。導出図・公理の流入・境界・経路を末尾にまとめる）" },
    { id: "notes",   ja: "注記（列の意味・測り方の説明）" },
  ];
  const ALL = SECTIONS.map((s) => s.id).filter((id) => id !== "notes");
  /* 書き方の選択。情報を落とす側は利用者が選んだときだけ（既定は落とさない）。 */
  const STYLE = [
    { id: "fullNames",     ja: "名前は完全名で（外すと末尾二成分）", def: true },
    { id: "edgeList",      ja: "区間の辺を一本ずつ列挙する（外すと節点ごとの隣接）", def: true },
  ];

  /* ---- Mermaid（付録） ----
     文章の図（木・層・関係の箇条書き）は線形で、二つの親に共有された前提（「既出」）の二本目の辺や、
     層をまたぐ辺が読めない。同じ事実を flowchart にも描く。文章側は一切変えない（描けない環境のため）。
     図は本文に挟まず、末尾の「付録: 図」に集める（章 figures）。Mermaid は節点・辺ごとに一行なので、
     本文に挟むと読みの流れを数百行ぶん断つ（cslib で実測）。各図の見出しに対応する節を書く。
     規約（全ての図で共通。付録の頭に「記法」として出す）:
       向き BT。辺 `x --> p` は「x が p を使う」（文章の `u → v` と同じ向き）。描画では使われる側
       （前提・材料・極小元）が上、使う側（結論・中心）が下。導出図の慣習（前提は横線の上）と、
       グラフ表示（上錐 = 中心が使う側）に合わせる。
       形: {{ }} 公理 / [ ] 命題 / ( ) 定義・型 / [/ /] 範囲外 / [[ ]] 名前空間の束
       辺: --> 主張（型）に現れる / -.-> 証明（値）にだけ現れる / ==> 最短の道筋 / 数字の札 = 束ねた辺の本数
       級: root 太枠（主語）/ more 破線枠（深さの先に前提が続く）/ src 橙枠（公理が最初に現れる宣言）/ sorry 赤
     大きさの上限（節点 150・辺 400。Mermaid の既定 maxEdges 500 の内側）を超える図は描かず、
     件数を添えてそう書く。文章版が全てを含むので情報は落ちない。 */
  const FIG_MAX = { nodes: 150, edges: 400 };
  const CLASS_DEF = {
    ax:     "fill:#ffedd5,stroke:#ea580c,color:#7c2d12",
    lem:    "fill:#eef2ff,stroke:#4f46e5,color:#1e1b4b",
    voc:    "fill:#f0fdfa,stroke:#0d9488,color:#134e4a",
    frame:  "fill:#f5f5f4,stroke:#a8a29e,color:#78716c",
    stub:   "fill:#fafaf9,stroke:#a8a29e,stroke-dasharray:4 3,color:#57534e",
    bundle: "fill:#fafaf9,stroke:#78716c,color:#292524",
    root:   "stroke-width:3px",
    more:   "stroke-dasharray:6 3",
    sorry:  "stroke:#dc2626,stroke-width:2px",
    src:    "stroke:#ea580c,stroke-width:2px",
  };
  const SHAPES = { axiom: ["{{", "}}"], lemma: ["[", "]"], vocab: ["([", "])"], stub: ["[/", "/]"], bundle: ["[[", "]]"] };
  const NOTATION = ["### 記法（全ての図で共通）", "",
    "- 向き: 辺 `x --> p` は「x が p を使う」（文章の `u → v` と同じ）。描画は下から上なので、使われる側（前提・材料・極小元）が上、使う側（結論・中心）が下",
    "- 形: 六角 `{{ }}` 公理 / 四角 `[ ]` 命題（定理・補題）/ 角丸 `( )` 定義・型 / 平行四辺形 `[/ /]` 範囲外（依存が分からない）/ 二重枠 `[[ ]]` 名前空間の束",
    "- 辺: 実線 `-->` 主張（型）に現れる / 点線 `-.->` 証明（値）にだけ現れる / 太線 `==>` 最短の道筋 / 数字の札 = 束ねた辺の本数",
    "- 枠: 太枠 = 主語 / 破線 = 深さの先にまだ前提がある / 橙 = 公理が最初に現れる宣言（その先は公理を直接使うか、範囲外で続く）/ 赤 = sorry を含む / 灰 = 論理の骨組み・断片",
    "- 公理の流入の図では、節点の札 `[P C Q]` がその宣言の持つ公理（略号は依存の表と同じ）",
    "- 経路の図は順序区間の推移簡約（Hasse 図）。推移で導ける辺は引かず、最短の道筋だけは太線で残す。直接の辺の全列挙は本文"];
  /* 推移簡約: 辺 u → v は、u の別の直接依存 w から v に到達できるなら引かない（順序は保たれる）。
     到達集合は記憶化の再帰で取る。巡回（整礎再帰の補助定義）があれば部分的な集合で近似する。 */
  function hasseEdges(nodes, adj) {
    const reach = new Map();
    const R = (x) => {
      if (reach.has(x)) return reach.get(x);
      const s = new Set(); reach.set(x, s);
      for (const y of adj[x] || []) { s.add(y); for (const z of R(y)) s.add(z); }
      return s;
    };
    const keep = [];
    for (const u of nodes) for (const v of adj[u] || []) {
      if (!(adj[u] || []).some((w) => w !== v && R(w).has(v))) keep.push([u, v]);
    }
    return keep;
  }
  function mermaidBuilder() {
    const ids = new Map(), nodes = [], order = [], cls = new Map(), edges = new Map(), subs = [];
    // ラベルの中で Mermaid が特別に読む文字は実体参照にする（`#` も実体の先頭なので先に）
    const esc = (s) => String(s).replace(/#/g, "#35;").replace(/"/g, "#quot;").replace(/</g, "#lt;").replace(/>/g, "#gt;");
    const id = (name) => { if (!ids.has(name)) ids.set(name, "n" + ids.size); return ids.get(name); };
    const b = {
      has: (name) => ids.has(name),
      node(name, label, shape, classes) {
        const i = id(name);
        if (!nodes.includes(i)) {
          const [l, r] = SHAPES[shape] || SHAPES.lemma;
          nodes.push(i); order.push(`${i}${l}"${esc(label)}"${r}`);
        }
        for (const c of classes || []) (cls.get(c) || cls.set(c, new Set()).get(c)).add(i);
        return i;
      },
      /* kind: "type" | "value" | "chain"。同じ対は一本（chain は上書き） */
      edge(a, c, kind, label) {
        const k = id(a) + " " + id(c);
        const prev = edges.get(k);
        if (prev && prev.kind === "chain" && kind !== "chain") return;
        edges.set(k, { a: id(a), c: id(c), kind, label: label || (prev && prev.label) || "" });
      },
      subgraph(key, title, names) { subs.push({ key, title, ids: names.map(id) }); },
      size: () => ({ nodes: nodes.length, edges: edges.size }),
      lines() {
        const out = ["```mermaid", "flowchart BT", ...order.map((l) => "  " + l)];
        for (const s of subs) {
          out.push(`  subgraph ${s.key}["${esc(s.title)}"]`);
          for (const i of s.ids) out.push("    " + i);
          out.push("  end");
        }
        for (const e of edges.values()) {
          const l = e.label ? `"${esc(e.label)}"` : "";
          const arrow = e.kind === "chain" ? (l ? `== ${l} ==>` : "==>")
                      : e.kind === "value" ? (l ? `-. ${l} .->` : "-.->")
                      : (l ? `-- ${l} -->` : "-->");
          out.push(`  ${e.a} ${arrow} ${e.c}`);
        }
        for (const c of cls.keys()) if (CLASS_DEF[c]) out.push(`  classDef ${c} ${CLASS_DEF[c]}`);
        for (const [c, set] of cls) if (CLASS_DEF[c]) out.push(`  class ${[...set].join(",")} ${c}`);
        out.push("```");
        return out;
      },
    };
    return b;
  }
  /* 図を付録に積む（本文には出さない）。section は対応する節の見出し。上限を超える図は件数だけ。 */
  function addFigure(fx, mm, caption, section) {
    if (!fx.on) return;
    const sz = mm.size();
    const over = sz.nodes > FIG_MAX.nodes || sz.edges > FIG_MAX.edges;
    fx.figs.push({ caption, section, nodes: sz.nodes, edges: sz.edges, lines: over ? null : mm.lines() });
  }
  function appendixLines(fx) {
    const out = ["", "## 付録: 図（Mermaid）", "",
      "本文の各節と同じ事実を flowchart で描いたもの。描けない環境では本文を読む。各図の見出しに対応する節を記す。", "",
      ...NOTATION];
    fx.figs.forEach((f, i) => {
      out.push("", `### 図 ${i + 1}: ${f.caption}（節: ${f.section}。節点 ${f.nodes}・辺 ${f.edges}）`);
      if (!f.lines) out.push("", `（上限 節点 ${FIG_MAX.nodes}・辺 ${FIG_MAX.edges} を超えるので図は省く。本文に全ての事実がある）`);
      else out.push("", ...f.lines);
    });
    return out;
  }
  /* 宣言を役割の形と級で置く。extra は root / more / src 等、label は名前以外を添えるとき */
  function declNode(mm, n, st, nm, extra, label) {
    const x = st.nodes[n] || {};
    const role = R.roleOf(n, x);
    const shape = x.stub ? "stub" : role === "axiom" ? "axiom" : x.isProp ? "lemma" : "vocab";
    const classes = [x.stub ? "stub" : role === "axiom" ? "ax" : (role === "frame" || role === "part") ? "frame" : x.isProp ? "lem" : "voc"];
    if (x.usesSorry) classes.push("sorry");
    return mm.node(n, label || nm(n), shape, classes.concat(extra || []));
  }

  const u = (n) => sig.userName(n);
  const code = (s) => "`" + String(s).replace(/`/g, "ˋ") + "`";
  const cell = (s) => String(s || "").replace(/\|/g, "\\|").replace(/\s*\n\s*/g, " ");
  const KIND_JA = { axiom: "公理", theorem: "定理", def: "定義", inductive: "帰納型", constructor: "構成子",
                    recursor: "再帰子", opaque: "opaque", quot: "quot", external: "範囲外", unknown: "不明" };
  const kindJa = (k) => KIND_JA[k] || k || "不明";
  const whereOf = (nd) => {
    if (!nd || !nd.module || nd.module.startsWith("(")) return "（所在不明。レポートの範囲外）";
    const file = nd.module.split(".").join("/") + ".lean";
    return file + (nd.line ? ":" + nd.line + (nd.lineEnd && nd.lineEnd !== nd.line ? "–" + nd.lineEnd : "") : "");
  };
  const pkgOf = (nd) => (P ? (P.labelOf(P.packageOf(nd && nd.module)) || "") : "");
  const concl = (nd) => (nd && (nd.conclusion || nd.typeString)) || "";
  const anon = (s) => (s === "[anonymous]" || /(^|\.)_@\.|_hyg/.test(String(s || "")) ? "" : String(s || ""));
  function binderText(b) {
    const nm = anon(b.name);
    switch (b.kind) {
      case "inst":           return nm ? `[${nm} : ${b.type}]` : `[${b.type}]`;
      case "implicit":       return `{${nm || "_"} : ${b.type}}`;
      case "strictImplicit": return `⦃${nm || "_"} : ${b.type}⦄`;
      default:               return nm ? `(${nm} : ${b.type})` : (b.prop ? b.type : `(_ : ${b.type})`);
    }
  }

  /* ---- 章 ---- */
  function headerLines(name, nd, st, nm) {
    const out = [];
    out.push(`# ${u(name)}`);
    const bits = [kindJa(nd.kind), whereOf(nd), pkgOf(nd) ? `パッケージ ${pkgOf(nd)}` : ""].filter(Boolean);
    out.push(bits.join(" · "));
    if (sig.isPrivateName(name)) out.push("private 宣言（実名 " + code(name) + "）");
    const url = P && P.docsUrl(nd, name);
    if (url) out.push(`docs: ${url}`);
    const OK = sig.ORIGIN_KIND, OR = sig.ORIGIN_REL;
    if (nd.originRel && nd.origin) out.push(`由来: ${code(nm(nd.origin))} の${(OR[nd.originRel] || {}).ja || nd.originRel}（${(OK[nd.originKind] || {}).ja || nd.originKind}）`);
    // 公理は「現状の証明項がそうである」という記録。将来の証明の改良で減り得る
    out.push(`公理（現状の証明項に基づく）: ${nd.axioms && nd.axioms.length ? nd.axioms.join(", ") : "なし（公理非依存）"}   sorry: ${nd.usesSorry ? "あり" : "なし"}`
      + (nd.isProp && nd.shape && sig.SHAPE[nd.shape] ? `   法則の形: ${sig.SHAPE[nd.shape].ja}（${nd.shapeRel ? nm(nd.shapeRel) : ""}${nd.shapeType ? " @ " + nm(nd.shapeType) : ""}）` : "")
      + (nd.numHyp || nd.numInst ? `   条件: 仮定 ${nd.numHyp} / インスタンス ${nd.numInst}` : "   無条件"));
    if (nd.docString) out.push("", nd.docString.trim());
    return out;
  }

  /* 公理の由来。↓x の中で公理 a を持つ宣言の集合 A_a = { y ∈ ↓x : a ∈ Ax(y) } は上に閉じているので、
     その極小元が「a が最初に入ってくる場所」。加えて、a が主張（型依存の閉包）に入っているか、
     証明にだけ入っているかを分ける。後者は証明の書き換えで外せる可能性があり、前者は主張を
     変えない限り外せない。Ax(y) は Lean 側 collectAxioms の正確な値（範囲外のスタブは不明）。 */
  function axiomsSection(name, st, dv, met, nm, fx) {
    const nd = st.nodes[name] || {};
    const axs = nd.axioms || [];
    const out = ["", "## 公理の由来（現状の証明項に基づく。証明の改良で減り得る）"];
    if (!axs.length) { out.push("", "公理に依存していない。"); return out; }
    const idx = dv.inlinedIdx || dv.declIdx;
    const down = G.reachable(name, idx.dep, 64);
    const axOf = (y) => ((st.nodes[y] || {}).axioms) || [];
    const tDeps = nd.typeDeps || [], vDeps = nd.valueDeps || [];
    const kindOf = (x, y) => (idx.edgeKind[x + " " + y] === "value" ? "value" : "type");
    /* 図は公理ごとに分けず一つにする。三つの公理の鎖は八割が同じ節点（cslib で実測）なので、別図に
       すると同じ図が三度出る。節点の札にその宣言が持つ公理を書けば、どの公理がどこから入るかは
       一つの図で読める。極小元（最初に現れる宣言）は橙。六角への辺は公理を直接使う宣言からだけ
       （範囲外を経由する極小元から全て引くと、六角への星が図を埋める。実測 102 辺のうち 40）。 */
    const mm = fx.on ? mermaidBuilder() : null;
    const axTag = (y) => { const l = axs.filter((a) => axOf(y).includes(a)).map((a) => AX_SHORT[a] || a); return l.length ? ` [${l.join(" ")}]` : ""; };
    if (mm) declNode(mm, name, st, nm, ["root"], nm(name) + axTag(name));
    const axUsers = new Map();      // 公理 → それを直接使う宣言（図の六角への辺）
    for (const a of axs) {
      const direct = tDeps.includes(a) || vDeps.includes(a);
      const entriesT = tDeps.filter((d) => d !== a && axOf(d).includes(a));
      const entriesV = vDeps.filter((d) => d !== a && axOf(d).includes(a));
      const inStatement = tDeps.includes(a) || entriesT.length > 0;
      out.push("", `### ${code(a)}`);
      out.push(`- ${inStatement
        ? "現在の主張（型）の依存や、その一部に入っている。"
        : "証明（値）にだけ入っている。証明を書き換えれば外せる可能性がある"}${direct ? "。この宣言が直接使っている" : ""}`);
      if (entriesT.length) out.push(`- 入口（型依存のうち ${a} を持つもの）: ${entriesT.map((d) => code(nm(d))).join(", ")}`);
      if (entriesV.length) out.push(`- 入口（値依存のうち ${a} を持つもの）: ${entriesV.map((d) => code(nm(d))).join(", ")}`);
      /* 最初に現れる宣言: A_a の極小元（公理そのものと、依存が分からないスタブは除く）。
         名前空間で束ね、中心からの段数（最短の依存の鎖の長さ）を添えて近いものから。 */
      const A = Object.keys(down).filter((y) => y !== name && st.nodes[y] && !st.nodes[y].stub && st.nodes[y].kind !== "axiom" && axOf(y).includes(a));
      const Aset = new Set(A);
      const sources = A.filter((y) => !(idx.dep[y] || []).some((z) => Aset.has(z)));
      if (sources.length) {
        out.push(`- 最初に現れる宣言（↓x の中で ${a} を持つ宣言の極小元 ${sources.length} 件。括弧は中心からの段数。それらの内側では ${a} を直接使うか、範囲外で依存が続く）:`);
        const byNs = new Map();
        for (const y of sources) {
          const s = nm(y), i = s.lastIndexOf(".");
          const ns = i < 0 ? "" : s.slice(0, i), leaf = i < 0 ? s : s.slice(i + 1);
          (byNs.get(ns) || byNs.set(ns, []).get(ns)).push({ leaf, hop: down[y] });
        }
        const rows = [...byNs.entries()].map(([ns, ls]) => ({ ns, ls: ls.sort((p, q) => p.hop - q.hop || (p.leaf < q.leaf ? -1 : 1)), min: Math.min(...ls.map((l) => l.hop)) }))
          .sort((p, q) => p.min - q.min || (p.ns < q.ns ? -1 : 1));
        for (const r of rows) out.push(`  - ${r.ns ? code(r.ns) + ": " : ""}${r.ls.map((l) => `${code(l.leaf)}(${l.hop})`).join(", ")}`);
      } else if (!direct) {
        out.push(`- 読み込んだ範囲では ${a} を持つ宣言が見当たらない（範囲外の依存の中で使われている）`);
      }
      /* 図（合成）: x から入口を経て最初に現れる宣言へ至る最短の鎖の合併（A_a ∪ {x} の中の BFS 木）。
         A_a は ↓x の中で上に閉じている（公理は依存に沿って遺伝する）ので、x から各極小元への
         最短路の内部の節点は全て a を持ち、この木の中にある。入口も終点に入れる（別の入口経由の
         最短路に隠れて消えないように）。 */
      if (mm && (sources.length || direct)) {
        const inA = (y) => y === name || Aset.has(y);
        const parent = { [name]: null }, q = [name];
        for (let i = 0; i < q.length; i++) for (const z of idx.dep[q[i]] || []) if (inA(z) && !(z in parent)) { parent[z] = q[i]; q.push(z); }
        const srcSet = new Set(sources);
        for (const t of [...sources, ...entriesT, ...entriesV]) {
          if (!(t in parent)) continue;
          for (let y = t; parent[y]; y = parent[y]) {
            declNode(mm, y, st, nm, srcSet.has(y) ? ["src"] : [], nm(y) + axTag(y));
            mm.edge(parent[y], y, kindOf(parent[y], y));
          }
        }
        const users = (direct ? [name] : []).concat(sources.filter((s) => (idx.dep[s] || []).includes(a)));
        if (users.length) axUsers.set(a, users);
      }
    }
    if (mm) {
      for (const [a, users] of axUsers) { mm.node(a, nm(a), "axiom", ["ax"]); for (const s of users) mm.edge(s, a, kindOf(s, a)); }
      if (mm.size().edges) addFigure(fx, mm, `公理の流入（${axs.map((a) => AX_SHORT[a] || a).join(" ")}）。${nm(name)} から入口を経て、最初に現れる宣言（橙）までの最短の鎖の合併。札はその宣言が持つ公理、六角への辺は直接使う宣言から`, "公理の由来");
    }
    return out;
  }

  function claimSection(nd) {
    const out = ["", nd.isProp ? "## 主張" : "## 定義（型と束縛）"];
    if (nd.source) out.push("", "```lean", nd.source, "```");
    const B = nd.binders || [];
    const args = B.filter((b) => !b.prop), hyps = B.filter((b) => b.prop);
    if (args.length) out.push("", "引数: " + args.map(binderText).join(" "));
    if (hyps.length) out.push("仮定: " + hyps.map(binderText).join(" "));
    /* 左辺・右辺に割るのは命題だけ。定義の型 `Scheme F R Party F` を関係の適用として割ると
       「左辺 Party / 右辺 F」という誤読になる（実測）。 */
    if (nd.isProp) {
      const d = sig.decompose(nd.conclusion || "");
      if (d.lhs !== null && d.rhs !== null) {
        out.push(`結論（主結合子 ${d.rel}${d.ctx.length ? " " + d.ctx.join(" ") : ""}）`, `- 左辺: ${d.lhs}`, `- 右辺: ${d.rhs}`);
      } else if (d.whole) out.push(`結論: ${d.whole}`);
    } else if (nd.conclusion) {
      out.push(`型: ${nd.conclusion}`);
    }
    if (!nd.source && nd.typeString) out.push("", "型（Lean の表示）: " + code(nd.typeString));
    return out;
  }

  // 公理の略号。P = propext, C = Classical.choice, Q = Quot.sound, S! = sorryAx。他はそのまま
  const AX_SHORT = { propext: "P", "Classical.choice": "C", "Quot.sound": "Q", sorryAx: "S!" };
  const AX_LEGEND = "公理の略号: P = propext, C = Classical.choice, Q = Quot.sound, S! = sorryAx, ? = 不明（範囲外）";
  function depTable(names, st, met, title, note, nm) {
    const out = ["", `## ${title}（${names.length} 件。総仮定量 |↓x| の昇順）`, note ? "" + note : ""];
    if (!names.length) { out.push("", "なし"); return out; }
    const sorted = names.slice().sort((a, b) => ((met.closure[a] || 0) - (met.closure[b] || 0)) || (a < b ? -1 : 1));
    out.push(AX_LEGEND, "", "| 宣言 | 種別 | 出どころ | 役割 | 公理 | 結論・型 |", "|---|---|---|---|---|---|");
    const OK = sig.ORIGIN_KIND, OR = sig.ORIGIN_REL;
    for (const n of sorted) {
      const nd = st.nodes[n] || {};
      const role = R.roleOf(n, nd);
      const roleJa = (R.ROLE[role] || {}).ja || role;
      const via = nd.originRel && nd.origin ? `${roleJa}（${nm(nd.origin)} の${(OR[nd.originRel] || {}).ja}: ${(OK[nd.originKind] || {}).ja || nd.originKind}）` : roleJa;
      const ax = nd.stub ? "？" : (nd.axioms || []).map((a) => AX_SHORT[a] || a).join(" ") || "—";
      out.push(`| ${code(nm(n))} | ${kindJa(nd.kind)} | ${pkgOf(nd) || "—"} | ${cell(via)} | ${ax} | ${cell(sig.abbrev(concl(nd))) || "—"} |`);
    }
    return out;
  }

  /* 定義の構成図。命題でない宣言に「前提」は無いので、何から組み立てられているかを木で示す。
     子は役割つき（○ 定義・型 / • 補題 / ★ 公理）、[型] は型に現れる・[証] は本体にだけ現れる。
     骨組み（And.intro …）と断片は通り抜け、同じ宣言は初出だけ展開する。深さ分だけ降りる。 */
  /* 深さの先に前提（補題・公理。構成図なら語彙も）が続くか。図の破線枠（more）に使う */
  const hasMore = (n, st, withVocab) => {
    const x = st.nodes[n] || {};
    if (x.stub) return false;
    const p = R.split(n, st.nodes);
    return p.axiom.length + p.lemma.length + (withVocab ? p.vocab.length : 0) > 0;
  };

  function constructionSection(name, st, depth, met, nm, fx) {
    const out = ["", `## 構成図（深さ ${depth}。○ 定義・型 / • 補題 / ★ 公理。[型] 型に現れる / [証] 本体にだけ現れる）`, "", "```"];
    const seen = new Set([name]);
    const byClosure = (a, b) => ((met.closure[a.name] || 0) - (met.closure[b.name] || 0)) || (a.name < b.name ? -1 : 1);
    const nd0 = st.nodes[name] || {};
    out.push(`${nm(name)} : ${sig.abbrev(concl(nd0)) || "—"}`);
    // 図は同じ走査で組む。既出の材料も辺は引く（木では二本目の辺が消える。図では DAG として残る）
    const mm = fx.on ? mermaidBuilder() : null;
    if (mm) declNode(mm, name, st, nm, ["root"]);
    const walk = (m, d, prefix) => {
      const parts = R.split(m, st.nodes);
      const kids = [...parts.axiom, ...parts.lemma, ...parts.vocab].sort(byClosure);
      kids.forEach((k, i) => {
        const last = i === kids.length - 1;
        const x = st.nodes[k.name] || {};
        const role = R.roleOf(k.name, x);
        const mark = role === "axiom" ? "★" : role === "lemma" ? "•" : "○";
        const dup = seen.has(k.name);
        out.push(`${prefix}${last ? "└─ " : "├─ "}${mark} ${nm(k.name)} [${k.via === "type" ? "型" : "証"}]${x.usesSorry ? " (sorry)" : ""} : ${sig.abbrev(concl(x)) || kindJa(x.kind)}${dup ? "  （既出）" : ""}`);
        const descend = d > 1 && ((x.typeDeps || []).length + (x.valueDeps || []).length) > 0 && !x.stub;
        if (mm) {
          declNode(mm, k.name, st, nm, !dup && !descend && hasMore(k.name, st, true) ? ["more"] : []);
          mm.edge(m, k.name, k.via);
        }
        if (dup) return;
        seen.add(k.name);
        if (descend) walk(k.name, d - 1, prefix + (last ? "   " : "│  "));
      });
    };
    walk(name, depth, "");
    out.push("```");
    // 材料が無ければ図は積まない（節点一つの図に意味は無い）
    if (mm && mm.size().edges) addFigure(fx, mm, `構成図（深さ ${depth}。既出の材料への辺も引く）`, "構成図");
    return out;
  }

  /* 導出図の文章版。前提を一行一前提で、深さ分だけ入れ子に。公理は ★。同じ宣言は初出だけ展開する。
     図は前提（補題・公理）の関係だけ（語彙は脚注のまま）。文章では初出の親の下にしか現れない共有の前提も、
     図では二本目以降の辺を引く。 */
  function figureSection(name, st, depth, met, nm, fx) {
    if (!(st.nodes[name] || {}).isProp) return constructionSection(name, st, depth, met, nm, fx);
    const out = ["", `## 導出図（深さ ${depth}。前提は横線の上、結論は下。★ 公理。[型] 主張に現れる / [証] 証明にだけ現れる）`, ""];
    const seen = new Set([name]);
    const byClosure = (a, b) => ((met.closure[a.name] || 0) - (met.closure[b.name] || 0)) || (a.name < b.name ? -1 : 1);
    const mm = fx.on ? mermaidBuilder() : null;
    if (mm) declNode(mm, name, st, nm, ["root"]);
    const fig = (m, d, ind) => {
      const pad = " ".repeat(ind);
      const nd = st.nodes[m] || {};
      const parts = R.split(m, st.nodes);
      const all = [...parts.axiom.slice().sort(byClosure), ...parts.lemma.slice().sort(byClosure)];
      const prem = all.filter((p) => !seen.has(p.name));
      if (mm) for (const p of all) {
        const x = st.nodes[p.name] || {};
        const descend = d > 1 && ((x.typeDeps || []).length + (x.valueDeps || []).length) > 0;
        declNode(mm, p.name, st, nm, !seen.has(p.name) && !descend && hasMore(p.name, st, false) ? ["more"] : []);
        mm.edge(m, p.name, p.via);
      }
      for (const p of prem) seen.add(p.name);
      if (!prem.length) {
        out.push(pad + "（前提なし — 定義そのもの、または論理の骨組みだけで閉じている）");
      }
      for (const p of prem) {
        const x = st.nodes[p.name] || {};
        const role = R.roleOf(p.name, x);
        const sh = x.isProp && x.shape && sig.SHAPE[x.shape] ? ` [${sig.SHAPE[x.shape].ja}]` : "";
        out.push(pad + `${role === "axiom" ? "★ " : "• "}${nm(p.name)}${sh} [${p.via === "type" ? "型" : "証"}]${x.usesSorry ? " (sorry)" : ""}`);
        const c = concl(x);
        if (c) out.push(pad + "    ⊢ " + sig.abbrev(c));
        if (d > 1 && ((x.typeDeps || []).length + (x.valueDeps || []).length) > 0) fig(p.name, d - 1, ind + 4);
      }
      out.push(pad + "─".repeat(Math.max(24, 60 - ind)) + " " + nm(m));
      out.push(pad + "⊢ " + (sig.abbrev(concl(nd)) || "—"));
      const foot = [];
      if (parts.vocab.length) foot.push(`語彙 ${parts.vocab.length}: ${parts.vocab.map((v) => nm(v.name)).join(", ")}`);
      if (parts.frame.length) foot.push(`骨組み ${parts.frame.length}: ${parts.frame.map((v) => nm(v.name)).join(", ")}`);
      if (parts.part && parts.part.length) foot.push(`断片 ${parts.part.length}: ${parts.part.map((v) => nm(v.name)).join(", ")}`);
      for (const f of foot) out.push(pad + "    " + f);
    };
    out.push("```");
    fig(name, depth, 0);
    out.push("```");
    // 前提が無ければ図は積まない（`Iff.rfl` で閉じる定理で節点一つの図を実測）
    if (mm && mm.size().edges) addFigure(fx, mm, `導出図（深さ ${depth}。前提の補題・公理だけ。共有された前提への辺も引く）`, "導出図");
    return out;
  }

  /* 基盤・原子・境界は同じ ↓x（断片を由来に埋め戻した索引）から取る。計量の |↓x| も同じ値を出す。 */
  function downSet(name, dv) {
    const idx = dv.inlinedIdx || dv.declIdx;
    const down = G.reachable(name, idx.dep, 64);
    return { idx, down };
  }

  /* 基盤 ∂_T x（graph.foundation）。対象 T（external でない節点）の閉包から外へ出る先を、
     型・構造体／定義／補題／配管 に分け、多重度（使う対象側の宣言）と、主張が立脚するか（型依存だけの
     閉包から出る）証明が持ち込んだかを添える。原子 min(↓x) は Mathlib の上ではどの定理でも同じ集合
     なので一行で済ませる（以前はこれが節の全部で、型クラスが原子として並んでいた）。 */
  function foundationSection(name, st, dv, nm) {
    const { idx, down } = downSet(name, dv);
    const mf = G.minimalAndFrontier(Object.keys(down), idx.dep, (n) => !!(st.nodes[n] && st.nodes[n].stub));
    const inT = (n) => !!st.nodes[n] && !st.nodes[n].external;
    const fd = G.foundation(name, idx.dep, (dv.inlinedTypeIdx || idx).dep, inT);
    const out = ["", `## 基盤（対象の閉包から外へ出る先 ∂_T x。${fd.list.length} 件）`, "",
      `対象 T（レポートの対象＋内部補助）の中で ${code(nm(name))} から辿れる宣言は ${fd.closureSize} 件（主張の閉包は ${fd.statementClosureSize} 件）。`,
      "その閉包から対象の外へ出る辺の先 z ∉ T を全て挙げる。×k は z を直接使う対象側の宣言の数。[主張] は主張（型依存だけの閉包）が立脚するもの、[証明] は証明が持ち込んだもの（主張には現れない）。"];
    // 原子は一行。公理を先に
    const atoms = mf.trueMinimal.slice().sort((a, b) => (((st.nodes[b] || {}).kind === "axiom") - ((st.nodes[a] || {}).kind === "axiom")) || (a < b ? -1 : 1));
    out.push("", `原子 min(↓x)（依存先を持たない宣言と公理。${atoms.length} 件 / 下方閉集合 ${Object.keys(down).length} 件）: `
      + (atoms.length ? atoms.map((m) => `${code(nm(m))}${(st.nodes[m] || {}).kind === "axiom" ? "（公理）" : ""}`).join(", ") : "なし"));
    const groups = new Map();
    for (const e of fd.list) {
      const g = R.foundationGroup(e.name, st.nodes[e.name]);
      (groups.get(g) || groups.set(g, []).get(g)).push(e);
    }
    for (const g of R.GROUP_ORDER) {
      if (!groups.has(g)) continue;
      const es = groups.get(g).slice().sort((a, b) => (b.users.length - a.users.length) || (a.name < b.name ? -1 : 1));
      out.push("", `### ${R.GROUP[g].ja}（${es.length}）`);
      for (const e of es) {
        const nd = st.nodes[e.name] || {};
        const users = e.users.map((y) => nm(y));
        out.push(`- ${code(nm(e.name))} ×${e.users.length} [${e.inStatement ? "主張" : "証明"}]${pkgOf(nd) ? ` ${pkgOf(nd)}` : ""}${concl(nd) ? ` — ${cell(sig.abbrev(concl(nd)))}` : ""}`
          + `　← ${users.slice(0, 6).map(code).join(", ")}${users.length > 6 ? ` ほか ${users.length - 6} 件` : ""}`);
      }
    }
    if (!fd.list.length) out.push("", "対象の閉包は外へ出ない（対象の中で閉じている）。");
    return out;
  }

  /* 境界 ∂x = ↓x ∖ K（K = レポートの知識領域: 対象＋内部補助＋外部一段）。
     集合の列挙では「何が何を利用しているか」が消えるので、二部グラフ
       E_x = { (y, z) : y ∈ ↓x ∩ K, z ∈ ∂x, y → z }
     として、既知の宣言 y（中心からの段数つき、近い順）ごとに、その直接依存のうち範囲外のもの z を
     名前空間で束ねて全て示す。既知の構造体の成員（射影・構成子）と注釈は境界から外して別に数える
     （graph.cleanFrontier。射影への依存は構造体への依存と同じ情報で、「依存が分からない点」ではない）。 */
  function frontierSection(name, st, dv, nm, fx) {
    const { idx, down } = downSet(name, dv);
    const mf = G.minimalAndFrontier(Object.keys(down), idx.dep, (n) => !!(st.nodes[n] && st.nodes[n].stub));
    const fc = G.cleanFrontier(mf.frontier, st.nodes);
    const out = ["", `## 境界（読み込んだ範囲の切れ目。${fc.rest.length} 件）`, "",
      "レポートの範囲外へ依存が続く点（外部の宣言は一段しか辿っていない）。極小元ではなく、本当の極小元はこの先を辿らなければ確定しない。",
      "「既知の宣言(中心からの段数) → その直接依存のうち範囲外のもの」の形で、近い順に全て示す。右側は名前空間で束ね `Ns.{a, b}`。"];
    const memberCount = [...fc.members.values()].reduce((a, b) => a + b.length, 0);
    if (memberCount) out.push(`既知の構造体の成員（射影・構成子）${memberCount} 件は境界に数えず構造体に畳む: `
      + [...fc.members.entries()].sort((a, b) => b[1].length - a[1].length).map(([o, ls]) => `${code(nm(o))} {${ls.join(", ")}}`).join("; "));
    if (fc.annotations.length) out.push(`elaborator の注釈 ${fc.annotations.length} 件（${[...new Set(fc.annotations.map((a) => a.replace(/^.*\./, "")))].join(", ")}）は依存に数えない。`);
    if (fc.rest.length) {
      const fr = new Set(fc.rest);
      out.push("");
      const refs = [];
      for (const y of Object.keys(down)) {
        if (fr.has(y)) continue;
        const zs = (idx.dep[y] || []).filter((z) => fr.has(z));
        if (zs.length) refs.push([y, zs]);
      }
      refs.sort((a, b) => (down[a[0]] - down[b[0]]) || (a[0] < b[0] ? -1 : 1));
      const bundle = (zs) => {
        const g = new Map();
        for (const z of zs) {
          const s = nm(z), i = s.lastIndexOf(".");
          const ns = i < 0 ? "" : s.slice(0, i), leaf = i < 0 ? s : s.slice(i + 1);
          (g.get(ns) || g.set(ns, []).get(ns)).push(leaf);
        }
        return [...g.entries()].sort((a, b) => b[1].length - a[1].length || (a[0] < b[0] ? -1 : 1))
          .map(([ns, ls]) => (ns ? `${code(ns)}.{${ls.join(", ")}}` : ls.map(code).join(", "))).join("; ");
      };
      /* 型クラスの配管（構造体の射影 `X.toY`・インスタンス・構成子 `mk`）は数が多く、補題・定義の行を
         埋める。情報は落とさず、二つの小節に分けて同じ形式で全て出す。判定は roles.isPlumbing（基盤と共通）。 */
      const plumbing = (y) => R.isPlumbing(y, st.nodes[y]);
      const main = refs.filter(([y]) => !plumbing(y)), pipes = refs.filter(([y]) => plumbing(y));
      out.push(`#### 補題・定義から（${main.length} 件）`);
      for (const [y, zs] of main) out.push(`- ${code(nm(y))}(${down[y]}) → ${bundle(zs)}`);
      out.push("", `#### 型クラスの配管から（射影・インスタンス・構成子。${pipes.length} 件）`);
      for (const [y, zs] of pipes) out.push(`- ${code(nm(y))}(${down[y]}) → ${bundle(zs)}`);
      out.push("", `（既知の宣言 ${refs.length} 件が、範囲外の ${fc.rest.length} 件を参照している）`);
      /* 図: 二部関係 E_x のうち、読み手にとって意味のある部分。
           左 = 対象（レポートの範囲）の宣言。範囲外の宣言（Mathlib の補題）が範囲外を参照する分は
               「Mathlib が Mathlib を使う」事実で、この定理の読み手の関心ではない（文章版には全て
               ある）。対象の宣言が ↓x に無い主語（Mathlib の宣言そのもの）なら、全体を名前空間の
               商で描く。
           右 = 範囲外の宣言を名前空間 k 成分で束ねたもの。k は図が上限に収まる最大
               （完全な名前空間 → 3 → 2 → 1）。札 = 束ねた辺の本数（1 なら無印）。
         cslib の定理で実測: 全体の商は k=1 でも 270 節点で描けないが、対象 → 名前空間なら収まる。 */
      if (fx.on) {
        const nsOf = (n, k) => {
          const p = u(n).split(".").slice(0, -1);
          if (!p.length) return "（名前空間なし）";
          return k === Infinity ? p.join(".") : p.slice(0, k).join(".");
        };
        const kDesc = (k) => (k === Infinity ? "完全な名前空間" : `先頭 ${k} 成分`);
        const own = refs.filter(([y]) => !((st.nodes[y] || {}).external));
        const mm = mermaidBuilder();
        let caption;
        if (own.length) {
          let chosen = null;
          for (const k of [Infinity, 3, 2, 1]) {
            const right = new Map(), pairs = new Map();
            for (const [y, zs] of own) for (const z of zs) {
              const Rn = nsOf(z, k);
              (right.get(Rn) || right.set(Rn, new Set()).get(Rn)).add(z);
              const key = y + "\u0000" + Rn;
              const c = pairs.get(key) || pairs.set(key, { y, R: Rn, n: 0 }).get(key);
              c.n++;
            }
            if ((own.length + right.size <= FIG_MAX.nodes && pairs.size <= FIG_MAX.edges) || k === 1) { chosen = { k, right, pairs }; break; }
          }
          for (const [y] of own) declNode(mm, y, st, nm, [], `${nm(y)} (${down[y]})`);
          for (const [Rn, set] of chosen.right) mm.node("F:" + Rn, `${Rn}（範囲外 ${set.size}）`, "stub", ["stub"]);
          for (const c of chosen.pairs.values()) mm.edge(c.y, "F:" + c.R, "type", c.n > 1 ? String(c.n) : "");
          caption = `境界のうち対象の宣言 ${own.length} 件（括弧は段数）が範囲外を直接参照する先。右は名前空間（${kDesc(chosen.k)}）で束ね、札は辺の本数。範囲外の宣言どうしの参照は本文のみ`;
        } else {
          let chosen = null;
          for (const k of [Infinity, 3, 2, 1]) {
            const left = new Map(), right = new Map(), pairs = new Map();
            for (const [y, zs] of refs) {
              const L = nsOf(y, k), isPipe = plumbing(y);
              (left.get(L) || left.set(L, new Set()).get(L)).add(y);
              for (const z of zs) {
                const Rn = nsOf(z, k);
                (right.get(Rn) || right.set(Rn, new Set()).get(Rn)).add(z);
                const key = L + "\u0000" + Rn;
                const c = pairs.get(key) || pairs.set(key, { L, R: Rn, main: 0, pipe: 0 }).get(key);
                if (isPipe) c.pipe++; else c.main++;
              }
            }
            // 左右で同名の束（既知の `PMF` と範囲外の `PMF`）は別の節点（鍵に K: / F: を付ける）
            if ((left.size + right.size <= FIG_MAX.nodes && pairs.size <= FIG_MAX.edges) || k === 1) { chosen = { k, left, right, pairs }; break; }
          }
          for (const [L, set] of chosen.left) mm.node("K:" + L, `${L}（既知 ${set.size}）`, "bundle", ["bundle"]);
          for (const [Rn, set] of chosen.right) mm.node("F:" + Rn, `${Rn}（範囲外 ${set.size}）`, "stub", ["stub"]);
          for (const c of chosen.pairs.values()) {
            const lab = [c.main ? String(c.main) : "", c.pipe ? `配管 ${c.pipe}` : ""].filter(Boolean).join(" / ");
            mm.edge("K:" + c.L, "F:" + c.R, "type", lab);
          }
          caption = `境界の関係を名前空間で束ねたもの（${kDesc(chosen.k)}。既知 ${chosen.left.size} 束 → 範囲外 ${chosen.right.size} 束。札は辺の本数、「配管」は型クラスの配管からの分）`;
        }
        addFigure(fx, mm, caption, "極小元と境界");
      }
    }
    return out;
  }

  function refsSection(name, st, dv, met, nm) {
    const idx = dv.declIdx;
    const out = [];
    out.push(...depTable(idx.refType[name] || [], st, met, `主張で参照（${nm(name)} についての定理・性質）`,
      `${code(nm(name))} を主張（型）に含む宣言。`, nm));
    out.push(...depTable(idx.refValue[name] || [], st, met, `証明で参照（${nm(name)} を道具として使う）`,
      `${code(nm(name))} を証明（値）でのみ使う宣言。`, nm));
    return out;
  }

  /* 順序区間 [s, c] = ↑s ∩ ↓c を、c から s へ下る層と辺で。一本の道筋（最短）も添える。 */
  function pathSection(subject, center, st, dv, nm, edgeList, fx) {
    const idx = dv.declIdx;
    const u = nm;
    if (!subject || subject === center) return ["", "## 経路", "", "主語が中心そのものなので区間はありません。"];
    let top = center, bottom = subject;
    let iv = G.orderInterval(center, subject, idx.dep, idx.ref, 64);
    let dir = `${u(center)}（中心）が ${u(subject)} を使う向き`;
    if (!iv.size) { iv = G.orderInterval(subject, center, idx.dep, idx.ref, 64); top = subject; bottom = center; dir = `${u(subject)} が ${u(center)}（中心）を使う向き`; }
    const out = ["", `## 経路（順序区間 [${u(bottom)}, ${u(top)}] = ↑${u(bottom)} ∩ ↓${u(top)}）`];
    if (!iv.size) { out.push("", `読み込んだ範囲に ${u(subject)} と ${u(center)} を結ぶ経路はありません。`); return out; }
    out.push("", `${dir}。区間の節点 ${iv.size} 件。`);
    const adj = {};
    for (const x of iv) adj[x] = (idx.dep[x] || []).filter((y) => iv.has(y));
    const hop = G.reachable(top, adj, 64);
    const lv = G.longestPathLevels(top, adj, hop);
    // 断片・派生には役割を添える（`schemeWith._proof_1` が何かを名前だけで読ませない）
    const OR = sig.ORIGIN_REL, OK = sig.ORIGIN_KIND;
    const tag = (x) => {
      const n = st.nodes[x] || {};
      return n.originRel && n.origin ? `（${u(n.origin)} の${(OR[n.originRel] || {}).ja}: ${(OK[n.originKind] || {}).ja || n.originKind}）` : "";
    };
    out.push("", "### 層（ℓ = 上端からの最長導出鎖の長さ）");
    lv.layers.forEach((L, l) => { if (L.length) out.push(`- ℓ${l}: ${L.map((x) => code(u(x)) + tag(x)).join(", ")}`); });
    // 一本の道筋（最短）
    const parent = { [top]: null }, q = [top];
    for (let i = 0; i < q.length && !(bottom in parent); i++) for (const y of adj[q[i]]) if (!(y in parent)) { parent[y] = q[i]; q.push(y); }
    let chain = null;
    if (bottom in parent) {
      chain = []; for (let x = bottom; x; x = parent[x]) chain.push(x);
      chain.reverse();
      out.push("", "### 一本の道筋（最短）", "", chain.map((x, i) => {
        if (!i) return code(u(x));
        const k = idx.edgeKind[chain[i - 1] + " " + x] === "value" ? "証" : "型";
        return `→[${k}] ${code(u(x))}`;
      }).join(" "));
    }
    const order = [];
    lv.layers.forEach((L) => order.push(...L));
    const kindOf = (x, y) => (idx.edgeKind[x + " " + y] === "value" ? "証" : "型");
    if (edgeList) {
      out.push("", "### 区間の辺（u → v: u が v を使う。[型] 主張に現れる / [証] 証明にだけ現れる）");
      for (const x of order) for (const y of adj[x]) out.push(`- ${code(u(x))} →[${kindOf(x, y)}] ${code(u(y))}`);
    } else {
      out.push("", "### 区間の中での依存（u → v₁, v₂ …: u が v を使う。[型] 主張に現れる / [証] 証明にだけ現れる）");
      for (const x of order) {
        if (!adj[x].length) continue;
        out.push(`- ${code(u(x))} → ${adj[x].map((y) => `${code(u(y))}[${kindOf(x, y)}]`).join(", ")}`);
      }
    }
    /* 図: 区間の全節点を層 ℓ の囲みに置き、辺は推移簡約（Hasse 図）で引く。区間の下端が `Field` の
       ような型クラスだと全節点がそれを直接参照し、52 節点で 233 辺になる（実測）。順序の情報は
       推移簡約で保たれ、直接の辺の全列挙は本文にある。最短の道筋は推移で落ちる辺でも太線で残す。
       上限を超える区間は道筋だけを描き（層の札は節点名に添える）、そう記す。 */
    if (fx.on) {
      const ek = (x, y) => (idx.edgeKind[x + " " + y] === "value" ? "value" : "type");
      const hasse = hasseEdges(order, adj);
      const whole = iv.size <= FIG_MAX.nodes && hasse.length <= FIG_MAX.edges;
      const mm = mermaidBuilder();
      if (whole) {
        for (const x of order) declNode(mm, x, st, u, x === top || x === bottom ? ["root"] : []);
        lv.layers.forEach((L, l) => { if (L.length) mm.subgraph("L" + l, `ℓ${l}`, L); });
        for (const [x, y] of hasse) mm.edge(x, y, ek(x, y));
      } else if (chain) {
        for (const x of chain) mm.node(x, `${u(x)}  ℓ${lv.level[x]}`, (st.nodes[x] || {}).isProp ? "lemma" : "vocab",
          [(st.nodes[x] || {}).isProp ? "lem" : "voc"].concat(x === top || x === bottom ? ["root"] : []));
      }
      if (chain) for (let i = 1; i < chain.length; i++) mm.edge(chain[i - 1], chain[i], "chain");
      addFigure(fx, mm, whole
        ? `順序区間 [${u(bottom)}, ${u(top)}] の Hasse 図。囲みは層 ℓ、太線は最短の道筋（直接の辺 ${order.reduce((s, x) => s + adj[x].length, 0)} 本のうち推移簡約で ${hasse.length} 本）`
        : `順序区間が大きい（${iv.size} 件）ので最短の道筋だけ。節点名の後ろに層 ℓ`, "経路");
    }
    return out;
  }

  function metricsSection(name, st, dv, met) {
    const idx = dv.declIdx;
    const nd = st.nodes[name] || {};
    /* |↓x| は基盤・境界と同じ索引（断片を由来に埋め戻したもの）で数える。以前は元の索引で数えた値を
       ここに、埋め戻した値を極小元の節に出し、同じ記号に二つの値が並んでいた（実測 1446 と 1301）。 */
    const { down } = downSet(name, dv);
    const raw = met.closure[name];
    return ["", "## 計量", "",
      `- 総仮定量 |↓x|: ${Object.keys(down).length}（断片 _proof_<i> を由来に埋め戻して数える${met.exact && raw !== undefined && raw !== Object.keys(down).length ? `。断片を別に数えると ${raw}` : ""}）`,
      `- 導出鎖の深さ: ${met.depth[name] ?? "—"}`,
      `- 直接依存: 型 ${(nd.typeDeps || []).length} / 値 ${(nd.valueDeps || []).length}   参照: 主張 ${(idx.refType[name] || []).length} / 証明 ${(idx.refValue[name] || []).length}`,
      `- 節点数: 型 ${nd.typeSize || 0} / 証明 ${nd.valueSize || 0}`,
      `- 無条件で閉じる: ${met.hered && met.hered[name] ? "はい（依存先も全て無条件）" : "いいえ"}`];
  }

  function metaSection() {
    const m = LDR.DEFAULT_META;
    const isDefault = !!(LDR.DEFAULT_REPORT && S.state.rawText === LDR.DEFAULT_REPORT);
    const out = ["", "## 来歴", ""];
    if (isDefault && m && m.target) {
      out.push(`- 対象: ${m.target.name || "?"}${m.target.gitRev ? " @ " + m.target.gitRev.slice(0, 8) : ""}${m.target.dirty ? "（dirty）" : ""}`);
      out.push(`- toolchain: ${m.target.toolchain || "?"}`);
      if (m.modules) out.push(`- モジュール: ${m.modules.join(" ")}${m.extraArgs && m.extraArgs.length ? "（" + m.extraArgs.join(" ") + "）" : ""}`);
      if (m.generatedAt) out.push(`- 生成: ${m.generatedAt}`);
    } else {
      out.push(`- 読み込んだレポート（宣言 ${S.state.order.length} 件）。来歴の記録なし`);
    }
    out.push(`- 出力: Lean4SemanticBench ビューア、${new Date().toISOString()}`);
    return out;
  }

  /* 注記（列の意味・測り方）。宣言の情報ではないので、選んだときだけ末尾に付ける。 */
  const NOTES = ["", "## 注記", "",
    "- 事実は依存グラフの元の形で測っている（表示用の派生の畳み込み・骨組みの縮約は行わない）。",
    "- 型依存 = 主張（型）に現れる宣言（何を述べているかを決める）。値依存 = 証明（値）にだけ現れる宣言（どう示したかを決める）。",
    "- 公理は Lean の collectAxioms による現状の証明項の正確な集合。証明の改良で減り得る。「主張に入る」= 型依存の閉包に公理を持つ宣言がある。",
    "- 基盤 ∂_T x = 対象（レポートの対象＋内部補助）の閉包から外へ出る辺の先。原子 min(↓x) は依存先を持たない宣言と公理。境界 ∂x はレポートの範囲外で依存が続く宣言で、極小元ではない（既知の構造体の成員と注釈は数えない）。",
    "- 導出図は論理の骨組み（And.intro / Eq.mpr …）と断片（_proof_<i>）を通り抜けて前提を拾う。",
    "- 順序区間 [s, c] = ↑s ∩ ↓c。ℓ は上端からの最長導出鎖の長さ。",
    "- 付録の図は本文の各節と同じ事実を Mermaid の flowchart で描いたもの（記法は付録の頭）。描けない環境では本文を読む。",
  ];

  /* 末尾の但し書き。レポートの性格（現状の証明構造の解析であって、成否や意味論の保証ではないこと、
     何のための材料か）を、章の選択に関わらず常に最後に置く。 */
  const DISCLAIMER = ["",
    "※上記はあくまで現状の証明構造に関する解析結果であり、その成否や意味論の保証をする事は無いです。しかし、これらの結果を踏まえた上での、メタ的な改善を実施することは、同じ証明や構成を行う事が出来る、より本質的な文脈や流れ、その他の可能な構成・経路を模索する為のレポートとしての側面を持ち、公理依存・過剰な依存が解消について考えたり、意味論や体系について考えを深め、整理する為の材料を提供します。"];

  /** kind: "center" | "selected" | "minimal"。
      opts: { sections: string[], depth: 1..3, fullNames, frontierNames, edgeList }（書き方の既定は情報を落とさない側）。
      章 figures を選ぶと、各節が積んだ図を末尾の付録にまとめる。 */
  function build(kind, opts) {
    const st = S.state, dv = S.derived;
    const sections = new Set((opts && opts.sections) || ALL);
    const depth = Math.max(1, Math.min(3, (opts && opts.depth) || 2));
    const o = opts || {};
    const fullNames = o.fullNames !== false, edgeList = o.edgeList !== false;
    const nm = fullNames ? u : sig.shortName;
    const fx = { on: sections.has("figures"), figs: [] };    // 図を積む入れ物（付録でまとめて出す）
    const center = dv.center;
    let subject, label;
    if (kind === "selected") { subject = st.selected && st.selected !== center ? st.selected : null; label = "選択"; }
    else if (kind === "minimal") { subject = st.traceTarget; label = "経路の対象"; }
    else { subject = center; label = "中心"; }
    if (!subject || !st.nodes[subject]) {
      return { ok: false, text: "", msg: kind === "minimal"
        ? "経路の対象が選ばれていません。基盤・原子・境界のチップ（または公理のチップ）を押して経路を表示してから"
        : kind === "selected" ? "中心と異なる宣言が選ばれていません。グラフや一覧で宣言を押してから" : "中心がありません" };
    }
    const nd = st.nodes[subject];
    const met = S.metrics();
    const out = [];
    out.push(...headerLines(subject, nd, st, nm));
    out.push("", `主語: ${label}${subject !== center ? `（グラフの中心は ${code(nm(center))}）` : "（グラフの中心）"}`);
    if (sections.has("claim")) out.push(...claimSection(nd));
    if (sections.has("path") && kind !== "center") out.push(...pathSection(subject, center, st, dv, nm, edgeList, fx));
    if (sections.has("type")) out.push(...depTable(nd.typeDeps || [], st, met, "型依存", `${code(nm(subject))} の主張（型）に現れる宣言。この宣言が何を述べているかを決める。`, nm));
    if (sections.has("value")) out.push(...depTable(nd.valueDeps || [], st, met, "値依存", `${code(nm(subject))} の証明（値）にだけ現れる宣言。定理ならカーネル検査済み。`, nm));
    if (sections.has("axioms")) out.push(...axiomsSection(subject, st, dv, met, nm, fx));
    if (sections.has("figure")) out.push(...figureSection(subject, st, depth, met, nm, fx));
    if (sections.has("foundation")) out.push(...foundationSection(subject, st, dv, nm));
    if (sections.has("frontier")) out.push(...frontierSection(subject, st, dv, nm, fx));
    if (sections.has("refs")) out.push(...refsSection(subject, st, dv, met, nm));
    if (sections.has("metrics")) out.push(...metricsSection(subject, st, dv, met));
    if (sections.has("meta")) out.push(...metaSection());
    if (fx.on && fx.figs.length) out.push(...appendixLines(fx));
    if (sections.has("notes")) out.push(...NOTES);
    out.push(...DISCLAIMER);
    return { ok: true, text: out.join("\n") + "\n", subject, msg: "" };
  }

  LDR.report = { build, SECTIONS, ALL, STYLE };
})(window.LDR = window.LDR || {});
