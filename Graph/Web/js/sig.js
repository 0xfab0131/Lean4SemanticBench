/* ============================================================
   js/sig.js — シグネチャの表示補助

   束縛の分解そのものは Lean 側が行い、`binders`（`prop` 旗つき）と
   `conclusion` として渡してくる。こちらで Π 連鎖を再解析すると、
   必ず本家と乖離する。ここに置くのは表示のためだけの処理に限る。

     abbrev     完全修飾名を末尾二成分に畳む。桁が溢れて読めないのが
                最大の障害なので、既定でこちらを見せ、元は title で保つ。
     decompose  結論を 関係 / 左辺 / 右辺 に割る。Lean は結論の頭部
                （head）と各引数の頭部（conclArgs）は渡してくるが、
                引数の文字列は渡さないので、表示のためにここで切る。
   ============================================================ */
(function (LDR) {
  "use strict";

  const OPEN = { "(": ")", "{": "}", "[": "]", "⟨": "⟩" };
  const CLOSE = new Set([")", "}", "]", "⟩"]);

  /** 括弧の外側だけを見て、最初に現れる区切りを返す。無ければ null。 */
  function findTop(s, tokens, from) {
    let d = 0;
    for (let i = from || 0; i < s.length; i++) {
      const c = s[i];
      if (OPEN[c]) { d++; continue; }
      if (CLOSE.has(c)) { d--; continue; }
      if (d !== 0) continue;
      for (const t of tokens) if (s.startsWith(t, i)) return { at: i, tok: t };
    }
    return null;
  }

  /** 括弧の外側の空白で分割する。適用の頭部と引数を取り出す。 */
  function splitTopSpaces(s) {
    const out = [];
    let d = 0, cur = "";
    for (const c of s) {
      if (OPEN[c]) { d++; cur += c; continue; }
      if (CLOSE.has(c)) { d--; cur += c; continue; }
      if (d === 0 && /\s/.test(c)) { if (cur) out.push(cur); cur = ""; continue; }
      cur += c;
    }
    if (cur) out.push(cur);
    return out;
  }

  /** 全体を包む括弧だけを外す。途中で閉じるものは外さない。 */
  function strip(s) {
    let t = String(s || "").trim();
    while (t.length > 1 && OPEN[t[0]] && t[t.length - 1] === OPEN[t[0]]) {
      let d = 0, ok = true;
      for (let i = 0; i < t.length; i++) {
        if (OPEN[t[i]]) d++;
        else if (CLOSE.has(t[i])) { d--; if (d === 0 && i < t.length - 1) { ok = false; break; } }
      }
      if (!ok) break;
      t = t.slice(1, -1).trim();
    }
    return t;
  }

  /* 中置の結合子を **結合の弱い順**（= 主結合子になる順）に並べる。Lean の優先度は
       `↔` 20 ＜ `∨` 30 ＜ `∧` 35 ＜ `=` `≠` `≤` `<` `∈` `⊆` … 50
     なので、`a = a' ∧ b = b'` の主結合子は `∧` であり、`=` ではない。括弧の外で最初に
     見つかった記号で切ると「左辺 a / 右辺 a' ∧ b = b'」という主張の誤読になる
     （フィクスチャの `pair_inj`、cslib の `injEq` で実測）。同じ群の中では左から最初の
     出現で切る（`∧` `∨` は右結合なので、最初の出現が最外の結合子）。 */
  const REL_GROUPS = [
    [" ↔ "],
    [" ∨ "],
    [" ∧ "],
    [" = ", " ≠ ", " ≤ ", " < ", " ≥ ", " > ", " ∈ ", " ∉ ", " ⊆ ", " ⊂ ", " ∣ "],
  ];
  const BINDER_HEAD = /^(∃|∀|∃!|fun |λ )/;

  /**
   * 結論を 関係 / 文脈 / 左辺 / 右辺 に割る。
   * 中置記法で書かれていれば主結合子（最も弱い結合子）で、前置適用なら末尾二引数で切る。
   * 先頭が束縛（∃ x, …）や否定（¬a = b は ¬(a = b)）なら、中置で割ると束縛の内側を
   * 切ることになるので割らない（whole のまま見せる）。
   * 二引数に満たなければ左辺・右辺は null（割らずにそのまま見せる）。
   */
  function decompose(conclusion) {
    const c = strip(String(conclusion || "").replace(/\s+/g, " "));
    if (!c) return { rel: null, ctx: [], lhs: null, rhs: null, whole: "" };
    if (BINDER_HEAD.test(c)) return { rel: c.match(BINDER_HEAD)[0].trim(), ctx: [], lhs: null, rhs: null, whole: c };
    if (c.startsWith("¬")) return { rel: "¬", ctx: [], lhs: null, rhs: null, whole: c };
    for (const group of REL_GROUPS) {
      const hit = findTop(c, group, 0);
      if (!hit) continue;
      // 両辺を包むだけの括弧は外す（`(x = y) = (p ∧ q)` の左辺は `x = y`）
      return {
        rel: hit.tok.trim(), ctx: [],
        lhs: strip(c.slice(0, hit.at)),
        rhs: strip(c.slice(hit.at + hit.tok.length)),
        whole: c,
      };
    }
    const parts = splitTopSpaces(c);
    if (parts.length >= 3) {
      return {
        rel: parts[0], ctx: parts.slice(1, parts.length - 2),
        lhs: parts[parts.length - 2], rhs: parts[parts.length - 1], whole: c,
      };
    }
    return { rel: parts.length > 1 ? parts[0] : null, ctx: parts.slice(1), lhs: null, rhs: null, whole: c };
  }

  /* 完全修飾名を末尾二成分に畳む。 */
  const DOTTED = /(?:[^\s().,{}[\]→⟨⟩:]+\.)+[^\s().,{}[\]→⟨⟩:]+/g;
  const abbrev = (s) => String(s || "").replace(DOTTED, (m) => {
    const p = m.split(".");
    return p.length <= 2 ? m : p.slice(-2).join(".");
  });
  /* private 宣言の名前は `_private.<Module>.0.<Decl>`。表示は利用者名 `<Decl>` で行う
     （鍵・索引は実名のまま。実名でなければ依存の辺と一致しない）。 */
  const userName = (n) => String(n || "").replace(/^_private\.(?:[^.]+\.)*?0\./, "");
  const isPrivateName = (n) => /^_private\./.test(String(n || ""));
  const shortName = (n) => {
    const p = userName(n).split(".");
    return p.length <= 2 ? userName(n) : p.slice(-2).join(".");
  };

  /** 主張の形につける短い日本語。Lean 側 `relShape` の値に対応する。 */
  const SHAPE = {
    refl:     { ja: "反射", note: "R a a の形" },
    irrefl:   { ja: "非反射", note: "¬ R a a の形" },
    symm:     { ja: "対称", note: "R a b から R b a" },
    trans:    { ja: "推移", note: "R a m と R m b から R a b" },
    antisymm: { ja: "反対称", note: "R a b と R b a から a = b" },
    total:    { ja: "全域", note: "R a b ∨ R b a の形（線形性）" },
    comm:     { ja: "可換", note: "f a b = f b a の形" },
    assoc:    { ja: "結合", note: "f (f a b) c = f a (f b c) の形" },
    idem:     { ja: "冪等", note: "f a a = a の形" },
    absorb:   { ja: "吸収", note: "f a (g a b) = a の形。二つの半束を束に結ぶ" },
    distrib:  { ja: "分配", note: "f a (g b c) = g (f a b) (f a c) の形" },
    mono:     { ja: "単調", note: "関係 R の仮定から、同じ頭部 f の像について R。担い手は f、関係は相方" },
  };

  /** 由来の種類（Lean 側 `originOf` の kind）につける日本語。一覧・グラフ・検査で共通。 */
  const ORIGIN_KIND = {
    constructor:     { ja: "構成子",   note: "帰納型の構成子（カーネルの宣言）" },
    projection:      { ja: "射影",     note: "構造体のフィールドの射影関数" },
    rec:             { ja: "再帰子",   note: "カーネルの再帰子（普遍性）" },
    recOn:           { ja: "再帰子",   note: "再帰子の言い換え（主引数を先に）" },
    brecOn:          { ja: "再帰子",   note: "累積再帰（構造的再帰の実装用）" },
    auxRec:          { ja: "再帰子",   note: "補助再帰子（構成子ごとの除去など）" },
    casesOn:         { ja: "場合分け", note: "帰納仮定なしの場合分け" },
    ctorIdx:         { ja: "番号",     note: "構成子の番号を返す関数" },
    noConfusion:     { ja: "区別",     note: "構成子が互いに素であること・単射であること" },
    noConfusionType: { ja: "区別",     note: "noConfusion の結論の型" },
    inj:             { ja: "単射性",   note: "構成子の単射性（含意の形）" },
    injEq:           { ja: "単射性",   note: "構成子の単射性（等式の形、simp 用）" },
    hinj:            { ja: "単射性",   note: "添字つきの単射性" },
    sizeOf_spec:     { ja: "大きさ",   note: "sizeOf の計算規則" },
    sizeOf_inst:     { ja: "大きさ",   note: "SizeOf のインスタンス" },
    sizeOf:          { ja: "大きさ",   note: "sizeOf の実装関数" },
    eqn:             { ja: "等式",     note: "定義の等式補題（eq_<i> / eq_def）" },
    matcher:         { ja: "断片",     note: "match 式の補助関数" },
    proof:           { ja: "断片",     note: "証明の切り出し（_proof_<i>）" },
    internal:        { ja: "断片",     note: "内部補助" },
  };
  const ORIGIN_REL = {
    member: { ja: "成員", note: "定義の一部として利用者が書いたもの" },
    facet:  { ja: "派生", note: "由来から機械的に導かれる別の宣言" },
    part:   { ja: "断片", note: "由来の証明・本体の一部" },
  };

  LDR.sig = { decompose, abbrev, shortName, userName, isPrivateName, splitTopSpaces, findTop, strip, SHAPE, ORIGIN_KIND, ORIGIN_REL };
})(window.LDR = window.LDR || {});
