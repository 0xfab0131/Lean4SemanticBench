/* ============================================================
   js/roles.js — 依存を役割で分ける

   証明項に現れる定数を一列に並べても、それは証明の図ではない。
   数学者が読みたいのは「どの既知の結果を使ってこれが出たか」であって、
   `Prod.fst` や `Iff.mpr` がそこに混ざっていると本筋が埋もれる。
   四つに分ける。

     lemma  既に証明された言明。導出図の前提になる。isProp が真のもの。
     vocab  主張を書くための語彙。定義・型。isProp が偽のもの。
     frame  論理の骨組み。連言・選言・存在・等式の構成子と除去子。
            読み手が確認する対象ではない。core の論理結合子に限る（名前の一覧）。
     part   断片。`_proof_<i>` / `match_<i>` のように、ある宣言の証明・本体の一部を
            切り出したもの（レポートの originRel = "part"）。由来の中身として通り抜ける。

   派生（originRel = "facet"。`mk.inj` / `casesOn` 等）は骨組みではない。
   `pair_inj` の前提は `mk.inj`（単射性）であり、導出図ではそのまま前提として残す。
   由来による畳み込みはグラフ側（graph.effectiveNodes）の仕事で、ここでは扱わない。

   公理だけは骨組みに見えても決して畳まない。`propext` や `Classical.choice`
   がここに紛れて消えるようなことがあってはならない。
   ============================================================ */
(function (LDR) {
  "use strict";

  /* 論理の骨組みとして畳んでよい定数。Lean core の論理結合子まわりに限る。 */
  const FRAME_NAMES = new Set([
    "And", "And.intro", "And.left", "And.right", "And.elim",
    "Or", "Or.inl", "Or.inr", "Or.elim",
    "Iff", "Iff.intro", "Iff.mp", "Iff.mpr", "Iff.rfl",
    "Exists", "Exists.intro", "Exists.elim",
    "Eq", "Eq.refl", "Eq.symm", "Eq.trans", "Eq.mp", "Eq.mpr", "Eq.subst", "Eq.ndrec",
    "HEq", "HEq.refl",
    "True", "True.intro", "False", "False.elim", "Not",
    "id", "congrArg", "congrFun", "congrFun'", "congr", "cast", "rfl", "trivial", "absurd",
    /* simp が置く書き換えの補助。`of_eq_true` / `eq_self` / `eq_true` / `eq_false` は `Eq.rec` と propext
       だけで閉じ、数学的な前提ではない。畳むと、その中の propext が ★ の前提として直接現れる
       （simp が公理を持ち込んだ事実は隠れない）。 */
    "of_eq_true", "of_eq_false", "eq_self", "eq_true", "eq_false", "ne_eq", "iff_self", "implies_true",
    "true_and", "and_true", "true_or", "or_true", "and_self", "or_self", "not_false_eq_true", "iff_true", "true_iff",
    "Prod", "Prod.mk", "Prod.fst", "Prod.snd",
    "PProd", "PProd.mk", "PProd.fst", "PProd.snd",
    "Sigma", "Sigma.mk", "Sigma.fst", "Sigma.snd",
    "PSigma", "PSigma.mk", "PSigma.fst", "PSigma.snd",
    "Subtype", "Subtype.mk", "Subtype.val", "Subtype.property",
    "Unit", "Unit.unit", "PUnit", "PUnit.unit", "PLift", "ULift",
    "Function.comp", "Membership.mem", "Setoid",
  ]);

  /* 骨組みは core の論理結合子の一覧だけで決める。生成物・内部補助は名前では判定しない
     （由来 originRel がレポートに入っている。旧形式は graph.legacyOrigin が補う）。 */
  function isFrameName(name) {
    return FRAME_NAMES.has(String(name || ""));
  }

  /**
   * 役割を返す。node は store の nodes の要素（無くても名前だけで判定する）。
   *   "axiom" | "lemma" | "vocab" | "plumbing" | "unknown" | "frame" | "part"
   *
   * plumbing  型クラスの配管（射影 `X.toY`・インスタンス・構成子 `mk`）。命題でも（Prop 値クラスの親射影
   *           `RingHomClass.toAddMonoidHomClass`、インスタンス `RingHom.instRingHomClass`）数学的な前提では
   *           ないので、導出図の前提に並べない（cslib の定理で前提 12 件のうち 2 件が配管だった。実測）。
   * unknown   範囲外のスタブ。種別も isProp も分からないので、語彙（定義）とは言えない。導出図では
   *           「前提は範囲外」と正直に書く（以前は語彙に落ち、`map_multiset_sum`（定理）が語彙に混じって
   *           「前提なし」と出ていた。実測）。
   */
  function roleOf(name, node) {
    const nd = node || {};
    if (nd.kind === "axiom") return "axiom";          // 公理は決して畳まない
    if (isFrameName(name)) return "frame";
    if (nd.originRel === "part" && nd.origin) return "part";
    if (nd.stub) return "unknown";
    if (isPlumbing(name, nd)) return "plumbing";
    if (nd.isProp) return "lemma";
    return "vocab";
  }

  const ROLE = {
    axiom:    { ja: "公理",  c: "#EA580C", note: "これ以上遡れない仮定" },
    lemma:    { ja: "補題",  c: "#4F46E5", note: "既に証明された言明。導出の前提" },
    vocab:    { ja: "語彙",  c: "#0D9488", note: "主張を書くための定義・型（概念）" },
    plumbing: { ja: "配管",  c: "#78716C", note: "型クラスの配管（射影・インスタンス・構成子）。前提ではない" },
    unknown:  { ja: "範囲外", c: "#A8A29E", note: "レポートの範囲外で種別が分からない" },
    frame:    { ja: "骨組み", c: "#A8A29E", note: "論理結合子（And.intro / Eq.mpr …）と simp の補助" },
    part:     { ja: "断片",  c: "#A8A29E", note: "ある宣言の証明・本体から切り出された一部（_proof_<i> / match_<i>）" },
  };

  /**
   * 一つの宣言の依存を役割ごとに仕分ける。
   * `via` は型に現れたか値に現れたかで、前者は主張を、後者は証明を支えている。
   *
   * 骨組みと断片は **通り抜ける**。`double_eq` の証明が `_proof_1_1`（omega が切り出した
   * 断片）だけを直接呼ぶとき、その中で使われた補題や公理は `_proof_1_1` の依存にある。
   * 直接依存だけを見ると前提が空になり、公理チップとの矛盾が生じる（自己解析で実測）。
   * 断片は由来の証明の一部なので、その先の補題・公理を前提として拾う。`via` は初手を継承する。
   * 直接の骨組み・断片だけを `frame` / `part` に数える（通り抜けた先は数えない）。
   * 派生（`mk.inj` 等）は通り抜けない。それ自体が前提である。
   */
  function split(name, nodes) {
    const nd = nodes[name];
    const out = { axiom: [], lemma: [], vocab: [], plumbing: [], unknown: [], frame: [], part: [] };
    if (!nd) return out;
    const seen = new Set([name]);
    const visit = (d, via, direct) => {
      if (seen.has(d)) return;
      seen.add(d);
      const r = roleOf(d, nodes[d]);
      if (r === "frame" || r === "part") {
        if (direct) out[r].push({ name: d, via });
        const c = nodes[d];
        if (c) {
          for (const x of c.typeDeps || []) visit(x, via, false);
          for (const x of c.valueDeps || []) visit(x, via, false);
        }
        return;
      }
      out[r].push({ name: d, via });
    };
    for (const d of nd.typeDeps || []) visit(d, "type", true);
    for (const d of nd.valueDeps || []) visit(d, "value", true);
    return out;
  }

  /* ---- 配管の判定 ----
     型クラスの配管（構造体の射影 `X.toY`・インスタンス・構成子 `mk`）は数が多く、補題・定義の行を
     埋める。役割（roleOf）・レポートの境界・ビューアの基盤で同じ判定を使う（二か所で別々に組むと必ず乖離する）。
     関数宣言なので roleOf より後に書いてあっても巻き上げで使える。 */
  function isPlumbing(name, node) {
    const nd = node || {};
    const u = LDR.sig ? LDR.sig.userName(name) : String(name);
    return !!nd.isInstance || nd.kind === "constructor" || nd.originRel === "member"
      || /\.(to[A-Z][^.]*|inst[A-Z][^.]*|mk)$/.test(u) || /^inst[A-Z]/.test(u);
  }
  /** 基盤の群: "type"（型・構造体）/ "def"（定義）/ "lemma"（補題）/ "plumbing"（配管）/ "axiom"。
      範囲外のスタブ（種別不明）は "unknown"。 */
  function foundationGroup(name, node) {
    const nd = node || {};
    if (nd.stub) return "unknown";
    if (nd.kind === "axiom") return "axiom";
    if (isPlumbing(name, nd)) return "plumbing";
    if (nd.kind === "inductive") return "type";
    if (nd.isProp) return "lemma";
    return "def";
  }
  const GROUP = {
    axiom:    { ja: "公理",      note: "これ以上遡れない仮定" },
    type:     { ja: "型・構造体", note: "帰納型・構造体・型クラス" },
    def:      { ja: "定義",      note: "定義（命題でないもの）" },
    lemma:    { ja: "補題",      note: "既に証明された言明" },
    plumbing: { ja: "配管",      note: "型クラスの配管（射影・インスタンス・構成子）" },
    unknown:  { ja: "不明",      note: "範囲外で種別が分からない" },
  };
  const GROUP_ORDER = ["axiom", "type", "def", "lemma", "plumbing", "unknown"];

  LDR.roles = { roleOf, isFrameName, split, ROLE, FRAME_NAMES, isPlumbing, foundationGroup, GROUP, GROUP_ORDER };
})(window.LDR = window.LDR || {});
