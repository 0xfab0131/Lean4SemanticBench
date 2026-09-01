/* ============================================================
   js/roles.js — 依存を役割で分ける

   証明項に現れる定数を一列に並べても、それは証明の図ではない。
   数学者が読みたいのは「どの既知の結果を使ってこれが出たか」であって、
   `Prod.fst` や `Iff.mpr` がそこに混ざっていると本筋が埋もれる。
   三つに分ける。

     lemma  既に証明された言明。導出図の前提になる。isProp が真のもの。
     vocab  主張を書くための語彙。定義・型。isProp が偽のもの。
     frame  論理の骨組み。連言・選言・存在・等式の構成子と除去子、
            再帰子、内部生成された補助宣言。読み手が確認する対象ではない。

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
    "id", "congrArg", "congrFun", "cast", "rfl", "trivial", "absurd",
    "Prod", "Prod.mk", "Prod.fst", "Prod.snd",
    "PProd", "PProd.mk", "PProd.fst", "PProd.snd",
    "Sigma", "Sigma.mk", "Sigma.fst", "Sigma.snd",
    "PSigma", "PSigma.mk", "PSigma.fst", "PSigma.snd",
    "Subtype", "Subtype.mk", "Subtype.val", "Subtype.property",
    "Unit", "Unit.unit", "PUnit", "PUnit.unit", "PLift", "ULift",
    "Function.comp", "Membership.mem", "Setoid",
  ]);

  /* 名前の形で分かる自動生成物。再帰子・場合分け・内部補助。 */
  const FRAME_SUFFIX = /(\.rec|\.recOn|\.casesOn|\.brecOn|\.below|\.ndrec|\.noConfusion|\.noConfusionType|\.injEq|\.sizeOf|\.sizeOf_spec|\.mk\.injEq)$/;
  const FRAME_INTERNAL = /(^_|\._|\.match_\d|\.proof_\d|\.eq_\d|\.eq_def|\.congr_|\.«)/;

  function isFrameName(name) {
    const n = String(name || "");
    return FRAME_NAMES.has(n) || FRAME_SUFFIX.test(n) || FRAME_INTERNAL.test(n);
  }

  /**
   * 役割を返す。node は store の nodes の要素（無くても名前だけで判定する）。
   *   "axiom" | "lemma" | "vocab" | "frame"
   */
  function roleOf(name, node) {
    const nd = node || {};
    if (nd.kind === "axiom") return "axiom";          // 公理は決して畳まない
    if (isFrameName(name)) return "frame";
    if (nd.isProp) return "lemma";
    return "vocab";
  }

  const ROLE = {
    axiom: { ja: "公理",  c: "#EA580C", note: "これ以上遡れない仮定" },
    lemma: { ja: "補題",  c: "#4F46E5", note: "既に証明された言明。導出の前提" },
    vocab: { ja: "語彙",  c: "#0D9488", note: "主張を書くための定義・型" },
    frame: { ja: "骨組み", c: "#A8A29E", note: "論理結合子・再帰子・内部生成物" },
  };

  /**
   * 一つの宣言の直接依存を役割ごとに仕分ける。
   * `via` は型に現れたか値に現れたかで、前者は主張を、後者は証明を支えている。
   */
  function split(name, nodes) {
    const nd = nodes[name];
    const out = { axiom: [], lemma: [], vocab: [], frame: [] };
    if (!nd) return out;
    const push = (d, via) => {
      const r = roleOf(d, nodes[d]);
      if (!out[r].some((x) => x.name === d)) out[r].push({ name: d, via });
    };
    for (const d of nd.typeDeps || []) push(d, "type");
    for (const d of nd.valueDeps || []) push(d, "value");
    return out;
  }

  LDR.roles = { roleOf, isFrameName, split, ROLE, FRAME_NAMES };
})(window.LDR = window.LDR || {});
