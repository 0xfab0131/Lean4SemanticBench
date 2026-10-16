/* ============================================================
   js/pkg.js — パッケージ（依存の出どころ）

   宣言が「どのパッケージに属するか」はモジュール名の先頭成分で決まる
   （`Mathlib.Order.Defs` → Mathlib、`Cslib.Crypto…` → Cslib）。Lean core は
   `Init` / `Lean` / `Std` / `Lake` の四つの根に分かれているが、読み手にとっては
   一つの「core」なので束ねる。

   ここに置くのは三つ。どれも「データから推定する」類ではなく外部の事実の表なので、
   一か所にまとめて持つ（分散すると必ず乖離する）。
     packageOf   モジュール名 → パッケージ名
     colorOf     パッケージ → 色（既知のものは固定、未知のものは名前から決める）
     docsUrl     宣言 → 公式ドキュメントの宣言ページ（doc-gen4 の規則）

   doc-gen4 の文書は `<根 URL>/<モジュールのパス>.html#<完全名>` で宣言ページが決まる
   （mathlib4_docs と cslib の https://api.cslib.io/docs/ で同じ規則を実確認）。
   mathlib4_docs は Mathlib の依存（core / Batteries / Aesop / Qq …）も同じ場所に置く。
   ============================================================ */
(function (LDR) {
  "use strict";

  const CORE = new Set(["Init", "Lean", "Std", "Lake"]);
  const MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs/";

  /* 既知のパッケージ。色は錐の色（藍・青緑・橙）や種別の点の色と衝突しない帯域から選ぶ。
     docs は doc-gen4 の根 URL。無ければ公式文書は出さない（検索リンクは別）。 */
  const KNOWN = {
    core:             { ja: "core",      c: "#78716C", docs: MATHLIB_DOCS },
    Mathlib:          { ja: "Mathlib",   c: "#0284C7", docs: MATHLIB_DOCS },
    Batteries:        { ja: "Batteries", c: "#B45309", docs: MATHLIB_DOCS },
    Aesop:            { ja: "Aesop",     c: "#9333EA", docs: MATHLIB_DOCS },
    Qq:               { ja: "Qq",        c: "#9333EA", docs: MATHLIB_DOCS },
    Plausible:        { ja: "Plausible", c: "#9333EA", docs: MATHLIB_DOCS },
    LeanSearchClient: { ja: "LeanSearchClient", c: "#9333EA", docs: MATHLIB_DOCS },
    ProofWidgets:     { ja: "ProofWidgets", c: "#9333EA", docs: MATHLIB_DOCS },
    Cslib:            { ja: "cslib",     c: "#16A34A", docs: "https://api.cslib.io/docs/" },
  };

  /** モジュール名 → パッケージ名。範囲外のスタブ（"(範囲外)"）や空は ""。 */
  function packageOf(module) {
    const m = String(module || "");
    if (!m || m.startsWith("(")) return "";
    const p = m.split(".")[0];
    return CORE.has(p) ? "core" : p;
  }

  function hash01(s) {
    let h = 2166136261;
    for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); }
    return ((h >>> 0) % 1000) / 1000;
  }

  /** パッケージの色。未知のパッケージは名前から決めた色相（再描画でも同じ）。 */
  function colorOf(pkg) {
    if (!pkg) return "#A8A29E";
    if (KNOWN[pkg]) return KNOWN[pkg].c;
    return `hsl(${Math.round(hash01("pkg:" + pkg) * 360)}, 55%, 45%)`;
  }

  const labelOf = (pkg) => (KNOWN[pkg] ? KNOWN[pkg].ja : pkg);

  /** 宣言の公式ドキュメントの URL。モジュールが分かれば宣言ページへ直接、
      スタブ（範囲外の補完で module が無い）なら名前の根から検索ページへ。無ければ null。 */
  function docsUrl(nd, name) {
    const pkg = packageOf(nd && nd.module);
    if (pkg && KNOWN[pkg] && KNOWN[pkg].docs) {
      return KNOWN[pkg].docs + String(nd.module).split(".").join("/") + ".html#" + String(name);
    }
    const rootPkg = packageOf(String(name || ""));
    if (!pkg && rootPkg && KNOWN[rootPkg] && KNOWN[rootPkg].docs) {
      return KNOWN[rootPkg].docs + "search.html?q=" + encodeURIComponent(String(name));
    }
    return null;
  }

  /** 依存先モジュールの列をパッケージごとに数える。{ pkg → { n, modules[] } } */
  function summarize(depModules) {
    const out = {};
    for (const m of depModules || []) {
      const p = packageOf(m);
      if (!p) continue;
      (out[p] || (out[p] = { n: 0, modules: [] })).n++;
      out[p].modules.push(m);
    }
    return out;
  }

  LDR.pkg = { packageOf, colorOf, labelOf, docsUrl, summarize, KNOWN, CORE };
})(window.LDR = window.LDR || {});
