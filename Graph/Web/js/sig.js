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

  const REL = [" ↔ ", " = ", " ≠ ", " ≤ ", " < ", " ≥ ", " > ", " ∈ ", " ⊆ ", " ∧ ", " ∨ "];

  /**
   * 結論を 関係 / 文脈 / 左辺 / 右辺 に割る。
   * 中置記法で書かれていればそこで、前置適用なら末尾二引数で切る。
   * 二引数に満たなければ左辺・右辺は null（割らずにそのまま見せる）。
   */
  function decompose(conclusion) {
    const c = strip(String(conclusion || "").replace(/\s+/g, " "));
    if (!c) return { rel: null, ctx: [], lhs: null, rhs: null, whole: "" };
    const hit = findTop(c, REL, 0);
    if (hit) {
      return {
        rel: hit.tok.trim(), ctx: [],
        lhs: c.slice(0, hit.at).trim(),
        rhs: c.slice(hit.at + hit.tok.length).trim(),
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
  const shortName = (n) => {
    const p = String(n || "").split(".");
    return p.length <= 2 ? String(n || "") : p.slice(-2).join(".");
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
    mono:     { ja: "単調", note: "関係の仮定から、同じ頭部の像について同じ関係" },
  };

  LDR.sig = { decompose, abbrev, shortName, splitTopSpaces, findTop, strip, SHAPE };
})(window.LDR = window.LDR || {});
