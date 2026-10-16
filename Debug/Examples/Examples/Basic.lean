/-!
# 検証用フィクスチャ

LeanDeclReport の各観測を発火させるための小さな理論。core のみで閉じる
(mathlib 非依存・omega と core 補題だけ)。発火させるもの:

- 法則判定: 反射・非反射・対称・推移(→ 同値)/ 可換・結合・冪等(→ 半束)/
  吸収(→ 束)/ 分配/ 反対称・全域(→ 全順序)/ 単調
- 誤判定の防止: 形が付いてはならない否定例(単射性・準同型)
- 公理検出: `Classical.em` 経由の古典公理依存
- sorry 検出: 未完成宣言 1 件
- 依存の層: def の連鎖と、それについての定理
-/

/-- テンプレート由来(Main.lean が参照)。 -/
def hello := "world"

namespace Examples

/-! ## 同値関係(反射・対称・推移 → 「同値」の判定) -/

/-- 偶奇が等しい、という自前の二項関係。 -/
def sameParity (m n : Nat) : Prop := m % 2 = n % 2

theorem sameParity_refl (n : Nat) : sameParity n n := rfl

theorem sameParity_symm {m n : Nat} (h : sameParity m n) : sameParity n m :=
  h.symm

theorem sameParity_trans {a b c : Nat} (h₁ : sameParity a b) (h₂ : sameParity b c) :
    sameParity a c :=
  h₁.trans h₂

/-! ## 二項演算(可換・結合・冪等 → 「半束」の判定) -/

/-- 自前の結び(最大値)。 -/
def join (m n : Nat) : Nat := Nat.max m n

theorem join_comm (m n : Nat) : join m n = join n m := by
  unfold join; exact Nat.max_comm m n

theorem join_assoc (a b c : Nat) : join (join a b) c = join a (join b c) := by
  unfold join; exact Nat.max_assoc a b c

theorem join_idem (n : Nat) : join n n = n := by
  unfold join; exact Nat.max_self n

/-- 自前の交わり(最小値)。`join` の双対。 -/
def meet (m n : Nat) : Nat := Nat.min m n

theorem meet_comm (m n : Nat) : meet m n = meet n m := by
  unfold meet; exact Nat.min_comm m n

theorem meet_assoc (a b c : Nat) : meet (meet a b) c = meet a (meet b c) := by
  unfold meet; exact Nat.min_assoc a b c

theorem meet_idem (n : Nat) : meet n n = n := by
  unfold meet; exact Nat.min_self n

/-- 吸収律(join 側)。双対な二つの半束を一つの束へ結ぶ(「吸収」+「束」の判定)。 -/
theorem join_absorb (m n : Nat) : join m (meet m n) = m := by
  unfold join meet; exact Nat.max_eq_left (Nat.min_le_left m n)

/-- 吸収律(meet 側)。 -/
theorem meet_absorb (m n : Nat) : meet m (join m n) = m := by
  unfold meet join; exact Nat.min_eq_left (Nat.le_max_left m n)

/-- 乗法の加法への分配(担い手対 (·*·, ·+·) の「分配」の判定を発火させる)。 -/
theorem mul_add_distrib (a b c : Nat) : a * (b + c) = a * b + a * c :=
  Nat.mul_add a b c

/-! ## 順序(反射・推移・反対称 → 「半順序」の判定) -/

/-- 自前の順序(Nat の ≤ の包み)。 -/
def le' (m n : Nat) : Prop := m ≤ n

theorem le'_refl (n : Nat) : le' n n := Nat.le_refl n

theorem le'_trans {a b c : Nat} (h₁ : le' a b) (h₂ : le' b c) : le' a c :=
  Nat.le_trans h₁ h₂

theorem le'_antisymm {m n : Nat} (h₁ : le' m n) (h₂ : le' n m) : m = n :=
  Nat.le_antisymm h₁ h₂

/-- 全域性(「全域」の判定を発火させ、半順序を全順序の判断へ持ち上げる)。 -/
theorem le'_total (m n : Nat) : le' m n ∨ le' n m := Nat.le_total m n

/-- 自前の狭義順序。「非反射」の判定を発火させる(`¬ R a a` の形)。 -/
def lt' (m n : Nat) : Prop := m < n

theorem lt'_irrefl (n : Nat) : ¬ lt' n n := Nat.lt_irrefl n

/-! ## 依存の連鎖と単調性 -/

/-- 2 倍。依存の層を作るための最初の定義。 -/
def double (n : Nat) : Nat := n + n

/-- 4 倍。`double` を経由する 2 段目の定義。 -/
def quadruple (n : Nat) : Nat := double (double n)

theorem double_eq (n : Nat) : double n = 2 * n := by
  unfold double; omega

theorem quadruple_eq (n : Nat) : quadruple n = 4 * n := by
  unfold quadruple double; omega

/-- `double` の単調性(「単調」の判定を発火させる)。 -/
theorem double_mono {m n : Nat} (h : le' m n) : le' (double m) (double n) := by
  unfold le' double at *; omega

/-! ## 誤判定の防止(形が付いてはならない否定例)

判定は「誤って付けない」向きに倒してある。ここは、過去に実際に誤って付いた形を
二度と付けないための否定例。レポートではこれらの `shape` が空でなければならない
(法則の件数は否定例を足しても増えない)。 -/

/-- 構成子の単射性を出すための構造体。帰納型・構成子・再帰子の種別も発火する。
    由来の検証: `casesOn` / `rec` / `ctorIdx` / `noConfusion*` / `_sizeOf_*` は `Pair` の派生、
    `mk.inj` / `mk.injEq` / `mk.noConfusion` / `mk.sizeOf_spec` は `mk` の派生、`fst` / `snd` は射影（成員）。
    `deriving Repr` のインスタンス `instReprPair` は範囲を持ち core に由来の記録が無いので、
    手書きと区別されない（既知の限界を実測で残す）。 -/
structure Pair where
  fst : Nat
  snd : Nat
  deriving Repr

/-- 単射性。結論の両辺の頭部は共に `=` だが、仮定の関係 `=` と枠 `∧` が違い、
    両辺はどの (x, y) の像でもない。「両辺の頭部が同じ」だけを見る規則では
    単調と誤認した(自己解析の `DirectDeps.mk.inj` で実測)。 -/
theorem pair_inj {a b a' b' : Nat} (h : Pair.mk a b = Pair.mk a' b') : a = a' ∧ b = b' :=
  Pair.mk.inj h

/-- 準同型 `↑(n + m) = ↑n + ↑m`。`Nat.cast {R} [NatCast R] n` は単項の写像で、
    末尾二つの引数はインスタンスと n。末尾二引数を機械的に取る規則では
    分配律 f x (g p q) = g (f x p) (f x q) の x にインスタンスが入り、分配と
    誤認した(`double_eq` の導出図の `Int.natCast_add` で実測)。 -/
theorem cast_add (n m : Nat) : ((n + m : Nat) : Int) = (n : Int) + (m : Int) :=
  Int.natCast_add n m

/-! ## 公理依存と未完成 -/

/-- 排中律。古典公理(`Classical.choice` / `propext`)への依存を発火させる。 -/
theorem em_or (p : Prop) : p ∨ ¬p := Classical.em p

/-- 未完成の宣言(sorry 検出の検証用。意図的に残している)。
    shape(反射)は付くが、sorry のため法則在庫からは除外されるべき例でもある。 -/
theorem wip_meet_join_refl (m n : Nat) : sameParity (meet m n) (meet m n) := sorry

end Examples
