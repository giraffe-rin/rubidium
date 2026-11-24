/-
  Rubidium.K13 — 定理 K13 の形式化

  定理 K13：m + 1 = 8u、{v2(9u+1), v2(11u+1)} = {1, 3} なら「100 型」：(n, 0) が P ⇔ n mod (3m+4) ∈ {0, m+2, 2m+3}。
  h = 4u、X₁ = (9u+1)/2、X₃ = (11u+1)/2。仮定より一方は奇数、他方は Y = 4y（y は奇数）。
  L = 3m+4、a = iL、b = a + (m+2)、c = b + (m+1) とする。ブロックの理論 H(j) を使わず、局面の言葉で示す。
  - 行 a：奇数 d・Y・h の (a + d, d) は P（`p_four`：D = 4z（z 奇数）の (a + D, D) は P）。
  - 行 b：(b + u, u)・(b + 3u, 3u) は N（手 X₁・X₃）、(b + 2u, 2u)・(b + 6u, 6u) は P（`p_two`）、(b + h, h) は N。
  - 行 c：奇数 d は P、(c + 6u, 6u)・(c + h + 2y, h + 2y)・(c + h, h) は N。
-/
import Rubidium.K10

namespace Rubidium

/-- 手 k で P 局面に移れれば N。-/
theorem not_isP_move (m r p k : Nat) (hk1 : 1 ≤ k) (hkm : k ≤ m) (hkr : k ≤ r) (hkp : k ≠ p)
    (hP : IsP m (r - k) k) : ¬ IsP m r p := by
  intro h
  rw [isP_iff] at h
  exact h k hk1 hkm hkr hkp hP

/-- 偶数番目の種類のブロック a の、D = 4z（z 奇数）の (a + D, D) は P。行 a がすべての p で P、奇数 d の (a + d, d) が P で、
    a = 0 か、a = c + (m+1)（行 c はすべての p で P、(c + (h + 2z), h + 2z) は N。h = (m+1)/2）。-/
theorem p_four (m a z : Nat) (hmo : m % 2 = 1) (hz : z % 2 = 1) (hzm : 4 * z ≤ m) (hrow : ∀ p, IsP m a p)
    (hodd : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d)
    (hprev : a = 0 ∨ ∃ c, a = c + (m + 1) ∧ (∀ p, IsP m c p) ∧
      ¬ IsP m (c + ((m + 1) / 2 + 2 * z)) ((m + 1) / 2 + 2 * z)) :
    IsP m (a + 4 * z) (4 * z) := by
  rw [isP_iff]
  intro k hk1 hkm hkr hkp hPk
  by_cases hlt : k < 4 * z
  · rw [show a + 4 * z - k = a + (4 * z - k) by omega] at hPk
    by_cases hk : k = 4 * z - k
    · -- k = 2z：(a + 2z, 2z) は手 z で (a + z, z)（P）に移れる
      rw [← hk] at hPk
      exact not_isP_move m (a + k) k z (by omega) (by omega) (by omega) (by omega)
        (by rw [show a + k - z = a + z by omega]; exact hodd z (by omega) (by omega) hz) hPk
    · exact not_isP_of_row m a (4 * z - k) k hrow (by omega) (by omega) hk hPk
  · rcases hprev with h0 | ⟨c, hc, hrowc, hcz⟩
    · omega
    · rw [show a + 4 * z - k = c + (m + 1 + 4 * z - k) by omega] at hPk
      by_cases hk : k = m + 1 + 4 * z - k
      · rw [← hk, show k = (m + 1) / 2 + 2 * z by omega] at hPk
        exact hcz hPk
      · exact not_isP_of_row m c (m + 1 + 4 * z - k) k hrowc (by omega) (by omega) hk hPk

/-- 奇数番目の種類のブロック b = a + (m+2) の、D = 2z の (b + D, D) は P。行 a・行 b がすべての p で P、(a + h, h) が P、
    (b + z, z) が N、D + 1 ≠ h、m + 2 + D が奇数。-/
theorem p_two (m a z : Nat) (hmo : m % 2 = 1) (hz1 : 1 ≤ z) (hzm : 2 * z + 1 ≤ m) (hzh : 2 * z + 1 ≠ (m + 1) / 2)
    (hh1 : 1 ≤ (m + 1) / 2) (hrow : ∀ p, IsP m a p) (hrowb : ∀ p, IsP m (a + (m + 2)) p)
    (hah : IsP m (a + (m + 1) / 2) ((m + 1) / 2)) (hbz : ¬ IsP m (a + (m + 2) + z) z) :
    IsP m (a + (m + 2) + 2 * z) (2 * z) := by
  rw [isP_iff]
  intro k hk1 hkm hkr hkp hPk
  by_cases hlt : k < 2 * z
  · rw [show a + (m + 2) + 2 * z - k = a + (m + 2) + (2 * z - k) by omega] at hPk
    by_cases hk : k = 2 * z - k
    · rw [← hk, show k = z by omega] at hPk; exact hbz hPk
    · exact not_isP_of_row m _ (2 * z - k) k hrowb (by omega) (by omega) hk hPk
  · by_cases hk1' : k = 2 * z + 1
    · rw [hk1', show a + (m + 2) + 2 * z - (2 * z + 1) = a + (m + 1) by omega] at hPk
      exact not_isP_near m a ((m + 1) / 2) _ (by omega) hh1 (by omega) hah (by omega) hPk
    · rw [show a + (m + 2) + 2 * z - k = a + (m + 2 + 2 * z - k) by omega] at hPk
      exact not_isP_of_row m a (m + 2 + 2 * z - k) k hrow (by omega) (by omega) (by omega) hPk

section K13

variable (m u y : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2 = 1) (hy : y % 2 = 1)
  (hX : ((9 * u + 1) / 2 % 2 = 1 ∧ (11 * u + 1) / 2 = 4 * y) ∨ ((11 * u + 1) / 2 % 2 = 1 ∧ (9 * u + 1) / 2 = 4 * y))
include hmu hu hy hX

/-- K13 の 1 周期分。行 a がすべての p で P、奇数 d・Y・h の (a + d, d) が P なら、行 b・行 c・行 a + (3m+4) はすべての p で P、
    行 c の (c + 6u, 6u)・(c + h + 2y, h + 2y) は N、行 a + (3m+4) の奇数 d・Y・h は P。-/
theorem k13_step (a : Nat) (hrow : ∀ p, IsP m a p) (hodd : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d)
    (haY : IsP m (a + 4 * y) (4 * y)) (hah : IsP m (a + 4 * u) (4 * u)) :
    (∀ p, IsP m (a + (m + 2)) p) ∧ (∀ p, IsP m (a + (2 * m + 3)) p) ∧ (∀ p, IsP m (a + (3 * m + 4)) p) ∧
    (∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + (3 * m + 4) + d) d) ∧
    IsP m (a + (3 * m + 4) + 4 * y) (4 * y) ∧ IsP m (a + (3 * m + 4) + 4 * u) (4 * u) := by
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hb := row_long m a hmo (by omega) hrow (by rw [hh]; exact hah)
  -- 行 b
  have hX1 : IsP m (a + (9 * u + 1) / 2) ((9 * u + 1) / 2) := by
    rcases hX with ⟨h1, _⟩ | ⟨_, h3⟩
    · exact hodd _ (by omega) (by omega) h1
    · rw [h3]; exact haY
  have hX3 : IsP m (a + (11 * u + 1) / 2) ((11 * u + 1) / 2) := by
    rcases hX with ⟨_, h3⟩ | ⟨h1, _⟩
    · rw [h3]; exact haY
    · exact hodd _ (by omega) (by omega) h1
  have hbu : ¬ IsP m (a + (m + 2) + u) u :=
    not_isP_move m _ u ((9 * u + 1) / 2) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + u - (9 * u + 1) / 2 = a + (9 * u + 1) / 2 by omega]; exact hX1)
  have hb3u : ¬ IsP m (a + (m + 2) + 3 * u) (3 * u) :=
    not_isP_move m _ (3 * u) ((11 * u + 1) / 2) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + 3 * u - (11 * u + 1) / 2 = a + (11 * u + 1) / 2 by omega]; exact hX3)
  have hah' : IsP m (a + (m + 1) / 2) ((m + 1) / 2) := by rw [hh]; exact hah
  have hb2u := p_two m a u hmo (by omega) (by omega) (by omega) (by omega) hrow hb hah' hbu
  have hb6u : IsP m (a + (m + 2) + 6 * u) (6 * u) := by
    rw [show 6 * u = 2 * (3 * u) by omega]
    exact p_two m a (3 * u) hmo (by omega) (by omega) (by omega) (by omega) hrow hb hah' hb3u
  have hbh : ¬ IsP m (a + (m + 2) + (m + 1) / 2) ((m + 1) / 2) := by
    rw [hh]
    exact not_isP_move m _ _ (2 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + 4 * u - 2 * u = a + (m + 2) + 2 * u by omega]; exact hb2u)
  -- 行 c = b + (m+1)
  have hc0 := row_next m (a + (m + 2)) hb hbh
  have hc : ∀ p, IsP m (a + (2 * m + 3)) p := by
    intro p; rw [show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega]; exact hc0 p
  have hcodd := odd_of_rows m (a + (2 * m + 3)) hmo hc (Or.inr ⟨a + (m + 2), by omega, hb⟩)
  have hc6u : ¬ IsP m (a + (2 * m + 3) + 6 * u) (6 * u) :=
    not_isP_move m _ _ (3 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (2 * m + 3) + 6 * u - 3 * u = a + (2 * m + 3) + 3 * u by omega]
          exact hcodd _ (by omega) (by omega) (by omega))
  have hchY : ¬ IsP m (a + (2 * m + 3) + ((m + 1) / 2 + 2 * y)) ((m + 1) / 2 + 2 * y) :=
    not_isP_move m _ _ (2 * u + y) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (2 * m + 3) + ((m + 1) / 2 + 2 * y) - (2 * u + y) = a + (2 * m + 3) + (2 * u + y) by omega]
          exact hcodd _ (by omega) (by omega) (by omega))
  have hch : ¬ IsP m (a + (2 * m + 3) + (m + 1) / 2) ((m + 1) / 2) := by
    rw [hh]
    exact not_isP_move m _ _ (6 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (2 * m + 3) + 4 * u - 6 * u = a + (m + 2) + 6 * u by omega]; exact hb6u)
  -- 行 a' = c + (m+1)
  have ha0 := row_next m (a + (2 * m + 3)) hc hch
  have ha' : ∀ p, IsP m (a + (3 * m + 4)) p := by
    intro p; rw [show a + (3 * m + 4) = a + (2 * m + 3) + (m + 1) by omega]; exact ha0 p
  have haodd := odd_of_rows m (a + (3 * m + 4)) hmo ha' (Or.inr ⟨a + (2 * m + 3), by omega, hc⟩)
  have haY' := p_four m (a + (3 * m + 4)) y hmo hy (by omega) ha' haodd
    (Or.inr ⟨a + (2 * m + 3), by omega, hc, hchY⟩)
  have hah'' := p_four m (a + (3 * m + 4)) u hmo hu (by omega) ha' haodd
    (Or.inr ⟨a + (2 * m + 3), by omega, hc, by rw [show (m + 1) / 2 + 2 * u = 6 * u by omega]; exact hc6u⟩)
  exact ⟨hb, hc, ha', haodd, haY', hah''⟩

/-- K13 の不変量：すべての i で、行 iL・iL + (m+2)・iL + (2m+3) はすべての p で P、行 iL の奇数 d・Y・h は P。-/
theorem k13_rows :
    ∀ i, (∀ p, IsP m (i * (3 * m + 4)) p) ∧ (∀ p, IsP m (i * (3 * m + 4) + (m + 2)) p) ∧
      (∀ p, IsP m (i * (3 * m + 4) + (2 * m + 3)) p) ∧ IsP m (i * (3 * m + 4) + 4 * u) (4 * u) ∧
      (∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (i * (3 * m + 4) + d) d) ∧
      IsP m (i * (3 * m + 4) + 4 * y) (4 * y) := by
  have hmo : m % 2 = 1 := by omega
  have hYm : 4 * y ≤ m := by omega
  intro i
  induction i with
  | zero =>
    have hrow : ∀ p, IsP m (0 * (3 * m + 4)) p := by intro p; rw [Nat.zero_mul]; exact isP_zero m p
    have hodd := odd_of_rows m (0 * (3 * m + 4)) hmo hrow (Or.inl (Nat.zero_mul _))
    have haY := p_four m _ y hmo hy hYm hrow hodd (Or.inl (Nat.zero_mul _))
    have hah := p_four m _ u hmo hu (by omega) hrow hodd (Or.inl (Nat.zero_mul _))
    obtain ⟨hb, hc, _⟩ := k13_step m u y hmu hu hy hX _ hrow hodd haY hah
    exact ⟨hrow, hb, hc, hah, hodd, haY⟩
  | succ i ih =>
    obtain ⟨hrow, _, _, hah, hodd, haY⟩ := ih
    obtain ⟨_, _, ha', haodd, haY', hah'⟩ := k13_step m u y hmu hu hy hX _ hrow hodd haY hah
    obtain ⟨hb', hc', _⟩ := k13_step m u y hmu hu hy hX _ ha' haodd haY' hah'
    rw [Nat.succ_mul]
    exact ⟨ha', hb', hc', hah', haodd, haY'⟩

end K13

/-- v2 x = 1 なら x % 4 = 2。-/
theorem mod4_of_v2_one (x : Nat) (hx : 1 ≤ x) (h : v2 x = 1) : x % 4 = 2 := by
  have he : x % 2 = 0 := even_of_v2_pos x (by omega)
  have h2 := v2_even x (by omega) he
  have ho : (x / 2) % 2 = 1 := by
    apply Decidable.byContradiction; intro hne
    have := v2_even (x / 2) (by omega) (by omega); omega
  omega

/-- v2 x = 3 なら x % 16 = 8。-/
theorem mod16_of_v2_three (x : Nat) (hx : 1 ≤ x) (h : v2 x = 3) : x % 16 = 8 := by
  have he : x % 2 = 0 := even_of_v2_pos x (by omega)
  have h2 := v2_even x (by omega) he
  have he2 : (x / 2) % 2 = 0 := even_of_v2_pos (x / 2) (by omega)
  have h4 := v2_even (x / 2) (by omega) he2
  have := mod4_of_v2_one (x / 2 / 2) (by omega) (by omega)
  omega

/-- 定理 K13：m + 1 = 8u（m % 8 = 7）、{v2(9u+1), v2(11u+1)} = {1, 3} なら、(n, 0) が P ⇔ n mod (3m+4) ∈ {0, m+2, 2m+3}。-/
theorem K13 (m : Nat) (hm : m % 8 = 7)
    (hc : (v2 (9 * ((m + 1) / 8) + 1) = 1 ∧ v2 (11 * ((m + 1) / 8) + 1) = 3) ∨
          (v2 (9 * ((m + 1) / 8) + 1) = 3 ∧ v2 (11 * ((m + 1) / 8) + 1) = 1)) (n : Nat) :
    IsP m n 0 ↔ (n % (3 * m + 4) = 0 ∨ n % (3 * m + 4) = m + 2 ∨ n % (3 * m + 4) = 2 * m + 3) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  -- 仮定を剰余の形にする
  have hX : ∃ y, y % 2 = 1 ∧ ((m + 1) / 8) % 2 = 1 ∧
      (((9 * ((m + 1) / 8) + 1) / 2 % 2 = 1 ∧ (11 * ((m + 1) / 8) + 1) / 2 = 4 * y) ∨
       ((11 * ((m + 1) / 8) + 1) / 2 % 2 = 1 ∧ (9 * ((m + 1) / 8) + 1) / 2 = 4 * y)) := by
    rcases hc with ⟨h1, h3⟩ | ⟨h3, h1⟩
    · have a1 := mod4_of_v2_one _ (by omega) h1
      have a3 := mod16_of_v2_three _ (by omega) h3
      exact ⟨(11 * ((m + 1) / 8) + 1) / 8, by omega, by omega, Or.inl ⟨by omega, by omega⟩⟩
    · have a1 := mod4_of_v2_one _ (by omega) h1
      have a3 := mod16_of_v2_three _ (by omega) h3
      exact ⟨(9 * ((m + 1) / 8) + 1) / 8, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩
  obtain ⟨y, hy, hu, hX⟩ := hX
  obtain ⟨hrow, hrowb, hrowc, hah, _, _⟩ := k13_rows m _ y hmu hu hy hX (n / (3 * m + 4))
  have hdiv : n = (n / (3 * m + 4)) * (3 * m + 4) + n % (3 * m + 4) := by
    have := Nat.div_add_mod n (3 * m + 4)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (3 * m + 4) < 3 * m + 4 := Nat.mod_lt n (by omega)
  generalize hcc : n % (3 * m + 4) = c at hdiv hlt
  generalize ha : n / (3 * m + 4) * (3 * m + 4) = a at hdiv hrow hrowb hrowc hah
  subst hdiv
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases h1 : c ≤ m
    · exact not_isP_of_row m a c 0 hrow (by omega) h1 (by omega) hP
    · by_cases h2 : c = m + 1
      · subst h2
        exact not_isP_near m a (4 * ((m + 1) / 8)) 0 (by omega) (by omega) (by omega) hah (by omega) hP
      · by_cases h3 : c ≤ 2 * m + 2
        · rw [show a + c = a + (m + 2) + (c - (m + 2)) by omega] at hP
          exact not_isP_of_row m (a + (m + 2)) (c - (m + 2)) 0 hrowb (by omega) (by omega) (by omega) hP
        · rw [show a + c = a + (2 * m + 3) + (c - (2 * m + 3)) by omega] at hP
          exact not_isP_of_row m (a + (2 * m + 3)) (c - (2 * m + 3)) 0 hrowc (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h]; exact hrowb 0
    · rw [h]; exact hrowc 0

end Rubidium
