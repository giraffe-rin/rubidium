/-
  Rubidium.K10 — 定理 K10 (a) の形式化

  定理 K10 (a)：m + 1 = 8u、u ≡ 1 (mod 8)、u ≥ 9 なら交互型：(n, 0) が P ⇔ n mod (2m+3) ∈ {0, m+2}。
  h = 4u、e₁ = (9u+1)/2（奇数）、w = (11u+1)/2（w/2 は奇数）。a = i(2m+3)、b = a + (m+2) とする。
  もとの証明（ブロックの理論 H(j) を使う）の事実を、局面の言葉で直接示す。
  - 偶数番目のブロック a：奇数 d の (a + d, d) は P、(a + h, h) は P（`hE_h`）。
  - 奇数番目のブロック b：(b + u, u) は N、(b + 2u, 2u) は P、(b + 3u, 3u) は P、(b + 6u, 6u) は N、(b + h, h) は N。
-/
import Rubidium.K9

namespace Rubidium

/-- (a + h, h) が P（m + 1 = 2h、h ≤ m）なら、p ≠ h の (a + (m+1), p) は N（手 h で (a + h, h) に移れる）。-/
theorem not_isP_near (m a h p : Nat) (hm : m + 1 = 2 * h) (hh1 : 1 ≤ h) (hhm : h ≤ m)
    (hah : IsP m (a + h) h) (hp : p ≠ h) : ¬ IsP m (a + (m + 1)) p := by
  intro hP
  rw [isP_iff] at hP
  apply hP h hh1 hhm (by omega) (fun e => hp e.symm)
  rw [show a + (m + 1) - h = a + h by omega]
  exact hah

section K10a

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu8 : u % 8 = 1) (hu9 : 9 ≤ u)
include hmu hu8 hu9

/-- 偶数番目のブロックの (a + h, h) は P。行 a がすべての p で P、奇数 d の (a + d, d) が P で、
    a = 0 か、a = b + (m+1)（行 b はすべての p で P、(b + 6u, 6u) は N）。-/
theorem k10_E_h (a : Nat) (hrow : ∀ p, IsP m a p) (hodd : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d)
    (hprev : a = 0 ∨ ∃ b, a = b + (m + 1) ∧ (∀ p, IsP m b p) ∧ ¬ IsP m (b + 6 * u) (6 * u)) :
    IsP m (a + 4 * u) (4 * u) := by
  rw [isP_iff]
  intro k hk1 hkm hkr hkp hPk
  by_cases hlt : k < 4 * u
  · rw [show a + 4 * u - k = a + (4 * u - k) by omega] at hPk
    by_cases hk : k = 4 * u - k
    · -- k = 2u：(a + 2u, 2u) は手 u で (a + u, u)（P）に移れる
      rw [← hk, isP_iff] at hPk
      apply hPk u (by omega) (by omega) (by omega) (by omega)
      rw [show a + k - u = a + u by omega]
      exact hodd u (by omega) (by omega) (by omega)
    · exact not_isP_of_row m a (4 * u - k) k hrow (by omega) (by omega) hk hPk
  · rcases hprev with h0 | ⟨b, hb, hrowb, hb6⟩
    · omega
    · rw [show a + 4 * u - k = b + (m + 1 + 4 * u - k) by omega] at hPk
      by_cases hk : k = m + 1 + 4 * u - k
      · -- k = 6u
        rw [← hk, show k = 6 * u by omega] at hPk
        exact hb6 hPk
      · exact not_isP_of_row m b (m + 1 + 4 * u - k) k hrowb (by omega) (by omega) hk hPk

/-- 奇数番目のブロック b = a + (m+2) の事実。行 a・行 b がすべての p で P、奇数 d の (a + d, d) と (a + h, h) が P なら、
    (b + u, u) は N、(b + 3u, 3u) は P、(b + 6u, 6u) は N、(b + h, h) は N。-/
theorem k10_O (a : Nat) (hrow : ∀ p, IsP m a p) (hrowb : ∀ p, IsP m (a + (m + 2)) p)
    (hodd : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d) (hah : IsP m (a + 4 * u) (4 * u)) :
    ¬ IsP m (a + (m + 2) + 6 * u) (6 * u) ∧ ¬ IsP m (a + (m + 2) + 4 * u) (4 * u) := by
  have hnear : ∀ p, p ≠ 4 * u → ¬ IsP m (a + (m + 1)) p :=
    fun p hp => not_isP_near m a (4 * u) p (by omega) (by omega) (by omega) hah hp
  -- (b + u, u) は N：手 e₁ = (9u+1)/2 で (a + e₁, e₁)（e₁ は奇数）に移れる
  have hO1 : ¬ IsP m (a + (m + 2) + u) u := by
    intro hP
    rw [isP_iff] at hP
    apply hP ((9 * u + 1) / 2) (by omega) (by omega) (by omega) (by omega)
    rw [show a + (m + 2) + u - (9 * u + 1) / 2 = a + (9 * u + 1) / 2 by omega]
    exact hodd _ (by omega) (by omega) (by omega)
  -- (b + 2u, 2u) は P
  have hO2u : IsP m (a + (m + 2) + 2 * u) (2 * u) := by
    rw [isP_iff]
    intro k hk1 hkm hkr hkp hPk
    by_cases hlt : k < 2 * u
    · rw [show a + (m + 2) + 2 * u - k = a + (m + 2) + (2 * u - k) by omega] at hPk
      by_cases hk : k = 2 * u - k
      · rw [← hk, show k = u by omega] at hPk; exact hO1 hPk
      · exact not_isP_of_row m _ (2 * u - k) k hrowb (by omega) (by omega) hk hPk
    · by_cases hk1' : k = 2 * u + 1
      · rw [hk1', show a + (m + 2) + 2 * u - (2 * u + 1) = a + (m + 1) by omega] at hPk
        exact hnear _ (by omega) hPk
      · rw [show a + (m + 2) + 2 * u - k = a + (m + 2 + 2 * u - k) by omega] at hPk
        exact not_isP_of_row m a (m + 2 + 2 * u - k) k hrow (by omega) (by omega) (by omega) hPk
  -- (b + 3u, 3u) は P
  have hO3u : IsP m (a + (m + 2) + 3 * u) (3 * u) := by
    rw [isP_iff]
    intro k hk1 hkm hkr hkp hPk
    by_cases hlt : k < 3 * u
    · rw [show a + (m + 2) + 3 * u - k = a + (m + 2) + (3 * u - k) by omega] at hPk
      exact not_isP_of_row m _ (3 * u - k) k hrowb (by omega) (by omega) (by omega) hPk
    · by_cases hk1' : k = 3 * u + 1
      · rw [hk1', show a + (m + 2) + 3 * u - (3 * u + 1) = a + (m + 1) by omega] at hPk
        exact hnear _ (by omega) hPk
      · rw [show a + (m + 2) + 3 * u - k = a + (m + 2 + 3 * u - k) by omega] at hPk
        by_cases hk : k = m + 2 + 3 * u - k
        · -- k = w = (11u+1)/2：(a + w, w) は手 w/2（奇数）で (a + w/2, w/2) に移れる
          rw [← hk, isP_iff] at hPk
          apply hPk (k / 2) (by omega) (by omega) (by omega) (by omega)
          rw [show a + k - k / 2 = a + k / 2 by omega]
          exact hodd _ (by omega) (by omega) (by omega)
        · exact not_isP_of_row m a (m + 2 + 3 * u - k) k hrow (by omega) (by omega) hk hPk
  constructor
  · -- (b + 6u, 6u) は N：手 3u で (b + 3u, 3u) に移れる
    intro hP
    rw [isP_iff] at hP
    apply hP (3 * u) (by omega) (by omega) (by omega) (by omega)
    rw [show a + (m + 2) + 6 * u - 3 * u = a + (m + 2) + 3 * u by omega]
    exact hO3u
  · -- (b + h, h) は N：手 2u で (b + 2u, 2u) に移れる
    intro hP
    rw [isP_iff] at hP
    apply hP (2 * u) (by omega) (by omega) (by omega) (by omega)
    rw [show a + (m + 2) + 4 * u - 2 * u = a + (m + 2) + 2 * u by omega]
    exact hO2u

/-- K10 (a) の不変量：すべての i で、行 i(2m+3)・行 i(2m+3) + (m+2) はすべての p で P、奇数 d と d = h の (i(2m+3) + d, d) は P。-/
theorem k10_rows :
    ∀ i, (∀ p, IsP m (i * (2 * m + 3)) p) ∧ (∀ p, IsP m (i * (2 * m + 3) + (m + 2)) p) ∧
      (∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (i * (2 * m + 3) + d) d) ∧
      IsP m (i * (2 * m + 3) + 4 * u) (4 * u) := by
  have hmo : m % 2 = 1 := by omega
  have hh2 : 2 ≤ (m + 1) / 2 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have step : ∀ a, (∀ p, IsP m a p) → (∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d) →
      IsP m (a + 4 * u) (4 * u) →
      (∀ p, IsP m (a + (m + 2)) p) ∧ (∀ p, IsP m (a + (2 * m + 3)) p) ∧
      (∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + (2 * m + 3) + d) d) ∧
      IsP m (a + (2 * m + 3) + 4 * u) (4 * u) := by
    intro a hrow hodd hah
    have hb := row_long m a hmo hh2 hrow (by rw [hh]; exact hah)
    obtain ⟨hb6, hbh⟩ := k10_O m u hmu hu8 hu9 a hrow hb hodd hah
    have hnext := row_next m (a + (m + 2)) hb (by rw [hh]; exact hbh)
    have hnext' : ∀ p, IsP m (a + (2 * m + 3)) p := by
      intro p; rw [show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega]; exact hnext p
    have hodd' := odd_of_rows m (a + (2 * m + 3)) hmo hnext' (Or.inr ⟨a + (m + 2), by omega, hb⟩)
    exact ⟨hb, hnext', hodd', k10_E_h m u hmu hu8 hu9 _ hnext' hodd' (Or.inr ⟨a + (m + 2), by omega, hb, hb6⟩)⟩
  intro i
  induction i with
  | zero =>
    have hrow : ∀ p, IsP m (0 * (2 * m + 3)) p := by intro p; rw [Nat.zero_mul]; exact isP_zero m p
    have hodd := odd_of_rows m (0 * (2 * m + 3)) hmo hrow (Or.inl (Nat.zero_mul _))
    have hah := k10_E_h m u hmu hu8 hu9 _ hrow hodd (Or.inl (Nat.zero_mul _))
    exact ⟨hrow, (step _ hrow hodd hah).1, hodd, hah⟩
  | succ i ih =>
    obtain ⟨hrow, _, hodd, hah⟩ := ih
    obtain ⟨_, hnext, hodd', hah'⟩ := step _ hrow hodd hah
    rw [Nat.succ_mul]
    exact ⟨hnext, (step _ hnext hodd' hah').1, hodd', hah'⟩

end K10a

/-- 定理 K10 (a)：m % 64 = 7、m ≥ 71（m + 1 = 8u、u ≡ 1 (mod 8)、u ≥ 9）なら、(n, 0) が P ⇔ n mod (2m+3) が 0 または m+2。-/
theorem K10a (m : Nat) (hm : m % 64 = 7) (hm71 : 71 ≤ m) (n : Nat) :
    IsP m n 0 ↔ (n % (2 * m + 3) = 0 ∨ n % (2 * m + 3) = m + 2) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hrowb, _, hah⟩ := k10_rows m ((m + 1) / 8) hmu (by omega) (by omega) (n / (2 * m + 3))
  have hdiv : n = (n / (2 * m + 3)) * (2 * m + 3) + n % (2 * m + 3) := by
    have := Nat.div_add_mod n (2 * m + 3)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (2 * m + 3) < 2 * m + 3 := Nat.mod_lt n (by omega)
  generalize hc : n % (2 * m + 3) = c at hdiv hlt
  generalize ha : n / (2 * m + 3) * (2 * m + 3) = a at hdiv hrow hrowb hah
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
      · rw [show a + c = a + (m + 2) + (c - (m + 2)) by omega] at hP
        exact not_isP_of_row m (a + (m + 2)) (c - (m + 2)) 0 hrowb (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h]; exact hrowb 0

end Rubidium
