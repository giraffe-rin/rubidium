/-
  Rubidium.K6 — 定理 K6 の形式化

  定理 K6：m ≡ 5 (mod 8) なら、すべての n で (n, 0) が P 局面 ⇔ n mod (2m+3) ∈ {0, m+2}。
  h = (m+1)/2（奇数、h ≥ 3）、e* = (3h+1)/2（奇数、h < e* ≤ m）とおく。a = i(2m+3)、b = a + (m+2) とする。
  i についての帰納法で、次の 2 つを示す（`k6_rows`）。
  - 行 a はすべての p で P。
  - Odd a：1 ≤ d ≤ m の奇数 d で (a + d, d) は P。
  帰納法の 1 段は、次の 4 つから成る。
  - `row_long`：行 b はすべての p で P。手 1 の行き先 (a + m + 1, 1) は、手 h で (a + h, h) に移れるので N。
    ほかの手 k ≥ 2 の行き先 (a + (m+2−k), k) は、m+2 が奇数なので k ≠ m+2−k となり、`not_isP_of_row` より N。
  - (b + h, h) は N：手 e* で (a + e*, e*) に移れて、e* は奇数なので Odd a より P。
  - 行 b + (m+1) = a + (2m+3) は `row_next`（Rubidium.K4Full）より P。
  - `odd_of_rows`：奇数 d の (a' + d, d) が P。手 k < d の行き先は k = d − k（d が偶数）でないと P にならず、
    手 k > d の行き先 (b + (m+1+d−k), k) は k = m+1+d−k（m+1+d が偶数）でないと P にならない。どちらも d が奇数なので起こらない。
-/
import Rubidium.K4Full

namespace Rubidium

/-- 行 r がすべての p で P、r = 0 か r = r' + (m+1)（行 r' もすべての p で P）なら、m が奇数のとき、奇数 d の (r + d, d) は P。-/
theorem odd_of_rows (m r : Nat) (hmo : m % 2 = 1) (hrow : ∀ p, IsP m r p)
    (hprev : r = 0 ∨ ∃ r', r = r' + (m + 1) ∧ ∀ p, IsP m r' p) :
    ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (r + d) d := by
  intro d hd1 hdm hdo
  rw [isP_iff]
  intro k hk1 hkm hkr hkd hPk
  by_cases hlt : k < d
  · rw [show r + d - k = r + (d - k) by omega] at hPk
    exact not_isP_of_row m r (d - k) k hrow (by omega) (by omega) (by omega) hPk
  · rcases hprev with h0 | ⟨r', hr', hrow'⟩
    · omega
    · rw [show r + d - k = r' + (m + 1 + d - k) by omega] at hPk
      exact not_isP_of_row m r' (m + 1 + d - k) k hrow' (by omega) (by omega) (by omega) hPk

/-- 行 a がすべての p で P で、(a + h, h) が P（h = (m+1)/2 ≥ 2）なら、m が奇数のとき、行 a + (m+2) はすべての p で P。-/
theorem row_long (m a : Nat) (hmo : m % 2 = 1) (hh2 : 2 ≤ (m + 1) / 2) (hrow : ∀ p, IsP m a p)
    (hh : IsP m (a + (m + 1) / 2) ((m + 1) / 2)) : ∀ p, IsP m (a + (m + 2)) p := by
  intro p
  rw [isP_iff]
  intro k hk1 hkm _ _ hPk
  by_cases hk : k = 1
  · -- 行き先 (a + m + 1, 1) は、手 h で (a + h, h) に移れるので N
    subst hk
    rw [show a + (m + 2) - 1 = a + (m + 1) by omega, isP_iff] at hPk
    apply hPk ((m + 1) / 2) (by omega) (by omega) (by omega) (by omega)
    rw [show a + (m + 1) - (m + 1) / 2 = a + (m + 1) / 2 by omega]
    exact hh
  · rw [show a + (m + 2) - k = a + (m + 2 - k) by omega] at hPk
    exact not_isP_of_row m a (m + 2 - k) k hrow (by omega) (by omega) (by omega) hPk

/-- m ≡ 5 (mod 8) なら、すべての i で、行 i(2m+3) と行 i(2m+3) + (m+2) はすべての p で P、かつ奇数 d の (i(2m+3) + d, d) は P。-/
theorem k6_rows (m : Nat) (hm : m % 8 = 5) :
    ∀ i, (∀ p, IsP m (i * (2 * m + 3)) p) ∧ (∀ p, IsP m (i * (2 * m + 3) + (m + 2)) p) ∧
      (∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (i * (2 * m + 3) + d) d) := by
  have hmo : m % 2 = 1 := by omega
  have hh2 : 2 ≤ (m + 1) / 2 := by omega
  have hho : (m + 1) / 2 % 2 = 1 := by omega
  -- 1 段：行 a と Odd a から、行 a + (m+2)、行 a + (2m+3)、Odd (a + (2m+3))
  have step : ∀ a, (∀ p, IsP m a p) → (∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d) →
      (∀ p, IsP m (a + (m + 2)) p) ∧ (∀ p, IsP m (a + (2 * m + 3)) p) ∧
      (∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + (2 * m + 3) + d) d) := by
    intro a hrow hodd
    have hb := row_long m a hmo hh2 hrow (hodd ((m + 1) / 2) (by omega) (by omega) hho)
    -- (b + h, h) は N：手 e* = (3h+1)/2 で (a + e*, e*) に移れる
    have hbh : ¬ IsP m (a + (m + 2) + (m + 1) / 2) ((m + 1) / 2) := by
      intro hP
      rw [isP_iff] at hP
      have he1 : (3 * ((m + 1) / 2) + 1) / 2 ≤ m := by omega
      apply hP ((3 * ((m + 1) / 2) + 1) / 2) (by omega) he1 (by omega) (by omega)
      rw [show a + (m + 2) + (m + 1) / 2 - (3 * ((m + 1) / 2) + 1) / 2 = a + (3 * ((m + 1) / 2) + 1) / 2 by omega]
      exact hodd _ (by omega) he1 (by omega)
    have hnext := row_next m (a + (m + 2)) hb hbh
    have hnext' : ∀ p, IsP m (a + (2 * m + 3)) p := by
      intro p; rw [show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega]; exact hnext p
    refine ⟨hb, hnext', ?_⟩
    exact odd_of_rows m (a + (2 * m + 3)) hmo hnext' (Or.inr ⟨a + (m + 2), by omega, hb⟩)
  intro i
  induction i with
  | zero =>
    have hrow : ∀ p, IsP m (0 * (2 * m + 3)) p := by intro p; rw [Nat.zero_mul]; exact isP_zero m p
    have hodd := odd_of_rows m (0 * (2 * m + 3)) hmo hrow (Or.inl (Nat.zero_mul _))
    exact ⟨hrow, (step _ hrow hodd).1, hodd⟩
  | succ i ih =>
    obtain ⟨hrow, _, hodd⟩ := ih
    obtain ⟨_, hnext, hodd'⟩ := step _ hrow hodd
    have he : (i + 1) * (2 * m + 3) = i * (2 * m + 3) + (2 * m + 3) := Nat.succ_mul i (2 * m + 3)
    rw [he]
    exact ⟨hnext, (step _ hnext hodd').1, hodd'⟩

/-- 定理 K6：m ≡ 5 (mod 8) なら、(n, 0) が P 局面 ⇔ n mod (2m+3) が 0 または m+2。-/
theorem K6 (m : Nat) (hm : m % 8 = 5) (n : Nat) :
    IsP m n 0 ↔ (n % (2 * m + 3) = 0 ∨ n % (2 * m + 3) = m + 2) := by
  have hdiv : n = (n / (2 * m + 3)) * (2 * m + 3) + n % (2 * m + 3) := by
    have := Nat.div_add_mod n (2 * m + 3)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (2 * m + 3) < 2 * m + 3 := Nat.mod_lt n (by omega)
  obtain ⟨hrow, hrowb, hodd⟩ := k6_rows m hm (n / (2 * m + 3))
  generalize hc : n % (2 * m + 3) = c at hdiv hlt
  generalize ha : n / (2 * m + 3) * (2 * m + 3) = a at hdiv hrow hrowb hodd
  subst hdiv
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases h1 : c ≤ m
    · exact not_isP_of_row m a c 0 hrow (by omega) h1 (by omega) hP
    · by_cases h2 : c = m + 1
      · -- (a + m + 1, 0)：手 h で (a + h, h) に移れる
        subst h2
        rw [isP_iff] at hP
        apply hP ((m + 1) / 2) (by omega) (by omega) (by omega) (by omega)
        rw [show a + (m + 1) - (m + 1) / 2 = a + (m + 1) / 2 by omega]
        exact hodd _ (by omega) (by omega) (by omega)
      · -- m + 3 ≤ c ≤ 2m + 2：行 a + (m+2) から c − (m+2) 先
        rw [show a + c = a + (m + 2) + (c - (m + 2)) by omega] at hP
        exact not_isP_of_row m (a + (m + 2)) (c - (m + 2)) 0 hrowb (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h]; exact hrowb 0

end Rubidium
