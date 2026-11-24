/-
  Rubidium.K66 — 定理 K66（m + 1 = 8u、u ≡ 11 (mod 16) なら 110 型）

  定理 K66：m + 1 = 8u、u ≡ 11 (mod 16) なら、(n, 0) が P ⇔ n mod (3m+5) ∈ {0, m+2, 2m+4}（110 型）。
  h = 4u。行 a（始まり）、b = a + (m+2)（O）、c = b + (m+2)（O）、a' = c + (m+1)（次の始まり）。
  始まりの行で使うのは Blk m 1（奇数は P、v2 = 1 は N）と (a + 4u) が P であることだけ。
  - (b + 4u) は P：半分の規則で (b + u) が P ⇔ …、(b + u) の相手 X₁ = (9u+1)/2 は v2 = 1 なので行 a で N。
  - (c + 4u) は N：(c + u) の相手 (b + X₁)、X₁ = 2·o₁、(b + o₁) の相手 Y = (41u+5)/8 は奇数で行 a で P。
  - (a' + 4u) は P（`e_iff`）：(a' + 2u) は N（v2 = 1）、(c + 6u) は N。(c + 3u) の相手 X₃ = (11u+1)/2（奇数）、
    (b + X₃) の相手 Z = (27u+3)/4 は奇数で行 a で P。
-/
import Rubidium.K64

namespace Rubidium

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section K66

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 16 = 11)
include hmu hu

theorem k66_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 1 a) (hah : IsP m (a + 4 * u) (4 * u)) :
    (∀ p, IsP m (a + (m + 2)) p) ∧ (∀ p, IsP m (a + (2 * m + 4)) p) ∧ (∀ p, IsP m (a + (3 * m + 5)) p) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧ Blk m 1 (a + (3 * m + 5)) ∧ IsP m (a + (3 * m + 5) + 4 * u) (4 * u) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hoddA : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d :=
    fun d hd1 hdm hdo => (hblk d hd1 hdm (by rw [v2_odd d hdo]; omega)).mpr (by rw [v2_odd d hdo])
  have hb := row_long m a hmo (by omega) hrow (by rw [hh]; exact hah)
  -- (b + u) は P：相手 X₁ = (9u+1)/2（v2 = 1）は行 a で N
  have hX1 : ¬ IsP m (a + (9 * u + 1) / 2) ((9 * u + 1) / 2) := by
    have hv : v2 ((9 * u + 1) / 2) = 1 := v2_of_mod4 _ (by omega)
    rw [hblk _ (by omega) (by omega) (by omega), hv]; omega
  have hbu : IsP m (a + (m + 2) + u) u :=
    (o_odd_iff m (4 * u) a u hmh hrow hb hah (by omega) (by omega) (by omega) (by omega)).mpr
      (by rw [show (m + 2 + u) / 2 = (9 * u + 1) / 2 by omega]; exact hX1)
  have hb2 : ¬ IsP m (a + (m + 2) + 2 * u) (2 * u) := by
    rw [o_half' m (4 * u) a u hmh hrow hb hah (by omega) (by omega) (by omega)]; exact fun h => h hbu
  have hb4 : IsP m (a + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * (2 * u) by omega, o_half' m (4 * u) a (2 * u) hmh hrow hb hah (by omega) (by omega) (by omega)]
    exact hb2
  have hc0 := row_long m (a + (m + 2)) hmo (by omega) hb (by rw [hh]; exact hb4)
  have hc : ∀ p, IsP m (a + (2 * m + 4)) p := by
    intro p; rw [show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hc0 p
  -- (b + o₁) は N：相手 Y = (41u+5)/8（奇数）は行 a で P
  have hbo1 : ¬ IsP m (a + (m + 2) + (9 * u + 1) / 4) ((9 * u + 1) / 4) := by
    rw [o_odd_iff m (4 * u) a _ hmh hrow hb hah (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + (9 * u + 1) / 4) / 2 = (41 * u + 5) / 8 by omega]
    exact fun h => h (hoddA _ (by omega) (by omega) (by omega))
  -- (b + X₁) は P
  have hbX1 : IsP m (a + (m + 2) + (9 * u + 1) / 2) ((9 * u + 1) / 2) := by
    rw [show (9 * u + 1) / 2 = 2 * ((9 * u + 1) / 4) by omega,
      o_half' m (4 * u) a _ hmh hrow hb hah (by omega) (by omega) (by omega)]
    exact hbo1
  -- (c + u) は N、(c + 2u) は P、(c + 4u) は N
  have hcu : ¬ IsP m (a + (m + 2) + (m + 2) + u) u := by
    rw [o_odd_iff m (4 * u) (a + (m + 2)) u hmh hb hc0 hb4 (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + u) / 2 = (9 * u + 1) / 2 by omega]
    exact fun h => h hbX1
  have hc2 : IsP m (a + (m + 2) + (m + 2) + 2 * u) (2 * u) := by
    rw [o_half' m (4 * u) (a + (m + 2)) u hmh hb hc0 hb4 (by omega) (by omega) (by omega)]; exact hcu
  have hc4 : ¬ IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * (2 * u) by omega, o_half' m (4 * u) (a + (m + 2)) (2 * u) hmh hb hc0 hb4 (by omega) (by omega) (by omega)]
    exact fun h => h hc2
  -- 行 a' = c + (m+1)
  have ha0 := row_next m (a + (m + 2) + (m + 2)) hc0 (by rw [hh]; exact hc4)
  have ha' : ∀ p, IsP m (a + (3 * m + 5)) p := by
    intro p; rw [show a + (3 * m + 5) = a + (m + 2) + (m + 2) + (m + 1) by omega]; exact ha0 p
  have hodd' := odd_of_rows m (a + (3 * m + 5)) hmo ha' (Or.inr ⟨a + (m + 2) + (m + 2), by omega, hc0⟩)
  have hblk' := blk1_direct m _ ha' hodd'
  -- (b + X₃) は N：相手 Z = (27u+3)/4（奇数）は行 a で P
  have hbX3 : ¬ IsP m (a + (m + 2) + (11 * u + 1) / 2) ((11 * u + 1) / 2) := by
    rw [o_odd_iff m (4 * u) a _ hmh hrow hb hah (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + (11 * u + 1) / 2) / 2 = (27 * u + 3) / 4 by omega]
    exact fun h => h (hoddA _ (by omega) (by omega) (by omega))
  -- (c + 3u) は P、(c + 6u) は N
  have hc3 : IsP m (a + (m + 2) + (m + 2) + 3 * u) (3 * u) := by
    rw [o_odd_iff m (4 * u) (a + (m + 2)) (3 * u) hmh hb hc0 hb4 (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + 3 * u) / 2 = (11 * u + 1) / 2 by omega]
    exact hbX3
  have hc6 : ¬ IsP m (a + (m + 2) + (m + 2) + 6 * u) (6 * u) := by
    rw [show 6 * u = 2 * (3 * u) by omega, o_half' m (4 * u) (a + (m + 2)) (3 * u) hmh hb hc0 hb4 (by omega) (by omega) (by omega)]
    exact fun h => h hc3
  -- (a' + 4u) は P
  have ha2 : ¬ IsP m (a + (3 * m + 5) + 2 * u) (2 * u) := by
    have hv : v2 (2 * u) = 1 := by rw [v2_two_mul u (by omega), v2_odd u (by omega)]
    rw [hblk' _ (by omega) (by omega) (by omega), hv]; omega
  have ha4 : IsP m (a + (3 * m + 5) + 4 * u) (4 * u) := by
    rw [show a + (3 * m + 5) = a + (m + 2) + (m + 2) + (m + 1) by omega,
      e_iff m (4 * u) _ (4 * u) hmh hc0 ha0 (by omega) (by omega) (by omega),
      show 4 * u / 2 = 2 * u by omega, show 4 * u + 2 * u = 6 * u by omega,
      ← show a + (3 * m + 5) = a + (m + 2) + (m + 2) + (m + 1) by omega]
    exact ⟨ha2, hc6⟩
  exact ⟨hb, hc, ha', hb4, hblk', ha4⟩

theorem k66_rows : ∀ i, (∀ p, IsP m (i * (3 * m + 5)) p) ∧ Blk m 1 (i * (3 * m + 5)) ∧
    IsP m (i * (3 * m + 5) + 4 * u) (4 * u) := by
  intro i
  induction i with
  | zero =>
    rw [Nat.zero_mul, Nat.zero_add]
    refine ⟨isP_zero m, blk_zero m 1, ?_⟩
    rw [K3 m _ _ (by omega) (by omega)]
    refine ⟨rfl, ?_⟩
    rw [ev2_four u (by omega), ev2_odd u (by omega)]
  | succ i ih =>
    obtain ⟨hrow, hblk, hah⟩ := ih
    obtain ⟨_, _, ha', _, hb', ha4⟩ := k66_step m u hmu hu _ hrow hblk hah
    rw [Nat.succ_mul]
    exact ⟨ha', hb', ha4⟩

end K66

/-- 定理 K66：m + 1 = 8u、u ≡ 11 (mod 16) なら、(n, 0) が P ⇔ n mod (3m+5) ∈ {0, m+2, 2m+4}。-/
theorem K66 (m : Nat) (hm : (m + 1) % 128 = 88) (n : Nat) :
    IsP m n 0 ↔ (n % (3 * m + 5) = 0 ∨ n % (3 * m + 5) = m + 2 ∨ n % (3 * m + 5) = 2 * m + 4) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk, hah⟩ := k66_rows m _ hmu (by omega) (n / (3 * m + 5))
  obtain ⟨hrowb, hrowc, _, hbh, _, _⟩ := k66_step m _ hmu (by omega) _ hrow hblk hah
  have hdiv : n = (n / (3 * m + 5)) * (3 * m + 5) + n % (3 * m + 5) := by
    have := Nat.div_add_mod n (3 * m + 5)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (3 * m + 5) < 3 * m + 5 := Nat.mod_lt n (by omega)
  generalize hcc : n % (3 * m + 5) = c at hdiv hlt
  generalize ha : n / (3 * m + 5) * (3 * m + 5) = a at hdiv hrow hrowb hrowc hah hbh
  subst hdiv
  have hmh : m + 1 = 2 * (4 * ((m + 1) / 8)) := by omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases h1 : c ≤ m
    · exact not_isP_of_row m a c 0 hrow (by omega) h1 (by omega) hP
    · by_cases h2 : c = m + 1
      · subst h2
        exact not_isP_near m a _ 0 hmh (by omega) (by omega) hah (by omega) hP
      · by_cases h3 : c ≤ 2 * m + 2
        · rw [show a + c = a + (m + 2) + (c - (m + 2)) by omega] at hP
          exact not_isP_of_row m (a + (m + 2)) (c - (m + 2)) 0 hrowb (by omega) (by omega) (by omega) hP
        · by_cases h4 : c = 2 * m + 3
          · rw [h4, show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega] at hP
            exact not_isP_near m (a + (m + 2)) _ 0 hmh (by omega) (by omega) hbh (by omega) hP
          · rw [show a + c = a + (2 * m + 4) + (c - (2 * m + 4)) by omega] at hP
            exact not_isP_of_row m (a + (2 * m + 4)) (c - (2 * m + 4)) 0 hrowc (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h]; exact hrowb 0
    · rw [h]; exact hrowc 0

end Rubidium
