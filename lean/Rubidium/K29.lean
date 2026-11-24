/-
  Rubidium.K29 — 定理 K29.2（v2(m+1) = 5 の 100 型）の形式化

  定理 K29.2：m + 1 = 32u、u ≡ 1 (mod 4) なら「100 型」：(n, 0) が P ⇔ n mod (3m+4) ∈ {0, m+2, 2m+3}。
  h = 16u、X = (43u+1)/2、Y = (39u+1)/2。L = 3m+4、a = iL、b = a + (m+2)、c = b + (m+1) とする。
  もとの証明（ノート 2026-11-23-claude-1-k29-v5-first.md・k29-v5-full.md）の事実を、H(j) を使わず局面の言葉で示す。
  - 汎用の補題 `p_oddb`：行 a・行 b がすべての p で P、(a + h, h) が P で、奇数 d の相手 e = (m+2+d)/2 の (a + e, e) が N なら、
    (b + d, d) は P。`e_even`：c = b + (m+1)（行 b・行 c がすべての p で P）で、偶数 D について (c + D/2, D/2) と
    (b + h + D/2, h + D/2) が N なら (c + D, D) は P。
  - 行 b：(b + u)・(b + 5u)・(b + 9u) は N（手 (33u+1)/2・(37u+1)/2・(41u+1)/2、どれも奇数）。
    (b + 2u)・(b + 8u)・(b + 10u)・(b + 18u) は P（`p_two`）。(b + 16u) は N（手 8u）。
    (★) (b + 22u) が P なら (b + 11u) は N、よって (a + X) は P、よって (a + Y) は N、(b + 7u) は P、(b + 14u) は N、(b + 28u) は P。
  - 行 c：(c + 4u) は N（手 18u）、(c + 8u) は P（`e_even`）、(c + 16u) は N（手 8u）、(c + 18u) は N（手 9u）。
    (c + 24u) は N：(c + 12u) が P なら手 12u、N なら `e_even` の対偶で (b + 22u) は P、(★) より手 28u。
  - 行 a + L：(a' + 4u) は P、(a' + 8u) は N、(a' + 16u) は P（`e_even`）。
-/
import Rubidium.K11

namespace Rubidium

set_option maxHeartbeats 4000000

/-- 奇数 d の (b + d, d)（b = a + (m+2)）は、相手 (a + e, e)（e = (m+2+d)/2）が N なら P。-/
theorem p_oddb (m h a d : Nat) (hmh : m + 1 = 2 * h) (hh1 : 1 ≤ h) (hrow : ∀ p, IsP m a p)
    (hrowb : ∀ p, IsP m (a + (m + 2)) p) (hah : IsP m (a + h) h) (hd1 : 1 ≤ d) (hdo : d % 2 = 1)
    (hdh : d + 1 ≠ h) (hem : (m + 2 + d) / 2 ≤ m) (hN : ¬ IsP m (a + (m + 2 + d) / 2) ((m + 2 + d) / 2)) :
    IsP m (a + (m + 2) + d) d := by
  rw [isP_iff]
  intro k hk1 hkm hkr hkd hPk
  by_cases hlt : k < d
  · rw [show a + (m + 2) + d - k = a + (m + 2) + (d - k) by omega] at hPk
    exact not_isP_of_row m _ (d - k) k hrowb (by omega) (by omega) (by omega) hPk
  · by_cases hk1' : k = d + 1
    · rw [hk1', show a + (m + 2) + d - (d + 1) = a + (m + 1) by omega] at hPk
      exact not_isP_near m a h _ hmh hh1 (by omega) hah (by omega) hPk
    · rw [show a + (m + 2) + d - k = a + (m + 2 + d - k) by omega] at hPk
      by_cases hk : k = m + 2 + d - k
      · rw [← hk, show k = (m + 2 + d) / 2 by omega] at hPk; exact hN hPk
      · exact not_isP_of_row m a (m + 2 + d - k) k hrow (by omega) (by omega) hk hPk

/-- c = b + (m+1) の偶数 D：(c + D/2, D/2) と (b + h + D/2, h + D/2) が N なら (c + D, D) は P。-/
theorem e_even (m h b D : Nat) (hmh : m + 1 = 2 * h) (hrowb : ∀ p, IsP m b p) (hrowc : ∀ p, IsP m (b + (m + 1)) p)
    (hD2 : 2 ≤ D) (hDm : D ≤ m) (hDe : D % 2 = 0)
    (hN1 : ¬ IsP m (b + (m + 1) + D / 2) (D / 2)) (hN2 : ¬ IsP m (b + (h + D / 2)) (h + D / 2)) :
    IsP m (b + (m + 1) + D) D := by
  rw [isP_iff]
  intro k hk1 hkm hkr hkd hPk
  by_cases hlt : k < D
  · rw [show b + (m + 1) + D - k = b + (m + 1) + (D - k) by omega] at hPk
    by_cases hk : k = D - k
    · rw [← hk, show k = D / 2 by omega] at hPk; exact hN1 hPk
    · exact not_isP_of_row m _ (D - k) k hrowc (by omega) (by omega) hk hPk
  · rw [show b + (m + 1) + D - k = b + (m + 1 + D - k) by omega] at hPk
    by_cases hk : k = m + 1 + D - k
    · rw [← hk, show k = h + D / 2 by omega] at hPk; exact hN2 hPk
    · exact not_isP_of_row m b (m + 1 + D - k) k hrowb (by omega) (by omega) hk hPk

section K29

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu4 : u % 4 = 1)
include hmu hu4

/-- K29.2 の 1 周期分。 -/
theorem k29_step (a : Nat) (hrow : ∀ p, IsP m a p) (hodd : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d)
    (hah : IsP m (a + 16 * u) (16 * u)) :
    (∀ p, IsP m (a + (m + 2)) p) ∧ (∀ p, IsP m (a + (2 * m + 3)) p) ∧ (∀ p, IsP m (a + (3 * m + 4)) p) ∧
    (∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + (3 * m + 4) + d) d) ∧
    IsP m (a + (3 * m + 4) + 16 * u) (16 * u) := by
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 16 * u := by omega
  have hmh : m + 1 = 2 * (16 * u) := by omega
  have hb := row_long m a hmo (by omega) hrow (by rw [hh]; exact hah)
  have hah' : IsP m (a + (m + 1) / 2) ((m + 1) / 2) := by rw [hh]; exact hah
  -- 行 b の奇数
  have mvodd : ∀ d c, d % 2 = 1 → (m + 2 + d) = 2 * c → c % 2 = 1 → c ≤ m → c ≠ d → 1 ≤ d →
      ¬ IsP m (a + (m + 2) + d) d := by
    intro d c hdo hc hco hcm hcd hd1
    exact not_isP_move m _ d c (by omega) hcm (by omega) hcd
      (by rw [show a + (m + 2) + d - c = a + c by omega]; exact hodd c (by omega) hcm hco)
  have hbu := mvodd u ((33 * u + 1) / 2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hb5 := mvodd (5 * u) ((37 * u + 1) / 2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hb9 := mvodd (9 * u) ((41 * u + 1) / 2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have p2 : ∀ z, 1 ≤ z → 2 * z + 1 ≤ m → 2 * z + 1 ≠ 16 * u → ¬ IsP m (a + (m + 2) + z) z →
      IsP m (a + (m + 2) + 2 * z) (2 * z) :=
    fun z hz1 hzm hzh hbz => p_two m a z hmo hz1 hzm (by rw [hh]; exact hzh) (by omega) hrow hb hah' hbz
  have hb2 := p2 u (by omega) (by omega) (by omega) hbu
  have hb4 : ¬ IsP m (a + (m + 2) + 4 * u) (4 * u) :=
    not_isP_move m _ _ (2 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + 4 * u - 2 * u = a + (m + 2) + 2 * u by omega]; exact hb2)
  have hb8 : IsP m (a + (m + 2) + 8 * u) (8 * u) := by
    have := p2 (4 * u) (by omega) (by omega) (by omega) hb4; rwa [show 2 * (4 * u) = 8 * u by omega] at this
  have hb16 : ¬ IsP m (a + (m + 2) + 16 * u) (16 * u) :=
    not_isP_move m _ _ (8 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + 16 * u - 8 * u = a + (m + 2) + 8 * u by omega]; exact hb8)
  have hb18 : IsP m (a + (m + 2) + 18 * u) (18 * u) := by
    have := p2 (9 * u) (by omega) (by omega) (by omega) hb9; rwa [show 2 * (9 * u) = 18 * u by omega] at this
  have hb10 : IsP m (a + (m + 2) + 10 * u) (10 * u) := by
    have := p2 (5 * u) (by omega) (by omega) (by omega) hb5; rwa [show 2 * (5 * u) = 10 * u by omega] at this
  have hb20 : ¬ IsP m (a + (m + 2) + 20 * u) (20 * u) :=
    not_isP_move m _ _ (10 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + 20 * u - 10 * u = a + (m + 2) + 10 * u by omega]; exact hb10)
  -- 行 a の (a + X) か (a + Y) は N
  have hXY : ¬ IsP m (a + (43 * u + 1) / 2) ((43 * u + 1) / 2) ∨ ¬ IsP m (a + (39 * u + 1) / 2) ((39 * u + 1) / 2) := by
    by_cases h8 : u % 8 = 1
    · left
      exact not_isP_move m _ _ ((43 * u + 1) / 4) (by omega) (by omega) (by omega) (by omega)
        (by rw [show a + (43 * u + 1) / 2 - (43 * u + 1) / 4 = a + (43 * u + 1) / 4 by omega]
            exact hodd _ (by omega) (by omega) (by omega))
    · right
      exact not_isP_move m _ _ ((39 * u + 1) / 4) (by omega) (by omega) (by omega) (by omega)
        (by rw [show a + (39 * u + 1) / 2 - (39 * u + 1) / 4 = a + (39 * u + 1) / 4 by omega]
            exact hodd _ (by omega) (by omega) (by omega))
  -- (★)
  have hstar : IsP m (a + (m + 2) + 22 * u) (22 * u) → IsP m (a + (m + 2) + 28 * u) (28 * u) := by
    intro h22
    have hb11 : ¬ IsP m (a + (m + 2) + 11 * u) (11 * u) := fun h11 =>
      not_isP_move m _ _ (11 * u) (by omega) (by omega) (by omega) (by omega)
        (by rw [show a + (m + 2) + 22 * u - 11 * u = a + (m + 2) + 11 * u by omega]; exact h11) h22
    have haX : IsP m (a + (43 * u + 1) / 2) ((43 * u + 1) / 2) := by
      apply Classical.byContradiction
      intro hN
      apply hb11
      exact p_oddb m (16 * u) a (11 * u) hmh (by omega) hrow hb hah (by omega) (by omega) (by omega) (by omega)
        (by rw [show (m + 2 + 11 * u) / 2 = (43 * u + 1) / 2 by omega]; exact hN)
    have haY : ¬ IsP m (a + (39 * u + 1) / 2) ((39 * u + 1) / 2) := by
      rcases hXY with h | h
      · exact absurd haX h
      · exact h
    have hb7 := p_oddb m (16 * u) a (7 * u) hmh (by omega) hrow hb hah (by omega) (by omega) (by omega) (by omega)
      (by rw [show (m + 2 + 7 * u) / 2 = (39 * u + 1) / 2 by omega]; exact haY)
    have hb14 : ¬ IsP m (a + (m + 2) + 14 * u) (14 * u) :=
      not_isP_move m _ _ (7 * u) (by omega) (by omega) (by omega) (by omega)
        (by rw [show a + (m + 2) + 14 * u - 7 * u = a + (m + 2) + 7 * u by omega]; exact hb7)
    have := p2 (14 * u) (by omega) (by omega) (by omega) hb14
    rwa [show 2 * (14 * u) = 28 * u by omega] at this
  -- 行 c
  have hc0 := row_next m (a + (m + 2)) hb (by rw [hh]; exact hb16)
  have hc : ∀ p, IsP m (a + (m + 2) + (m + 1)) p := hc0
  have hcodd := odd_of_rows m (a + (m + 2) + (m + 1)) hmo hc (Or.inr ⟨a + (m + 2), rfl, hb⟩)
  have hc4 : ¬ IsP m (a + (m + 2) + (m + 1) + 4 * u) (4 * u) :=
    not_isP_move m _ _ (18 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + (m + 1) + 4 * u - 18 * u = a + (m + 2) + 18 * u by omega]; exact hb18)
  have hc2 : ¬ IsP m (a + (m + 2) + (m + 1) + 2 * u) (2 * u) :=
    not_isP_move m _ _ u (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + (m + 1) + 2 * u - u = a + (m + 2) + (m + 1) + u by omega]
          exact hcodd u (by omega) (by omega) (by omega))
  have hc8 : IsP m (a + (m + 2) + (m + 1) + 8 * u) (8 * u) :=
    e_even m (16 * u) (a + (m + 2)) (8 * u) hmh hb hc (by omega) (by omega) (by omega)
      (by rw [show 8 * u / 2 = 4 * u by omega]; exact hc4)
      (by rw [show 16 * u + 8 * u / 2 = 20 * u by omega]; exact hb20)
  have hc16 : ¬ IsP m (a + (m + 2) + (m + 1) + 16 * u) (16 * u) :=
    not_isP_move m _ _ (8 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + (m + 1) + 16 * u - 8 * u = a + (m + 2) + (m + 1) + 8 * u by omega]; exact hc8)
  have hc18 : ¬ IsP m (a + (m + 2) + (m + 1) + 18 * u) (18 * u) :=
    not_isP_move m _ _ (9 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + (m + 1) + 18 * u - 9 * u = a + (m + 2) + (m + 1) + 9 * u by omega]
          exact hcodd _ (by omega) (by omega) (by omega))
  have hc6 : ¬ IsP m (a + (m + 2) + (m + 1) + 6 * u) (6 * u) :=
    not_isP_move m _ _ (3 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + (m + 1) + 6 * u - 3 * u = a + (m + 2) + (m + 1) + 3 * u by omega]
          exact hcodd _ (by omega) (by omega) (by omega))
  have hc24 : ¬ IsP m (a + (m + 2) + (m + 1) + 24 * u) (24 * u) := by
    by_cases h12 : IsP m (a + (m + 2) + (m + 1) + 12 * u) (12 * u)
    · exact not_isP_move m _ _ (12 * u) (by omega) (by omega) (by omega) (by omega)
        (by rw [show a + (m + 2) + (m + 1) + 24 * u - 12 * u = a + (m + 2) + (m + 1) + 12 * u by omega]; exact h12)
    · have h22 : IsP m (a + (m + 2) + 22 * u) (22 * u) := by
        apply Classical.byContradiction
        intro hN
        apply h12
        exact e_even m (16 * u) (a + (m + 2)) (12 * u) hmh hb hc (by omega) (by omega) (by omega)
          (by rw [show 12 * u / 2 = 6 * u by omega]; exact hc6)
          (by rw [show 16 * u + 12 * u / 2 = 22 * u by omega]; exact hN)
      exact not_isP_move m _ _ (28 * u) (by omega) (by omega) (by omega) (by omega)
        (by rw [show a + (m + 2) + (m + 1) + 24 * u - 28 * u = a + (m + 2) + 28 * u by omega]; exact hstar h22)
  -- 行 a' = c + (m+1)
  have ha0 := row_next m (a + (m + 2) + (m + 1)) hc (by rw [hh]; exact hc16)
  have ha' : ∀ p, IsP m (a + (3 * m + 4)) p := by
    intro p; rw [show a + (3 * m + 4) = a + (m + 2) + (m + 1) + (m + 1) by omega]; exact ha0 p
  have haodd := odd_of_rows m (a + (3 * m + 4)) hmo ha' (Or.inr ⟨a + (m + 2) + (m + 1), by omega, hc⟩)
  have ha'2 : ¬ IsP m (a + (3 * m + 4) + 2 * u) (2 * u) :=
    not_isP_move m _ _ u (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (3 * m + 4) + 2 * u - u = a + (3 * m + 4) + u by omega]
          exact haodd u (by omega) (by omega) (by omega))
  have hcc : a + (3 * m + 4) = a + (m + 2) + (m + 1) + (m + 1) := by omega
  have ha'4 : IsP m (a + (3 * m + 4) + 4 * u) (4 * u) := by
    rw [hcc]
    exact e_even m (16 * u) (a + (m + 2) + (m + 1)) (4 * u) hmh hc ha0 (by omega) (by omega) (by omega)
      (by rw [show 4 * u / 2 = 2 * u by omega, ← hcc]; exact ha'2)
      (by rw [show 16 * u + 4 * u / 2 = 18 * u by omega]; exact hc18)
  have ha'8 : ¬ IsP m (a + (3 * m + 4) + 8 * u) (8 * u) :=
    not_isP_move m _ _ (4 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (3 * m + 4) + 8 * u - 4 * u = a + (3 * m + 4) + 4 * u by omega]; exact ha'4)
  have ha'16 : IsP m (a + (3 * m + 4) + 16 * u) (16 * u) := by
    rw [hcc]
    exact e_even m (16 * u) (a + (m + 2) + (m + 1)) (16 * u) hmh hc ha0 (by omega) (by omega) (by omega)
      (by rw [show 16 * u / 2 = 8 * u by omega, ← hcc]; exact ha'8)
      (by rw [show 16 * u + 16 * u / 2 = 24 * u by omega]; exact hc24)
  refine ⟨hb, ?_, ha', haodd, ha'16⟩
  intro p; rw [show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega]; exact hc p

theorem k29_rows :
    ∀ i, (∀ p, IsP m (i * (3 * m + 4)) p) ∧ (∀ p, IsP m (i * (3 * m + 4) + (m + 2)) p) ∧
      (∀ p, IsP m (i * (3 * m + 4) + (2 * m + 3)) p) ∧ IsP m (i * (3 * m + 4) + 16 * u) (16 * u) ∧
      (∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (i * (3 * m + 4) + d) d) := by
  have hmo : m % 2 = 1 := by omega
  intro i
  induction i with
  | zero =>
    have hrow : ∀ p, IsP m (0 * (3 * m + 4)) p := by intro p; rw [Nat.zero_mul]; exact isP_zero m p
    have hodd := odd_of_rows m (0 * (3 * m + 4)) hmo hrow (Or.inl (Nat.zero_mul _))
    have hah : IsP m (0 * (3 * m + 4) + 16 * u) (16 * u) := by
      rw [Nat.zero_mul, Nat.zero_add, K3 m _ _ (by omega) (by omega)]
      refine ⟨rfl, ?_⟩
      rw [show 16 * u = 4 * (4 * u) by omega, ev2_four _ (by omega), ev2_four _ (by omega), ev2_odd u (by omega)]
    obtain ⟨hb, hc, _⟩ := k29_step m u hmu hu4 _ hrow hodd hah
    exact ⟨hrow, hb, hc, hah, hodd⟩
  | succ i ih =>
    obtain ⟨hrow, _, _, hah, hodd⟩ := ih
    obtain ⟨_, _, ha', haodd, hah'⟩ := k29_step m u hmu hu4 _ hrow hodd hah
    obtain ⟨hb', hc', _⟩ := k29_step m u hmu hu4 _ ha' haodd hah'
    rw [Nat.succ_mul]
    exact ⟨ha', hb', hc', hah', haodd⟩

end K29

/-- 定理 K29.2：m + 1 = 32u、u ≡ 1 (mod 4) なら、(n, 0) が P ⇔ n mod (3m+4) ∈ {0, m+2, 2m+3}。-/
theorem K29_v5 (m : Nat) (hm : m % 128 = 31) (n : Nat) :
    IsP m n 0 ↔ (n % (3 * m + 4) = 0 ∨ n % (3 * m + 4) = m + 2 ∨ n % (3 * m + 4) = 2 * m + 3) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hrowb, hrowc, hah, _⟩ := k29_rows m ((m + 1) / 32) hmu (by omega) (n / (3 * m + 4))
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
        exact not_isP_near m a (16 * ((m + 1) / 32)) 0 (by omega) (by omega) (by omega) hah (by omega) hP
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
