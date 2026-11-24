/-
  Rubidium.K67c — 予想 K67 の u ≡ 61 (mod 64)（100 型）の証明

  定理：m + 1 = 8u、u ≡ 61 (mod 64) なら、(n, 0) が P ⇔ n mod (3m+4) ∈ {0, m+2, 2m+3}（100 型）。
  h = 4u、X₁ = (9u+1)/2（奇数）、X₃ = (11u+1)/2（v2 = 4）。行 a（始まり、Blk m 7）、b = a + (m+2)（O）、
  c = b + (m+1)（E）、a' = c + (m+1)（E、次の始まり）。
  - (b + 4u) は N：(b + u) の相手 X₁ は奇数で P、よって (b + u) は N、(b + 2u) は P、(b + 4u) は N。
  - (c + 4u) は N：`e_iff` で (b + 6u) が P（(b + 3u) の相手 X₃ は v2 = 4 で P、よって (b + 3u) は N）。
  - a' で Blk m 7：v2(d) ∈ {2, 4, 6} の d の手 4u + d/2 の行き先 (c + 4u + d/2) が N であること（`k67c_cY`）。
    v2(d) = 4, 6 では (c + Y) → (b + 2z) → (b + z) → (a + X₃ + d/16) に帰着し、v2(X₃ + d/16) = v2(d) − 4 は偶数。
-/
import Rubidium.K66

namespace Rubidium

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

section K67c

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 64 = 61)
include hmu hu

theorem k67c_vX3 : v2 ((11 * u + 1) / 2) = 4 := by
  have h32 : ((11 * u + 1) / 2) % 32 = 16 := by omega
  rw [v2_even _ (by omega) (by omega), v2_even (_ / 2) (by omega) (by omega),
    v2_even (_ / 2 / 2) (by omega) (by omega), v2_even (_ / 2 / 2 / 2) (by omega) (by omega),
    v2_odd _ (by omega)]

/-- c = b + (m+1)（行 a・b・c がすべての p で P、Blk m 7 a、Blk m 1 c）で、v2(d) ∈ {2, 4, 6} の偶数 d について
    (c + (4u + d/2)) は N。-/
theorem k67c_cY (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 7 a) (hah : IsP m (a + 4 * u) (4 * u))
    (hb : ∀ p, IsP m (a + (m + 2)) p) (hc : ∀ p, IsP m (a + (m + 2) + (m + 1)) p) (hblkc : Blk m 1 (a + (m + 2) + (m + 1)))
    (d : Nat) (hd1 : 1 ≤ d) (hdm : 4 * u + d / 2 ≤ m) (hdv : v2 d = 2 ∨ v2 d = 4 ∨ v2 d = 6) :
    ¬ IsP m (a + (m + 2) + (m + 1) + (4 * u + d / 2)) (4 * u + d / 2) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hX3 := k67c_vX3 m u hmu hu
  have hde : d % 2 = 0 := even_of_v2_pos d (by omega)
  have hv1 : v2 d = v2 (d / 2) + 1 := v2_even d (by omega) hde
  rcases hdv with h2 | h46
  · -- v2(4u + d/2) = v2(d/2) = 1
    have hv : v2 (d / 2 + 4 * u) = 1 := by
      rw [v2_add (d / 2) (4 * u) (by omega) (by omega) (by omega)]; omega
    rw [Nat.add_comm (4 * u), hblkc _ (by omega) (by omega) (by omega), hv]; omega
  · have hd2e : (d / 2) % 2 = 0 := even_of_v2_pos (d / 2) (by omega)
    have hv2 : v2 (d / 2) = v2 (d / 4) + 1 := by rw [v2_even (d / 2) (by omega) hd2e, show d / 2 / 2 = d / 4 by omega]
    have hd4e : (d / 4) % 2 = 0 := even_of_v2_pos (d / 4) (by omega)
    have hv3 : v2 (d / 4) = v2 (d / 8) + 1 := by rw [v2_even (d / 4) (by omega) hd4e, show d / 4 / 2 = d / 8 by omega]
    have hd8e : (d / 8) % 2 = 0 := even_of_v2_pos (d / 8) (by omega)
    have hv4 : v2 (d / 8) = v2 (d / 16) + 1 := by rw [v2_even (d / 8) (by omega) hd8e, show d / 8 / 2 = d / 16 by omega]
    -- (c + Y) は N：(b + (4u + Y/2)) = (b + 2z) が P（z = 3u + d/8 は奇数）
    have hd8m : (d / 8) % 4 = 2 ∨ (d / 8) % 16 = 8 := by
      rcases h46 with h4 | h6
      · left; exact mod4_of_v2_one _ (by omega) (by omega)
      · right; exact mod16_of_v2_three _ (by omega) (by omega)
    rw [e_iff m (4 * u) (a + (m + 2)) (4 * u + d / 2) hmh hb hc (by omega) hdm (by omega)]
    intro ⟨_, hN⟩
    apply hN
    rw [show 4 * u + (4 * u + d / 2) / 2 = 2 * (3 * u + d / 8) by omega,
      o_half' m (4 * u) a (3 * u + d / 8) hmh hrow hb hah (by omega) (by omega) (by omega),
      o_odd_iff m (4 * u) a (3 * u + d / 8) hmh hrow hb hah (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + (3 * u + d / 8)) / 2 = d / 16 + (11 * u + 1) / 2 by omega]
    have hv : v2 (d / 16 + (11 * u + 1) / 2) = v2 (d / 16) := v2_add _ _ (by omega) (by omega) (by omega)
    intro hNP; apply hNP
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)

/-- a' = c + (m+1) で Blk m 7（K4 の blk_step の形、手 4u + d/2 の場合を `k67c_cY` で扱う）。-/
theorem k67c_blk (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 7 a) (hah : IsP m (a + 4 * u) (4 * u))
    (hb : ∀ p, IsP m (a + (m + 2)) p) (hc : ∀ p, IsP m (a + (m + 2) + (m + 1)) p) (hblkc : Blk m 1 (a + (m + 2) + (m + 1)))
    (ha' : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 1)) p) : Blk m 7 (a + (m + 2) + (m + 1) + (m + 1)) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro hd1 hdm hds
    constructor
    · intro hP
      apply Decidable.byContradiction
      intro hodd
      have hde : d % 2 = 0 := even_of_v2_pos d (by omega)
      have hv : v2 d = v2 (d / 2) + 1 := v2_even d (by omega) hde
      rw [isP_iff] at hP
      apply hP (d / 2) (by omega) (by omega) (by omega) (by omega)
      rw [show a + (m + 2) + (m + 1) + (m + 1) + d - d / 2 = a + (m + 2) + (m + 1) + (m + 1) + d / 2 by omega]
      exact (ih (d / 2) (by omega) (by omega) (by omega) (by omega)).mpr (by omega)
    · intro hev
      rw [isP_iff]
      intro k hk1 hkm hkr hkd hPk
      by_cases hlt : k < d
      · rw [show a + (m + 2) + (m + 1) + (m + 1) + d - k = a + (m + 2) + (m + 1) + (m + 1) + (d - k) by omega] at hPk
        by_cases hk : k = d - k
        · have hde : d % 2 = 0 := by omega
          have hd2 : d / 2 = k := by omega
          have hv : v2 d = v2 k + 1 := by rw [v2_even d (by omega) hde, hd2]
          rw [← hk] at hPk
          have := (ih k hlt hk1 (by omega) (by omega)).mp hPk
          omega
        · exact not_isP_of_row m _ (d - k) k ha' (by omega) (by omega) hk hPk
      · rw [show a + (m + 2) + (m + 1) + (m + 1) + d - k = a + (m + 2) + (m + 1) + (m + 1 + d - k) by omega] at hPk
        by_cases hk : k = m + 1 + d - k
        · have hde : d % 2 = 0 := by omega
          have hv1 : v2 d = v2 (d / 2) + 1 := v2_even d (by omega) hde
          have hkx : k = 4 * u + d / 2 := by omega
          rw [← hk, hkx] at hPk
          exact k67c_cY m u hmu hu a hrow hblk hah hb hc hblkc d hd1 (by omega) (by omega) hPk
        · exact not_isP_of_row m _ (m + 1 + d - k) k hc (by omega) (by omega) hk hPk

theorem k67c_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 7 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧ (∀ p, IsP m (a + (2 * m + 3)) p) ∧ (∀ p, IsP m (a + (3 * m + 4)) p) ∧
    Blk m 7 (a + (3 * m + 4)) ∧ IsP m (a + 4 * u) (4 * u) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hX3 := k67c_vX3 m u hmu hu
  have hoddA : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d :=
    fun d hd1 hdm hdo => (hblk d hd1 hdm (by rw [v2_odd d hdo]; omega)).mpr (by rw [v2_odd d hdo])
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hah : IsP m (a + 4 * u) (4 * u) := (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hb := row_long m a hmo (by omega) hrow (by rw [hh]; exact hah)
  -- (b + u) は N（相手 X₁ は奇数で P）、(b + 2u) は P、(b + 4u) は N
  have hbu : ¬ IsP m (a + (m + 2) + u) u := by
    rw [o_odd_iff m (4 * u) a u hmh hrow hb hah (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + u) / 2 = (9 * u + 1) / 2 by omega]
    exact fun h => h (hoddA _ (by omega) (by omega) (by omega))
  have hb2 : IsP m (a + (m + 2) + 2 * u) (2 * u) := by
    rw [o_half' m (4 * u) a u hmh hrow hb hah (by omega) (by omega) (by omega)]; exact hbu
  have hb4 : ¬ IsP m (a + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * (2 * u) by omega, o_half' m (4 * u) a (2 * u) hmh hrow hb hah (by omega) (by omega) (by omega)]
    exact fun h => h hb2
  have hc := row_next m (a + (m + 2)) hb (by rw [hh]; exact hb4)
  have hoddc := odd_of_rows m _ hmo hc (Or.inr ⟨a + (m + 2), rfl, hb⟩)
  have hblkc := blk1_direct m _ hc hoddc
  -- (b + 3u) は N（相手 X₃ は v2 = 4 で P）、(b + 6u) は P
  have hb3 : ¬ IsP m (a + (m + 2) + 3 * u) (3 * u) := by
    rw [o_odd_iff m (4 * u) a (3 * u) hmh hrow hb hah (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + 3 * u) / 2 = (11 * u + 1) / 2 by omega]
    exact fun h => h ((hblk _ (by omega) (by omega) (by omega)).mpr (by omega))
  have hb6 : IsP m (a + (m + 2) + 6 * u) (6 * u) := by
    rw [show 6 * u = 2 * (3 * u) by omega, o_half' m (4 * u) a (3 * u) hmh hrow hb hah (by omega) (by omega) (by omega)]
    exact hb3
  -- (c + 4u) は N
  have hc4 : ¬ IsP m (a + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    rw [e_iff m (4 * u) (a + (m + 2)) (4 * u) hmh hb hc (by omega) (by omega) (by omega),
      show 4 * u / 2 = 2 * u by omega, show 4 * u + 2 * u = 6 * u by omega]
    exact fun ⟨_, h⟩ => h hb6
  have ha' := row_next m (a + (m + 2) + (m + 1)) hc (by rw [hh]; exact hc4)
  have hblk' := k67c_blk m u hmu hu a hrow hblk hah hb hc hblkc ha'
  have e1 : a + (3 * m + 4) = a + (m + 2) + (m + 1) + (m + 1) := by omega
  refine ⟨hb, ?_, ?_, ?_, hah⟩
  · intro p; rw [show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega]; exact hc p
  · intro p; rw [e1]; exact ha' p
  · rw [e1]; exact hblk'

theorem k67c_rows : ∀ i, (∀ p, IsP m (i * (3 * m + 4)) p) ∧ Blk m 7 (i * (3 * m + 4)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 7⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, ha', hb', _⟩ := k67c_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha', hb'⟩

end K67c

/-- 予想 K67 の u ≡ 61 (mod 64)：m + 1 = 8u なら、(n, 0) が P ⇔ n mod (3m+4) ∈ {0, m+2, 2m+3}。-/
theorem K67_61 (m : Nat) (hm : (m + 1) % 512 = 488) (n : Nat) :
    IsP m n 0 ↔ (n % (3 * m + 4) = 0 ∨ n % (3 * m + 4) = m + 2 ∨ n % (3 * m + 4) = 2 * m + 3) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k67c_rows m _ hmu (by omega) (n / (3 * m + 4))
  obtain ⟨hrowb, hrowc, _, _, hah⟩ := k67c_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (3 * m + 4)) * (3 * m + 4) + n % (3 * m + 4) := by
    have := Nat.div_add_mod n (3 * m + 4)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (3 * m + 4) < 3 * m + 4 := Nat.mod_lt n (by omega)
  generalize hcc : n % (3 * m + 4) = c at hdiv hlt
  generalize ha : n / (3 * m + 4) * (3 * m + 4) = a at hdiv hrow hrowb hrowc hah
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
        · rw [show a + c = a + (2 * m + 3) + (c - (2 * m + 3)) by omega] at hP
          exact not_isP_of_row m (a + (2 * m + 3)) (c - (2 * m + 3)) 0 hrowc (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h]; exact hrowb 0
    · rw [h]; exact hrowc 0

end Rubidium
