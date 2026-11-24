/-
  Rubidium.K68b — 予想 K68 の u ≡ 103 (mod 256)（u ≡ 103, 359 (mod 512)、100 型）の証明

  定理：m + 1 = 8u、u ≡ 103 (mod 256) なら、(n, 0) が P ⇔ n mod (3m+4) ∈ {0, m+2, 2m+3}（100 型）。
  X₁ = (9u+1)/2（v2 = 4）、X₃ = (11u+1)/2（奇数）。行 a（始まり）、b = a + (m+2)（O）、c = b + (m+1)（E）、
  a' = c + (m+1)（次の始まり）。始まりの行の不変量は「Blk m 3 かつ (a + X₁) が P」。
  - (b + u) は N（相手 X₁ で (a + X₁) が P）、よって (b + 2u) は P、(b + 4u) は N。
  - (c + 4u) は N：(b + 3u) の相手 X₃ は奇数で P、よって (b + 6u) は P。
  - a' で Blk m 3：K67b と同じ（手 4u + d/2 の行き先は v2 = 1 で N）。
  - (a' + X₁) は P：e_iff で (a' + X₁/2)（v2 = 3 で N）と (c + 4u + X₁/2) に分ける。後者は e_iff で
    (b + 2z)（z = 3u + X₁/8 は奇数）が P であることに帰着し、さらに (a + Y)（Y = (m+2+z)/2、v2 = 2）が P であることに帰着する。
-/
import Rubidium.K67b

namespace Rubidium

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

section K68b

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 256 = 103)
include hmu hu

/-- a' = c + (m+1)（行 c で Blk m 1）で Blk m 3。-/
theorem k68b_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
    Blk m 3 (c + (m + 1)) := by
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
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
      rw [show c + (m + 1) + d - d / 2 = c + (m + 1) + d / 2 by omega]
      exact (ih (d / 2) (by omega) (by omega) (by omega) (by omega)).mpr (by omega)
    · intro hev
      rw [isP_iff]
      intro k hk1 hkm hkr hkd hPk
      by_cases hlt : k < d
      · rw [show c + (m + 1) + d - k = c + (m + 1) + (d - k) by omega] at hPk
        by_cases hk : k = d - k
        · have hde : d % 2 = 0 := by omega
          have hd2 : d / 2 = k := by omega
          have hv : v2 d = v2 k + 1 := by rw [v2_even d (by omega) hde, hd2]
          rw [← hk] at hPk
          have := (ih k hlt hk1 (by omega) (by omega)).mp hPk
          omega
        · exact not_isP_of_row m _ (d - k) k ha' (by omega) (by omega) hk hPk
      · rw [show c + (m + 1) + d - k = c + (m + 1 + d - k) by omega] at hPk
        by_cases hk : k = m + 1 + d - k
        · have hde : d % 2 = 0 := by omega
          have hv1 : v2 d = v2 (d / 2) + 1 := v2_even d (by omega) hde
          have hkx : k = d / 2 + 4 * u := by omega
          have hvk : v2 k = 1 := by rw [hkx, v2_add (d / 2) (4 * u) (by omega) (by omega) (by omega)]; omega
          rw [← hk] at hPk
          rw [hblkc k hk1 hkm (by omega), hvk] at hPk; omega
        · exact not_isP_of_row m c (m + 1 + d - k) k hc (by omega) (by omega) hk hPk

theorem k68b_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) (hX : IsP m (a + (9 * u + 1) / 2) ((9 * u + 1) / 2)) :
    (∀ p, IsP m (a + (m + 2)) p) ∧ (∀ p, IsP m (a + (2 * m + 3)) p) ∧ (∀ p, IsP m (a + (3 * m + 4)) p) ∧
    Blk m 3 (a + (3 * m + 4)) ∧ IsP m (a + (3 * m + 4) + (9 * u + 1) / 2) ((9 * u + 1) / 2) ∧ IsP m (a + 4 * u) (4 * u) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hoddA : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d :=
    fun d hd1 hdm hdo => (hblk d hd1 hdm (by rw [v2_odd d hdo]; omega)).mpr (by rw [v2_odd d hdo])
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hah : IsP m (a + 4 * u) (4 * u) := (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hb := row_long m a hmo (by omega) hrow (by rw [hh]; exact hah)
  have hbu : ¬ IsP m (a + (m + 2) + u) u := by
    rw [o_odd_iff m (4 * u) a u hmh hrow hb hah (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + u) / 2 = (9 * u + 1) / 2 by omega]
    exact fun h => h hX
  have hb2 : IsP m (a + (m + 2) + 2 * u) (2 * u) := by
    rw [o_half' m (4 * u) a u hmh hrow hb hah (by omega) (by omega) (by omega)]; exact hbu
  have hb4 : ¬ IsP m (a + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * (2 * u) by omega, o_half' m (4 * u) a (2 * u) hmh hrow hb hah (by omega) (by omega) (by omega)]
    exact fun h => h hb2
  have hc := row_next m (a + (m + 2)) hb (by rw [hh]; exact hb4)
  have hoddc := odd_of_rows m _ hmo hc (Or.inr ⟨a + (m + 2), rfl, hb⟩)
  have hblkc := blk1_direct m _ hc hoddc
  have hb3 : ¬ IsP m (a + (m + 2) + 3 * u) (3 * u) := by
    rw [o_odd_iff m (4 * u) a (3 * u) hmh hrow hb hah (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + 3 * u) / 2 = (11 * u + 1) / 2 by omega]
    exact fun h => h (hoddA _ (by omega) (by omega) (by omega))
  have hb6 : IsP m (a + (m + 2) + 6 * u) (6 * u) := by
    rw [show 6 * u = 2 * (3 * u) by omega, o_half' m (4 * u) a (3 * u) hmh hrow hb hah (by omega) (by omega) (by omega)]
    exact hb3
  have hc4 : ¬ IsP m (a + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    rw [e_iff m (4 * u) (a + (m + 2)) (4 * u) hmh hb hc (by omega) (by omega) (by omega),
      show 4 * u / 2 = 2 * u by omega, show 4 * u + 2 * u = 6 * u by omega]
    exact fun ⟨_, h⟩ => h hb6
  have ha' := row_next m (a + (m + 2) + (m + 1)) hc (by rw [hh]; exact hc4)
  have hblk' := k68b_blk m u hmu hu _ hc hblkc ha'
  -- (a' + X₁) は P
  have hvX2 : v2 ((9 * u + 1) / 4) = 3 := by
    have h16 : ((9 * u + 1) / 4) % 16 = 8 := by omega
    rw [v2_even _ (by omega) (by omega), v2_even (_ / 2) (by omega) (by omega),
      v2_even (_ / 2 / 2) (by omega) (by omega), v2_odd _ (by omega)]
  have hvY : v2 ((11 * u + 1 + (9 * u + 1) / 16) / 2) = 2 := by
    have h8 : ((11 * u + 1 + (9 * u + 1) / 16) / 2) % 8 = 4 := by omega
    rw [v2_even _ (by omega) (by omega), v2_even (_ / 2) (by omega) (by omega), v2_odd _ (by omega)]
  have hX' : IsP m (a + (m + 2) + (m + 1) + (m + 1) + (9 * u + 1) / 2) ((9 * u + 1) / 2) := by
    rw [e_iff m (4 * u) (a + (m + 2) + (m + 1)) _ hmh hc ha' (by omega) (by omega) (by omega)]
    constructor
    · rw [show (9 * u + 1) / 2 / 2 = (9 * u + 1) / 4 by omega, hblk' _ (by omega) (by omega) (by omega), hvX2]
      omega
    · rw [show 4 * u + (9 * u + 1) / 2 / 2 = 4 * u + (9 * u + 1) / 4 by omega,
        e_iff m (4 * u) (a + (m + 2)) _ hmh hb hc (by omega) (by omega) (by omega)]
      intro ⟨_, hN⟩
      apply hN
      rw [show 4 * u + (4 * u + (9 * u + 1) / 4) / 2 = 2 * (3 * u + (9 * u + 1) / 16) by omega,
        o_half' m (4 * u) a (3 * u + (9 * u + 1) / 16) hmh hrow hb hah (by omega) (by omega) (by omega),
        o_odd_iff m (4 * u) a (3 * u + (9 * u + 1) / 16) hmh hrow hb hah (by omega) (by omega) (by omega) (by omega),
        show (m + 2 + (3 * u + (9 * u + 1) / 16)) / 2 = (11 * u + 1 + (9 * u + 1) / 16) / 2 by omega]
      intro hNP; apply hNP
      exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have e1 : a + (3 * m + 4) = a + (m + 2) + (m + 1) + (m + 1) := by omega
  refine ⟨hb, ?_, ?_, ?_, ?_, hah⟩
  · intro p; rw [show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega]; exact hc p
  · intro p; rw [e1]; exact ha' p
  · rw [e1]; exact hblk'
  · rw [e1]; exact hX'

theorem k68b_rows : ∀ i, (∀ p, IsP m (i * (3 * m + 4)) p) ∧ Blk m 3 (i * (3 * m + 4)) ∧
    IsP m (i * (3 * m + 4) + (9 * u + 1) / 2) ((9 * u + 1) / 2) := by
  intro i
  induction i with
  | zero =>
    rw [Nat.zero_mul]
    refine ⟨isP_zero m, blk_zero m 3, ?_⟩
    have hv : v2 ((9 * u + 1) / 2) = 4 := by
      have h32 : ((9 * u + 1) / 2) % 32 = 16 := by omega
      rw [v2_even _ (by omega) (by omega), v2_even (_ / 2) (by omega) (by omega),
        v2_even (_ / 2 / 2) (by omega) (by omega), v2_even (_ / 2 / 2 / 2) (by omega) (by omega), v2_odd _ (by omega)]
    exact (blk_zero m 4 _ (by omega) (by omega) (by omega)).mpr (by omega)
  | succ i ih =>
    obtain ⟨hrow, hblk, hX⟩ := ih
    obtain ⟨_, _, ha', hb', hX', _⟩ := k68b_step m u hmu hu _ hrow hblk hX
    rw [Nat.succ_mul]; exact ⟨ha', hb', hX'⟩

end K68b

/-- 予想 K68 の u ≡ 103 (mod 256)：m + 1 = 8u なら、(n, 0) が P ⇔ n mod (3m+4) ∈ {0, m+2, 2m+3}。-/
theorem K68_103 (m : Nat) (hm : (m + 1) % 2048 = 824) (n : Nat) :
    IsP m n 0 ↔ (n % (3 * m + 4) = 0 ∨ n % (3 * m + 4) = m + 2 ∨ n % (3 * m + 4) = 2 * m + 3) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk, hX⟩ := k68b_rows m _ hmu (by omega) (n / (3 * m + 4))
  obtain ⟨hrowb, hrowc, _, _, _, hah⟩ := k68b_step m _ hmu (by omega) _ hrow hblk hX
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
