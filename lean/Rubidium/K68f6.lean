/-
  Rubidium.K68f6 — v2(m+1) = 3 の類（u mod 8192）の型の証明（code/k68_gen.js で生成、code/k68_search.js 8192 の結果の第 6 組）

  証明の方法は K68e と同じ（始まりの行の不変量 Blk m 3）。
-/
import Rubidium.K67b

namespace Rubidium

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

section K68g6253

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 8192 = 6253)
include hmu hu

theorem k68g6253_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g6253_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (5 * m + 7)) p) ∧
    Blk m 3 (a + (5 * m + 7)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 4 * u) (4 * u) := by
    have hv : v2 (4 * u) = 2 := by
      have : (4 * u) % 8 = 4 := by omega
      rw [v2_even (4 * u) (by omega) (by omega),
        v2_even (4 * u / 2) (by omega) (by omega),
        v2_odd (4 * u / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : IsP m (a + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    have hv : v2 ((36 * u + 4) / 8) = 0 := by
      have : ((36 * u + 4) / 8) % 2 = 1 := by omega
      rw [v2_odd ((36 * u + 4) / 8) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F2 : ¬ IsP m (a + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F1
  have F3 : IsP m (a + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F2
  have F4 : ¬ IsP m (a + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((4 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F3
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 1)) p := row_next m (a + (m + 2)) hr1 (by rw [hh]; exact F4)
  have hb2 := blk1_direct m _ hr2 (odd_of_rows m _ hmo hr2 (Or.inr ⟨_, rfl, hr1⟩))
  have F5 : ¬ IsP m (a + (m + 2) + (m + 1) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    have hv : v2 ((4 * u + 0) / 2) = 1 := by
      have : ((4 * u + 0) / 2) % 4 = 2 := by omega
      rw [v2_even ((4 * u + 0) / 2) (by omega) (by omega),
        v2_odd ((4 * u + 0) / 2 / 2) (by omega)]
    intro h; have := (hb2 _ (by omega) (by omega) (by omega)).mp h; omega
  have F6 : ¬ IsP m (a + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    have hv : v2 ((44 * u + 4) / 8) = 3 := by
      have : ((44 * u + 4) / 8) % 16 = 8 := by omega
      rw [v2_even ((44 * u + 4) / 8) (by omega) (by omega),
        v2_even ((44 * u + 4) / 8 / 2) (by omega) (by omega),
        v2_even ((44 * u + 4) / 8 / 2 / 2) (by omega) (by omega),
        v2_odd ((44 * u + 4) / 8 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F7 : IsP m (a + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a) ((12 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F6
  have F8 : ¬ IsP m (a + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((12 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F7
  have F9 : IsP m (a + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    refine (e_iff m (4 * u) (a + (m + 2)) (4 * u) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show 4 * u / 2 = (4 * u + 0) / 2 by omega]; exact F5
    · rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F8
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2)) p := row_long m (a + (m + 2) + (m + 1)) hmo (by omega) hr2 (by rw [hh]; exact F9)
  have F10 : IsP m (a + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    have hv : v2 ((36 * u + 4) / 8) = 0 := by
      have : ((36 * u + 4) / 8) % 2 = 1 := by omega
      rw [v2_odd ((36 * u + 4) / 8) (by omega)]
    exact (hb2 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F11 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F10
  have F12 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F11
  have F13 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mp h F12
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2)) hr3 (by rw [hh]; exact F13)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F16 : IsP m (a + (684 * u + 68) / 128) ((684 * u + 68) / 128) := by
    have hv : v2 ((684 * u + 68) / 128) = 0 := by
      have : ((684 * u + 68) / 128) % 2 = 1 := by omega
      rw [v2_odd ((684 * u + 68) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F17 : ¬ IsP m (a + (m + 2) + (172 * u + 4) / 64) ((172 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((172 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (172 * u + 4) / 64) / 2 = (684 * u + 68) / 128 by omega]; exact F16
  have F18 : IsP m (a + (m + 2) + (172 * u + 4) / 32) ((172 * u + 4) / 32) := by
    rw [show (172 * u + 4) / 32 = 2 * ((172 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((172 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F17
  have F19 : ¬ IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 16) ((44 * u + 4) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 16) hmh hr1 hr2 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (44 * u + 4) / 16 / 2 = (172 * u + 4) / 32 by omega]; exact F18
  have F20 : ¬ IsP m (a + (4204 * u + 516) / 1024) ((4204 * u + 516) / 1024) := by
    have hv : v2 ((4204 * u + 516) / 1024) = 3 := by
      have : ((4204 * u + 516) / 1024) % 16 = 8 := by omega
      rw [v2_even ((4204 * u + 516) / 1024) (by omega) (by omega),
        v2_even ((4204 * u + 516) / 1024 / 2) (by omega) (by omega),
        v2_even ((4204 * u + 516) / 1024 / 2 / 2) (by omega) (by omega),
        v2_odd ((4204 * u + 516) / 1024 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F21 : IsP m (a + (m + 2) + (108 * u + 4) / 512) ((108 * u + 4) / 512) := by
    refine (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (108 * u + 4) / 512) / 2 = (4204 * u + 516) / 1024 by omega]; exact F20
  have F22 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    rw [show (108 * u + 4) / 256 = 2 * ((108 * u + 4) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F21
  have F23 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F23
  have F25 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F24
  have F26 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F25
  have F27 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F26
  have F28 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F27
  have F29 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F28
  have F30 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F29
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F30)
  have hblk' := k68g6253_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g6253_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g6253_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g6253

/-- 予想 K68 の u ≡ 6253 (mod 8192)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_6253 (m : Nat) (hm : (m + 1) % 65536 = 50024) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g6253_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g6253_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (5 * m + 7)) * (5 * m + 7) + n % (5 * m + 7) := by
    have := Nat.div_add_mod n (5 * m + 7)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (5 * m + 7) < 5 * m + 7 := Nat.mod_lt n (by omega)
  generalize hcc : n % (5 * m + 7) = c at hdiv hlt
  generalize ha : n / (5 * m + 7) * (5 * m + 7) = a at hdiv hrow hq1 hq2 hq3 hq4 ht0 ht2
  subst hdiv
  have hmh : m + 1 = 2 * (4 * ((m + 1) / 8)) := by omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases c0 : c ≤ 0 + m
    · rw [show a + c = a + (c - (0)) by omega] at hP
      exact not_isP_of_row m _ (c - (0)) 0 hrow (by omega) (by omega) (by omega) hP
    · by_cases d0 : c = 0 + (m + 1)
      · rw [d0, show a + (0 + (m + 1)) = a + (m + 1) by omega] at hP
        exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht0 (by omega) hP
      · by_cases c1 : c ≤ 1 * m + 2 + m
        · rw [show a + c = a + (m + 2) + (c - (1 * m + 2)) by omega] at hP
          exact not_isP_of_row m _ (c - (1 * m + 2)) 0 hq1 (by omega) (by omega) (by omega) hP
        · by_cases c2 : c ≤ 2 * m + 3 + m
          · rw [show a + c = a + (m + 2) + (m + 1) + (c - (2 * m + 3)) by omega] at hP
            exact not_isP_of_row m _ (c - (2 * m + 3)) 0 hq2 (by omega) (by omega) (by omega) hP
          · by_cases d2 : c = 2 * m + 3 + (m + 1)
            · rw [d2, show a + (2 * m + 3 + (m + 1)) = a + (m + 2) + (m + 1) + (m + 1) by omega] at hP
              exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht2 (by omega) hP
            · by_cases c3 : c ≤ 3 * m + 5 + m
              · rw [show a + c = a + (m + 2) + (m + 1) + (m + 2) + (c - (3 * m + 5)) by omega] at hP
                exact not_isP_of_row m _ (c - (3 * m + 5)) 0 hq3 (by omega) (by omega) (by omega) hP
              · rw [show a + c = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (c - (4 * m + 6)) by omega] at hP
                exact not_isP_of_row m _ (c - (4 * m + 6)) 0 hq4 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 5) = a + (m + 2) + (m + 1) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 6) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) by omega]; exact hq4 0

section K68g6307

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 8192 = 6307)
include hmu hu

theorem k68g6307_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g6307_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (9 * m + 15)) p) ∧
    Blk m 3 (a + (9 * m + 15)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 4 * u) (4 * u) := by
    have hv : v2 (4 * u) = 2 := by
      have : (4 * u) % 8 = 4 := by omega
      rw [v2_even (4 * u) (by omega) (by omega),
        v2_even (4 * u / 2) (by omega) (by omega),
        v2_odd (4 * u / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    have hv : v2 ((36 * u + 4) / 8) = 1 := by
      have : ((36 * u + 4) / 8) % 4 = 2 := by omega
      rw [v2_even ((36 * u + 4) / 8) (by omega) (by omega),
        v2_odd ((36 * u + 4) / 8 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a) ((4 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F4)
  have F5 : IsP m (a + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    have hv : v2 ((164 * u + 20) / 32) = 2 := by
      have : ((164 * u + 20) / 32) % 8 = 4 := by omega
      rw [v2_even ((164 * u + 20) / 32) (by omega) (by omega),
        v2_even ((164 * u + 20) / 32 / 2) (by omega) (by omega),
        v2_odd ((164 * u + 20) / 32 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F6 : ¬ IsP m (a + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((36 * u + 4) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F5
  have F7 : IsP m (a + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a) ((36 * u + 4) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F6
  have F8 : ¬ IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F7
  have F9 : IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F8
  have F10 : ¬ IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 2) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F9
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2)) hr2 (by rw [hh]; exact F10)
  have hb3 := blk1_direct m _ hr3 (odd_of_rows m _ hmo hr3 (Or.inr ⟨_, rfl, hr2⟩))
  have F11 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    have hv : v2 ((4 * u + 0) / 2) = 1 := by
      have : ((4 * u + 0) / 2) % 4 = 2 := by omega
      rw [v2_even ((4 * u + 0) / 2) (by omega) (by omega),
        v2_odd ((4 * u + 0) / 2 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F12 : IsP m (a + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    have hv : v2 ((108 * u + 12) / 16) = 0 := by
      have : ((108 * u + 12) / 16) % 2 = 1 := by omega
      rw [v2_odd ((108 * u + 12) / 16) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F13 : ¬ IsP m (a + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((44 * u + 4) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((12 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F13
  have F15 : ¬ IsP m (a + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((12 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F14
  have F16 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) (4 * u) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show 4 * u / 2 = (4 * u + 0) / 2 by omega]; exact F11
    · rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F15
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) hr3 (by rw [hh]; exact F16)
  have F17 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    have hv : v2 ((36 * u + 4) / 8) = 1 := by
      have : ((36 * u + 4) / 8) % 4 = 2 := by omega
      rw [v2_even ((36 * u + 4) / 8) (by omega) (by omega),
        v2_odd ((36 * u + 4) / 8 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F18 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F17
  have F19 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mp h F18
  have F20 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mpr F19
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hmo (by omega) hr4 (by rw [hh]; exact F20)
  have F22 : IsP m (a + (17828 * u + 2196) / 4096) ((17828 * u + 2196) / 4096) := by
    have hv : v2 ((17828 * u + 2196) / 4096) = 2 := by
      have : ((17828 * u + 2196) / 4096) % 8 = 4 := by omega
      rw [v2_even ((17828 * u + 2196) / 4096) (by omega) (by omega),
        v2_even ((17828 * u + 2196) / 4096 / 2) (by omega) (by omega),
        v2_odd ((17828 * u + 2196) / 4096 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F23 : ¬ IsP m (a + (m + 2) + (1444 * u + 148) / 2048) ((1444 * u + 148) / 2048) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((1444 * u + 148) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1444 * u + 148) / 2048) / 2 = (17828 * u + 2196) / 4096 by omega]; exact F22
  have F24 : IsP m (a + (m + 2) + (1444 * u + 148) / 1024) ((1444 * u + 148) / 1024) := by
    rw [show (1444 * u + 148) / 1024 = 2 * ((1444 * u + 148) / 2048) by omega]
    exact (o_half' m (4 * u) (a) ((1444 * u + 148) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (1444 * u + 148) / 512) ((1444 * u + 148) / 512) := by
    rw [show (1444 * u + 148) / 512 = 2 * ((1444 * u + 148) / 1024) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((1444 * u + 148) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (1444 * u + 148) / 256) ((1444 * u + 148) / 256) := by
    rw [show (1444 * u + 148) / 256 = 2 * ((1444 * u + 148) / 512) by omega]
    exact (o_half' m (4 * u) (a) ((1444 * u + 148) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 2) + (420 * u + 20) / 128) ((420 * u + 20) / 128) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((420 * u + 20) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (420 * u + 20) / 128) / 2 = (1444 * u + 148) / 256 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (420 * u + 20) / 64) ((420 * u + 20) / 64) := by
    rw [show (420 * u + 20) / 64 = 2 * ((420 * u + 20) / 128) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((420 * u + 20) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 32) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (164 * u + 20) / 32 / 2 = (420 * u + 20) / 64 by omega]; exact F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mp h F30
  have F32 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F20 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F31
  have F33 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mp h F32
  have F34 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mpr F33
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) hmo (by omega) hr5 (by rw [hh]; exact F34)
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (1188 * u + 148) / 256) ((1188 * u + 148) / 256) := by
    have hv : v2 ((1188 * u + 148) / 256) = 0 := by
      have : ((1188 * u + 148) / 256) % 2 = 1 := by omega
      rw [v2_odd ((1188 * u + 148) / 256) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (164 * u + 20) / 128) ((164 * u + 20) / 128) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((164 * u + 20) / 128) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 20) / 128) / 2 = (1188 * u + 148) / 256 by omega]; exact F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    rw [show (164 * u + 20) / 64 = 2 * ((164 * u + 20) / 128) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((164 * u + 20) / 128) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mpr F36
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((164 * u + 20) / 64) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mp h F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((36 * u + 4) / 16) hmh hr4 hr5 F20 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((36 * u + 4) / 16) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mp h F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr5 hr6 F34 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr5 hr6 F34 (by omega) (by omega) (by omega)).mp h F41
  have F43 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr5 hr6 F34 (by omega) (by omega) (by omega)).mpr F42
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) hmo (by omega) hr6 (by rw [hh]; exact F43)
  have F44 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (3236 * u + 404) / 512) ((3236 * u + 404) / 512) := by
    have hv : v2 ((3236 * u + 404) / 512) = 0 := by
      have : ((3236 * u + 404) / 512) % 2 = 1 := by omega
      rw [v2_odd ((3236 * u + 404) / 512) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F45 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (1188 * u + 148) / 256) ((1188 * u + 148) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((1188 * u + 148) / 256) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1188 * u + 148) / 256) / 2 = (3236 * u + 404) / 512 by omega]; exact F44
  have F46 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (164 * u + 20) / 128) ((164 * u + 20) / 128) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((164 * u + 20) / 128) hmh hr4 hr5 F20 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (164 * u + 20) / 128) / 2 = (1188 * u + 148) / 256 by omega]; exact F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    rw [show (164 * u + 20) / 64 = 2 * ((164 * u + 20) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((164 * u + 20) / 128) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mp h F46
  have F48 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((164 * u + 20) / 64) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mpr F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr5 hr6 F34 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr5 hr6 F34 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr6 hr7 F43 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F50
  have F52 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr6 hr7 F43 (by omega) (by omega) (by omega)).mpr F51
  have F53 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr6 hr7 F43 (by omega) (by omega) (by omega)).mp h F52
  have hr8 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hr7 (by rw [hh]; exact F53)
  have hb8 := blk1_direct m _ hr8 (odd_of_rows m _ hmo hr8 (Or.inr ⟨_, rfl, hr7⟩))
  have F55 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (492 * u + 60) / 64) ((492 * u + 60) / 64) := by
    have hv : v2 ((492 * u + 60) / 64) = 1 := by
      have : ((492 * u + 60) / 64) % 4 = 2 := by omega
      rw [v2_even ((492 * u + 60) / 64) (by omega) (by omega),
        v2_odd ((492 * u + 60) / 64 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F56 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (236 * u + 28) / 32) ((236 * u + 28) / 32) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((236 * u + 28) / 32) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (236 * u + 28) / 32) / 2 = (492 * u + 60) / 64 by omega]; exact F55
  have F57 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((108 * u + 12) / 16) hmh hr4 hr5 F20 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 16) / 2 = (236 * u + 28) / 32 by omega]; exact F56
  have F58 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((44 * u + 4) / 8) hmh hr5 hr6 F34 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F57
  have F59 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr6 hr7 F43 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F58
  have F60 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr6 hr7 F43 (by omega) (by omega) (by omega)).mpr F59
  have F61 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr7 hr8 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F60
  have hr9 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr8 (by rw [hh]; exact F61)
  have hblk' := k68g6307_blk m u hmu hu _ hr8 hb8 hr9
  rw [show a + (9 * m + 15) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hblk', F0, F4, F16, F20, F34, F43⟩

theorem k68g6307_rows : ∀ i, (∀ p, IsP m (i * (9 * m + 15)) p) ∧ Blk m 3 (i * (9 * m + 15)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, _, _, ha, hb, _⟩ := k68g6307_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g6307

/-- 予想 K68 の u ≡ 6307 (mod 8192)（110111100 型）：(n, 0) が P ⇔ n mod (9 * m + 15) が各行の始まり。-/
theorem K68_6307 (m : Nat) (hm : (m + 1) % 65536 = 50456) (n : Nat) :
    IsP m n 0 ↔ (n % (9 * m + 15) = 0 ∨ n % (9 * m + 15) = 1 * m + 2 ∨ n % (9 * m + 15) = 2 * m + 4 ∨ n % (9 * m + 15) = 3 * m + 5 ∨ n % (9 * m + 15) = 4 * m + 7 ∨ n % (9 * m + 15) = 5 * m + 9 ∨ n % (9 * m + 15) = 6 * m + 11 ∨ n % (9 * m + 15) = 7 * m + 13 ∨ n % (9 * m + 15) = 8 * m + 14) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g6307_rows m _ hmu (by omega) (n / (9 * m + 15))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, _, _, ht0, ht1, ht3, ht4, ht5, ht6⟩ := k68g6307_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (9 * m + 15)) * (9 * m + 15) + n % (9 * m + 15) := by
    have := Nat.div_add_mod n (9 * m + 15)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (9 * m + 15) < 9 * m + 15 := Nat.mod_lt n (by omega)
  generalize hcc : n % (9 * m + 15) = c at hdiv hlt
  generalize ha : n / (9 * m + 15) * (9 * m + 15) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 ht0 ht1 ht3 ht4 ht5 ht6
  subst hdiv
  have hmh : m + 1 = 2 * (4 * ((m + 1) / 8)) := by omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases c0 : c ≤ 0 + m
    · rw [show a + c = a + (c - (0)) by omega] at hP
      exact not_isP_of_row m _ (c - (0)) 0 hrow (by omega) (by omega) (by omega) hP
    · by_cases d0 : c = 0 + (m + 1)
      · rw [d0, show a + (0 + (m + 1)) = a + (m + 1) by omega] at hP
        exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht0 (by omega) hP
      · by_cases c1 : c ≤ 1 * m + 2 + m
        · rw [show a + c = a + (m + 2) + (c - (1 * m + 2)) by omega] at hP
          exact not_isP_of_row m _ (c - (1 * m + 2)) 0 hq1 (by omega) (by omega) (by omega) hP
        · by_cases d1 : c = 1 * m + 2 + (m + 1)
          · rw [d1, show a + (1 * m + 2 + (m + 1)) = a + (m + 2) + (m + 1) by omega] at hP
            exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht1 (by omega) hP
          · by_cases c2 : c ≤ 2 * m + 4 + m
            · rw [show a + c = a + (m + 2) + (m + 2) + (c - (2 * m + 4)) by omega] at hP
              exact not_isP_of_row m _ (c - (2 * m + 4)) 0 hq2 (by omega) (by omega) (by omega) hP
            · by_cases c3 : c ≤ 3 * m + 5 + m
              · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (c - (3 * m + 5)) by omega] at hP
                exact not_isP_of_row m _ (c - (3 * m + 5)) 0 hq3 (by omega) (by omega) (by omega) hP
              · by_cases d3 : c = 3 * m + 5 + (m + 1)
                · rw [d3, show a + (3 * m + 5 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega] at hP
                  exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht3 (by omega) hP
                · by_cases c4 : c ≤ 4 * m + 7 + m
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (c - (4 * m + 7)) by omega] at hP
                    exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
                  · by_cases d4 : c = 4 * m + 7 + (m + 1)
                    · rw [d4, show a + (4 * m + 7 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) by omega] at hP
                      exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht4 (by omega) hP
                    · by_cases c5 : c ≤ 5 * m + 9 + m
                      · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (c - (5 * m + 9)) by omega] at hP
                        exact not_isP_of_row m _ (c - (5 * m + 9)) 0 hq5 (by omega) (by omega) (by omega) hP
                      · by_cases d5 : c = 5 * m + 9 + (m + 1)
                        · rw [d5, show a + (5 * m + 9 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) by omega] at hP
                          exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht5 (by omega) hP
                        · by_cases c6 : c ≤ 6 * m + 11 + m
                          · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (c - (6 * m + 11)) by omega] at hP
                            exact not_isP_of_row m _ (c - (6 * m + 11)) 0 hq6 (by omega) (by omega) (by omega) hP
                          · by_cases d6 : c = 6 * m + 11 + (m + 1)
                            · rw [d6, show a + (6 * m + 11 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega] at hP
                              exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht6 (by omega) hP
                            · by_cases c7 : c ≤ 7 * m + 13 + m
                              · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (c - (7 * m + 13)) by omega] at hP
                                exact not_isP_of_row m _ (c - (7 * m + 13)) 0 hq7 (by omega) (by omega) (by omega) hP
                              · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (8 * m + 14)) by omega] at hP
                                exact not_isP_of_row m _ (c - (8 * m + 14)) 0 hq8 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 5) = a + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) by omega]; exact hq5 0
    · rw [h, show a + (6 * m + 11) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq6 0
    · rw [h, show a + (7 * m + 13) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq7 0
    · rw [h, show a + (8 * m + 14) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq8 0

section K68g6359

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 8192 = 6359)
include hmu hu

theorem k68g6359_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g6359_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (6 * m + 9)) p) ∧
    Blk m 3 (a + (6 * m + 9)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 4 * u) (4 * u) := by
    have hv : v2 (4 * u) = 2 := by
      have : (4 * u) % 8 = 4 := by omega
      rw [v2_even (4 * u) (by omega) (by omega),
        v2_even (4 * u / 2) (by omega) (by omega),
        v2_odd (4 * u / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    have hv : v2 ((36 * u + 4) / 8) = 3 := by
      have : ((36 * u + 4) / 8) % 16 = 8 := by omega
      rw [v2_even ((36 * u + 4) / 8) (by omega) (by omega),
        v2_even ((36 * u + 4) / 8 / 2) (by omega) (by omega),
        v2_even ((36 * u + 4) / 8 / 2 / 2) (by omega) (by omega),
        v2_odd ((36 * u + 4) / 8 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a) ((4 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F4)
  have F5 : IsP m (a + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    have hv : v2 ((548 * u + 68) / 128) = 0 := by
      have : ((548 * u + 68) / 128) % 2 = 1 := by omega
      rw [v2_odd ((548 * u + 68) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F6 : ¬ IsP m (a + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((36 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F5
  have F7 : IsP m (a + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((36 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F6
  have F8 : ¬ IsP m (a + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((36 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F7
  have F9 : IsP m (a + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a) ((36 * u + 4) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F8
  have F10 : ¬ IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F9
  have F11 : IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F10
  have F12 : ¬ IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 2) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F11
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2)) hr2 (by rw [hh]; exact F12)
  have hb3 := blk1_direct m _ hr3 (odd_of_rows m _ hmo hr3 (Or.inr ⟨_, rfl, hr2⟩))
  have F13 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    have hv : v2 ((4 * u + 0) / 2) = 1 := by
      have : ((4 * u + 0) / 2) % 4 = 2 := by omega
      rw [v2_even ((4 * u + 0) / 2) (by omega) (by omega),
        v2_odd ((4 * u + 0) / 2 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F14 : IsP m (a + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    have hv : v2 ((108 * u + 12) / 16) = 2 := by
      have : ((108 * u + 12) / 16) % 8 = 4 := by omega
      rw [v2_even ((108 * u + 12) / 16) (by omega) (by omega),
        v2_even ((108 * u + 12) / 16 / 2) (by omega) (by omega),
        v2_odd ((108 * u + 12) / 16 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F15 : ¬ IsP m (a + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((44 * u + 4) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F14
  have F16 : IsP m (a + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((12 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F15
  have F17 : ¬ IsP m (a + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((12 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F16
  have F18 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) (4 * u) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show 4 * u / 2 = (4 * u + 0) / 2 by omega]; exact F13
    · rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F17
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) hr3 (by rw [hh]; exact F18)
  have F20 : ¬ IsP m (a + (17060 * u + 2116) / 4096) ((17060 * u + 2116) / 4096) := by
    have hv : v2 ((17060 * u + 2116) / 4096) = 1 := by
      have : ((17060 * u + 2116) / 4096) % 4 = 2 := by omega
      rw [v2_even ((17060 * u + 2116) / 4096) (by omega) (by omega),
        v2_odd ((17060 * u + 2116) / 4096 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F21 : IsP m (a + (m + 2) + (676 * u + 68) / 2048) ((676 * u + 68) / 2048) := by
    refine (o_odd_iff m (4 * u) (a) ((676 * u + 68) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (676 * u + 68) / 2048) / 2 = (17060 * u + 2116) / 4096 by omega]; exact F20
  have F22 : ¬ IsP m (a + (m + 2) + (676 * u + 68) / 1024) ((676 * u + 68) / 1024) := by
    rw [show (676 * u + 68) / 1024 = 2 * ((676 * u + 68) / 2048) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((676 * u + 68) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F21
  have F23 : IsP m (a + (m + 2) + (676 * u + 68) / 512) ((676 * u + 68) / 512) := by
    rw [show (676 * u + 68) / 512 = 2 * ((676 * u + 68) / 1024) by omega]
    exact (o_half' m (4 * u) (a) ((676 * u + 68) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (676 * u + 68) / 256) ((676 * u + 68) / 256) := by
    rw [show (676 * u + 68) / 256 = 2 * ((676 * u + 68) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((676 * u + 68) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F23
  have F25 : IsP m (a + (m + 2) + (676 * u + 68) / 128) ((676 * u + 68) / 128) := by
    rw [show (676 * u + 68) / 128 = 2 * ((676 * u + 68) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F24
  have F26 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 64) ((164 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 4) / 64) / 2 = (676 * u + 68) / 128 by omega]; exact F25
  have F27 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 32) ((164 * u + 4) / 32) := by
    rw [show (164 * u + 4) / 32 = 2 * ((164 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F26
  have F28 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 16 / 2 = (164 * u + 4) / 32 by omega]; exact F27
  have F29 : ¬ IsP m (a + (24676 * u + 3076) / 4096) ((24676 * u + 3076) / 4096) := by
    have hv : v2 ((24676 * u + 3076) / 4096) = 1 := by
      have : ((24676 * u + 3076) / 4096) % 4 = 2 := by omega
      rw [v2_even ((24676 * u + 3076) / 4096) (by omega) (by omega),
        v2_odd ((24676 * u + 3076) / 4096 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F30 : IsP m (a + (m + 2) + (8292 * u + 1028) / 2048) ((8292 * u + 1028) / 2048) := by
    refine (o_odd_iff m (4 * u) (a) ((8292 * u + 1028) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (8292 * u + 1028) / 2048) / 2 = (24676 * u + 3076) / 4096 by omega]; exact F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 1024) ((100 * u + 4) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 1024) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (100 * u + 4) / 1024) / 2 = (8292 * u + 1028) / 2048 by omega]; exact F30
  have F32 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 512) ((100 * u + 4) / 512) := by
    rw [show (100 * u + 4) / 512 = 2 * ((100 * u + 4) / 1024) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 1024) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F31
  have F33 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 256) ((100 * u + 4) / 256) := by
    rw [show (100 * u + 4) / 256 = 2 * ((100 * u + 4) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 512) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F32
  have F34 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    rw [show (100 * u + 4) / 128 = 2 * ((100 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F33
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F34
  have F36 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F35
  have F37 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F36
  have F38 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (36 * u + 4) / 8 / 2 = (36 * u + 4) / 16 by omega]; exact F28
    · rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F37
  have F39 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F38
  have F40 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F39
  have F41 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F40
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F41)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F43 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    have hv : v2 ((44 * u + 4) / 8) = 0 := by
      have : ((44 * u + 4) / 8) % 2 = 1 := by omega
      rw [v2_odd ((44 * u + 4) / 8) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F44 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F43
  have F45 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F44
  have F46 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F45
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F46)
  have hblk' := k68g6359_blk m u hmu hu _ hr5 hb5 hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F4, F18⟩

theorem k68g6359_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 3 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k68g6359_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g6359

/-- 予想 K68 の u ≡ 6359 (mod 8192)（110100 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K68_6359 (m : Nat) (hm : (m + 1) % 65536 = 50872) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 5 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g6359_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht3⟩ := k68g6359_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (6 * m + 9)) * (6 * m + 9) + n % (6 * m + 9) := by
    have := Nat.div_add_mod n (6 * m + 9)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (6 * m + 9) < 6 * m + 9 := Nat.mod_lt n (by omega)
  generalize hcc : n % (6 * m + 9) = c at hdiv hlt
  generalize ha : n / (6 * m + 9) * (6 * m + 9) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 ht0 ht1 ht3
  subst hdiv
  have hmh : m + 1 = 2 * (4 * ((m + 1) / 8)) := by omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases c0 : c ≤ 0 + m
    · rw [show a + c = a + (c - (0)) by omega] at hP
      exact not_isP_of_row m _ (c - (0)) 0 hrow (by omega) (by omega) (by omega) hP
    · by_cases d0 : c = 0 + (m + 1)
      · rw [d0, show a + (0 + (m + 1)) = a + (m + 1) by omega] at hP
        exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht0 (by omega) hP
      · by_cases c1 : c ≤ 1 * m + 2 + m
        · rw [show a + c = a + (m + 2) + (c - (1 * m + 2)) by omega] at hP
          exact not_isP_of_row m _ (c - (1 * m + 2)) 0 hq1 (by omega) (by omega) (by omega) hP
        · by_cases d1 : c = 1 * m + 2 + (m + 1)
          · rw [d1, show a + (1 * m + 2 + (m + 1)) = a + (m + 2) + (m + 1) by omega] at hP
            exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht1 (by omega) hP
          · by_cases c2 : c ≤ 2 * m + 4 + m
            · rw [show a + c = a + (m + 2) + (m + 2) + (c - (2 * m + 4)) by omega] at hP
              exact not_isP_of_row m _ (c - (2 * m + 4)) 0 hq2 (by omega) (by omega) (by omega) hP
            · by_cases c3 : c ≤ 3 * m + 5 + m
              · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (c - (3 * m + 5)) by omega] at hP
                exact not_isP_of_row m _ (c - (3 * m + 5)) 0 hq3 (by omega) (by omega) (by omega) hP
              · by_cases d3 : c = 3 * m + 5 + (m + 1)
                · rw [d3, show a + (3 * m + 5 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega] at hP
                  exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht3 (by omega) hP
                · by_cases c4 : c ≤ 4 * m + 7 + m
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (c - (4 * m + 7)) by omega] at hP
                    exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (c - (5 * m + 8)) by omega] at hP
                    exact not_isP_of_row m _ (c - (5 * m + 8)) 0 hq5 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 5) = a + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) by omega]; exact hq5 0

section K68g6519

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 8192 = 6519)
include hmu hu

theorem k68g6519_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g6519_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (8 * m + 13)) p) ∧
    Blk m 3 (a + (8 * m + 13)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 4 * u) (4 * u) := by
    have hv : v2 (4 * u) = 2 := by
      have : (4 * u) % 8 = 4 := by omega
      rw [v2_even (4 * u) (by omega) (by omega),
        v2_even (4 * u / 2) (by omega) (by omega),
        v2_odd (4 * u / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    have hv : v2 ((36 * u + 4) / 8) = 3 := by
      have : ((36 * u + 4) / 8) % 16 = 8 := by omega
      rw [v2_even ((36 * u + 4) / 8) (by omega) (by omega),
        v2_even ((36 * u + 4) / 8 / 2) (by omega) (by omega),
        v2_even ((36 * u + 4) / 8 / 2 / 2) (by omega) (by omega),
        v2_odd ((36 * u + 4) / 8 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a) ((4 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F4)
  have F5 : ¬ IsP m (a + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    have hv : v2 ((548 * u + 68) / 128) = 1 := by
      have : ((548 * u + 68) / 128) % 4 = 2 := by omega
      rw [v2_even ((548 * u + 68) / 128) (by omega) (by omega),
        v2_odd ((548 * u + 68) / 128 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F6 : IsP m (a + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    refine (o_odd_iff m (4 * u) (a) ((36 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F5
  have F7 : ¬ IsP m (a + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((36 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F6
  have F8 : IsP m (a + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact (o_half' m (4 * u) (a) ((36 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F7
  have F9 : ¬ IsP m (a + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((36 * u + 4) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F9
  have F11 : ¬ IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F10
  have F12 : IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 2) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F11
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F12)
  have F13 : ¬ IsP m (a + (2596 * u + 324) / 512) ((2596 * u + 324) / 512) := by
    have hv : v2 ((2596 * u + 324) / 512) = 1 := by
      have : ((2596 * u + 324) / 512) % 4 = 2 := by omega
      rw [v2_even ((2596 * u + 324) / 512) (by omega) (by omega),
        v2_odd ((2596 * u + 324) / 512 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F14 : IsP m (a + (m + 2) + (548 * u + 68) / 256) ((548 * u + 68) / 256) := by
    refine (o_odd_iff m (4 * u) (a) ((548 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (548 * u + 68) / 256) / 2 = (2596 * u + 324) / 512 by omega]; exact F13
  have F15 : ¬ IsP m (a + (m + 2) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    rw [show (548 * u + 68) / 128 = 2 * ((548 * u + 68) / 256) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((548 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F14
  have F16 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((36 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F15
  have F17 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F16
  have F18 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F17
  have F19 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F18
  have F20 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F19
  have F21 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mp h F20
  have F22 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mpr F21
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 2)) hmo (by omega) hr3 (by rw [hh]; exact F22)
  have F23 : IsP m (a + (10788 * u + 1348) / 2048) ((10788 * u + 1348) / 2048) := by
    have hv : v2 ((10788 * u + 1348) / 2048) = 2 := by
      have : ((10788 * u + 1348) / 2048) % 8 = 4 := by omega
      rw [v2_even ((10788 * u + 1348) / 2048) (by omega) (by omega),
        v2_even ((10788 * u + 1348) / 2048 / 2) (by omega) (by omega),
        v2_odd ((10788 * u + 1348) / 2048 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F24 : ¬ IsP m (a + (m + 2) + (2596 * u + 324) / 1024) ((2596 * u + 324) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((2596 * u + 324) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2596 * u + 324) / 1024) / 2 = (10788 * u + 1348) / 2048 by omega]; exact F23
  have F25 : IsP m (a + (m + 2) + (2596 * u + 324) / 512) ((2596 * u + 324) / 512) := by
    rw [show (2596 * u + 324) / 512 = 2 * ((2596 * u + 324) / 1024) by omega]
    exact (o_half' m (4 * u) (a) ((2596 * u + 324) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F24
  have F26 : ¬ IsP m (a + (m + 2) + (m + 2) + (548 * u + 68) / 256) ((548 * u + 68) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((548 * u + 68) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (548 * u + 68) / 256) / 2 = (2596 * u + 324) / 512 by omega]; exact F25
  have F27 : IsP m (a + (m + 2) + (m + 2) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    rw [show (548 * u + 68) / 128 = 2 * ((548 * u + 68) / 256) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((548 * u + 68) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F26
  have F28 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 64) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F27
  have F29 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 64) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mpr F28
  have F30 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 32) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mp h F29
  have F31 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr3 hr4 F22 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr3 hr4 F22 (by omega) (by omega) (by omega)).mpr F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr3 hr4 F22 (by omega) (by omega) (by omega)).mp h F33
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hr4 (by rw [hh]; exact F34)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    have hv : v2 ((4 * u + 0) / 2) = 1 := by
      have : ((4 * u + 0) / 2) % 4 = 2 := by omega
      rw [v2_even ((4 * u + 0) / 2) (by omega) (by omega),
        v2_odd ((4 * u + 0) / 2 / 2) (by omega)]
    intro h; have := (hb5 _ (by omega) (by omega) (by omega)).mp h; omega
  have F36 : IsP m (a + (1644 * u + 204) / 256) ((1644 * u + 204) / 256) := by
    have hv : v2 ((1644 * u + 204) / 256) = 0 := by
      have : ((1644 * u + 204) / 256) % 2 = 1 := by omega
      rw [v2_odd ((1644 * u + 204) / 256) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F37 : ¬ IsP m (a + (m + 2) + (620 * u + 76) / 128) ((620 * u + 76) / 128) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((620 * u + 76) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (620 * u + 76) / 128) / 2 = (1644 * u + 204) / 256 by omega]; exact F36
  have F38 : IsP m (a + (m + 2) + (m + 2) + (108 * u + 12) / 64) ((108 * u + 12) / 64) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((108 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (108 * u + 12) / 64) / 2 = (620 * u + 76) / 128 by omega]; exact F37
  have F39 : ¬ IsP m (a + (m + 2) + (m + 2) + (108 * u + 12) / 32) ((108 * u + 12) / 32) := by
    rw [show (108 * u + 12) / 32 = 2 * ((108 * u + 12) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((108 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F38
  have F40 : IsP m (a + (m + 2) + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    rw [show (108 * u + 12) / 16 = 2 * ((108 * u + 12) / 32) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((108 * u + 12) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F39
  have F41 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((44 * u + 4) / 8) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F40
  have F42 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr3 hr4 F22 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F41
  have F43 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr3 hr4 F22 (by omega) (by omega) (by omega)).mp h F42
  have F44 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show 4 * u / 2 = (4 * u + 0) / 2 by omega]; exact F35
    · rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F43
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) hr5 (by rw [hh]; exact F44)
  have F46 : IsP m (a + (11940 * u + 1476) / 2048) ((11940 * u + 1476) / 2048) := by
    have hv : v2 ((11940 * u + 1476) / 2048) = 0 := by
      have : ((11940 * u + 1476) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((11940 * u + 1476) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F47 : ¬ IsP m (a + (m + 2) + (3748 * u + 452) / 1024) ((3748 * u + 452) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((3748 * u + 452) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (3748 * u + 452) / 1024) / 2 = (11940 * u + 1476) / 2048 by omega]; exact F46
  have F48 : IsP m (a + (m + 2) + (3748 * u + 452) / 512) ((3748 * u + 452) / 512) := by
    rw [show (3748 * u + 452) / 512 = 2 * ((3748 * u + 452) / 1024) by omega]
    exact (o_half' m (4 * u) (a) ((3748 * u + 452) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (1700 * u + 196) / 256) ((1700 * u + 196) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((1700 * u + 196) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1700 * u + 196) / 256) / 2 = (3748 * u + 452) / 512 by omega]; exact F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (676 * u + 68) / 128) ((676 * u + 68) / 128) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((676 * u + 68) / 128) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (676 * u + 68) / 128) / 2 = (1700 * u + 196) / 256 by omega]; exact F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (164 * u + 4) / 64) ((164 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((164 * u + 4) / 64) hmh hr3 hr4 F22 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 4) / 64) / 2 = (676 * u + 68) / 128 by omega]; exact F50
  have F52 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (164 * u + 4) / 32) ((164 * u + 4) / 32) := by
    rw [show (164 * u + 4) / 32 = 2 * ((164 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((164 * u + 4) / 64) hmh hr3 hr4 F22 (by omega) (by omega) (by omega)).mpr F51
  have F53 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 16 / 2 = (164 * u + 4) / 32 by omega]; exact F52
  have F54 : IsP m (a + (52324 * u + 6532) / 8192) ((52324 * u + 6532) / 8192) := by
    have hv : v2 ((52324 * u + 6532) / 8192) = 0 := by
      have : ((52324 * u + 6532) / 8192) % 2 = 1 := by omega
      rw [v2_odd ((52324 * u + 6532) / 8192) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F55 : ¬ IsP m (a + (m + 2) + (19556 * u + 2436) / 4096) ((19556 * u + 2436) / 4096) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((19556 * u + 2436) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (19556 * u + 2436) / 4096) / 2 = (52324 * u + 6532) / 8192 by omega]; exact F54
  have F56 : IsP m (a + (m + 2) + (m + 2) + (3172 * u + 388) / 2048) ((3172 * u + 388) / 2048) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((3172 * u + 388) / 2048) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (3172 * u + 388) / 2048) / 2 = (19556 * u + 2436) / 4096 by omega]; exact F55
  have F57 : ¬ IsP m (a + (m + 2) + (m + 2) + (3172 * u + 388) / 1024) ((3172 * u + 388) / 1024) := by
    rw [show (3172 * u + 388) / 1024 = 2 * ((3172 * u + 388) / 2048) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((3172 * u + 388) / 2048) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F56
  have F58 : IsP m (a + (m + 2) + (m + 2) + (3172 * u + 388) / 512) ((3172 * u + 388) / 512) := by
    rw [show (3172 * u + 388) / 512 = 2 * ((3172 * u + 388) / 1024) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((3172 * u + 388) / 1024) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F57
  have F59 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (1124 * u + 132) / 256) ((1124 * u + 132) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((1124 * u + 132) / 256) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1124 * u + 132) / 256) / 2 = (3172 * u + 388) / 512 by omega]; exact F58
  have F60 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((100 * u + 4) / 128) hmh hr3 hr4 F22 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (100 * u + 4) / 128) / 2 = (1124 * u + 132) / 256 by omega]; exact F59
  have F61 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((100 * u + 4) / 128) hmh hr3 hr4 F22 (by omega) (by omega) (by omega)).mp h F60
  have F62 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((100 * u + 4) / 64) hmh hr3 hr4 F22 (by omega) (by omega) (by omega)).mpr F61
  have F63 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((100 * u + 4) / 32) hmh hr3 hr4 F22 (by omega) (by omega) (by omega)).mp h F62
  have F64 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (36 * u + 4) / 8 / 2 = (36 * u + 4) / 16 by omega]; exact F53
    · rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F63
  have F65 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr5 hr6 F44 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F64
  have F66 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr5 hr6 F44 (by omega) (by omega) (by omega)).mpr F65
  have F67 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr5 hr6 F44 (by omega) (by omega) (by omega)).mp h F66
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr6 (by rw [hh]; exact F67)
  have hb7 := blk1_direct m _ hr7 (odd_of_rows m _ hmo hr7 (Or.inr ⟨_, rfl, hr6⟩))
  have F69 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    have hv : v2 ((44 * u + 4) / 8) = 0 := by
      have : ((44 * u + 4) / 8) % 2 = 1 := by omega
      rw [v2_odd ((44 * u + 4) / 8) (by omega)]
    exact (hb5 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F70 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr5 hr6 F44 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F69
  have F71 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr5 hr6 F44 (by omega) (by omega) (by omega)).mpr F70
  have F72 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr6 hr7 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F71
  have hr8 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr7 (by rw [hh]; exact F72)
  have hblk' := k68g6519_blk m u hmu hu _ hr7 hb7 hr8
  rw [show a + (8 * m + 13) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hblk', F0, F4, F12, F22, F44⟩

theorem k68g6519_rows : ∀ i, (∀ p, IsP m (i * (8 * m + 13)) p) ∧ Blk m 3 (i * (8 * m + 13)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, _, ha, hb, _⟩ := k68g6519_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g6519

/-- 予想 K68 の u ≡ 6519 (mod 8192)（11110100 型）：(n, 0) が P ⇔ n mod (8 * m + 13) が各行の始まり。-/
theorem K68_6519 (m : Nat) (hm : (m + 1) % 65536 = 52152) (n : Nat) :
    IsP m n 0 ↔ (n % (8 * m + 13) = 0 ∨ n % (8 * m + 13) = 1 * m + 2 ∨ n % (8 * m + 13) = 2 * m + 4 ∨ n % (8 * m + 13) = 3 * m + 6 ∨ n % (8 * m + 13) = 4 * m + 8 ∨ n % (8 * m + 13) = 5 * m + 9 ∨ n % (8 * m + 13) = 6 * m + 11 ∨ n % (8 * m + 13) = 7 * m + 12) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g6519_rows m _ hmu (by omega) (n / (8 * m + 13))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7, _, _, ht0, ht1, ht2, ht3, ht5⟩ := k68g6519_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (8 * m + 13)) * (8 * m + 13) + n % (8 * m + 13) := by
    have := Nat.div_add_mod n (8 * m + 13)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (8 * m + 13) < 8 * m + 13 := Nat.mod_lt n (by omega)
  generalize hcc : n % (8 * m + 13) = c at hdiv hlt
  generalize ha : n / (8 * m + 13) * (8 * m + 13) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 hq6 hq7 ht0 ht1 ht2 ht3 ht5
  subst hdiv
  have hmh : m + 1 = 2 * (4 * ((m + 1) / 8)) := by omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases c0 : c ≤ 0 + m
    · rw [show a + c = a + (c - (0)) by omega] at hP
      exact not_isP_of_row m _ (c - (0)) 0 hrow (by omega) (by omega) (by omega) hP
    · by_cases d0 : c = 0 + (m + 1)
      · rw [d0, show a + (0 + (m + 1)) = a + (m + 1) by omega] at hP
        exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht0 (by omega) hP
      · by_cases c1 : c ≤ 1 * m + 2 + m
        · rw [show a + c = a + (m + 2) + (c - (1 * m + 2)) by omega] at hP
          exact not_isP_of_row m _ (c - (1 * m + 2)) 0 hq1 (by omega) (by omega) (by omega) hP
        · by_cases d1 : c = 1 * m + 2 + (m + 1)
          · rw [d1, show a + (1 * m + 2 + (m + 1)) = a + (m + 2) + (m + 1) by omega] at hP
            exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht1 (by omega) hP
          · by_cases c2 : c ≤ 2 * m + 4 + m
            · rw [show a + c = a + (m + 2) + (m + 2) + (c - (2 * m + 4)) by omega] at hP
              exact not_isP_of_row m _ (c - (2 * m + 4)) 0 hq2 (by omega) (by omega) (by omega) hP
            · by_cases d2 : c = 2 * m + 4 + (m + 1)
              · rw [d2, show a + (2 * m + 4 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) by omega] at hP
                exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht2 (by omega) hP
              · by_cases c3 : c ≤ 3 * m + 6 + m
                · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (c - (3 * m + 6)) by omega] at hP
                  exact not_isP_of_row m _ (c - (3 * m + 6)) 0 hq3 (by omega) (by omega) (by omega) hP
                · by_cases d3 : c = 3 * m + 6 + (m + 1)
                  · rw [d3, show a + (3 * m + 6 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega] at hP
                    exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht3 (by omega) hP
                  · by_cases c4 : c ≤ 4 * m + 8 + m
                    · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (c - (4 * m + 8)) by omega] at hP
                      exact not_isP_of_row m _ (c - (4 * m + 8)) 0 hq4 (by omega) (by omega) (by omega) hP
                    · by_cases c5 : c ≤ 5 * m + 9 + m
                      · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (5 * m + 9)) by omega] at hP
                        exact not_isP_of_row m _ (c - (5 * m + 9)) 0 hq5 (by omega) (by omega) (by omega) hP
                      · by_cases d5 : c = 5 * m + 9 + (m + 1)
                        · rw [d5, show a + (5 * m + 9 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega] at hP
                          exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht5 (by omega) hP
                        · by_cases c6 : c ≤ 6 * m + 11 + m
                          · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (c - (6 * m + 11)) by omega] at hP
                            exact not_isP_of_row m _ (c - (6 * m + 11)) 0 hq6 (by omega) (by omega) (by omega) hP
                          · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (c - (7 * m + 12)) by omega] at hP
                            exact not_isP_of_row m _ (c - (7 * m + 12)) 0 hq7 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 9) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq5 0
    · rw [h, show a + (6 * m + 11) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) by omega]; exact hq6 0
    · rw [h, show a + (7 * m + 12) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) by omega]; exact hq7 0

section K68g6723

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 8192 = 6723)
include hmu hu

theorem k68g6723_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g6723_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (7 * m + 12)) p) ∧
    Blk m 3 (a + (7 * m + 12)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 4 * u) (4 * u) := by
    have hv : v2 (4 * u) = 2 := by
      have : (4 * u) % 8 = 4 := by omega
      rw [v2_even (4 * u) (by omega) (by omega),
        v2_even (4 * u / 2) (by omega) (by omega),
        v2_odd (4 * u / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    have hv : v2 ((36 * u + 4) / 8) = 1 := by
      have : ((36 * u + 4) / 8) % 4 = 2 := by omega
      rw [v2_even ((36 * u + 4) / 8) (by omega) (by omega),
        v2_odd ((36 * u + 4) / 8 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a) ((4 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F4)
  have F5 : ¬ IsP m (a + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    have hv : v2 ((164 * u + 20) / 32) = 3 := by
      have : ((164 * u + 20) / 32) % 16 = 8 := by omega
      rw [v2_even ((164 * u + 20) / 32) (by omega) (by omega),
        v2_even ((164 * u + 20) / 32 / 2) (by omega) (by omega),
        v2_even ((164 * u + 20) / 32 / 2 / 2) (by omega) (by omega),
        v2_odd ((164 * u + 20) / 32 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F6 : IsP m (a + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    refine (o_odd_iff m (4 * u) (a) ((36 * u + 4) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F5
  have F7 : ¬ IsP m (a + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((36 * u + 4) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F6
  have F8 : IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F7
  have F9 : ¬ IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 2) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F9
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F10)
  have F11 : ¬ IsP m (a + (2212 * u + 276) / 512) ((2212 * u + 276) / 512) := by
    have hv : v2 ((2212 * u + 276) / 512) = 1 := by
      have : ((2212 * u + 276) / 512) % 4 = 2 := by omega
      rw [v2_even ((2212 * u + 276) / 512) (by omega) (by omega),
        v2_odd ((2212 * u + 276) / 512 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F12 : IsP m (a + (m + 2) + (164 * u + 20) / 256) ((164 * u + 20) / 256) := by
    refine (o_odd_iff m (4 * u) (a) ((164 * u + 20) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (164 * u + 20) / 256) / 2 = (2212 * u + 276) / 512 by omega]; exact F11
  have F13 : ¬ IsP m (a + (m + 2) + (164 * u + 20) / 128) ((164 * u + 20) / 128) := by
    rw [show (164 * u + 20) / 128 = 2 * ((164 * u + 20) / 256) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((164 * u + 20) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F12
  have F14 : IsP m (a + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    rw [show (164 * u + 20) / 64 = 2 * ((164 * u + 20) / 128) by omega]
    exact (o_half' m (4 * u) (a) ((164 * u + 20) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F13
  have F15 : ¬ IsP m (a + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((164 * u + 20) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F14
  have F16 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F15
  have F17 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F16
  have F18 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F17
  have F19 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mp h F18
  have F20 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mpr F19
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 2)) hmo (by omega) hr3 (by rw [hh]; exact F20)
  have F21 : ¬ IsP m (a + (10404 * u + 1300) / 2048) ((10404 * u + 1300) / 2048) := by
    have hv : v2 ((10404 * u + 1300) / 2048) = 1 := by
      have : ((10404 * u + 1300) / 2048) % 4 = 2 := by omega
      rw [v2_even ((10404 * u + 1300) / 2048) (by omega) (by omega),
        v2_odd ((10404 * u + 1300) / 2048 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F22 : IsP m (a + (m + 2) + (2212 * u + 276) / 1024) ((2212 * u + 276) / 1024) := by
    refine (o_odd_iff m (4 * u) (a) ((2212 * u + 276) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (2212 * u + 276) / 1024) / 2 = (10404 * u + 1300) / 2048 by omega]; exact F21
  have F23 : ¬ IsP m (a + (m + 2) + (2212 * u + 276) / 512) ((2212 * u + 276) / 512) := by
    rw [show (2212 * u + 276) / 512 = 2 * ((2212 * u + 276) / 1024) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((2212 * u + 276) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 20) / 256) ((164 * u + 20) / 256) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((164 * u + 20) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (164 * u + 20) / 256) / 2 = (2212 * u + 276) / 512 by omega]; exact F23
  have F25 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 20) / 128) ((164 * u + 20) / 128) := by
    rw [show (164 * u + 20) / 128 = 2 * ((164 * u + 20) / 256) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 20) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    rw [show (164 * u + 20) / 64 = 2 * ((164 * u + 20) / 128) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 20) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 20) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mp h F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr3 hr4 F20 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr3 hr4 F20 (by omega) (by omega) (by omega)).mp h F30
  have F32 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr3 hr4 F20 (by omega) (by omega) (by omega)).mpr F31
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hmo (by omega) hr4 (by rw [hh]; exact F32)
  have F33 : IsP m (a + (43172 * u + 5396) / 8192) ((43172 * u + 5396) / 8192) := by
    have hv : v2 ((43172 * u + 5396) / 8192) = 0 := by
      have : ((43172 * u + 5396) / 8192) % 2 = 1 := by omega
      rw [v2_odd ((43172 * u + 5396) / 8192) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F34 : ¬ IsP m (a + (m + 2) + (10404 * u + 1300) / 4096) ((10404 * u + 1300) / 4096) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((10404 * u + 1300) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (10404 * u + 1300) / 4096) / 2 = (43172 * u + 5396) / 8192 by omega]; exact F33
  have F35 : IsP m (a + (m + 2) + (10404 * u + 1300) / 2048) ((10404 * u + 1300) / 2048) := by
    rw [show (10404 * u + 1300) / 2048 = 2 * ((10404 * u + 1300) / 4096) by omega]
    exact (o_half' m (4 * u) (a) ((10404 * u + 1300) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (2212 * u + 276) / 1024) ((2212 * u + 276) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((2212 * u + 276) / 1024) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2212 * u + 276) / 1024) / 2 = (10404 * u + 1300) / 2048 by omega]; exact F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (2212 * u + 276) / 512) ((2212 * u + 276) / 512) := by
    rw [show (2212 * u + 276) / 512 = 2 * ((2212 * u + 276) / 1024) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((2212 * u + 276) / 1024) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F36
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (164 * u + 20) / 256) ((164 * u + 20) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 256) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 20) / 256) / 2 = (2212 * u + 276) / 512 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (164 * u + 20) / 128) ((164 * u + 20) / 128) := by
    rw [show (164 * u + 20) / 128 = 2 * ((164 * u + 20) / 256) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 256) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    rw [show (164 * u + 20) / 64 = 2 * ((164 * u + 20) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 128) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mp h F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 64) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mpr F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr3 hr4 F20 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F41
  have F43 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr3 hr4 F20 (by omega) (by omega) (by omega)).mpr F42
  have F44 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F32 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F43
  have F45 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F32 (by omega) (by omega) (by omega)).mpr F44
  have F46 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F32 (by omega) (by omega) (by omega)).mp h F45
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F46)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F48 : IsP m (a + (2540 * u + 316) / 512) ((2540 * u + 316) / 512) := by
    have hv : v2 ((2540 * u + 316) / 512) = 0 := by
      have : ((2540 * u + 316) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2540 * u + 316) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F49 : ¬ IsP m (a + (m + 2) + (492 * u + 60) / 256) ((492 * u + 60) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((492 * u + 60) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (492 * u + 60) / 256) / 2 = (2540 * u + 316) / 512 by omega]; exact F48
  have F50 : IsP m (a + (m + 2) + (492 * u + 60) / 128) ((492 * u + 60) / 128) := by
    rw [show (492 * u + 60) / 128 = 2 * ((492 * u + 60) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((492 * u + 60) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (492 * u + 60) / 64) ((492 * u + 60) / 64) := by
    rw [show (492 * u + 60) / 64 = 2 * ((492 * u + 60) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((492 * u + 60) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F50
  have F52 : IsP m (a + (m + 2) + (m + 2) + (236 * u + 28) / 32) ((236 * u + 28) / 32) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((236 * u + 28) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (236 * u + 28) / 32) / 2 = (492 * u + 60) / 64 by omega]; exact F51
  have F53 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((108 * u + 12) / 16) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 16) / 2 = (236 * u + 28) / 32 by omega]; exact F52
  have F54 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((44 * u + 4) / 8) hmh hr3 hr4 F20 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F53
  have F55 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F32 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F54
  have F56 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F32 (by omega) (by omega) (by omega)).mpr F55
  have F57 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F56
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F57)
  have hblk' := k68g6723_blk m u hmu hu _ hr6 hb6 hr7
  rw [show a + (7 * m + 12) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F4, F10, F20, F32⟩

theorem k68g6723_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 12)) p) ∧ Blk m 3 (i * (7 * m + 12)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k68g6723_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g6723

/-- 予想 K68 の u ≡ 6723 (mod 8192)（1111100 型）：(n, 0) が P ⇔ n mod (7 * m + 12) が各行の始まり。-/
theorem K68_6723 (m : Nat) (hm : (m + 1) % 65536 = 53784) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 12) = 0 ∨ n % (7 * m + 12) = 1 * m + 2 ∨ n % (7 * m + 12) = 2 * m + 4 ∨ n % (7 * m + 12) = 3 * m + 6 ∨ n % (7 * m + 12) = 4 * m + 8 ∨ n % (7 * m + 12) = 5 * m + 10 ∨ n % (7 * m + 12) = 6 * m + 11) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g6723_rows m _ hmu (by omega) (n / (7 * m + 12))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht2, ht3, ht4⟩ := k68g6723_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (7 * m + 12)) * (7 * m + 12) + n % (7 * m + 12) := by
    have := Nat.div_add_mod n (7 * m + 12)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (7 * m + 12) < 7 * m + 12 := Nat.mod_lt n (by omega)
  generalize hcc : n % (7 * m + 12) = c at hdiv hlt
  generalize ha : n / (7 * m + 12) * (7 * m + 12) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 hq6 ht0 ht1 ht2 ht3 ht4
  subst hdiv
  have hmh : m + 1 = 2 * (4 * ((m + 1) / 8)) := by omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases c0 : c ≤ 0 + m
    · rw [show a + c = a + (c - (0)) by omega] at hP
      exact not_isP_of_row m _ (c - (0)) 0 hrow (by omega) (by omega) (by omega) hP
    · by_cases d0 : c = 0 + (m + 1)
      · rw [d0, show a + (0 + (m + 1)) = a + (m + 1) by omega] at hP
        exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht0 (by omega) hP
      · by_cases c1 : c ≤ 1 * m + 2 + m
        · rw [show a + c = a + (m + 2) + (c - (1 * m + 2)) by omega] at hP
          exact not_isP_of_row m _ (c - (1 * m + 2)) 0 hq1 (by omega) (by omega) (by omega) hP
        · by_cases d1 : c = 1 * m + 2 + (m + 1)
          · rw [d1, show a + (1 * m + 2 + (m + 1)) = a + (m + 2) + (m + 1) by omega] at hP
            exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht1 (by omega) hP
          · by_cases c2 : c ≤ 2 * m + 4 + m
            · rw [show a + c = a + (m + 2) + (m + 2) + (c - (2 * m + 4)) by omega] at hP
              exact not_isP_of_row m _ (c - (2 * m + 4)) 0 hq2 (by omega) (by omega) (by omega) hP
            · by_cases d2 : c = 2 * m + 4 + (m + 1)
              · rw [d2, show a + (2 * m + 4 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) by omega] at hP
                exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht2 (by omega) hP
              · by_cases c3 : c ≤ 3 * m + 6 + m
                · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (c - (3 * m + 6)) by omega] at hP
                  exact not_isP_of_row m _ (c - (3 * m + 6)) 0 hq3 (by omega) (by omega) (by omega) hP
                · by_cases d3 : c = 3 * m + 6 + (m + 1)
                  · rw [d3, show a + (3 * m + 6 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega] at hP
                    exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht3 (by omega) hP
                  · by_cases c4 : c ≤ 4 * m + 8 + m
                    · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (c - (4 * m + 8)) by omega] at hP
                      exact not_isP_of_row m _ (c - (4 * m + 8)) 0 hq4 (by omega) (by omega) (by omega) hP
                    · by_cases d4 : c = 4 * m + 8 + (m + 1)
                      · rw [d4, show a + (4 * m + 8 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega] at hP
                        exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht4 (by omega) hP
                      · by_cases c5 : c ≤ 5 * m + 10 + m
                        · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (c - (5 * m + 10)) by omega] at hP
                          exact not_isP_of_row m _ (c - (5 * m + 10)) 0 hq5 (by omega) (by omega) (by omega) hP
                        · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (6 * m + 11)) by omega] at hP
                          exact not_isP_of_row m _ (c - (6 * m + 11)) 0 hq6 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 10) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq5 0
    · rw [h, show a + (6 * m + 11) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq6 0

section K68g6967

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 8192 = 6967)
include hmu hu

theorem k68g6967_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g6967_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (7 * m + 11)) p) ∧
    Blk m 3 (a + (7 * m + 11)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 4 * u) (4 * u) := by
    have hv : v2 (4 * u) = 2 := by
      have : (4 * u) % 8 = 4 := by omega
      rw [v2_even (4 * u) (by omega) (by omega),
        v2_even (4 * u / 2) (by omega) (by omega),
        v2_odd (4 * u / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    have hv : v2 ((36 * u + 4) / 8) = 3 := by
      have : ((36 * u + 4) / 8) % 16 = 8 := by omega
      rw [v2_even ((36 * u + 4) / 8) (by omega) (by omega),
        v2_even ((36 * u + 4) / 8 / 2) (by omega) (by omega),
        v2_even ((36 * u + 4) / 8 / 2 / 2) (by omega) (by omega),
        v2_odd ((36 * u + 4) / 8 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a) ((4 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F4)
  have F5 : IsP m (a + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    have hv : v2 ((548 * u + 68) / 128) = 2 := by
      have : ((548 * u + 68) / 128) % 8 = 4 := by omega
      rw [v2_even ((548 * u + 68) / 128) (by omega) (by omega),
        v2_even ((548 * u + 68) / 128 / 2) (by omega) (by omega),
        v2_odd ((548 * u + 68) / 128 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F6 : ¬ IsP m (a + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((36 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F5
  have F7 : IsP m (a + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((36 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F6
  have F8 : ¬ IsP m (a + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((36 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F7
  have F9 : IsP m (a + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a) ((36 * u + 4) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F8
  have F10 : ¬ IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F9
  have F11 : IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F10
  have F12 : ¬ IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 2) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F11
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2)) hr2 (by rw [hh]; exact F12)
  have hb3 := blk1_direct m _ hr3 (odd_of_rows m _ hmo hr3 (Or.inr ⟨_, rfl, hr2⟩))
  have F13 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    have hv : v2 ((4 * u + 0) / 2) = 1 := by
      have : ((4 * u + 0) / 2) % 4 = 2 := by omega
      rw [v2_even ((4 * u + 0) / 2) (by omega) (by omega),
        v2_odd ((4 * u + 0) / 2 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F14 : IsP m (a + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    have hv : v2 ((108 * u + 12) / 16) = 2 := by
      have : ((108 * u + 12) / 16) % 8 = 4 := by omega
      rw [v2_even ((108 * u + 12) / 16) (by omega) (by omega),
        v2_even ((108 * u + 12) / 16 / 2) (by omega) (by omega),
        v2_odd ((108 * u + 12) / 16 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F15 : ¬ IsP m (a + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((44 * u + 4) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F14
  have F16 : IsP m (a + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((12 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F15
  have F17 : ¬ IsP m (a + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((12 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F16
  have F18 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) (4 * u) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show 4 * u / 2 = (4 * u + 0) / 2 by omega]; exact F13
    · rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F17
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) hr3 (by rw [hh]; exact F18)
  have F25 : IsP m (a + (5220 * u + 644) / 1024) ((5220 * u + 644) / 1024) := by
    have hv : v2 ((5220 * u + 644) / 1024) = 2 := by
      have : ((5220 * u + 644) / 1024) % 8 = 4 := by omega
      rw [v2_even ((5220 * u + 644) / 1024) (by omega) (by omega),
        v2_even ((5220 * u + 644) / 1024 / 2) (by omega) (by omega),
        v2_odd ((5220 * u + 644) / 1024 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F26 : ¬ IsP m (a + (m + 2) + (1124 * u + 132) / 512) ((1124 * u + 132) / 512) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((1124 * u + 132) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1124 * u + 132) / 512) / 2 = (5220 * u + 644) / 1024 by omega]; exact F25
  have F27 : IsP m (a + (m + 2) + (1124 * u + 132) / 256) ((1124 * u + 132) / 256) := by
    rw [show (1124 * u + 132) / 256 = 2 * ((1124 * u + 132) / 512) by omega]
    exact (o_half' m (4 * u) (a) ((1124 * u + 132) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F26
  have F28 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (100 * u + 4) / 128) / 2 = (1124 * u + 132) / 256 by omega]; exact F27
  have F29 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F28
  have F30 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F29
  have F31 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F34
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hmo (by omega) hr4 (by rw [hh]; exact F35)
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (548 * u + 68) / 256) ((548 * u + 68) / 256) := by
    have hv : v2 ((548 * u + 68) / 256) = 1 := by
      have : ((548 * u + 68) / 256) % 4 = 2 := by omega
      rw [v2_even ((548 * u + 68) / 256) (by omega) (by omega),
        v2_odd ((548 * u + 68) / 256 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F37 : IsP m (a + (38436 * u + 4676) / 8192) ((38436 * u + 4676) / 8192) := by
    have hv : v2 ((38436 * u + 4676) / 8192) = 0 := by
      have : ((38436 * u + 4676) / 8192) % 2 = 1 := by omega
      rw [v2_odd ((38436 * u + 4676) / 8192) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F38 : ¬ IsP m (a + (m + 2) + (5668 * u + 580) / 4096) ((5668 * u + 580) / 4096) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((5668 * u + 580) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (5668 * u + 580) / 4096) / 2 = (38436 * u + 4676) / 8192 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (5668 * u + 580) / 2048) ((5668 * u + 580) / 2048) := by
    rw [show (5668 * u + 580) / 2048 = 2 * ((5668 * u + 580) / 4096) by omega]
    exact (o_half' m (4 * u) (a) ((5668 * u + 580) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (5668 * u + 580) / 1024) ((5668 * u + 580) / 1024) := by
    rw [show (5668 * u + 580) / 1024 = 2 * ((5668 * u + 580) / 2048) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((5668 * u + 580) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (1572 * u + 68) / 512) ((1572 * u + 68) / 512) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((1572 * u + 68) / 512) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (1572 * u + 68) / 512) / 2 = (5668 * u + 580) / 1024 by omega]; exact F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (1572 * u + 68) / 256) ((1572 * u + 68) / 256) := by
    rw [show (1572 * u + 68) / 256 = 2 * ((1572 * u + 68) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((1572 * u + 68) / 512) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F41
  have F43 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((548 * u + 68) / 128) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (548 * u + 68) / 128 / 2 = (548 * u + 68) / 256 by omega]; exact F36
    · rw [show 4 * u + (548 * u + 68) / 128 / 2 = (1572 * u + 68) / 256 by omega]; exact F42
  have F44 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F43
  have F45 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F44
  have F46 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 32) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F45
  have F47 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F46
  have F48 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F35 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F47
  have F49 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F35 (by omega) (by omega) (by omega)).mpr F48
  have F50 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F35 (by omega) (by omega) (by omega)).mp h F49
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F50)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F53 : IsP m (a + (2796 * u + 332) / 512) ((2796 * u + 332) / 512) := by
    have hv : v2 ((2796 * u + 332) / 512) = 0 := by
      have : ((2796 * u + 332) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2796 * u + 332) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F54 : ¬ IsP m (a + (m + 2) + (748 * u + 76) / 256) ((748 * u + 76) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((748 * u + 76) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (748 * u + 76) / 256) / 2 = (2796 * u + 332) / 512 by omega]; exact F53
  have F55 : IsP m (a + (m + 2) + (748 * u + 76) / 128) ((748 * u + 76) / 128) := by
    rw [show (748 * u + 76) / 128 = 2 * ((748 * u + 76) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((748 * u + 76) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F54
  have F56 : ¬ IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 64) ((236 * u + 12) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (236 * u + 12) / 64) / 2 = (748 * u + 76) / 128 by omega]; exact F55
  have F57 : IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 32) ((236 * u + 12) / 32) := by
    rw [show (236 * u + 12) / 32 = 2 * ((236 * u + 12) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F56
  have F58 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((108 * u + 12) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (108 * u + 12) / 16 / 2 = (236 * u + 12) / 32 by omega]; exact F57
  have F59 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((44 * u + 4) / 8) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F58
  have F60 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F35 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F59
  have F61 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F35 (by omega) (by omega) (by omega)).mpr F60
  have F62 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) (4 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F61
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F62)
  have hblk' := k68g6967_blk m u hmu hu _ hr6 hb6 hr7
  rw [show a + (7 * m + 11) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F4, F18, F35⟩

theorem k68g6967_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 11)) p) ∧ Blk m 3 (i * (7 * m + 11)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k68g6967_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g6967

/-- 予想 K68 の u ≡ 6967 (mod 8192)（1101100 型）：(n, 0) が P ⇔ n mod (7 * m + 11) が各行の始まり。-/
theorem K68_6967 (m : Nat) (hm : (m + 1) % 65536 = 55736) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 11) = 0 ∨ n % (7 * m + 11) = 1 * m + 2 ∨ n % (7 * m + 11) = 2 * m + 4 ∨ n % (7 * m + 11) = 3 * m + 5 ∨ n % (7 * m + 11) = 4 * m + 7 ∨ n % (7 * m + 11) = 5 * m + 9 ∨ n % (7 * m + 11) = 6 * m + 10) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g6967_rows m _ hmu (by omega) (n / (7 * m + 11))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3, ht4⟩ := k68g6967_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (7 * m + 11)) * (7 * m + 11) + n % (7 * m + 11) := by
    have := Nat.div_add_mod n (7 * m + 11)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (7 * m + 11) < 7 * m + 11 := Nat.mod_lt n (by omega)
  generalize hcc : n % (7 * m + 11) = c at hdiv hlt
  generalize ha : n / (7 * m + 11) * (7 * m + 11) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 hq6 ht0 ht1 ht3 ht4
  subst hdiv
  have hmh : m + 1 = 2 * (4 * ((m + 1) / 8)) := by omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases c0 : c ≤ 0 + m
    · rw [show a + c = a + (c - (0)) by omega] at hP
      exact not_isP_of_row m _ (c - (0)) 0 hrow (by omega) (by omega) (by omega) hP
    · by_cases d0 : c = 0 + (m + 1)
      · rw [d0, show a + (0 + (m + 1)) = a + (m + 1) by omega] at hP
        exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht0 (by omega) hP
      · by_cases c1 : c ≤ 1 * m + 2 + m
        · rw [show a + c = a + (m + 2) + (c - (1 * m + 2)) by omega] at hP
          exact not_isP_of_row m _ (c - (1 * m + 2)) 0 hq1 (by omega) (by omega) (by omega) hP
        · by_cases d1 : c = 1 * m + 2 + (m + 1)
          · rw [d1, show a + (1 * m + 2 + (m + 1)) = a + (m + 2) + (m + 1) by omega] at hP
            exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht1 (by omega) hP
          · by_cases c2 : c ≤ 2 * m + 4 + m
            · rw [show a + c = a + (m + 2) + (m + 2) + (c - (2 * m + 4)) by omega] at hP
              exact not_isP_of_row m _ (c - (2 * m + 4)) 0 hq2 (by omega) (by omega) (by omega) hP
            · by_cases c3 : c ≤ 3 * m + 5 + m
              · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (c - (3 * m + 5)) by omega] at hP
                exact not_isP_of_row m _ (c - (3 * m + 5)) 0 hq3 (by omega) (by omega) (by omega) hP
              · by_cases d3 : c = 3 * m + 5 + (m + 1)
                · rw [d3, show a + (3 * m + 5 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega] at hP
                  exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht3 (by omega) hP
                · by_cases c4 : c ≤ 4 * m + 7 + m
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (c - (4 * m + 7)) by omega] at hP
                    exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
                  · by_cases d4 : c = 4 * m + 7 + (m + 1)
                    · rw [d4, show a + (4 * m + 7 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) by omega] at hP
                      exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht4 (by omega) hP
                    · by_cases c5 : c ≤ 5 * m + 9 + m
                      · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (c - (5 * m + 9)) by omega] at hP
                        exact not_isP_of_row m _ (c - (5 * m + 9)) 0 hq5 (by omega) (by omega) (by omega) hP
                      · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (c - (6 * m + 10)) by omega] at hP
                        exact not_isP_of_row m _ (c - (6 * m + 10)) 0 hq6 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 5) = a + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) by omega]; exact hq5 0
    · rw [h, show a + (6 * m + 10) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq6 0

section K68g7011

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 8192 = 7011)
include hmu hu

theorem k68g7011_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g7011_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (8 * m + 13)) p) ∧
    Blk m 3 (a + (8 * m + 13)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 4 * u) (4 * u) := by
    have hv : v2 (4 * u) = 2 := by
      have : (4 * u) % 8 = 4 := by omega
      rw [v2_even (4 * u) (by omega) (by omega),
        v2_even (4 * u / 2) (by omega) (by omega),
        v2_odd (4 * u / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    have hv : v2 ((36 * u + 4) / 8) = 1 := by
      have : ((36 * u + 4) / 8) % 4 = 2 := by omega
      rw [v2_even ((36 * u + 4) / 8) (by omega) (by omega),
        v2_odd ((36 * u + 4) / 8 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a) ((4 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F4)
  have F5 : IsP m (a + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    have hv : v2 ((164 * u + 20) / 32) = 2 := by
      have : ((164 * u + 20) / 32) % 8 = 4 := by omega
      rw [v2_even ((164 * u + 20) / 32) (by omega) (by omega),
        v2_even ((164 * u + 20) / 32 / 2) (by omega) (by omega),
        v2_odd ((164 * u + 20) / 32 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F6 : ¬ IsP m (a + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((36 * u + 4) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F5
  have F7 : IsP m (a + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a) ((36 * u + 4) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F6
  have F8 : ¬ IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F7
  have F9 : IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F8
  have F10 : ¬ IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 2) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F9
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2)) hr2 (by rw [hh]; exact F10)
  have hb3 := blk1_direct m _ hr3 (odd_of_rows m _ hmo hr3 (Or.inr ⟨_, rfl, hr2⟩))
  have F11 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    have hv : v2 ((4 * u + 0) / 2) = 1 := by
      have : ((4 * u + 0) / 2) % 4 = 2 := by omega
      rw [v2_even ((4 * u + 0) / 2) (by omega) (by omega),
        v2_odd ((4 * u + 0) / 2 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F12 : IsP m (a + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    have hv : v2 ((108 * u + 12) / 16) = 0 := by
      have : ((108 * u + 12) / 16) % 2 = 1 := by omega
      rw [v2_odd ((108 * u + 12) / 16) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F13 : ¬ IsP m (a + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((44 * u + 4) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((12 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F13
  have F15 : ¬ IsP m (a + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((12 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F14
  have F16 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) (4 * u) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show 4 * u / 2 = (4 * u + 0) / 2 by omega]; exact F11
    · rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F15
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) hr3 (by rw [hh]; exact F16)
  have F17 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    have hv : v2 ((36 * u + 4) / 8) = 1 := by
      have : ((36 * u + 4) / 8) % 4 = 2 := by omega
      rw [v2_even ((36 * u + 4) / 8) (by omega) (by omega),
        v2_odd ((36 * u + 4) / 8 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F18 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F17
  have F19 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mp h F18
  have F20 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mpr F19
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hmo (by omega) hr4 (by rw [hh]; exact F20)
  have F22 : ¬ IsP m (a + (3492 * u + 404) / 512) ((3492 * u + 404) / 512) := by
    have hv : v2 ((3492 * u + 404) / 512) = 1 := by
      have : ((3492 * u + 404) / 512) % 4 = 2 := by omega
      rw [v2_even ((3492 * u + 404) / 512) (by omega) (by omega),
        v2_odd ((3492 * u + 404) / 512 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F23 : IsP m (a + (m + 2) + (1444 * u + 148) / 256) ((1444 * u + 148) / 256) := by
    refine (o_odd_iff m (4 * u) (a) ((1444 * u + 148) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (1444 * u + 148) / 256) / 2 = (3492 * u + 404) / 512 by omega]; exact F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (420 * u + 20) / 128) ((420 * u + 20) / 128) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((420 * u + 20) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (420 * u + 20) / 128) / 2 = (1444 * u + 148) / 256 by omega]; exact F23
  have F25 : IsP m (a + (m + 2) + (m + 2) + (420 * u + 20) / 64) ((420 * u + 20) / 64) := by
    rw [show (420 * u + 20) / 64 = 2 * ((420 * u + 20) / 128) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((420 * u + 20) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F24
  have F26 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 32) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (164 * u + 20) / 32 / 2 = (420 * u + 20) / 64 by omega]; exact F25
  have F27 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F26
  have F28 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mp h F27
  have F29 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F20 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F28
  have F30 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mp h F29
  have F31 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mpr F30
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) hmo (by omega) hr5 (by rw [hh]; exact F31)
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (1188 * u + 148) / 1024) ((1188 * u + 148) / 1024) := by
    have hv : v2 ((1188 * u + 148) / 1024) = 1 := by
      have : ((1188 * u + 148) / 1024) % 4 = 2 := by omega
      rw [v2_even ((1188 * u + 148) / 1024) (by omega) (by omega),
        v2_odd ((1188 * u + 148) / 1024 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F33 : IsP m (a + (54436 * u + 6292) / 8192) ((54436 * u + 6292) / 8192) := by
    have hv : v2 ((54436 * u + 6292) / 8192) = 0 := by
      have : ((54436 * u + 6292) / 8192) % 2 = 1 := by omega
      rw [v2_odd ((54436 * u + 6292) / 8192) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F34 : ¬ IsP m (a + (m + 2) + (21668 * u + 2196) / 4096) ((21668 * u + 2196) / 4096) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((21668 * u + 2196) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (21668 * u + 2196) / 4096) / 2 = (54436 * u + 6292) / 8192 by omega]; exact F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (5284 * u + 148) / 2048) ((5284 * u + 148) / 2048) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((5284 * u + 148) / 2048) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (5284 * u + 148) / 2048) / 2 = (21668 * u + 2196) / 4096 by omega]; exact F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (5284 * u + 148) / 1024) ((5284 * u + 148) / 1024) := by
    rw [show (5284 * u + 148) / 1024 = 2 * ((5284 * u + 148) / 2048) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((5284 * u + 148) / 2048) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (1188 * u + 148) / 512) ((1188 * u + 148) / 512) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((1188 * u + 148) / 512) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (1188 * u + 148) / 512 / 2 = (1188 * u + 148) / 1024 by omega]; exact F32
    · rw [show 4 * u + (1188 * u + 148) / 512 / 2 = (5284 * u + 148) / 1024 by omega]; exact F36
  have F45 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (1188 * u + 148) / 256) ((1188 * u + 148) / 256) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((1188 * u + 148) / 256) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).1
    rw [show (1188 * u + 148) / 256 / 2 = (1188 * u + 148) / 512 by omega]; exact F37
  have F46 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (164 * u + 20) / 128) ((164 * u + 20) / 128) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((164 * u + 20) / 128) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (164 * u + 20) / 128) / 2 = (1188 * u + 148) / 256 by omega]; exact F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    rw [show (164 * u + 20) / 64 = 2 * ((164 * u + 20) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((164 * u + 20) / 128) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mp h F46
  have F48 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((164 * u + 20) / 64) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mpr F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((36 * u + 4) / 16) hmh hr4 hr5 F20 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((36 * u + 4) / 16) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr5 hr6 F31 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F50
  have F52 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr5 hr6 F31 (by omega) (by omega) (by omega)).mpr F51
  have F53 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr5 hr6 F31 (by omega) (by omega) (by omega)).mp h F52
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) hr6 (by rw [hh]; exact F53)
  have hb7 := blk1_direct m _ hr7 (odd_of_rows m _ hmo hr7 (Or.inr ⟨_, rfl, hr6⟩))
  have F55 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (236 * u + 28) / 32) ((236 * u + 28) / 32) := by
    have hv : v2 ((236 * u + 28) / 32) = 0 := by
      have : ((236 * u + 28) / 32) % 2 = 1 := by omega
      rw [v2_odd ((236 * u + 28) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F56 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((108 * u + 12) / 16) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 16) / 2 = (236 * u + 28) / 32 by omega]; exact F55
  have F57 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((44 * u + 4) / 8) hmh hr4 hr5 F20 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F56
  have F58 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr5 hr6 F31 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F57
  have F59 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr5 hr6 F31 (by omega) (by omega) (by omega)).mpr F58
  have F60 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr6 hr7 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F59
  have hr8 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr7 (by rw [hh]; exact F60)
  have hblk' := k68g7011_blk m u hmu hu _ hr7 hb7 hr8
  rw [show a + (8 * m + 13) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hblk', F0, F4, F16, F20, F31⟩

theorem k68g7011_rows : ∀ i, (∀ p, IsP m (i * (8 * m + 13)) p) ∧ Blk m 3 (i * (8 * m + 13)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, _, ha, hb, _⟩ := k68g7011_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g7011

/-- 予想 K68 の u ≡ 7011 (mod 8192)（11011100 型）：(n, 0) が P ⇔ n mod (8 * m + 13) が各行の始まり。-/
theorem K68_7011 (m : Nat) (hm : (m + 1) % 65536 = 56088) (n : Nat) :
    IsP m n 0 ↔ (n % (8 * m + 13) = 0 ∨ n % (8 * m + 13) = 1 * m + 2 ∨ n % (8 * m + 13) = 2 * m + 4 ∨ n % (8 * m + 13) = 3 * m + 5 ∨ n % (8 * m + 13) = 4 * m + 7 ∨ n % (8 * m + 13) = 5 * m + 9 ∨ n % (8 * m + 13) = 6 * m + 11 ∨ n % (8 * m + 13) = 7 * m + 12) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g7011_rows m _ hmu (by omega) (n / (8 * m + 13))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7, _, _, ht0, ht1, ht3, ht4, ht5⟩ := k68g7011_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (8 * m + 13)) * (8 * m + 13) + n % (8 * m + 13) := by
    have := Nat.div_add_mod n (8 * m + 13)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (8 * m + 13) < 8 * m + 13 := Nat.mod_lt n (by omega)
  generalize hcc : n % (8 * m + 13) = c at hdiv hlt
  generalize ha : n / (8 * m + 13) * (8 * m + 13) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 hq6 hq7 ht0 ht1 ht3 ht4 ht5
  subst hdiv
  have hmh : m + 1 = 2 * (4 * ((m + 1) / 8)) := by omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases c0 : c ≤ 0 + m
    · rw [show a + c = a + (c - (0)) by omega] at hP
      exact not_isP_of_row m _ (c - (0)) 0 hrow (by omega) (by omega) (by omega) hP
    · by_cases d0 : c = 0 + (m + 1)
      · rw [d0, show a + (0 + (m + 1)) = a + (m + 1) by omega] at hP
        exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht0 (by omega) hP
      · by_cases c1 : c ≤ 1 * m + 2 + m
        · rw [show a + c = a + (m + 2) + (c - (1 * m + 2)) by omega] at hP
          exact not_isP_of_row m _ (c - (1 * m + 2)) 0 hq1 (by omega) (by omega) (by omega) hP
        · by_cases d1 : c = 1 * m + 2 + (m + 1)
          · rw [d1, show a + (1 * m + 2 + (m + 1)) = a + (m + 2) + (m + 1) by omega] at hP
            exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht1 (by omega) hP
          · by_cases c2 : c ≤ 2 * m + 4 + m
            · rw [show a + c = a + (m + 2) + (m + 2) + (c - (2 * m + 4)) by omega] at hP
              exact not_isP_of_row m _ (c - (2 * m + 4)) 0 hq2 (by omega) (by omega) (by omega) hP
            · by_cases c3 : c ≤ 3 * m + 5 + m
              · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (c - (3 * m + 5)) by omega] at hP
                exact not_isP_of_row m _ (c - (3 * m + 5)) 0 hq3 (by omega) (by omega) (by omega) hP
              · by_cases d3 : c = 3 * m + 5 + (m + 1)
                · rw [d3, show a + (3 * m + 5 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega] at hP
                  exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht3 (by omega) hP
                · by_cases c4 : c ≤ 4 * m + 7 + m
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (c - (4 * m + 7)) by omega] at hP
                    exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
                  · by_cases d4 : c = 4 * m + 7 + (m + 1)
                    · rw [d4, show a + (4 * m + 7 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) by omega] at hP
                      exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht4 (by omega) hP
                    · by_cases c5 : c ≤ 5 * m + 9 + m
                      · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (c - (5 * m + 9)) by omega] at hP
                        exact not_isP_of_row m _ (c - (5 * m + 9)) 0 hq5 (by omega) (by omega) (by omega) hP
                      · by_cases d5 : c = 5 * m + 9 + (m + 1)
                        · rw [d5, show a + (5 * m + 9 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) by omega] at hP
                          exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht5 (by omega) hP
                        · by_cases c6 : c ≤ 6 * m + 11 + m
                          · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (c - (6 * m + 11)) by omega] at hP
                            exact not_isP_of_row m _ (c - (6 * m + 11)) 0 hq6 (by omega) (by omega) (by omega) hP
                          · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (7 * m + 12)) by omega] at hP
                            exact not_isP_of_row m _ (c - (7 * m + 12)) 0 hq7 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 5) = a + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) by omega]; exact hq5 0
    · rw [h, show a + (6 * m + 11) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq6 0
    · rw [h, show a + (7 * m + 12) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq7 0

section K68g7219

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 8192 = 7219)
include hmu hu

theorem k68g7219_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g7219_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (7 * m + 12)) p) ∧
    Blk m 3 (a + (7 * m + 12)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 4 * u) (4 * u) := by
    have hv : v2 (4 * u) = 2 := by
      have : (4 * u) % 8 = 4 := by omega
      rw [v2_even (4 * u) (by omega) (by omega),
        v2_even (4 * u / 2) (by omega) (by omega),
        v2_odd (4 * u / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    have hv : v2 ((36 * u + 4) / 8) = 1 := by
      have : ((36 * u + 4) / 8) % 4 = 2 := by omega
      rw [v2_even ((36 * u + 4) / 8) (by omega) (by omega),
        v2_odd ((36 * u + 4) / 8 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((4 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a) ((4 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F4)
  have F5 : ¬ IsP m (a + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    have hv : v2 ((164 * u + 20) / 32) = 1 := by
      have : ((164 * u + 20) / 32) % 4 = 2 := by omega
      rw [v2_even ((164 * u + 20) / 32) (by omega) (by omega),
        v2_odd ((164 * u + 20) / 32 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F6 : IsP m (a + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    refine (o_odd_iff m (4 * u) (a) ((36 * u + 4) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F5
  have F7 : ¬ IsP m (a + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((36 * u + 4) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F6
  have F8 : IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F7
  have F9 : ¬ IsP m (a + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 4) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((4 * u + 0) / 2) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F9
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F10)
  have F11 : ¬ IsP m (a + (676 * u + 84) / 128) ((676 * u + 84) / 128) := by
    have hv : v2 ((676 * u + 84) / 128) = 1 := by
      have : ((676 * u + 84) / 128) % 4 = 2 := by omega
      rw [v2_even ((676 * u + 84) / 128) (by omega) (by omega),
        v2_odd ((676 * u + 84) / 128 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F12 : IsP m (a + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    refine (o_odd_iff m (4 * u) (a) ((164 * u + 20) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (164 * u + 20) / 64) / 2 = (676 * u + 84) / 128 by omega]; exact F11
  have F13 : ¬ IsP m (a + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((164 * u + 20) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F13
  have F15 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F14
  have F16 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F15
  have F17 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mp h F16
  have F18 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mpr F17
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 2)) hmo (by omega) hr3 (by rw [hh]; exact F18)
  have F19 : ¬ IsP m (a + (2724 * u + 340) / 512) ((2724 * u + 340) / 512) := by
    have hv : v2 ((2724 * u + 340) / 512) = 3 := by
      have : ((2724 * u + 340) / 512) % 16 = 8 := by omega
      rw [v2_even ((2724 * u + 340) / 512) (by omega) (by omega),
        v2_even ((2724 * u + 340) / 512 / 2) (by omega) (by omega),
        v2_even ((2724 * u + 340) / 512 / 2 / 2) (by omega) (by omega),
        v2_odd ((2724 * u + 340) / 512 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F20 : IsP m (a + (m + 2) + (676 * u + 84) / 256) ((676 * u + 84) / 256) := by
    refine (o_odd_iff m (4 * u) (a) ((676 * u + 84) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (676 * u + 84) / 256) / 2 = (2724 * u + 340) / 512 by omega]; exact F19
  have F21 : ¬ IsP m (a + (m + 2) + (676 * u + 84) / 128) ((676 * u + 84) / 128) := by
    rw [show (676 * u + 84) / 128 = 2 * ((676 * u + 84) / 256) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((676 * u + 84) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F20
  have F22 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((164 * u + 20) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (164 * u + 20) / 64) / 2 = (676 * u + 84) / 128 by omega]; exact F21
  have F23 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 20) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F23
  have F25 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F27
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hmo (by omega) hr4 (by rw [hh]; exact F28)
  have F29 : IsP m (a + (35492 * u + 4436) / 8192) ((35492 * u + 4436) / 8192) := by
    have hv : v2 ((35492 * u + 4436) / 8192) = 0 := by
      have : ((35492 * u + 4436) / 8192) % 2 = 1 := by omega
      rw [v2_odd ((35492 * u + 4436) / 8192) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F30 : ¬ IsP m (a + (m + 2) + (2724 * u + 340) / 4096) ((2724 * u + 340) / 4096) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((2724 * u + 340) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2724 * u + 340) / 4096) / 2 = (35492 * u + 4436) / 8192 by omega]; exact F29
  have F31 : IsP m (a + (m + 2) + (2724 * u + 340) / 2048) ((2724 * u + 340) / 2048) := by
    rw [show (2724 * u + 340) / 2048 = 2 * ((2724 * u + 340) / 4096) by omega]
    exact (o_half' m (4 * u) (a) ((2724 * u + 340) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (2724 * u + 340) / 1024) ((2724 * u + 340) / 1024) := by
    rw [show (2724 * u + 340) / 1024 = 2 * ((2724 * u + 340) / 2048) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((2724 * u + 340) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F31
  have F33 : IsP m (a + (m + 2) + (2724 * u + 340) / 512) ((2724 * u + 340) / 512) := by
    rw [show (2724 * u + 340) / 512 = 2 * ((2724 * u + 340) / 1024) by omega]
    exact (o_half' m (4 * u) (a) ((2724 * u + 340) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (676 * u + 84) / 256) ((676 * u + 84) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((676 * u + 84) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (676 * u + 84) / 256) / 2 = (2724 * u + 340) / 512 by omega]; exact F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (676 * u + 84) / 128) ((676 * u + 84) / 128) := by
    rw [show (676 * u + 84) / 128 = 2 * ((676 * u + 84) / 256) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((676 * u + 84) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 64) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 20) / 64) / 2 = (676 * u + 84) / 128 by omega]; exact F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 64) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mpr F36
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F28 (by omega) (by omega) (by omega)).mpr F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F28 (by omega) (by omega) (by omega)).mp h F41
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F42)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F44 : IsP m (a + (1004 * u + 124) / 128) ((1004 * u + 124) / 128) := by
    have hv : v2 ((1004 * u + 124) / 128) = 0 := by
      have : ((1004 * u + 124) / 128) % 2 = 1 := by omega
      rw [v2_odd ((1004 * u + 124) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F45 : ¬ IsP m (a + (m + 2) + (492 * u + 60) / 64) ((492 * u + 60) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((492 * u + 60) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (492 * u + 60) / 64) / 2 = (1004 * u + 124) / 128 by omega]; exact F44
  have F46 : IsP m (a + (m + 2) + (m + 2) + (236 * u + 28) / 32) ((236 * u + 28) / 32) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((236 * u + 28) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (236 * u + 28) / 32) / 2 = (492 * u + 60) / 64 by omega]; exact F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((108 * u + 12) / 16) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 16) / 2 = (236 * u + 28) / 32 by omega]; exact F46
  have F48 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((44 * u + 4) / 8) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F28 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F50
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F51)
  have hblk' := k68g7219_blk m u hmu hu _ hr6 hb6 hr7
  rw [show a + (7 * m + 12) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F4, F10, F18, F28⟩

theorem k68g7219_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 12)) p) ∧ Blk m 3 (i * (7 * m + 12)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k68g7219_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g7219

/-- 予想 K68 の u ≡ 7219 (mod 8192)（1111100 型）：(n, 0) が P ⇔ n mod (7 * m + 12) が各行の始まり。-/
theorem K68_7219 (m : Nat) (hm : (m + 1) % 65536 = 57752) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 12) = 0 ∨ n % (7 * m + 12) = 1 * m + 2 ∨ n % (7 * m + 12) = 2 * m + 4 ∨ n % (7 * m + 12) = 3 * m + 6 ∨ n % (7 * m + 12) = 4 * m + 8 ∨ n % (7 * m + 12) = 5 * m + 10 ∨ n % (7 * m + 12) = 6 * m + 11) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g7219_rows m _ hmu (by omega) (n / (7 * m + 12))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht2, ht3, ht4⟩ := k68g7219_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (7 * m + 12)) * (7 * m + 12) + n % (7 * m + 12) := by
    have := Nat.div_add_mod n (7 * m + 12)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (7 * m + 12) < 7 * m + 12 := Nat.mod_lt n (by omega)
  generalize hcc : n % (7 * m + 12) = c at hdiv hlt
  generalize ha : n / (7 * m + 12) * (7 * m + 12) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 hq6 ht0 ht1 ht2 ht3 ht4
  subst hdiv
  have hmh : m + 1 = 2 * (4 * ((m + 1) / 8)) := by omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases c0 : c ≤ 0 + m
    · rw [show a + c = a + (c - (0)) by omega] at hP
      exact not_isP_of_row m _ (c - (0)) 0 hrow (by omega) (by omega) (by omega) hP
    · by_cases d0 : c = 0 + (m + 1)
      · rw [d0, show a + (0 + (m + 1)) = a + (m + 1) by omega] at hP
        exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht0 (by omega) hP
      · by_cases c1 : c ≤ 1 * m + 2 + m
        · rw [show a + c = a + (m + 2) + (c - (1 * m + 2)) by omega] at hP
          exact not_isP_of_row m _ (c - (1 * m + 2)) 0 hq1 (by omega) (by omega) (by omega) hP
        · by_cases d1 : c = 1 * m + 2 + (m + 1)
          · rw [d1, show a + (1 * m + 2 + (m + 1)) = a + (m + 2) + (m + 1) by omega] at hP
            exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht1 (by omega) hP
          · by_cases c2 : c ≤ 2 * m + 4 + m
            · rw [show a + c = a + (m + 2) + (m + 2) + (c - (2 * m + 4)) by omega] at hP
              exact not_isP_of_row m _ (c - (2 * m + 4)) 0 hq2 (by omega) (by omega) (by omega) hP
            · by_cases d2 : c = 2 * m + 4 + (m + 1)
              · rw [d2, show a + (2 * m + 4 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 1) by omega] at hP
                exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht2 (by omega) hP
              · by_cases c3 : c ≤ 3 * m + 6 + m
                · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (c - (3 * m + 6)) by omega] at hP
                  exact not_isP_of_row m _ (c - (3 * m + 6)) 0 hq3 (by omega) (by omega) (by omega) hP
                · by_cases d3 : c = 3 * m + 6 + (m + 1)
                  · rw [d3, show a + (3 * m + 6 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega] at hP
                    exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht3 (by omega) hP
                  · by_cases c4 : c ≤ 4 * m + 8 + m
                    · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (c - (4 * m + 8)) by omega] at hP
                      exact not_isP_of_row m _ (c - (4 * m + 8)) 0 hq4 (by omega) (by omega) (by omega) hP
                    · by_cases d4 : c = 4 * m + 8 + (m + 1)
                      · rw [d4, show a + (4 * m + 8 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega] at hP
                        exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht4 (by omega) hP
                      · by_cases c5 : c ≤ 5 * m + 10 + m
                        · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (c - (5 * m + 10)) by omega] at hP
                          exact not_isP_of_row m _ (c - (5 * m + 10)) 0 hq5 (by omega) (by omega) (by omega) hP
                        · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (6 * m + 11)) by omega] at hP
                          exact not_isP_of_row m _ (c - (6 * m + 11)) 0 hq6 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 10) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq5 0
    · rw [h, show a + (6 * m + 11) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq6 0

end Rubidium
