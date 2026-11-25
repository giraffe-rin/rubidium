/-
  Rubidium.K68e — v2(m+1) = 3 の 38 の類（u mod 2048）の型の証明（code/k68_gen.js で生成）

  各類 u ≡ r (mod 2048) で、型の語 w（1 = 間隔 m+2、0 = 間隔 m+1）について、(n, 0) が P ⇔ n mod（周期）が各行の始まり。
  始まりの行の不変量は Blk m 3。各行の (行 + 4u) の P/N を、O 型の行の規則（o_half'・o_odd_iff）と
  E 型の行の規則（blk1_direct・e_iff）で始まりの行の距離に落として Blk m 3 で決める。
  生成器は u = r + 2048t（t = 0..7）で証明の形が同じことを確かめてから出力する。
-/
import Rubidium.K67b

namespace Rubidium

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

section K68g55

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 55)
include hmu hu

theorem k68g55_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g55_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
    have hv : v2 ((5220 * u + 644) / 1024) = 0 := by
      have : ((5220 * u + 644) / 1024) % 2 = 1 := by omega
      rw [v2_odd ((5220 * u + 644) / 1024) (by omega)]
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
  have F37 : IsP m (a + (13860 * u + 1604) / 2048) ((13860 * u + 1604) / 2048) := by
    have hv : v2 ((13860 * u + 1604) / 2048) = 0 := by
      have : ((13860 * u + 1604) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((13860 * u + 1604) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F38 : ¬ IsP m (a + (m + 2) + (5668 * u + 580) / 1024) ((5668 * u + 580) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((5668 * u + 580) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (5668 * u + 580) / 1024) / 2 = (13860 * u + 1604) / 2048 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (1572 * u + 68) / 512) ((1572 * u + 68) / 512) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((1572 * u + 68) / 512) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (1572 * u + 68) / 512) / 2 = (5668 * u + 580) / 1024 by omega]; exact F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (1572 * u + 68) / 256) ((1572 * u + 68) / 256) := by
    rw [show (1572 * u + 68) / 256 = 2 * ((1572 * u + 68) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((1572 * u + 68) / 512) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((548 * u + 68) / 128) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (548 * u + 68) / 128 / 2 = (548 * u + 68) / 256 by omega]; exact F36
    · rw [show 4 * u + (548 * u + 68) / 128 / 2 = (1572 * u + 68) / 256 by omega]; exact F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F41
  have F43 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F42
  have F44 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 32) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F43
  have F45 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F44
  have F46 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F35 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F45
  have F47 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F35 (by omega) (by omega) (by omega)).mpr F46
  have F48 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F35 (by omega) (by omega) (by omega)).mp h F47
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F48)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F51 : IsP m (a + (2796 * u + 332) / 512) ((2796 * u + 332) / 512) := by
    have hv : v2 ((2796 * u + 332) / 512) = 0 := by
      have : ((2796 * u + 332) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2796 * u + 332) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F52 : ¬ IsP m (a + (m + 2) + (748 * u + 76) / 256) ((748 * u + 76) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((748 * u + 76) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (748 * u + 76) / 256) / 2 = (2796 * u + 332) / 512 by omega]; exact F51
  have F53 : IsP m (a + (m + 2) + (748 * u + 76) / 128) ((748 * u + 76) / 128) := by
    rw [show (748 * u + 76) / 128 = 2 * ((748 * u + 76) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((748 * u + 76) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F52
  have F54 : ¬ IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 64) ((236 * u + 12) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (236 * u + 12) / 64) / 2 = (748 * u + 76) / 128 by omega]; exact F53
  have F55 : IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 32) ((236 * u + 12) / 32) := by
    rw [show (236 * u + 12) / 32 = 2 * ((236 * u + 12) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F54
  have F56 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((108 * u + 12) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (108 * u + 12) / 16 / 2 = (236 * u + 12) / 32 by omega]; exact F55
  have F57 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((44 * u + 4) / 8) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F56
  have F58 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F35 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F57
  have F59 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F35 (by omega) (by omega) (by omega)).mpr F58
  have F60 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) (4 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F59
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F60)
  have hblk' := k68g55_blk m u hmu hu _ hr6 hb6 hr7
  rw [show a + (7 * m + 11) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F4, F18, F35⟩

theorem k68g55_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 11)) p) ∧ Blk m 3 (i * (7 * m + 11)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k68g55_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g55

/-- 予想 K68 の u ≡ 55 (mod 2048)（1101100 型）：(n, 0) が P ⇔ n mod (7 * m + 11) が各行の始まり。-/
theorem K68_55 (m : Nat) (hm : (m + 1) % 16384 = 440) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 11) = 0 ∨ n % (7 * m + 11) = 1 * m + 2 ∨ n % (7 * m + 11) = 2 * m + 4 ∨ n % (7 * m + 11) = 3 * m + 5 ∨ n % (7 * m + 11) = 4 * m + 7 ∨ n % (7 * m + 11) = 5 * m + 9 ∨ n % (7 * m + 11) = 6 * m + 10) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g55_rows m _ hmu (by omega) (n / (7 * m + 11))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3, ht4⟩ := k68g55_step m _ hmu (by omega) _ hrow hblk
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

section K68g87

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 87)
include hmu hu

theorem k68g87_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g87_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : ¬ IsP m (a + (4772 * u + 580) / 1024) ((4772 * u + 580) / 1024) := by
    have hv : v2 ((4772 * u + 580) / 1024) = 1 := by
      have : ((4772 * u + 580) / 1024) % 4 = 2 := by omega
      rw [v2_even ((4772 * u + 580) / 1024) (by omega) (by omega),
        v2_odd ((4772 * u + 580) / 1024 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F21 : IsP m (a + (m + 2) + (676 * u + 68) / 512) ((676 * u + 68) / 512) := by
    refine (o_odd_iff m (4 * u) (a) ((676 * u + 68) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (676 * u + 68) / 512) / 2 = (4772 * u + 580) / 1024 by omega]; exact F20
  have F22 : ¬ IsP m (a + (m + 2) + (676 * u + 68) / 256) ((676 * u + 68) / 256) := by
    rw [show (676 * u + 68) / 256 = 2 * ((676 * u + 68) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((676 * u + 68) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F21
  have F23 : IsP m (a + (m + 2) + (676 * u + 68) / 128) ((676 * u + 68) / 128) := by
    rw [show (676 * u + 68) / 128 = 2 * ((676 * u + 68) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 64) ((164 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 4) / 64) / 2 = (676 * u + 68) / 128 by omega]; exact F23
  have F25 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 32) ((164 * u + 4) / 32) := by
    rw [show (164 * u + 4) / 32 = 2 * ((164 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F24
  have F26 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 16 / 2 = (164 * u + 4) / 32 by omega]; exact F25
  have F27 : IsP m (a + (12388 * u + 1540) / 2048) ((12388 * u + 1540) / 2048) := by
    have hv : v2 ((12388 * u + 1540) / 2048) = 0 := by
      have : ((12388 * u + 1540) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((12388 * u + 1540) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F28 : ¬ IsP m (a + (m + 2) + (4196 * u + 516) / 1024) ((4196 * u + 516) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((4196 * u + 516) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4196 * u + 516) / 1024) / 2 = (12388 * u + 1540) / 2048 by omega]; exact F27
  have F29 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 512) ((100 * u + 4) / 512) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 512) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (100 * u + 4) / 512) / 2 = (4196 * u + 516) / 1024 by omega]; exact F28
  have F30 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 256) ((100 * u + 4) / 256) := by
    rw [show (100 * u + 4) / 256 = 2 * ((100 * u + 4) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 512) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F29
  have F31 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    rw [show (100 * u + 4) / 128 = 2 * ((100 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (36 * u + 4) / 8 / 2 = (36 * u + 4) / 16 by omega]; exact F26
    · rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F36
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F37
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F38)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F40 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    have hv : v2 ((44 * u + 4) / 8) = 0 := by
      have : ((44 * u + 4) / 8) % 2 = 1 := by omega
      rw [v2_odd ((44 * u + 4) / 8) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F41 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F40
  have F42 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F41
  have F43 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F42
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F43)
  have hblk' := k68g87_blk m u hmu hu _ hr5 hb5 hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F4, F18⟩

theorem k68g87_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 3 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k68g87_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g87

/-- 予想 K68 の u ≡ 87 (mod 2048)（110100 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K68_87 (m : Nat) (hm : (m + 1) % 16384 = 696) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 5 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g87_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht3⟩ := k68g87_step m _ hmu (by omega) _ hrow hblk
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

section K68g119

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 119)
include hmu hu

theorem k68g119_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g119_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (5 * m + 8)) p) ∧
    Blk m 3 (a + (5 * m + 8)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
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
  have F13 : IsP m (a + (2596 * u + 324) / 512) ((2596 * u + 324) / 512) := by
    have hv : v2 ((2596 * u + 324) / 512) = 2 := by
      have : ((2596 * u + 324) / 512) % 8 = 4 := by omega
      rw [v2_even ((2596 * u + 324) / 512) (by omega) (by omega),
        v2_even ((2596 * u + 324) / 512 / 2) (by omega) (by omega),
        v2_odd ((2596 * u + 324) / 512 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F14 : ¬ IsP m (a + (m + 2) + (548 * u + 68) / 256) ((548 * u + 68) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((548 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (548 * u + 68) / 256) / 2 = (2596 * u + 324) / 512 by omega]; exact F13
  have F15 : IsP m (a + (m + 2) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    rw [show (548 * u + 68) / 128 = 2 * ((548 * u + 68) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((548 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F14
  have F16 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((36 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F15
  have F17 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F16
  have F18 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F17
  have F19 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F18
  have F20 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F19
  have F21 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mpr F20
  have F22 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mp h F21
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hr3 (by rw [hh]; exact F22)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F24 : IsP m (a + (620 * u + 76) / 128) ((620 * u + 76) / 128) := by
    have hv : v2 ((620 * u + 76) / 128) = 0 := by
      have : ((620 * u + 76) / 128) % 2 = 1 := by omega
      rw [v2_odd ((620 * u + 76) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 12) / 64) ((108 * u + 12) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 12) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 64) / 2 = (620 * u + 76) / 128 by omega]; exact F24
  have F26 : IsP m (a + (m + 2) + (108 * u + 12) / 32) ((108 * u + 12) / 32) := by
    rw [show (108 * u + 12) / 32 = 2 * ((108 * u + 12) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 12) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F25
  have F27 : ¬ IsP m (a + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    rw [show (108 * u + 12) / 16 = 2 * ((108 * u + 12) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 12) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mpr F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F30
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F31)
  have hblk' := k68g119_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F4, F12⟩

theorem k68g119_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 8)) p) ∧ Blk m 3 (i * (5 * m + 8)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g119_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g119

/-- 予想 K68 の u ≡ 119 (mod 2048)（11100 型）：(n, 0) が P ⇔ n mod (5 * m + 8) が各行の始まり。-/
theorem K68_119 (m : Nat) (hm : (m + 1) % 16384 = 952) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 8) = 0 ∨ n % (5 * m + 8) = 1 * m + 2 ∨ n % (5 * m + 8) = 2 * m + 4 ∨ n % (5 * m + 8) = 3 * m + 6 ∨ n % (5 * m + 8) = 4 * m + 7) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g119_rows m _ hmu (by omega) (n / (5 * m + 8))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht1, ht2⟩ := k68g119_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (5 * m + 8)) * (5 * m + 8) + n % (5 * m + 8) := by
    have := Nat.div_add_mod n (5 * m + 8)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (5 * m + 8) < 5 * m + 8 := Nat.mod_lt n (by omega)
  generalize hcc : n % (5 * m + 8) = c at hdiv hlt
  generalize ha : n / (5 * m + 8) * (5 * m + 8) = a at hdiv hrow hq1 hq2 hq3 hq4 ht0 ht1 ht2
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
                · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (4 * m + 7)) by omega] at hP
                  exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq4 0

section K68g151

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 151)
include hmu hu

theorem k68g151_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g151_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2724 * u + 324) / 512) ((2724 * u + 324) / 512) := by
    have hv : v2 ((2724 * u + 324) / 512) = 2 := by
      have : ((2724 * u + 324) / 512) % 8 = 4 := by omega
      rw [v2_even ((2724 * u + 324) / 512) (by omega) (by omega),
        v2_even ((2724 * u + 324) / 512 / 2) (by omega) (by omega),
        v2_odd ((2724 * u + 324) / 512 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (676 * u + 68) / 256) ((676 * u + 68) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (676 * u + 68) / 256) / 2 = (2724 * u + 324) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (676 * u + 68) / 128) ((676 * u + 68) / 128) := by
    rw [show (676 * u + 68) / 128 = 2 * ((676 * u + 68) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 64) ((164 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 4) / 64) / 2 = (676 * u + 68) / 128 by omega]; exact F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 32) ((164 * u + 4) / 32) := by
    rw [show (164 * u + 4) / 32 = 2 * ((164 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 16 / 2 = (164 * u + 4) / 32 by omega]; exact F24
  have F26 : IsP m (a + (10340 * u + 1284) / 2048) ((10340 * u + 1284) / 2048) := by
    have hv : v2 ((10340 * u + 1284) / 2048) = 0 := by
      have : ((10340 * u + 1284) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((10340 * u + 1284) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F27 : ¬ IsP m (a + (m + 2) + (2148 * u + 260) / 1024) ((2148 * u + 260) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((2148 * u + 260) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2148 * u + 260) / 1024) / 2 = (10340 * u + 1284) / 2048 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (2148 * u + 260) / 512) ((2148 * u + 260) / 512) := by
    rw [show (2148 * u + 260) / 512 = 2 * ((2148 * u + 260) / 1024) by omega]
    exact (o_half' m (4 * u) (a) ((2148 * u + 260) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 256) ((100 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (100 * u + 4) / 256) / 2 = (2148 * u + 260) / 512 by omega]; exact F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    rw [show (100 * u + 4) / 128 = 2 * ((100 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F30
  have F32 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F31
  have F33 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F32
  have F34 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (36 * u + 4) / 8 / 2 = (36 * u + 4) / 16 by omega]; exact F25
    · rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F33
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F34
  have F36 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F35
  have F37 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F36
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F37)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    have hv : v2 ((44 * u + 4) / 8) = 0 := by
      have : ((44 * u + 4) / 8) % 2 = 1 := by omega
      rw [v2_odd ((44 * u + 4) / 8) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F41
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F42)
  have hblk' := k68g151_blk m u hmu hu _ hr5 hb5 hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F4, F18⟩

theorem k68g151_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 3 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k68g151_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g151

/-- 予想 K68 の u ≡ 151 (mod 2048)（110100 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K68_151 (m : Nat) (hm : (m + 1) % 16384 = 1208) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 5 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g151_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht3⟩ := k68g151_step m _ hmu (by omega) _ hrow hblk
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

section K68g173

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 173)
include hmu hu

theorem k68g173_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g173_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2156 * u + 260) / 512) ((2156 * u + 260) / 512) := by
    have hv : v2 ((2156 * u + 260) / 512) = 0 := by
      have : ((2156 * u + 260) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2156 * u + 260) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 4) / 256) / 2 = (2156 * u + 260) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F28
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F29)
  have hblk' := k68g173_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g173_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g173_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g173

/-- 予想 K68 の u ≡ 173 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_173 (m : Nat) (hm : (m + 1) % 16384 = 1384) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g173_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g173_step m _ hmu (by omega) _ hrow hblk
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

section K68g237

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 237)
include hmu hu

theorem k68g237_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g237_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (8300 * u + 1028) / 2048) ((8300 * u + 1028) / 2048) := by
    have hv : v2 ((8300 * u + 1028) / 2048) = 0 := by
      have : ((8300 * u + 1028) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((8300 * u + 1028) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 1024) ((108 * u + 4) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 4) / 1024) / 2 = (8300 * u + 1028) / 2048 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (108 * u + 4) / 512) ((108 * u + 4) / 512) := by
    rw [show (108 * u + 4) / 512 = 2 * ((108 * u + 4) / 1024) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    rw [show (108 * u + 4) / 256 = 2 * ((108 * u + 4) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F25
  have F27 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F26
  have F28 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F28
  have F30 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F30
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F31)
  have hblk' := k68g237_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g237_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g237_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g237

/-- 予想 K68 の u ≡ 237 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_237 (m : Nat) (hm : (m + 1) % 16384 = 1896) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g237_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g237_step m _ hmu (by omega) _ hrow hblk
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

section K68g279

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 279)
include hmu hu

theorem k68g279_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g279_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2724 * u + 324) / 512) ((2724 * u + 324) / 512) := by
    have hv : v2 ((2724 * u + 324) / 512) = 0 := by
      have : ((2724 * u + 324) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2724 * u + 324) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (676 * u + 68) / 256) ((676 * u + 68) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (676 * u + 68) / 256) / 2 = (2724 * u + 324) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (676 * u + 68) / 128) ((676 * u + 68) / 128) := by
    rw [show (676 * u + 68) / 128 = 2 * ((676 * u + 68) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 64) ((164 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 4) / 64) / 2 = (676 * u + 68) / 128 by omega]; exact F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 32) ((164 * u + 4) / 32) := by
    rw [show (164 * u + 4) / 32 = 2 * ((164 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 16 / 2 = (164 * u + 4) / 32 by omega]; exact F24
  have F26 : ¬ IsP m (a + (6244 * u + 772) / 1024) ((6244 * u + 772) / 1024) := by
    have hv : v2 ((6244 * u + 772) / 1024) = 1 := by
      have : ((6244 * u + 772) / 1024) % 4 = 2 := by omega
      rw [v2_even ((6244 * u + 772) / 1024) (by omega) (by omega),
        v2_odd ((6244 * u + 772) / 1024 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F27 : IsP m (a + (m + 2) + (2148 * u + 260) / 512) ((2148 * u + 260) / 512) := by
    refine (o_odd_iff m (4 * u) (a) ((2148 * u + 260) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (2148 * u + 260) / 512) / 2 = (6244 * u + 772) / 1024 by omega]; exact F26
  have F28 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 256) ((100 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (100 * u + 4) / 256) / 2 = (2148 * u + 260) / 512 by omega]; exact F27
  have F29 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    rw [show (100 * u + 4) / 128 = 2 * ((100 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F28
  have F30 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F29
  have F31 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (36 * u + 4) / 8 / 2 = (36 * u + 4) / 16 by omega]; exact F25
    · rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F35
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F36)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F38 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    have hv : v2 ((44 * u + 4) / 8) = 0 := by
      have : ((44 * u + 4) / 8) % 2 = 1 := by omega
      rw [v2_odd ((44 * u + 4) / 8) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F39 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F38
  have F40 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F39
  have F41 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F40
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F41)
  have hblk' := k68g279_blk m u hmu hu _ hr5 hb5 hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F4, F18⟩

theorem k68g279_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 3 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k68g279_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g279

/-- 予想 K68 の u ≡ 279 (mod 2048)（110100 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K68_279 (m : Nat) (hm : (m + 1) % 16384 = 2232) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 5 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g279_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht3⟩ := k68g279_step m _ hmu (by omega) _ hrow hblk
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

section K68g301

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 301)
include hmu hu

theorem k68g301_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g301_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2156 * u + 260) / 512) ((2156 * u + 260) / 512) := by
    have hv : v2 ((2156 * u + 260) / 512) = 2 := by
      have : ((2156 * u + 260) / 512) % 8 = 4 := by omega
      rw [v2_even ((2156 * u + 260) / 512) (by omega) (by omega),
        v2_even ((2156 * u + 260) / 512 / 2) (by omega) (by omega),
        v2_odd ((2156 * u + 260) / 512 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 4) / 256) / 2 = (2156 * u + 260) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F28
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F29)
  have hblk' := k68g301_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g301_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g301_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g301

/-- 予想 K68 の u ≡ 301 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_301 (m : Nat) (hm : (m + 1) % 16384 = 2408) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g301_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g301_step m _ hmu (by omega) _ hrow hblk
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

section K68g307

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 307)
include hmu hu

theorem k68g307_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g307_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
    have hv : v2 ((2724 * u + 340) / 512) = 1 := by
      have : ((2724 * u + 340) / 512) % 4 = 2 := by omega
      rw [v2_even ((2724 * u + 340) / 512) (by omega) (by omega),
        v2_odd ((2724 * u + 340) / 512 / 2) (by omega)]
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
  have F29 : IsP m (a + (10916 * u + 1364) / 2048) ((10916 * u + 1364) / 2048) := by
    have hv : v2 ((10916 * u + 1364) / 2048) = 0 := by
      have : ((10916 * u + 1364) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((10916 * u + 1364) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F30 : ¬ IsP m (a + (m + 2) + (2724 * u + 340) / 1024) ((2724 * u + 340) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((2724 * u + 340) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2724 * u + 340) / 1024) / 2 = (10916 * u + 1364) / 2048 by omega]; exact F29
  have F31 : IsP m (a + (m + 2) + (2724 * u + 340) / 512) ((2724 * u + 340) / 512) := by
    rw [show (2724 * u + 340) / 512 = 2 * ((2724 * u + 340) / 1024) by omega]
    exact (o_half' m (4 * u) (a) ((2724 * u + 340) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (676 * u + 84) / 256) ((676 * u + 84) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((676 * u + 84) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (676 * u + 84) / 256) / 2 = (2724 * u + 340) / 512 by omega]; exact F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (676 * u + 84) / 128) ((676 * u + 84) / 128) := by
    rw [show (676 * u + 84) / 128 = 2 * ((676 * u + 84) / 256) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((676 * u + 84) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 64) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 20) / 64) / 2 = (676 * u + 84) / 128 by omega]; exact F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 64) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mpr F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F36
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F28 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F28 (by omega) (by omega) (by omega)).mp h F39
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F40)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F42 : IsP m (a + (1004 * u + 124) / 128) ((1004 * u + 124) / 128) := by
    have hv : v2 ((1004 * u + 124) / 128) = 0 := by
      have : ((1004 * u + 124) / 128) % 2 = 1 := by omega
      rw [v2_odd ((1004 * u + 124) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F43 : ¬ IsP m (a + (m + 2) + (492 * u + 60) / 64) ((492 * u + 60) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((492 * u + 60) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (492 * u + 60) / 64) / 2 = (1004 * u + 124) / 128 by omega]; exact F42
  have F44 : IsP m (a + (m + 2) + (m + 2) + (236 * u + 28) / 32) ((236 * u + 28) / 32) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((236 * u + 28) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (236 * u + 28) / 32) / 2 = (492 * u + 60) / 64 by omega]; exact F43
  have F45 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((108 * u + 12) / 16) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 16) / 2 = (236 * u + 28) / 32 by omega]; exact F44
  have F46 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((44 * u + 4) / 8) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F46
  have F48 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F28 (by omega) (by omega) (by omega)).mpr F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F48
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F49)
  have hblk' := k68g307_blk m u hmu hu _ hr6 hb6 hr7
  rw [show a + (7 * m + 12) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F4, F10, F18, F28⟩

theorem k68g307_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 12)) p) ∧ Blk m 3 (i * (7 * m + 12)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k68g307_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g307

/-- 予想 K68 の u ≡ 307 (mod 2048)（1111100 型）：(n, 0) が P ⇔ n mod (7 * m + 12) が各行の始まり。-/
theorem K68_307 (m : Nat) (hm : (m + 1) % 16384 = 2456) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 12) = 0 ∨ n % (7 * m + 12) = 1 * m + 2 ∨ n % (7 * m + 12) = 2 * m + 4 ∨ n % (7 * m + 12) = 3 * m + 6 ∨ n % (7 * m + 12) = 4 * m + 8 ∨ n % (7 * m + 12) = 5 * m + 10 ∨ n % (7 * m + 12) = 6 * m + 11) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g307_rows m _ hmu (by omega) (n / (7 * m + 12))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht2, ht3, ht4⟩ := k68g307_step m _ hmu (by omega) _ hrow hblk
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

section K68g311

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 311)
include hmu hu

theorem k68g311_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g311_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : ¬ IsP m (a + (1700 * u + 196) / 256) ((1700 * u + 196) / 256) := by
    have hv : v2 ((1700 * u + 196) / 256) = 1 := by
      have : ((1700 * u + 196) / 256) % 4 = 2 := by omega
      rw [v2_even ((1700 * u + 196) / 256) (by omega) (by omega),
        v2_odd ((1700 * u + 196) / 256 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F21 : IsP m (a + (m + 2) + (676 * u + 68) / 128) ((676 * u + 68) / 128) := by
    refine (o_odd_iff m (4 * u) (a) ((676 * u + 68) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (676 * u + 68) / 128) / 2 = (1700 * u + 196) / 256 by omega]; exact F20
  have F22 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 64) ((164 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 4) / 64) / 2 = (676 * u + 68) / 128 by omega]; exact F21
  have F23 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 32) ((164 * u + 4) / 32) := by
    rw [show (164 * u + 4) / 32 = 2 * ((164 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 16 / 2 = (164 * u + 4) / 32 by omega]; exact F23
  have F25 : ¬ IsP m (a + (5220 * u + 644) / 1024) ((5220 * u + 644) / 1024) := by
    have hv : v2 ((5220 * u + 644) / 1024) = 1 := by
      have : ((5220 * u + 644) / 1024) % 4 = 2 := by omega
      rw [v2_even ((5220 * u + 644) / 1024) (by omega) (by omega),
        v2_odd ((5220 * u + 644) / 1024 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F26 : IsP m (a + (m + 2) + (1124 * u + 132) / 512) ((1124 * u + 132) / 512) := by
    refine (o_odd_iff m (4 * u) (a) ((1124 * u + 132) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (1124 * u + 132) / 512) / 2 = (5220 * u + 644) / 1024 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (1124 * u + 132) / 256) ((1124 * u + 132) / 256) := by
    rw [show (1124 * u + 132) / 256 = 2 * ((1124 * u + 132) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((1124 * u + 132) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (100 * u + 4) / 128) / 2 = (1124 * u + 132) / 256 by omega]; exact F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F30
  have F32 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (36 * u + 4) / 8 / 2 = (36 * u + 4) / 16 by omega]; exact F24
    · rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F31
  have F33 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F32
  have F34 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F33
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F34
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F35)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    have hv : v2 ((44 * u + 4) / 8) = 0 := by
      have : ((44 * u + 4) / 8) % 2 = 1 := by omega
      rw [v2_odd ((44 * u + 4) / 8) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F39
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F40)
  have hblk' := k68g311_blk m u hmu hu _ hr5 hb5 hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F4, F18⟩

theorem k68g311_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 3 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k68g311_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g311

/-- 予想 K68 の u ≡ 311 (mod 2048)（110100 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K68_311 (m : Nat) (hm : (m + 1) % 16384 = 2488) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 5 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g311_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht3⟩ := k68g311_step m _ hmu (by omega) _ hrow hblk
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

section K68g323

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 323)
include hmu hu

theorem k68g323_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g323_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (5 * m + 8)) p) ∧
    Blk m 3 (a + (5 * m + 8)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
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
  have F11 : IsP m (a + (2212 * u + 276) / 512) ((2212 * u + 276) / 512) := by
    have hv : v2 ((2212 * u + 276) / 512) = 2 := by
      have : ((2212 * u + 276) / 512) % 8 = 4 := by omega
      rw [v2_even ((2212 * u + 276) / 512) (by omega) (by omega),
        v2_even ((2212 * u + 276) / 512 / 2) (by omega) (by omega),
        v2_odd ((2212 * u + 276) / 512 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F12 : ¬ IsP m (a + (m + 2) + (164 * u + 20) / 256) ((164 * u + 20) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((164 * u + 20) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 20) / 256) / 2 = (2212 * u + 276) / 512 by omega]; exact F11
  have F13 : IsP m (a + (m + 2) + (164 * u + 20) / 128) ((164 * u + 20) / 128) := by
    rw [show (164 * u + 20) / 128 = 2 * ((164 * u + 20) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((164 * u + 20) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F12
  have F14 : ¬ IsP m (a + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    rw [show (164 * u + 20) / 64 = 2 * ((164 * u + 20) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((164 * u + 20) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F13
  have F15 : IsP m (a + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((164 * u + 20) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F14
  have F16 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F15
  have F17 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F16
  have F18 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F17
  have F19 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mpr F18
  have F20 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mp h F19
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hr3 (by rw [hh]; exact F20)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F22 : IsP m (a + (236 * u + 28) / 32) ((236 * u + 28) / 32) := by
    have hv : v2 ((236 * u + 28) / 32) = 0 := by
      have : ((236 * u + 28) / 32) % 2 = 1 := by omega
      rw [v2_odd ((236 * u + 28) / 32) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 12) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 16) / 2 = (236 * u + 28) / 32 by omega]; exact F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F23
  have F25 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F24
  have F26 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mpr F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F26
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F27)
  have hblk' := k68g323_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F4, F10⟩

theorem k68g323_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 8)) p) ∧ Blk m 3 (i * (5 * m + 8)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g323_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g323

/-- 予想 K68 の u ≡ 323 (mod 2048)（11100 型）：(n, 0) が P ⇔ n mod (5 * m + 8) が各行の始まり。-/
theorem K68_323 (m : Nat) (hm : (m + 1) % 16384 = 2584) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 8) = 0 ∨ n % (5 * m + 8) = 1 * m + 2 ∨ n % (5 * m + 8) = 2 * m + 4 ∨ n % (5 * m + 8) = 3 * m + 6 ∨ n % (5 * m + 8) = 4 * m + 7) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g323_rows m _ hmu (by omega) (n / (5 * m + 8))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht1, ht2⟩ := k68g323_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (5 * m + 8)) * (5 * m + 8) + n % (5 * m + 8) := by
    have := Nat.div_add_mod n (5 * m + 8)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (5 * m + 8) < 5 * m + 8 := Nat.mod_lt n (by omega)
  generalize hcc : n % (5 * m + 8) = c at hdiv hlt
  generalize ha : n / (5 * m + 8) * (5 * m + 8) = a at hdiv hrow hq1 hq2 hq3 hq4 ht0 ht1 ht2
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
                · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (4 * m + 7)) by omega] at hP
                  exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq4 0

section K68g429

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 429)
include hmu hu

theorem k68g429_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g429_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2156 * u + 260) / 512) ((2156 * u + 260) / 512) := by
    have hv : v2 ((2156 * u + 260) / 512) = 0 := by
      have : ((2156 * u + 260) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2156 * u + 260) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 4) / 256) / 2 = (2156 * u + 260) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F28
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F29)
  have hblk' := k68g429_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g429_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g429_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g429

/-- 予想 K68 の u ≡ 429 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_429 (m : Nat) (hm : (m + 1) % 16384 = 3432) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g429_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g429_step m _ hmu (by omega) _ hrow hblk
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

section K68g535

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 535)
include hmu hu

theorem k68g535_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g535_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F26 : IsP m (a + (6244 * u + 772) / 1024) ((6244 * u + 772) / 1024) := by
    have hv : v2 ((6244 * u + 772) / 1024) = 0 := by
      have : ((6244 * u + 772) / 1024) % 2 = 1 := by omega
      rw [v2_odd ((6244 * u + 772) / 1024) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F27 : ¬ IsP m (a + (m + 2) + (2148 * u + 260) / 512) ((2148 * u + 260) / 512) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((2148 * u + 260) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2148 * u + 260) / 512) / 2 = (6244 * u + 772) / 1024 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 256) ((100 * u + 4) / 256) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (100 * u + 4) / 256) / 2 = (2148 * u + 260) / 512 by omega]; exact F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    rw [show (100 * u + 4) / 128 = 2 * ((100 * u + 4) / 256) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F30
  have F32 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F31
  have F33 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F32
  have F34 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F33
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F34
  have F36 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F35
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hmo (by omega) hr4 (by rw [hh]; exact F36)
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    have hv : v2 ((548 * u + 68) / 128) = 0 := by
      have : ((548 * u + 68) / 128) % 2 = 1 := by omega
      rw [v2_odd ((548 * u + 68) / 128) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 32) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F36 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F41
  have F43 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mpr F42
  have F44 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mp h F43
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F44)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F47 : ¬ IsP m (a + (1772 * u + 204) / 256) ((1772 * u + 204) / 256) := by
    have hv : v2 ((1772 * u + 204) / 256) = 3 := by
      have : ((1772 * u + 204) / 256) % 16 = 8 := by omega
      rw [v2_even ((1772 * u + 204) / 256) (by omega) (by omega),
        v2_even ((1772 * u + 204) / 256 / 2) (by omega) (by omega),
        v2_even ((1772 * u + 204) / 256 / 2 / 2) (by omega) (by omega),
        v2_odd ((1772 * u + 204) / 256 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F48 : IsP m (a + (m + 2) + (748 * u + 76) / 128) ((748 * u + 76) / 128) := by
    refine (o_odd_iff m (4 * u) (a) ((748 * u + 76) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (748 * u + 76) / 128) / 2 = (1772 * u + 204) / 256 by omega]; exact F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 64) ((236 * u + 12) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (236 * u + 12) / 64) / 2 = (748 * u + 76) / 128 by omega]; exact F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 32) ((236 * u + 12) / 32) := by
    rw [show (236 * u + 12) / 32 = 2 * ((236 * u + 12) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((108 * u + 12) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (108 * u + 12) / 16 / 2 = (236 * u + 12) / 32 by omega]; exact F50
  have F52 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((44 * u + 4) / 8) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F51
  have F53 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F36 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F52
  have F54 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mpr F53
  have F55 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) (4 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F54
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F55)
  have hblk' := k68g535_blk m u hmu hu _ hr6 hb6 hr7
  rw [show a + (7 * m + 11) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F4, F18, F36⟩

theorem k68g535_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 11)) p) ∧ Blk m 3 (i * (7 * m + 11)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k68g535_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g535

/-- 予想 K68 の u ≡ 535 (mod 2048)（1101100 型）：(n, 0) が P ⇔ n mod (7 * m + 11) が各行の始まり。-/
theorem K68_535 (m : Nat) (hm : (m + 1) % 16384 = 4280) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 11) = 0 ∨ n % (7 * m + 11) = 1 * m + 2 ∨ n % (7 * m + 11) = 2 * m + 4 ∨ n % (7 * m + 11) = 3 * m + 5 ∨ n % (7 * m + 11) = 4 * m + 7 ∨ n % (7 * m + 11) = 5 * m + 9 ∨ n % (7 * m + 11) = 6 * m + 10) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g535_rows m _ hmu (by omega) (n / (7 * m + 11))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3, ht4⟩ := k68g535_step m _ hmu (by omega) _ hrow hblk
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

section K68g621

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 621)
include hmu hu

theorem k68g621_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g621_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
    have hv : v2 ((4204 * u + 516) / 1024) = 1 := by
      have : ((4204 * u + 516) / 1024) % 4 = 2 := by omega
      rw [v2_even ((4204 * u + 516) / 1024) (by omega) (by omega),
        v2_odd ((4204 * u + 516) / 1024 / 2) (by omega)]
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
  have hblk' := k68g621_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g621_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g621_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g621

/-- 予想 K68 の u ≡ 621 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_621 (m : Nat) (hm : (m + 1) % 16384 = 4968) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g621_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g621_step m _ hmu (by omega) _ hrow hblk
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

section K68g663

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 663)
include hmu hu

theorem k68g663_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g663_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F19 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    have hv : v2 ((36 * u + 4) / 32) = 1 := by
      have : ((36 * u + 4) / 32) % 4 = 2 := by omega
      rw [v2_even ((36 * u + 4) / 32) (by omega) (by omega),
        v2_odd ((36 * u + 4) / 32 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F20 : ¬ IsP m (a + (2724 * u + 324) / 512) ((2724 * u + 324) / 512) := by
    have hv : v2 ((2724 * u + 324) / 512) = 3 := by
      have : ((2724 * u + 324) / 512) % 16 = 8 := by omega
      rw [v2_even ((2724 * u + 324) / 512) (by omega) (by omega),
        v2_even ((2724 * u + 324) / 512 / 2) (by omega) (by omega),
        v2_even ((2724 * u + 324) / 512 / 2 / 2) (by omega) (by omega),
        v2_odd ((2724 * u + 324) / 512 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F21 : IsP m (a + (m + 2) + (676 * u + 68) / 256) ((676 * u + 68) / 256) := by
    refine (o_odd_iff m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (676 * u + 68) / 256) / 2 = (2724 * u + 324) / 512 by omega]; exact F20
  have F22 : ¬ IsP m (a + (m + 2) + (676 * u + 68) / 128) ((676 * u + 68) / 128) := by
    rw [show (676 * u + 68) / 128 = 2 * ((676 * u + 68) / 256) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F21
  have F23 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 64) ((164 * u + 4) / 64) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (164 * u + 4) / 64) / 2 = (676 * u + 68) / 128 by omega]; exact F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 32) ((164 * u + 4) / 32) := by
    rw [show (164 * u + 4) / 32 = 2 * ((164 * u + 4) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F23
  have F25 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (36 * u + 4) / 16 / 2 = (36 * u + 4) / 32 by omega]; exact F19
    · rw [show 4 * u + (36 * u + 4) / 16 / 2 = (164 * u + 4) / 32 by omega]; exact F24
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).1
    rw [show (36 * u + 4) / 8 / 2 = (36 * u + 4) / 16 by omega]; exact F25
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F36
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hmo (by omega) hr4 (by rw [hh]; exact F37)
  have F38 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    have hv : v2 ((548 * u + 68) / 128) = 0 := by
      have : ((548 * u + 68) / 128) % 2 = 1 := by omega
      rw [v2_odd ((548 * u + 68) / 128) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F39 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F38
  have F40 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F39
  have F41 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 32) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F40
  have F42 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F41
  have F43 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F37 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F42
  have F44 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F37 (by omega) (by omega) (by omega)).mpr F43
  have F45 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F37 (by omega) (by omega) (by omega)).mp h F44
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F45)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F48 : ¬ IsP m (a + (1772 * u + 204) / 256) ((1772 * u + 204) / 256) := by
    have hv : v2 ((1772 * u + 204) / 256) = 1 := by
      have : ((1772 * u + 204) / 256) % 4 = 2 := by omega
      rw [v2_even ((1772 * u + 204) / 256) (by omega) (by omega),
        v2_odd ((1772 * u + 204) / 256 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F49 : IsP m (a + (m + 2) + (748 * u + 76) / 128) ((748 * u + 76) / 128) := by
    refine (o_odd_iff m (4 * u) (a) ((748 * u + 76) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (748 * u + 76) / 128) / 2 = (1772 * u + 204) / 256 by omega]; exact F48
  have F50 : ¬ IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 64) ((236 * u + 12) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (236 * u + 12) / 64) / 2 = (748 * u + 76) / 128 by omega]; exact F49
  have F51 : IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 32) ((236 * u + 12) / 32) := by
    rw [show (236 * u + 12) / 32 = 2 * ((236 * u + 12) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F50
  have F52 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((108 * u + 12) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (108 * u + 12) / 16 / 2 = (236 * u + 12) / 32 by omega]; exact F51
  have F53 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((44 * u + 4) / 8) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F52
  have F54 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F37 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F53
  have F55 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F37 (by omega) (by omega) (by omega)).mpr F54
  have F56 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) (4 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F55
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F56)
  have hblk' := k68g663_blk m u hmu hu _ hr6 hb6 hr7
  rw [show a + (7 * m + 11) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F4, F18, F37⟩

theorem k68g663_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 11)) p) ∧ Blk m 3 (i * (7 * m + 11)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k68g663_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g663

/-- 予想 K68 の u ≡ 663 (mod 2048)（1101100 型）：(n, 0) が P ⇔ n mod (7 * m + 11) が各行の始まり。-/
theorem K68_663 (m : Nat) (hm : (m + 1) % 16384 = 5304) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 11) = 0 ∨ n % (7 * m + 11) = 1 * m + 2 ∨ n % (7 * m + 11) = 2 * m + 4 ∨ n % (7 * m + 11) = 3 * m + 5 ∨ n % (7 * m + 11) = 4 * m + 7 ∨ n % (7 * m + 11) = 5 * m + 9 ∨ n % (7 * m + 11) = 6 * m + 10) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g663_rows m _ hmu (by omega) (n / (7 * m + 11))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3, ht4⟩ := k68g663_step m _ hmu (by omega) _ hrow hblk
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

section K68g685

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 685)
include hmu hu

theorem k68g685_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g685_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2156 * u + 260) / 512) ((2156 * u + 260) / 512) := by
    have hv : v2 ((2156 * u + 260) / 512) = 0 := by
      have : ((2156 * u + 260) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2156 * u + 260) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 4) / 256) / 2 = (2156 * u + 260) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F28
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F29)
  have hblk' := k68g685_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g685_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g685_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g685

/-- 予想 K68 の u ≡ 685 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_685 (m : Nat) (hm : (m + 1) % 16384 = 5480) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g685_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g685_step m _ hmu (by omega) _ hrow hblk
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

section K68g941

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 941)
include hmu hu

theorem k68g941_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g941_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2156 * u + 260) / 512) ((2156 * u + 260) / 512) := by
    have hv : v2 ((2156 * u + 260) / 512) = 0 := by
      have : ((2156 * u + 260) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2156 * u + 260) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 4) / 256) / 2 = (2156 * u + 260) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F28
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F29)
  have hblk' := k68g941_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g941_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g941_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g941

/-- 予想 K68 の u ≡ 941 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_941 (m : Nat) (hm : (m + 1) % 16384 = 7528) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g941_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g941_step m _ hmu (by omega) _ hrow hblk
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

section K68g951

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 951)
include hmu hu

theorem k68g951_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g951_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (5 * m + 8)) p) ∧
    Blk m 3 (a + (5 * m + 8)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
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
    have hv : v2 ((548 * u + 68) / 128) = 3 := by
      have : ((548 * u + 68) / 128) % 16 = 8 := by omega
      rw [v2_even ((548 * u + 68) / 128) (by omega) (by omega),
        v2_even ((548 * u + 68) / 128 / 2) (by omega) (by omega),
        v2_even ((548 * u + 68) / 128 / 2 / 2) (by omega) (by omega),
        v2_odd ((548 * u + 68) / 128 / 2 / 2 / 2) (by omega)]
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
  have F13 : IsP m (a + (8740 * u + 1092) / 2048) ((8740 * u + 1092) / 2048) := by
    have hv : v2 ((8740 * u + 1092) / 2048) = 0 := by
      have : ((8740 * u + 1092) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((8740 * u + 1092) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F14 : ¬ IsP m (a + (m + 2) + (548 * u + 68) / 1024) ((548 * u + 68) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((548 * u + 68) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (548 * u + 68) / 1024) / 2 = (8740 * u + 1092) / 2048 by omega]; exact F13
  have F15 : IsP m (a + (m + 2) + (548 * u + 68) / 512) ((548 * u + 68) / 512) := by
    rw [show (548 * u + 68) / 512 = 2 * ((548 * u + 68) / 1024) by omega]
    exact (o_half' m (4 * u) (a) ((548 * u + 68) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F14
  have F16 : ¬ IsP m (a + (m + 2) + (548 * u + 68) / 256) ((548 * u + 68) / 256) := by
    rw [show (548 * u + 68) / 256 = 2 * ((548 * u + 68) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((548 * u + 68) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F15
  have F17 : IsP m (a + (m + 2) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    rw [show (548 * u + 68) / 128 = 2 * ((548 * u + 68) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((548 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F16
  have F18 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((36 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F17
  have F19 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F18
  have F20 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F19
  have F21 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F20
  have F22 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F21
  have F23 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mp h F23
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hr3 (by rw [hh]; exact F24)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F26 : IsP m (a + (620 * u + 76) / 128) ((620 * u + 76) / 128) := by
    have hv : v2 ((620 * u + 76) / 128) = 0 := by
      have : ((620 * u + 76) / 128) % 2 = 1 := by omega
      rw [v2_odd ((620 * u + 76) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F27 : ¬ IsP m (a + (m + 2) + (108 * u + 12) / 64) ((108 * u + 12) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 12) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 64) / 2 = (620 * u + 76) / 128 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (108 * u + 12) / 32) ((108 * u + 12) / 32) := by
    rw [show (108 * u + 12) / 32 = 2 * ((108 * u + 12) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 12) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    rw [show (108 * u + 12) / 16 = 2 * ((108 * u + 12) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 12) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F30
  have F32 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mpr F31
  have F33 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F32
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F33)
  have hblk' := k68g951_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F4, F12⟩

theorem k68g951_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 8)) p) ∧ Blk m 3 (i * (5 * m + 8)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g951_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g951

/-- 予想 K68 の u ≡ 951 (mod 2048)（11100 型）：(n, 0) が P ⇔ n mod (5 * m + 8) が各行の始まり。-/
theorem K68_951 (m : Nat) (hm : (m + 1) % 16384 = 7608) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 8) = 0 ∨ n % (5 * m + 8) = 1 * m + 2 ∨ n % (5 * m + 8) = 2 * m + 4 ∨ n % (5 * m + 8) = 3 * m + 6 ∨ n % (5 * m + 8) = 4 * m + 7) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g951_rows m _ hmu (by omega) (n / (5 * m + 8))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht1, ht2⟩ := k68g951_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (5 * m + 8)) * (5 * m + 8) + n % (5 * m + 8) := by
    have := Nat.div_add_mod n (5 * m + 8)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (5 * m + 8) < 5 * m + 8 := Nat.mod_lt n (by omega)
  generalize hcc : n % (5 * m + 8) = c at hdiv hlt
  generalize ha : n / (5 * m + 8) * (5 * m + 8) = a at hdiv hrow hq1 hq2 hq3 hq4 ht0 ht1 ht2
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
                · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (4 * m + 7)) by omega] at hP
                  exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq4 0

section K68g1079

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1079)
include hmu hu

theorem k68g1079_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1079_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
    have hv : v2 ((5220 * u + 644) / 1024) = 0 := by
      have : ((5220 * u + 644) / 1024) % 2 = 1 := by omega
      rw [v2_odd ((5220 * u + 644) / 1024) (by omega)]
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
  have F37 : IsP m (a + (13860 * u + 1604) / 2048) ((13860 * u + 1604) / 2048) := by
    have hv : v2 ((13860 * u + 1604) / 2048) = 0 := by
      have : ((13860 * u + 1604) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((13860 * u + 1604) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F38 : ¬ IsP m (a + (m + 2) + (5668 * u + 580) / 1024) ((5668 * u + 580) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((5668 * u + 580) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (5668 * u + 580) / 1024) / 2 = (13860 * u + 1604) / 2048 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (1572 * u + 68) / 512) ((1572 * u + 68) / 512) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((1572 * u + 68) / 512) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (1572 * u + 68) / 512) / 2 = (5668 * u + 580) / 1024 by omega]; exact F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (1572 * u + 68) / 256) ((1572 * u + 68) / 256) := by
    rw [show (1572 * u + 68) / 256 = 2 * ((1572 * u + 68) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((1572 * u + 68) / 512) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((548 * u + 68) / 128) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (548 * u + 68) / 128 / 2 = (548 * u + 68) / 256 by omega]; exact F36
    · rw [show 4 * u + (548 * u + 68) / 128 / 2 = (1572 * u + 68) / 256 by omega]; exact F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F41
  have F43 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F42
  have F44 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 32) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F43
  have F45 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F44
  have F46 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F35 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F45
  have F47 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F35 (by omega) (by omega) (by omega)).mpr F46
  have F48 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F35 (by omega) (by omega) (by omega)).mp h F47
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F48)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F51 : IsP m (a + (2796 * u + 332) / 512) ((2796 * u + 332) / 512) := by
    have hv : v2 ((2796 * u + 332) / 512) = 0 := by
      have : ((2796 * u + 332) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2796 * u + 332) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F52 : ¬ IsP m (a + (m + 2) + (748 * u + 76) / 256) ((748 * u + 76) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((748 * u + 76) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (748 * u + 76) / 256) / 2 = (2796 * u + 332) / 512 by omega]; exact F51
  have F53 : IsP m (a + (m + 2) + (748 * u + 76) / 128) ((748 * u + 76) / 128) := by
    rw [show (748 * u + 76) / 128 = 2 * ((748 * u + 76) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((748 * u + 76) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F52
  have F54 : ¬ IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 64) ((236 * u + 12) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (236 * u + 12) / 64) / 2 = (748 * u + 76) / 128 by omega]; exact F53
  have F55 : IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 32) ((236 * u + 12) / 32) := by
    rw [show (236 * u + 12) / 32 = 2 * ((236 * u + 12) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F54
  have F56 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((108 * u + 12) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (108 * u + 12) / 16 / 2 = (236 * u + 12) / 32 by omega]; exact F55
  have F57 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((44 * u + 4) / 8) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F56
  have F58 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F35 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F57
  have F59 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F35 (by omega) (by omega) (by omega)).mpr F58
  have F60 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) (4 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F59
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F60)
  have hblk' := k68g1079_blk m u hmu hu _ hr6 hb6 hr7
  rw [show a + (7 * m + 11) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F4, F18, F35⟩

theorem k68g1079_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 11)) p) ∧ Blk m 3 (i * (7 * m + 11)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k68g1079_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1079

/-- 予想 K68 の u ≡ 1079 (mod 2048)（1101100 型）：(n, 0) が P ⇔ n mod (7 * m + 11) が各行の始まり。-/
theorem K68_1079 (m : Nat) (hm : (m + 1) % 16384 = 8632) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 11) = 0 ∨ n % (7 * m + 11) = 1 * m + 2 ∨ n % (7 * m + 11) = 2 * m + 4 ∨ n % (7 * m + 11) = 3 * m + 5 ∨ n % (7 * m + 11) = 4 * m + 7 ∨ n % (7 * m + 11) = 5 * m + 9 ∨ n % (7 * m + 11) = 6 * m + 10) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1079_rows m _ hmu (by omega) (n / (7 * m + 11))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3, ht4⟩ := k68g1079_step m _ hmu (by omega) _ hrow hblk
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

section K68g1111

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1111)
include hmu hu

theorem k68g1111_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1111_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : ¬ IsP m (a + (4772 * u + 580) / 1024) ((4772 * u + 580) / 1024) := by
    have hv : v2 ((4772 * u + 580) / 1024) = 1 := by
      have : ((4772 * u + 580) / 1024) % 4 = 2 := by omega
      rw [v2_even ((4772 * u + 580) / 1024) (by omega) (by omega),
        v2_odd ((4772 * u + 580) / 1024 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F21 : IsP m (a + (m + 2) + (676 * u + 68) / 512) ((676 * u + 68) / 512) := by
    refine (o_odd_iff m (4 * u) (a) ((676 * u + 68) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (676 * u + 68) / 512) / 2 = (4772 * u + 580) / 1024 by omega]; exact F20
  have F22 : ¬ IsP m (a + (m + 2) + (676 * u + 68) / 256) ((676 * u + 68) / 256) := by
    rw [show (676 * u + 68) / 256 = 2 * ((676 * u + 68) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((676 * u + 68) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F21
  have F23 : IsP m (a + (m + 2) + (676 * u + 68) / 128) ((676 * u + 68) / 128) := by
    rw [show (676 * u + 68) / 128 = 2 * ((676 * u + 68) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 64) ((164 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 4) / 64) / 2 = (676 * u + 68) / 128 by omega]; exact F23
  have F25 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 32) ((164 * u + 4) / 32) := by
    rw [show (164 * u + 4) / 32 = 2 * ((164 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F24
  have F26 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 16 / 2 = (164 * u + 4) / 32 by omega]; exact F25
  have F27 : IsP m (a + (12388 * u + 1540) / 2048) ((12388 * u + 1540) / 2048) := by
    have hv : v2 ((12388 * u + 1540) / 2048) = 0 := by
      have : ((12388 * u + 1540) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((12388 * u + 1540) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F28 : ¬ IsP m (a + (m + 2) + (4196 * u + 516) / 1024) ((4196 * u + 516) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((4196 * u + 516) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4196 * u + 516) / 1024) / 2 = (12388 * u + 1540) / 2048 by omega]; exact F27
  have F29 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 512) ((100 * u + 4) / 512) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 512) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (100 * u + 4) / 512) / 2 = (4196 * u + 516) / 1024 by omega]; exact F28
  have F30 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 256) ((100 * u + 4) / 256) := by
    rw [show (100 * u + 4) / 256 = 2 * ((100 * u + 4) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 512) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F29
  have F31 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    rw [show (100 * u + 4) / 128 = 2 * ((100 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (36 * u + 4) / 8 / 2 = (36 * u + 4) / 16 by omega]; exact F26
    · rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F36
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F37
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F38)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F40 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    have hv : v2 ((44 * u + 4) / 8) = 0 := by
      have : ((44 * u + 4) / 8) % 2 = 1 := by omega
      rw [v2_odd ((44 * u + 4) / 8) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F41 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F40
  have F42 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F41
  have F43 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F42
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F43)
  have hblk' := k68g1111_blk m u hmu hu _ hr5 hb5 hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F4, F18⟩

theorem k68g1111_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 3 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k68g1111_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1111

/-- 予想 K68 の u ≡ 1111 (mod 2048)（110100 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K68_1111 (m : Nat) (hm : (m + 1) % 16384 = 8888) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 5 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1111_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht3⟩ := k68g1111_step m _ hmu (by omega) _ hrow hblk
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

section K68g1143

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1143)
include hmu hu

theorem k68g1143_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1143_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (5 * m + 8)) p) ∧
    Blk m 3 (a + (5 * m + 8)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
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
  have F13 : IsP m (a + (2596 * u + 324) / 512) ((2596 * u + 324) / 512) := by
    have hv : v2 ((2596 * u + 324) / 512) = 2 := by
      have : ((2596 * u + 324) / 512) % 8 = 4 := by omega
      rw [v2_even ((2596 * u + 324) / 512) (by omega) (by omega),
        v2_even ((2596 * u + 324) / 512 / 2) (by omega) (by omega),
        v2_odd ((2596 * u + 324) / 512 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F14 : ¬ IsP m (a + (m + 2) + (548 * u + 68) / 256) ((548 * u + 68) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((548 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (548 * u + 68) / 256) / 2 = (2596 * u + 324) / 512 by omega]; exact F13
  have F15 : IsP m (a + (m + 2) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    rw [show (548 * u + 68) / 128 = 2 * ((548 * u + 68) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((548 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F14
  have F16 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((36 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F15
  have F17 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F16
  have F18 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F17
  have F19 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F18
  have F20 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F19
  have F21 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mpr F20
  have F22 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mp h F21
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hr3 (by rw [hh]; exact F22)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F24 : IsP m (a + (620 * u + 76) / 128) ((620 * u + 76) / 128) := by
    have hv : v2 ((620 * u + 76) / 128) = 0 := by
      have : ((620 * u + 76) / 128) % 2 = 1 := by omega
      rw [v2_odd ((620 * u + 76) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 12) / 64) ((108 * u + 12) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 12) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 64) / 2 = (620 * u + 76) / 128 by omega]; exact F24
  have F26 : IsP m (a + (m + 2) + (108 * u + 12) / 32) ((108 * u + 12) / 32) := by
    rw [show (108 * u + 12) / 32 = 2 * ((108 * u + 12) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 12) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F25
  have F27 : ¬ IsP m (a + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    rw [show (108 * u + 12) / 16 = 2 * ((108 * u + 12) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 12) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mpr F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F30
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F31)
  have hblk' := k68g1143_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F4, F12⟩

theorem k68g1143_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 8)) p) ∧ Blk m 3 (i * (5 * m + 8)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g1143_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1143

/-- 予想 K68 の u ≡ 1143 (mod 2048)（11100 型）：(n, 0) が P ⇔ n mod (5 * m + 8) が各行の始まり。-/
theorem K68_1143 (m : Nat) (hm : (m + 1) % 16384 = 9144) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 8) = 0 ∨ n % (5 * m + 8) = 1 * m + 2 ∨ n % (5 * m + 8) = 2 * m + 4 ∨ n % (5 * m + 8) = 3 * m + 6 ∨ n % (5 * m + 8) = 4 * m + 7) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1143_rows m _ hmu (by omega) (n / (5 * m + 8))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht1, ht2⟩ := k68g1143_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (5 * m + 8)) * (5 * m + 8) + n % (5 * m + 8) := by
    have := Nat.div_add_mod n (5 * m + 8)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (5 * m + 8) < 5 * m + 8 := Nat.mod_lt n (by omega)
  generalize hcc : n % (5 * m + 8) = c at hdiv hlt
  generalize ha : n / (5 * m + 8) * (5 * m + 8) = a at hdiv hrow hq1 hq2 hq3 hq4 ht0 ht1 ht2
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
                · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (4 * m + 7)) by omega] at hP
                  exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq4 0

section K68g1175

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1175)
include hmu hu

theorem k68g1175_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1175_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2724 * u + 324) / 512) ((2724 * u + 324) / 512) := by
    have hv : v2 ((2724 * u + 324) / 512) = 2 := by
      have : ((2724 * u + 324) / 512) % 8 = 4 := by omega
      rw [v2_even ((2724 * u + 324) / 512) (by omega) (by omega),
        v2_even ((2724 * u + 324) / 512 / 2) (by omega) (by omega),
        v2_odd ((2724 * u + 324) / 512 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (676 * u + 68) / 256) ((676 * u + 68) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (676 * u + 68) / 256) / 2 = (2724 * u + 324) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (676 * u + 68) / 128) ((676 * u + 68) / 128) := by
    rw [show (676 * u + 68) / 128 = 2 * ((676 * u + 68) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 64) ((164 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 4) / 64) / 2 = (676 * u + 68) / 128 by omega]; exact F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 32) ((164 * u + 4) / 32) := by
    rw [show (164 * u + 4) / 32 = 2 * ((164 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 16 / 2 = (164 * u + 4) / 32 by omega]; exact F24
  have F26 : IsP m (a + (10340 * u + 1284) / 2048) ((10340 * u + 1284) / 2048) := by
    have hv : v2 ((10340 * u + 1284) / 2048) = 0 := by
      have : ((10340 * u + 1284) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((10340 * u + 1284) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F27 : ¬ IsP m (a + (m + 2) + (2148 * u + 260) / 1024) ((2148 * u + 260) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((2148 * u + 260) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2148 * u + 260) / 1024) / 2 = (10340 * u + 1284) / 2048 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (2148 * u + 260) / 512) ((2148 * u + 260) / 512) := by
    rw [show (2148 * u + 260) / 512 = 2 * ((2148 * u + 260) / 1024) by omega]
    exact (o_half' m (4 * u) (a) ((2148 * u + 260) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 256) ((100 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (100 * u + 4) / 256) / 2 = (2148 * u + 260) / 512 by omega]; exact F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    rw [show (100 * u + 4) / 128 = 2 * ((100 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F30
  have F32 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F31
  have F33 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F32
  have F34 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (36 * u + 4) / 8 / 2 = (36 * u + 4) / 16 by omega]; exact F25
    · rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F33
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F34
  have F36 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F35
  have F37 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F36
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F37)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    have hv : v2 ((44 * u + 4) / 8) = 0 := by
      have : ((44 * u + 4) / 8) % 2 = 1 := by omega
      rw [v2_odd ((44 * u + 4) / 8) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F41
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F42)
  have hblk' := k68g1175_blk m u hmu hu _ hr5 hb5 hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F4, F18⟩

theorem k68g1175_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 3 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k68g1175_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1175

/-- 予想 K68 の u ≡ 1175 (mod 2048)（110100 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K68_1175 (m : Nat) (hm : (m + 1) % 16384 = 9400) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 5 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1175_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht3⟩ := k68g1175_step m _ hmu (by omega) _ hrow hblk
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

section K68g1187

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1187)
include hmu hu

theorem k68g1187_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1187_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
    have hv : v2 ((17828 * u + 2196) / 4096) = 0 := by
      have : ((17828 * u + 2196) / 4096) % 2 = 1 := by omega
      rw [v2_odd ((17828 * u + 2196) / 4096) (by omega)]
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
  have hblk' := k68g1187_blk m u hmu hu _ hr8 hb8 hr9
  rw [show a + (9 * m + 15) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hblk', F0, F4, F16, F20, F34, F43⟩

theorem k68g1187_rows : ∀ i, (∀ p, IsP m (i * (9 * m + 15)) p) ∧ Blk m 3 (i * (9 * m + 15)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, _, _, ha, hb, _⟩ := k68g1187_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1187

/-- 予想 K68 の u ≡ 1187 (mod 2048)（110111100 型）：(n, 0) が P ⇔ n mod (9 * m + 15) が各行の始まり。-/
theorem K68_1187 (m : Nat) (hm : (m + 1) % 16384 = 9496) (n : Nat) :
    IsP m n 0 ↔ (n % (9 * m + 15) = 0 ∨ n % (9 * m + 15) = 1 * m + 2 ∨ n % (9 * m + 15) = 2 * m + 4 ∨ n % (9 * m + 15) = 3 * m + 5 ∨ n % (9 * m + 15) = 4 * m + 7 ∨ n % (9 * m + 15) = 5 * m + 9 ∨ n % (9 * m + 15) = 6 * m + 11 ∨ n % (9 * m + 15) = 7 * m + 13 ∨ n % (9 * m + 15) = 8 * m + 14) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1187_rows m _ hmu (by omega) (n / (9 * m + 15))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, _, _, ht0, ht1, ht3, ht4, ht5, ht6⟩ := k68g1187_step m _ hmu (by omega) _ hrow hblk
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

section K68g1197

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1197)
include hmu hu

theorem k68g1197_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1197_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2156 * u + 260) / 512) ((2156 * u + 260) / 512) := by
    have hv : v2 ((2156 * u + 260) / 512) = 0 := by
      have : ((2156 * u + 260) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2156 * u + 260) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 4) / 256) / 2 = (2156 * u + 260) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F28
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F29)
  have hblk' := k68g1197_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g1197_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g1197_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1197

/-- 予想 K68 の u ≡ 1197 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_1197 (m : Nat) (hm : (m + 1) % 16384 = 9576) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1197_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g1197_step m _ hmu (by omega) _ hrow hblk
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

section K68g1261

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1261)
include hmu hu

theorem k68g1261_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1261_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (8300 * u + 1028) / 2048) ((8300 * u + 1028) / 2048) := by
    have hv : v2 ((8300 * u + 1028) / 2048) = 0 := by
      have : ((8300 * u + 1028) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((8300 * u + 1028) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 1024) ((108 * u + 4) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 4) / 1024) / 2 = (8300 * u + 1028) / 2048 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (108 * u + 4) / 512) ((108 * u + 4) / 512) := by
    rw [show (108 * u + 4) / 512 = 2 * ((108 * u + 4) / 1024) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    rw [show (108 * u + 4) / 256 = 2 * ((108 * u + 4) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F25
  have F27 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F26
  have F28 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F28
  have F30 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F30
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F31)
  have hblk' := k68g1261_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g1261_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g1261_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1261

/-- 予想 K68 の u ≡ 1261 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_1261 (m : Nat) (hm : (m + 1) % 16384 = 10088) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1261_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g1261_step m _ hmu (by omega) _ hrow hblk
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

section K68g1303

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1303)
include hmu hu

theorem k68g1303_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1303_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2724 * u + 324) / 512) ((2724 * u + 324) / 512) := by
    have hv : v2 ((2724 * u + 324) / 512) = 0 := by
      have : ((2724 * u + 324) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2724 * u + 324) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (676 * u + 68) / 256) ((676 * u + 68) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (676 * u + 68) / 256) / 2 = (2724 * u + 324) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (676 * u + 68) / 128) ((676 * u + 68) / 128) := by
    rw [show (676 * u + 68) / 128 = 2 * ((676 * u + 68) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((676 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 64) ((164 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 4) / 64) / 2 = (676 * u + 68) / 128 by omega]; exact F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 32) ((164 * u + 4) / 32) := by
    rw [show (164 * u + 4) / 32 = 2 * ((164 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 16 / 2 = (164 * u + 4) / 32 by omega]; exact F24
  have F26 : ¬ IsP m (a + (6244 * u + 772) / 1024) ((6244 * u + 772) / 1024) := by
    have hv : v2 ((6244 * u + 772) / 1024) = 1 := by
      have : ((6244 * u + 772) / 1024) % 4 = 2 := by omega
      rw [v2_even ((6244 * u + 772) / 1024) (by omega) (by omega),
        v2_odd ((6244 * u + 772) / 1024 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F27 : IsP m (a + (m + 2) + (2148 * u + 260) / 512) ((2148 * u + 260) / 512) := by
    refine (o_odd_iff m (4 * u) (a) ((2148 * u + 260) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (2148 * u + 260) / 512) / 2 = (6244 * u + 772) / 1024 by omega]; exact F26
  have F28 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 256) ((100 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (100 * u + 4) / 256) / 2 = (2148 * u + 260) / 512 by omega]; exact F27
  have F29 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    rw [show (100 * u + 4) / 128 = 2 * ((100 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F28
  have F30 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F29
  have F31 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (36 * u + 4) / 8 / 2 = (36 * u + 4) / 16 by omega]; exact F25
    · rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F35
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F36)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F38 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    have hv : v2 ((44 * u + 4) / 8) = 0 := by
      have : ((44 * u + 4) / 8) % 2 = 1 := by omega
      rw [v2_odd ((44 * u + 4) / 8) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F39 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F38
  have F40 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F39
  have F41 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F40
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F41)
  have hblk' := k68g1303_blk m u hmu hu _ hr5 hb5 hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F4, F18⟩

theorem k68g1303_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 3 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k68g1303_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1303

/-- 予想 K68 の u ≡ 1303 (mod 2048)（110100 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K68_1303 (m : Nat) (hm : (m + 1) % 16384 = 10424) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 5 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1303_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht3⟩ := k68g1303_step m _ hmu (by omega) _ hrow hblk
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

section K68g1325

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1325)
include hmu hu

theorem k68g1325_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1325_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2156 * u + 260) / 512) ((2156 * u + 260) / 512) := by
    have hv : v2 ((2156 * u + 260) / 512) = 2 := by
      have : ((2156 * u + 260) / 512) % 8 = 4 := by omega
      rw [v2_even ((2156 * u + 260) / 512) (by omega) (by omega),
        v2_even ((2156 * u + 260) / 512 / 2) (by omega) (by omega),
        v2_odd ((2156 * u + 260) / 512 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 4) / 256) / 2 = (2156 * u + 260) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F28
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F29)
  have hblk' := k68g1325_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g1325_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g1325_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1325

/-- 予想 K68 の u ≡ 1325 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_1325 (m : Nat) (hm : (m + 1) % 16384 = 10600) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1325_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g1325_step m _ hmu (by omega) _ hrow hblk
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

section K68g1331

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1331)
include hmu hu

theorem k68g1331_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1331_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
    have hv : v2 ((2724 * u + 340) / 512) = 1 := by
      have : ((2724 * u + 340) / 512) % 4 = 2 := by omega
      rw [v2_even ((2724 * u + 340) / 512) (by omega) (by omega),
        v2_odd ((2724 * u + 340) / 512 / 2) (by omega)]
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
  have F29 : IsP m (a + (10916 * u + 1364) / 2048) ((10916 * u + 1364) / 2048) := by
    have hv : v2 ((10916 * u + 1364) / 2048) = 0 := by
      have : ((10916 * u + 1364) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((10916 * u + 1364) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F30 : ¬ IsP m (a + (m + 2) + (2724 * u + 340) / 1024) ((2724 * u + 340) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((2724 * u + 340) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2724 * u + 340) / 1024) / 2 = (10916 * u + 1364) / 2048 by omega]; exact F29
  have F31 : IsP m (a + (m + 2) + (2724 * u + 340) / 512) ((2724 * u + 340) / 512) := by
    rw [show (2724 * u + 340) / 512 = 2 * ((2724 * u + 340) / 1024) by omega]
    exact (o_half' m (4 * u) (a) ((2724 * u + 340) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (676 * u + 84) / 256) ((676 * u + 84) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((676 * u + 84) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (676 * u + 84) / 256) / 2 = (2724 * u + 340) / 512 by omega]; exact F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (676 * u + 84) / 128) ((676 * u + 84) / 128) := by
    rw [show (676 * u + 84) / 128 = 2 * ((676 * u + 84) / 256) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((676 * u + 84) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 64) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 20) / 64) / 2 = (676 * u + 84) / 128 by omega]; exact F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 64) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mpr F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F36
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F28 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F28 (by omega) (by omega) (by omega)).mp h F39
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F40)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F42 : IsP m (a + (1004 * u + 124) / 128) ((1004 * u + 124) / 128) := by
    have hv : v2 ((1004 * u + 124) / 128) = 0 := by
      have : ((1004 * u + 124) / 128) % 2 = 1 := by omega
      rw [v2_odd ((1004 * u + 124) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F43 : ¬ IsP m (a + (m + 2) + (492 * u + 60) / 64) ((492 * u + 60) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((492 * u + 60) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (492 * u + 60) / 64) / 2 = (1004 * u + 124) / 128 by omega]; exact F42
  have F44 : IsP m (a + (m + 2) + (m + 2) + (236 * u + 28) / 32) ((236 * u + 28) / 32) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((236 * u + 28) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (236 * u + 28) / 32) / 2 = (492 * u + 60) / 64 by omega]; exact F43
  have F45 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((108 * u + 12) / 16) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 16) / 2 = (236 * u + 28) / 32 by omega]; exact F44
  have F46 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((44 * u + 4) / 8) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F46
  have F48 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F28 (by omega) (by omega) (by omega)).mpr F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F48
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F49)
  have hblk' := k68g1331_blk m u hmu hu _ hr6 hb6 hr7
  rw [show a + (7 * m + 12) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F4, F10, F18, F28⟩

theorem k68g1331_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 12)) p) ∧ Blk m 3 (i * (7 * m + 12)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k68g1331_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1331

/-- 予想 K68 の u ≡ 1331 (mod 2048)（1111100 型）：(n, 0) が P ⇔ n mod (7 * m + 12) が各行の始まり。-/
theorem K68_1331 (m : Nat) (hm : (m + 1) % 16384 = 10648) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 12) = 0 ∨ n % (7 * m + 12) = 1 * m + 2 ∨ n % (7 * m + 12) = 2 * m + 4 ∨ n % (7 * m + 12) = 3 * m + 6 ∨ n % (7 * m + 12) = 4 * m + 8 ∨ n % (7 * m + 12) = 5 * m + 10 ∨ n % (7 * m + 12) = 6 * m + 11) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1331_rows m _ hmu (by omega) (n / (7 * m + 12))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht2, ht3, ht4⟩ := k68g1331_step m _ hmu (by omega) _ hrow hblk
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

section K68g1335

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1335)
include hmu hu

theorem k68g1335_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1335_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : ¬ IsP m (a + (1700 * u + 196) / 256) ((1700 * u + 196) / 256) := by
    have hv : v2 ((1700 * u + 196) / 256) = 1 := by
      have : ((1700 * u + 196) / 256) % 4 = 2 := by omega
      rw [v2_even ((1700 * u + 196) / 256) (by omega) (by omega),
        v2_odd ((1700 * u + 196) / 256 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F21 : IsP m (a + (m + 2) + (676 * u + 68) / 128) ((676 * u + 68) / 128) := by
    refine (o_odd_iff m (4 * u) (a) ((676 * u + 68) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (676 * u + 68) / 128) / 2 = (1700 * u + 196) / 256 by omega]; exact F20
  have F22 : ¬ IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 64) ((164 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 4) / 64) / 2 = (676 * u + 68) / 128 by omega]; exact F21
  have F23 : IsP m (a + (m + 2) + (m + 2) + (164 * u + 4) / 32) ((164 * u + 4) / 32) := by
    rw [show (164 * u + 4) / 32 = 2 * ((164 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((164 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 16 / 2 = (164 * u + 4) / 32 by omega]; exact F23
  have F25 : ¬ IsP m (a + (5220 * u + 644) / 1024) ((5220 * u + 644) / 1024) := by
    have hv : v2 ((5220 * u + 644) / 1024) = 1 := by
      have : ((5220 * u + 644) / 1024) % 4 = 2 := by omega
      rw [v2_even ((5220 * u + 644) / 1024) (by omega) (by omega),
        v2_odd ((5220 * u + 644) / 1024 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F26 : IsP m (a + (m + 2) + (1124 * u + 132) / 512) ((1124 * u + 132) / 512) := by
    refine (o_odd_iff m (4 * u) (a) ((1124 * u + 132) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (1124 * u + 132) / 512) / 2 = (5220 * u + 644) / 1024 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (1124 * u + 132) / 256) ((1124 * u + 132) / 256) := by
    rw [show (1124 * u + 132) / 256 = 2 * ((1124 * u + 132) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((1124 * u + 132) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (100 * u + 4) / 128) / 2 = (1124 * u + 132) / 256 by omega]; exact F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F30
  have F32 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (36 * u + 4) / 8 / 2 = (36 * u + 4) / 16 by omega]; exact F24
    · rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F31
  have F33 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F32
  have F34 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F33
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F34
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F35)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    have hv : v2 ((44 * u + 4) / 8) = 0 := by
      have : ((44 * u + 4) / 8) % 2 = 1 := by omega
      rw [v2_odd ((44 * u + 4) / 8) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F39
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F40)
  have hblk' := k68g1335_blk m u hmu hu _ hr5 hb5 hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F4, F18⟩

theorem k68g1335_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 3 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k68g1335_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1335

/-- 予想 K68 の u ≡ 1335 (mod 2048)（110100 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K68_1335 (m : Nat) (hm : (m + 1) % 16384 = 10680) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 5 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1335_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht3⟩ := k68g1335_step m _ hmu (by omega) _ hrow hblk
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

section K68g1347

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1347)
include hmu hu

theorem k68g1347_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1347_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (5 * m + 8)) p) ∧
    Blk m 3 (a + (5 * m + 8)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
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
  have F11 : IsP m (a + (2212 * u + 276) / 512) ((2212 * u + 276) / 512) := by
    have hv : v2 ((2212 * u + 276) / 512) = 2 := by
      have : ((2212 * u + 276) / 512) % 8 = 4 := by omega
      rw [v2_even ((2212 * u + 276) / 512) (by omega) (by omega),
        v2_even ((2212 * u + 276) / 512 / 2) (by omega) (by omega),
        v2_odd ((2212 * u + 276) / 512 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F12 : ¬ IsP m (a + (m + 2) + (164 * u + 20) / 256) ((164 * u + 20) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((164 * u + 20) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 20) / 256) / 2 = (2212 * u + 276) / 512 by omega]; exact F11
  have F13 : IsP m (a + (m + 2) + (164 * u + 20) / 128) ((164 * u + 20) / 128) := by
    rw [show (164 * u + 20) / 128 = 2 * ((164 * u + 20) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((164 * u + 20) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F12
  have F14 : ¬ IsP m (a + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    rw [show (164 * u + 20) / 64 = 2 * ((164 * u + 20) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((164 * u + 20) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F13
  have F15 : IsP m (a + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((164 * u + 20) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F14
  have F16 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F15
  have F17 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F16
  have F18 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F17
  have F19 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mpr F18
  have F20 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mp h F19
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hr3 (by rw [hh]; exact F20)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F22 : IsP m (a + (236 * u + 28) / 32) ((236 * u + 28) / 32) := by
    have hv : v2 ((236 * u + 28) / 32) = 0 := by
      have : ((236 * u + 28) / 32) % 2 = 1 := by omega
      rw [v2_odd ((236 * u + 28) / 32) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 12) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 16) / 2 = (236 * u + 28) / 32 by omega]; exact F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F23
  have F25 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr2 hr3 F10 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F24
  have F26 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr2 hr3 F10 (by omega) (by omega) (by omega)).mpr F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F26
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F27)
  have hblk' := k68g1347_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F4, F10⟩

theorem k68g1347_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 8)) p) ∧ Blk m 3 (i * (5 * m + 8)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g1347_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1347

/-- 予想 K68 の u ≡ 1347 (mod 2048)（11100 型）：(n, 0) が P ⇔ n mod (5 * m + 8) が各行の始まり。-/
theorem K68_1347 (m : Nat) (hm : (m + 1) % 16384 = 10776) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 8) = 0 ∨ n % (5 * m + 8) = 1 * m + 2 ∨ n % (5 * m + 8) = 2 * m + 4 ∨ n % (5 * m + 8) = 3 * m + 6 ∨ n % (5 * m + 8) = 4 * m + 7) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1347_rows m _ hmu (by omega) (n / (5 * m + 8))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht1, ht2⟩ := k68g1347_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (5 * m + 8)) * (5 * m + 8) + n % (5 * m + 8) := by
    have := Nat.div_add_mod n (5 * m + 8)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (5 * m + 8) < 5 * m + 8 := Nat.mod_lt n (by omega)
  generalize hcc : n % (5 * m + 8) = c at hdiv hlt
  generalize ha : n / (5 * m + 8) * (5 * m + 8) = a at hdiv hrow hq1 hq2 hq3 hq4 ht0 ht1 ht2
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
                · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (4 * m + 7)) by omega] at hP
                  exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq4 0

section K68g1443

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1443)
include hmu hu

theorem k68g1443_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1443_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F22 : ¬ IsP m (a + (9636 * u + 1172) / 2048) ((9636 * u + 1172) / 2048) := by
    have hv : v2 ((9636 * u + 1172) / 2048) = 1 := by
      have : ((9636 * u + 1172) / 2048) % 4 = 2 := by omega
      rw [v2_even ((9636 * u + 1172) / 2048) (by omega) (by omega),
        v2_odd ((9636 * u + 1172) / 2048 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F23 : IsP m (a + (m + 2) + (1444 * u + 148) / 1024) ((1444 * u + 148) / 1024) := by
    refine (o_odd_iff m (4 * u) (a) ((1444 * u + 148) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (1444 * u + 148) / 1024) / 2 = (9636 * u + 1172) / 2048 by omega]; exact F22
  have F24 : ¬ IsP m (a + (m + 2) + (1444 * u + 148) / 512) ((1444 * u + 148) / 512) := by
    rw [show (1444 * u + 148) / 512 = 2 * ((1444 * u + 148) / 1024) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((1444 * u + 148) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F23
  have F25 : IsP m (a + (m + 2) + (1444 * u + 148) / 256) ((1444 * u + 148) / 256) := by
    rw [show (1444 * u + 148) / 256 = 2 * ((1444 * u + 148) / 512) by omega]
    exact (o_half' m (4 * u) (a) ((1444 * u + 148) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F24
  have F26 : ¬ IsP m (a + (m + 2) + (m + 2) + (420 * u + 20) / 128) ((420 * u + 20) / 128) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((420 * u + 20) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (420 * u + 20) / 128) / 2 = (1444 * u + 148) / 256 by omega]; exact F25
  have F27 : IsP m (a + (m + 2) + (m + 2) + (420 * u + 20) / 64) ((420 * u + 20) / 64) := by
    rw [show (420 * u + 20) / 64 = 2 * ((420 * u + 20) / 128) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((420 * u + 20) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F26
  have F28 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((164 * u + 20) / 32) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (164 * u + 20) / 32 / 2 = (420 * u + 20) / 64 by omega]; exact F27
  have F29 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F28
  have F30 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mp h F29
  have F31 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F20 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mp h F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mpr F32
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) hmo (by omega) hr5 (by rw [hh]; exact F33)
  have F34 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (1188 * u + 148) / 256) ((1188 * u + 148) / 256) := by
    have hv : v2 ((1188 * u + 148) / 256) = 0 := by
      have : ((1188 * u + 148) / 256) % 2 = 1 := by omega
      rw [v2_odd ((1188 * u + 148) / 256) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (164 * u + 20) / 128) ((164 * u + 20) / 128) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((164 * u + 20) / 128) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (164 * u + 20) / 128) / 2 = (1188 * u + 148) / 256 by omega]; exact F34
  have F36 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    rw [show (164 * u + 20) / 64 = 2 * ((164 * u + 20) / 128) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((164 * u + 20) / 128) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mpr F35
  have F37 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((164 * u + 20) / 64) hmh hr3 hr4 F16 (by omega) (by omega) (by omega)).mp h F36
  have F38 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((36 * u + 4) / 16) hmh hr4 hr5 F20 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F37
  have F39 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((36 * u + 4) / 16) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mp h F38
  have F40 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr5 hr6 F33 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F39
  have F41 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr5 hr6 F33 (by omega) (by omega) (by omega)).mp h F40
  have F42 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr5 hr6 F33 (by omega) (by omega) (by omega)).mpr F41
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) hmo (by omega) hr6 (by rw [hh]; exact F42)
  have F43 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (3236 * u + 404) / 512) ((3236 * u + 404) / 512) := by
    have hv : v2 ((3236 * u + 404) / 512) = 0 := by
      have : ((3236 * u + 404) / 512) % 2 = 1 := by omega
      rw [v2_odd ((3236 * u + 404) / 512) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F44 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (1188 * u + 148) / 256) ((1188 * u + 148) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((1188 * u + 148) / 256) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1188 * u + 148) / 256) / 2 = (3236 * u + 404) / 512 by omega]; exact F43
  have F45 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (164 * u + 20) / 128) ((164 * u + 20) / 128) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((164 * u + 20) / 128) hmh hr4 hr5 F20 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (164 * u + 20) / 128) / 2 = (1188 * u + 148) / 256 by omega]; exact F44
  have F46 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (164 * u + 20) / 64) ((164 * u + 20) / 64) := by
    rw [show (164 * u + 20) / 64 = 2 * ((164 * u + 20) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((164 * u + 20) / 128) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mp h F45
  have F47 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (164 * u + 20) / 32) ((164 * u + 20) / 32) := by
    rw [show (164 * u + 20) / 32 = 2 * ((164 * u + 20) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((164 * u + 20) / 64) hmh hr4 hr5 F20 (by omega) (by omega) (by omega)).mpr F46
  have F48 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr5 hr6 F33 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 16) / 2 = (164 * u + 20) / 32 by omega]; exact F47
  have F49 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((36 * u + 4) / 16) hmh hr5 hr6 F33 (by omega) (by omega) (by omega)).mpr F48
  have F50 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr6 hr7 F42 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F49
  have F51 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr6 hr7 F42 (by omega) (by omega) (by omega)).mpr F50
  have F52 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr6 hr7 F42 (by omega) (by omega) (by omega)).mp h F51
  have hr8 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hr7 (by rw [hh]; exact F52)
  have hb8 := blk1_direct m _ hr8 (odd_of_rows m _ hmo hr8 (Or.inr ⟨_, rfl, hr7⟩))
  have F54 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (492 * u + 60) / 64) ((492 * u + 60) / 64) := by
    have hv : v2 ((492 * u + 60) / 64) = 1 := by
      have : ((492 * u + 60) / 64) % 4 = 2 := by omega
      rw [v2_even ((492 * u + 60) / 64) (by omega) (by omega),
        v2_odd ((492 * u + 60) / 64 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F55 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (236 * u + 28) / 32) ((236 * u + 28) / 32) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((236 * u + 28) / 32) hmh hr3 hr4 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (236 * u + 28) / 32) / 2 = (492 * u + 60) / 64 by omega]; exact F54
  have F56 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((108 * u + 12) / 16) hmh hr4 hr5 F20 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 16) / 2 = (236 * u + 28) / 32 by omega]; exact F55
  have F57 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) ((44 * u + 4) / 8) hmh hr5 hr6 F33 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F56
  have F58 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr6 hr7 F42 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F57
  have F59 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr6 hr7 F42 (by omega) (by omega) (by omega)).mpr F58
  have F60 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr7 hr8 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F59
  have hr9 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr8 (by rw [hh]; exact F60)
  have hblk' := k68g1443_blk m u hmu hu _ hr8 hb8 hr9
  rw [show a + (9 * m + 15) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hblk', F0, F4, F16, F20, F33, F42⟩

theorem k68g1443_rows : ∀ i, (∀ p, IsP m (i * (9 * m + 15)) p) ∧ Blk m 3 (i * (9 * m + 15)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, _, _, ha, hb, _⟩ := k68g1443_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1443

/-- 予想 K68 の u ≡ 1443 (mod 2048)（110111100 型）：(n, 0) が P ⇔ n mod (9 * m + 15) が各行の始まり。-/
theorem K68_1443 (m : Nat) (hm : (m + 1) % 16384 = 11544) (n : Nat) :
    IsP m n 0 ↔ (n % (9 * m + 15) = 0 ∨ n % (9 * m + 15) = 1 * m + 2 ∨ n % (9 * m + 15) = 2 * m + 4 ∨ n % (9 * m + 15) = 3 * m + 5 ∨ n % (9 * m + 15) = 4 * m + 7 ∨ n % (9 * m + 15) = 5 * m + 9 ∨ n % (9 * m + 15) = 6 * m + 11 ∨ n % (9 * m + 15) = 7 * m + 13 ∨ n % (9 * m + 15) = 8 * m + 14) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1443_rows m _ hmu (by omega) (n / (9 * m + 15))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, _, _, ht0, ht1, ht3, ht4, ht5, ht6⟩ := k68g1443_step m _ hmu (by omega) _ hrow hblk
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

section K68g1453

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1453)
include hmu hu

theorem k68g1453_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1453_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2156 * u + 260) / 512) ((2156 * u + 260) / 512) := by
    have hv : v2 ((2156 * u + 260) / 512) = 0 := by
      have : ((2156 * u + 260) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2156 * u + 260) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 4) / 256) / 2 = (2156 * u + 260) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F28
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F29)
  have hblk' := k68g1453_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g1453_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g1453_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1453

/-- 予想 K68 の u ≡ 1453 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_1453 (m : Nat) (hm : (m + 1) % 16384 = 11624) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1453_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g1453_step m _ hmu (by omega) _ hrow hblk
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

section K68g1559

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1559)
include hmu hu

theorem k68g1559_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1559_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F26 : IsP m (a + (6244 * u + 772) / 1024) ((6244 * u + 772) / 1024) := by
    have hv : v2 ((6244 * u + 772) / 1024) = 0 := by
      have : ((6244 * u + 772) / 1024) % 2 = 1 := by omega
      rw [v2_odd ((6244 * u + 772) / 1024) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F27 : ¬ IsP m (a + (m + 2) + (2148 * u + 260) / 512) ((2148 * u + 260) / 512) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((2148 * u + 260) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2148 * u + 260) / 512) / 2 = (6244 * u + 772) / 1024 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 256) ((100 * u + 4) / 256) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (100 * u + 4) / 256) / 2 = (2148 * u + 260) / 512 by omega]; exact F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    rw [show (100 * u + 4) / 128 = 2 * ((100 * u + 4) / 256) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F30
  have F32 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F31
  have F33 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F32
  have F34 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F33
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F34
  have F36 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F35
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hmo (by omega) hr4 (by rw [hh]; exact F36)
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    have hv : v2 ((548 * u + 68) / 128) = 0 := by
      have : ((548 * u + 68) / 128) % 2 = 1 := by omega
      rw [v2_odd ((548 * u + 68) / 128) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 32) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F36 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F41
  have F43 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mpr F42
  have F44 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mp h F43
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F44)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F47 : ¬ IsP m (a + (1772 * u + 204) / 256) ((1772 * u + 204) / 256) := by
    have hv : v2 ((1772 * u + 204) / 256) = 3 := by
      have : ((1772 * u + 204) / 256) % 16 = 8 := by omega
      rw [v2_even ((1772 * u + 204) / 256) (by omega) (by omega),
        v2_even ((1772 * u + 204) / 256 / 2) (by omega) (by omega),
        v2_even ((1772 * u + 204) / 256 / 2 / 2) (by omega) (by omega),
        v2_odd ((1772 * u + 204) / 256 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F48 : IsP m (a + (m + 2) + (748 * u + 76) / 128) ((748 * u + 76) / 128) := by
    refine (o_odd_iff m (4 * u) (a) ((748 * u + 76) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (748 * u + 76) / 128) / 2 = (1772 * u + 204) / 256 by omega]; exact F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 64) ((236 * u + 12) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (236 * u + 12) / 64) / 2 = (748 * u + 76) / 128 by omega]; exact F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 32) ((236 * u + 12) / 32) := by
    rw [show (236 * u + 12) / 32 = 2 * ((236 * u + 12) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((108 * u + 12) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (108 * u + 12) / 16 / 2 = (236 * u + 12) / 32 by omega]; exact F50
  have F52 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((44 * u + 4) / 8) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F51
  have F53 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F36 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F52
  have F54 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mpr F53
  have F55 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) (4 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F54
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F55)
  have hblk' := k68g1559_blk m u hmu hu _ hr6 hb6 hr7
  rw [show a + (7 * m + 11) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F4, F18, F36⟩

theorem k68g1559_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 11)) p) ∧ Blk m 3 (i * (7 * m + 11)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k68g1559_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1559

/-- 予想 K68 の u ≡ 1559 (mod 2048)（1101100 型）：(n, 0) が P ⇔ n mod (7 * m + 11) が各行の始まり。-/
theorem K68_1559 (m : Nat) (hm : (m + 1) % 16384 = 12472) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 11) = 0 ∨ n % (7 * m + 11) = 1 * m + 2 ∨ n % (7 * m + 11) = 2 * m + 4 ∨ n % (7 * m + 11) = 3 * m + 5 ∨ n % (7 * m + 11) = 4 * m + 7 ∨ n % (7 * m + 11) = 5 * m + 9 ∨ n % (7 * m + 11) = 6 * m + 10) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1559_rows m _ hmu (by omega) (n / (7 * m + 11))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3, ht4⟩ := k68g1559_step m _ hmu (by omega) _ hrow hblk
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

section K68g1645

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1645)
include hmu hu

theorem k68g1645_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1645_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
    have hv : v2 ((4204 * u + 516) / 1024) = 1 := by
      have : ((4204 * u + 516) / 1024) % 4 = 2 := by omega
      rw [v2_even ((4204 * u + 516) / 1024) (by omega) (by omega),
        v2_odd ((4204 * u + 516) / 1024 / 2) (by omega)]
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
  have hblk' := k68g1645_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g1645_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g1645_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1645

/-- 予想 K68 の u ≡ 1645 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_1645 (m : Nat) (hm : (m + 1) % 16384 = 13160) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1645_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g1645_step m _ hmu (by omega) _ hrow hblk
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

section K68g1687

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1687)
include hmu hu

theorem k68g1687_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1687_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F26 : ¬ IsP m (a + (10340 * u + 1284) / 2048) ((10340 * u + 1284) / 2048) := by
    have hv : v2 ((10340 * u + 1284) / 2048) = 1 := by
      have : ((10340 * u + 1284) / 2048) % 4 = 2 := by omega
      rw [v2_even ((10340 * u + 1284) / 2048) (by omega) (by omega),
        v2_odd ((10340 * u + 1284) / 2048 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F27 : IsP m (a + (m + 2) + (2148 * u + 260) / 1024) ((2148 * u + 260) / 1024) := by
    refine (o_odd_iff m (4 * u) (a) ((2148 * u + 260) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (2148 * u + 260) / 1024) / 2 = (10340 * u + 1284) / 2048 by omega]; exact F26
  have F28 : ¬ IsP m (a + (m + 2) + (2148 * u + 260) / 512) ((2148 * u + 260) / 512) := by
    rw [show (2148 * u + 260) / 512 = 2 * ((2148 * u + 260) / 1024) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((2148 * u + 260) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F27
  have F29 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 256) ((100 * u + 4) / 256) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (100 * u + 4) / 256) / 2 = (2148 * u + 260) / 512 by omega]; exact F28
  have F30 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 128) ((100 * u + 4) / 128) := by
    rw [show (100 * u + 4) / 128 = 2 * ((100 * u + 4) / 256) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 256) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F29
  have F31 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 64) ((100 * u + 4) / 64) := by
    rw [show (100 * u + 4) / 64 = 2 * ((100 * u + 4) / 128) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 128) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 32) ((100 * u + 4) / 32) := by
    rw [show (100 * u + 4) / 32 = 2 * ((100 * u + 4) / 64) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (100 * u + 4) / 16) ((100 * u + 4) / 16) := by
    rw [show (100 * u + 4) / 16 = 2 * ((100 * u + 4) / 32) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((100 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (36 * u + 4) / 8 / 2 = (100 * u + 4) / 16 by omega]; exact F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F36
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hmo (by omega) hr4 (by rw [hh]; exact F37)
  have F38 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    have hv : v2 ((548 * u + 68) / 128) = 0 := by
      have : ((548 * u + 68) / 128) % 2 = 1 := by omega
      rw [v2_odd ((548 * u + 68) / 128) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F39 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F38
  have F40 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F39
  have F41 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 32) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F40
  have F42 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F41
  have F43 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F37 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F42
  have F44 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F37 (by omega) (by omega) (by omega)).mpr F43
  have F45 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F37 (by omega) (by omega) (by omega)).mp h F44
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F45)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F48 : ¬ IsP m (a + (1772 * u + 204) / 256) ((1772 * u + 204) / 256) := by
    have hv : v2 ((1772 * u + 204) / 256) = 1 := by
      have : ((1772 * u + 204) / 256) % 4 = 2 := by omega
      rw [v2_even ((1772 * u + 204) / 256) (by omega) (by omega),
        v2_odd ((1772 * u + 204) / 256 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F49 : IsP m (a + (m + 2) + (748 * u + 76) / 128) ((748 * u + 76) / 128) := by
    refine (o_odd_iff m (4 * u) (a) ((748 * u + 76) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (748 * u + 76) / 128) / 2 = (1772 * u + 204) / 256 by omega]; exact F48
  have F50 : ¬ IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 64) ((236 * u + 12) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (236 * u + 12) / 64) / 2 = (748 * u + 76) / 128 by omega]; exact F49
  have F51 : IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 32) ((236 * u + 12) / 32) := by
    rw [show (236 * u + 12) / 32 = 2 * ((236 * u + 12) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F50
  have F52 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((108 * u + 12) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (108 * u + 12) / 16 / 2 = (236 * u + 12) / 32 by omega]; exact F51
  have F53 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((44 * u + 4) / 8) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F52
  have F54 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F37 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F53
  have F55 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F37 (by omega) (by omega) (by omega)).mpr F54
  have F56 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) (4 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F55
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F56)
  have hblk' := k68g1687_blk m u hmu hu _ hr6 hb6 hr7
  rw [show a + (7 * m + 11) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F4, F18, F37⟩

theorem k68g1687_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 11)) p) ∧ Blk m 3 (i * (7 * m + 11)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k68g1687_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1687

/-- 予想 K68 の u ≡ 1687 (mod 2048)（1101100 型）：(n, 0) が P ⇔ n mod (7 * m + 11) が各行の始まり。-/
theorem K68_1687 (m : Nat) (hm : (m + 1) % 16384 = 13496) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 11) = 0 ∨ n % (7 * m + 11) = 1 * m + 2 ∨ n % (7 * m + 11) = 2 * m + 4 ∨ n % (7 * m + 11) = 3 * m + 5 ∨ n % (7 * m + 11) = 4 * m + 7 ∨ n % (7 * m + 11) = 5 * m + 9 ∨ n % (7 * m + 11) = 6 * m + 10) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1687_rows m _ hmu (by omega) (n / (7 * m + 11))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3, ht4⟩ := k68g1687_step m _ hmu (by omega) _ hrow hblk
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

section K68g1709

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1709)
include hmu hu

theorem k68g1709_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1709_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2156 * u + 260) / 512) ((2156 * u + 260) / 512) := by
    have hv : v2 ((2156 * u + 260) / 512) = 0 := by
      have : ((2156 * u + 260) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2156 * u + 260) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 4) / 256) / 2 = (2156 * u + 260) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F28
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F29)
  have hblk' := k68g1709_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g1709_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g1709_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1709

/-- 予想 K68 の u ≡ 1709 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_1709 (m : Nat) (hm : (m + 1) % 16384 = 13672) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1709_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g1709_step m _ hmu (by omega) _ hrow hblk
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

section K68g1965

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1965)
include hmu hu

theorem k68g1965_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1965_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
  have F20 : IsP m (a + (2156 * u + 260) / 512) ((2156 * u + 260) / 512) := by
    have hv : v2 ((2156 * u + 260) / 512) = 0 := by
      have : ((2156 * u + 260) / 512) % 2 = 1 := by omega
      rw [v2_odd ((2156 * u + 260) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F21 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 256) ((108 * u + 4) / 256) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 4) / 256) / 2 = (2156 * u + 260) / 512 by omega]; exact F20
  have F22 : IsP m (a + (m + 2) + (108 * u + 4) / 128) ((108 * u + 4) / 128) := by
    rw [show (108 * u + 4) / 128 = 2 * ((108 * u + 4) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 64) ((108 * u + 4) / 64) := by
    rw [show (108 * u + 4) / 64 = 2 * ((108 * u + 4) / 128) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (108 * u + 4) / 32) ((108 * u + 4) / 32) := by
    rw [show (108 * u + 4) / 32 = 2 * ((108 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 4) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F23
  have F25 : ¬ IsP m (a + (m + 2) + (108 * u + 4) / 16) ((108 * u + 4) / 16) := by
    rw [show (108 * u + 4) / 16 = 2 * ((108 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 4) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 1) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (e_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (44 * u + 4) / 8 / 2 = (44 * u + 4) / 16 by omega]; exact F19
    · rw [show 4 * u + (44 * u + 4) / 8 / 2 = (108 * u + 4) / 16 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (m + 1) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 1)) ((12 * u + 0) / 4) hmh hr2 hr3 F9 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 1) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F28
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F29)
  have hblk' := k68g1965_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 7) = a + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F9⟩

theorem k68g1965_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 7)) p) ∧ Blk m 3 (i * (5 * m + 7)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g1965_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1965

/-- 予想 K68 の u ≡ 1965 (mod 2048)（10100 型）：(n, 0) が P ⇔ n mod (5 * m + 7) が各行の始まり。-/
theorem K68_1965 (m : Nat) (hm : (m + 1) % 16384 = 15720) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 7) = 0 ∨ n % (5 * m + 7) = 1 * m + 2 ∨ n % (5 * m + 7) = 2 * m + 3 ∨ n % (5 * m + 7) = 3 * m + 5 ∨ n % (5 * m + 7) = 4 * m + 6) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1965_rows m _ hmu (by omega) (n / (5 * m + 7))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht2⟩ := k68g1965_step m _ hmu (by omega) _ hrow hblk
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

section K68g1975

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2048 = 1975)
include hmu hu

theorem k68g1975_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g1975_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (5 * m + 8)) p) ∧
    Blk m 3 (a + (5 * m + 8)) ∧
    IsP m (a + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + 4 * u) (4 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
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
    have hv : v2 ((548 * u + 68) / 128) = 3 := by
      have : ((548 * u + 68) / 128) % 16 = 8 := by omega
      rw [v2_even ((548 * u + 68) / 128) (by omega) (by omega),
        v2_even ((548 * u + 68) / 128 / 2) (by omega) (by omega),
        v2_even ((548 * u + 68) / 128 / 2 / 2) (by omega) (by omega),
        v2_odd ((548 * u + 68) / 128 / 2 / 2 / 2) (by omega)]
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
  have F13 : IsP m (a + (8740 * u + 1092) / 2048) ((8740 * u + 1092) / 2048) := by
    have hv : v2 ((8740 * u + 1092) / 2048) = 0 := by
      have : ((8740 * u + 1092) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((8740 * u + 1092) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F14 : ¬ IsP m (a + (m + 2) + (548 * u + 68) / 1024) ((548 * u + 68) / 1024) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((548 * u + 68) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (548 * u + 68) / 1024) / 2 = (8740 * u + 1092) / 2048 by omega]; exact F13
  have F15 : IsP m (a + (m + 2) + (548 * u + 68) / 512) ((548 * u + 68) / 512) := by
    rw [show (548 * u + 68) / 512 = 2 * ((548 * u + 68) / 1024) by omega]
    exact (o_half' m (4 * u) (a) ((548 * u + 68) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F14
  have F16 : ¬ IsP m (a + (m + 2) + (548 * u + 68) / 256) ((548 * u + 68) / 256) := by
    rw [show (548 * u + 68) / 256 = 2 * ((548 * u + 68) / 512) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((548 * u + 68) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F15
  have F17 : IsP m (a + (m + 2) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    rw [show (548 * u + 68) / 128 = 2 * ((548 * u + 68) / 256) by omega]
    exact (o_half' m (4 * u) (a) ((548 * u + 68) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F16
  have F18 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((36 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F17
  have F19 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F18
  have F20 : ¬ IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 32) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mp h F19
  have F21 : IsP m (a + (m + 2) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((36 * u + 4) / 16) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F20
  have F22 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F21
  have F23 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((4 * u + 0) / 2) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mp h F23
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hr3 (by rw [hh]; exact F24)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F26 : IsP m (a + (620 * u + 76) / 128) ((620 * u + 76) / 128) := by
    have hv : v2 ((620 * u + 76) / 128) = 0 := by
      have : ((620 * u + 76) / 128) % 2 = 1 := by omega
      rw [v2_odd ((620 * u + 76) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F27 : ¬ IsP m (a + (m + 2) + (108 * u + 12) / 64) ((108 * u + 12) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a) ((108 * u + 12) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (108 * u + 12) / 64) / 2 = (620 * u + 76) / 128 by omega]; exact F26
  have F28 : IsP m (a + (m + 2) + (108 * u + 12) / 32) ((108 * u + 12) / 32) := by
    rw [show (108 * u + 12) / 32 = 2 * ((108 * u + 12) / 64) by omega]
    exact (o_half' m (4 * u) (a) ((108 * u + 12) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F27
  have F29 : ¬ IsP m (a + (m + 2) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    rw [show (108 * u + 12) / 16 = 2 * ((108 * u + 12) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a) ((108 * u + 12) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2)) ((44 * u + 4) / 8) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F30
  have F32 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2)) ((12 * u + 0) / 4) hmh hr2 hr3 F12 (by omega) (by omega) (by omega)).mpr F31
  have F33 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 2)) (4 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F32
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F33)
  have hblk' := k68g1975_blk m u hmu hu _ hr4 hb4 hr5
  rw [show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hblk', F0, F4, F12⟩

theorem k68g1975_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 8)) p) ∧ Blk m 3 (i * (5 * m + 8)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha, hb, _⟩ := k68g1975_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g1975

/-- 予想 K68 の u ≡ 1975 (mod 2048)（11100 型）：(n, 0) が P ⇔ n mod (5 * m + 8) が各行の始まり。-/
theorem K68_1975 (m : Nat) (hm : (m + 1) % 16384 = 15800) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 8) = 0 ∨ n % (5 * m + 8) = 1 * m + 2 ∨ n % (5 * m + 8) = 2 * m + 4 ∨ n % (5 * m + 8) = 3 * m + 6 ∨ n % (5 * m + 8) = 4 * m + 7) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g1975_rows m _ hmu (by omega) (n / (5 * m + 8))
  obtain ⟨hq1, hq2, hq3, hq4, _, _, ht0, ht1, ht2⟩ := k68g1975_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (5 * m + 8)) * (5 * m + 8) + n % (5 * m + 8) := by
    have := Nat.div_add_mod n (5 * m + 8)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (5 * m + 8) < 5 * m + 8 := Nat.mod_lt n (by omega)
  generalize hcc : n % (5 * m + 8) = c at hdiv hlt
  generalize ha : n / (5 * m + 8) * (5 * m + 8) = a at hdiv hrow hq1 hq2 hq3 hq4 ht0 ht1 ht2
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
                · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (4 * m + 7)) by omega] at hP
                  exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq4 0

end Rubidium
