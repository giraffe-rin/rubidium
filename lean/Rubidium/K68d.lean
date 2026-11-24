/-
  Rubidium.K68d — 予想 K68 の u ≡ 407 (mod 512)（1101100 型）の証明

  定理：m + 1 = 8u、u ≡ 407 (mod 512) なら、(n, 0) が P ⇔ n mod (7m+11) が 7 つの行の始まりのどれか。
  始まりの行の不変量は Blk m 3。各行の (行 + 4u) の P/N を、O 型の行の規則（o_half'・o_odd_iff）と
  E 型の行の規則（blk1_direct・e_iff）で始まりの行 a の距離に落として、Blk m 3 で決める。
  証明は code/k68_gen.js で生成した（u = r + 512t、t = 0..7 で証明の形が同じことを確かめてから出力）。
-/
import Rubidium.K67b

namespace Rubidium

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

section K68g407

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 512 = 407)
include hmu hu

theorem k68g407_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
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

theorem k68g407_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
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
    have hv : v2 ((2724 * u + 324) / 512) = 1 := by
      have : ((2724 * u + 324) / 512) % 4 = 2 := by omega
      rw [v2_even ((2724 * u + 324) / 512) (by omega) (by omega),
        v2_odd ((2724 * u + 324) / 512 / 2) (by omega)]
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
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((36 * u + 4) / 8) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).1
    rw [show (36 * u + 4) / 8 / 2 = (36 * u + 4) / 16 by omega]; exact F25
  have F36 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F35
  have F37 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 4) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F36
  have F38 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((4 * u + 0) / 2) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F37
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hmo (by omega) hr4 (by rw [hh]; exact F38)
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (548 * u + 68) / 128) ((548 * u + 68) / 128) := by
    have hv : v2 ((548 * u + 68) / 128) = 0 := by
      have : ((548 * u + 68) / 128) % 2 = 1 := by omega
      rw [v2_odd ((548 * u + 68) / 128) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 64) ((36 * u + 4) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (36 * u + 4) / 64) / 2 = (548 * u + 68) / 128 by omega]; exact F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 32) ((36 * u + 4) / 32) := by
    rw [show (36 * u + 4) / 32 = 2 * ((36 * u + 4) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 64) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 16) ((36 * u + 4) / 16) := by
    rw [show (36 * u + 4) / 16 = 2 * ((36 * u + 4) / 32) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 32) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mp h F41
  have F43 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (36 * u + 4) / 8) ((36 * u + 4) / 8) := by
    rw [show (36 * u + 4) / 8 = 2 * ((36 * u + 4) / 16) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((36 * u + 4) / 16) hmh hr3 hr4 F18 (by omega) (by omega) (by omega)).mpr F42
  have F44 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 4) ((4 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4 * u + 0) / 4) / 2 = (36 * u + 4) / 8 by omega]; exact F43
  have F45 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (4 * u + 0) / 2) ((4 * u + 0) / 2) := by
    rw [show (4 * u + 0) / 2 = 2 * ((4 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 4) hmh hr4 hr5 F38 (by omega) (by omega) (by omega)).mpr F44
  have F46 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + 4 * u) (4 * u) := by
    rw [show 4 * u = 2 * ((4 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((4 * u + 0) / 2) hmh hr4 hr5 F38 (by omega) (by omega) (by omega)).mp h F45
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F46)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F49 : ¬ IsP m (a + (1772 * u + 204) / 256) ((1772 * u + 204) / 256) := by
    have hv : v2 ((1772 * u + 204) / 256) = 1 := by
      have : ((1772 * u + 204) / 256) % 4 = 2 := by omega
      rw [v2_even ((1772 * u + 204) / 256) (by omega) (by omega),
        v2_odd ((1772 * u + 204) / 256 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F50 : IsP m (a + (m + 2) + (748 * u + 76) / 128) ((748 * u + 76) / 128) := by
    refine (o_odd_iff m (4 * u) (a) ((748 * u + 76) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (748 * u + 76) / 128) / 2 = (1772 * u + 204) / 256 by omega]; exact F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 64) ((236 * u + 12) / 64) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (236 * u + 12) / 64) / 2 = (748 * u + 76) / 128 by omega]; exact F50
  have F52 : IsP m (a + (m + 2) + (m + 2) + (236 * u + 12) / 32) ((236 * u + 12) / 32) := by
    rw [show (236 * u + 12) / 32 = 2 * ((236 * u + 12) / 64) by omega]
    exact (o_half' m (4 * u) (a + (m + 2)) ((236 * u + 12) / 64) hmh hr1 hr2 F4 (by omega) (by omega) (by omega)).mpr F51
  have F53 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (108 * u + 12) / 16) ((108 * u + 12) / 16) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2)) ((108 * u + 12) / 16) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + (108 * u + 12) / 16 / 2 = (236 * u + 12) / 32 by omega]; exact F52
  have F54 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (44 * u + 4) / 8) ((44 * u + 4) / 8) := by
    refine (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((44 * u + 4) / 8) hmh hr3 hr4 F18 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (44 * u + 4) / 8) / 2 = (108 * u + 12) / 16 by omega]; exact F53
  have F55 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 4) ((12 * u + 0) / 4) := by
    intro h; apply (o_odd_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12 * u + 0) / 4) / 2 = (44 * u + 4) / 8 by omega]; exact F54
  have F56 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (12 * u + 0) / 2) ((12 * u + 0) / 2) := by
    rw [show (12 * u + 0) / 2 = 2 * ((12 * u + 0) / 4) by omega]
    exact (o_half' m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((12 * u + 0) / 4) hmh hr4 hr5 F38 (by omega) (by omega) (by omega)).mpr F55
  have F57 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    intro h; apply ((e_iff m (4 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2)) (4 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 4 * u + 4 * u / 2 = (12 * u + 0) / 2 by omega]; exact F56
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F57)
  have hblk' := k68g407_blk m u hmu hu _ hr6 hb6 hr7
  rw [show a + (7 * m + 11) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F4, F18, F38⟩

theorem k68g407_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 11)) p) ∧ Blk m 3 (i * (7 * m + 11)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k68g407_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g407

/-- 予想 K68 の u ≡ 407 (mod 512)（1101100 型）：(n, 0) が P ⇔ n mod (7 * m + 11) が各行の始まり。-/
theorem K68_407 (m : Nat) (hm : (m + 1) % 4096 = 3256) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 11) = 0 ∨ n % (7 * m + 11) = 1 * m + 2 ∨ n % (7 * m + 11) = 2 * m + 4 ∨ n % (7 * m + 11) = 3 * m + 5 ∨ n % (7 * m + 11) = 4 * m + 7 ∨ n % (7 * m + 11) = 5 * m + 9 ∨ n % (7 * m + 11) = 6 * m + 10) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k68g407_rows m _ hmu (by omega) (n / (7 * m + 11))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3, ht4⟩ := k68g407_step m _ hmu (by omega) _ hrow hblk
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

end Rubidium
