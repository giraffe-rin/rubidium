/-
  Rubidium.K69a — v2(m+1) = 5（m + 1 = 32u）の 9 の類（u mod 1024）の型の証明（code/k69_gen.js で生成）

  始まりの行の不変量は Blk m 4（h = 16u、v2(h) = 4）。各行の (行 + 16u) の P/N を K68e と同じ規則で始まりの行の距離に落とす。
  次の始まりの行の Blk m 4 は、最後の 2 つの E 型の行で blk_step2 を 2 回使って得る（型の語は 000 で終わる）。
-/
import Rubidium.K67b

namespace Rubidium

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

section K69g43

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 1024 = 43)
include hmu hu

theorem k69g43_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (6 * m + 9)) p) ∧
    Blk m 4 (a + (6 * m + 9)) ∧
    IsP m (a + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
  have hmh : m + 1 = 2 * (16 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 16 * u := by omega
  have hv4u : v2 (16 * u) = 4 := by
    rw [show 16 * u = 2 * (2 * (2 * (2 * u))) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 16 * u) (16 * u) := by
    have hv : v2 (16 * u) = 4 := by
      have : (16 * u) % 32 = 16 := by omega
      rw [v2_even (16 * u) (by omega) (by omega),
        v2_even (16 * u / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2 / 2) (by omega) (by omega),
        v2_odd (16 * u / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    have hv : v2 ((528 * u + 16) / 32) = 1 := by
      have : ((528 * u + 16) / 32) % 4 = 2 := by omega
      rw [v2_even ((528 * u + 16) / 32) (by omega) (by omega),
        v2_odd ((528 * u + 16) / 32 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have F5 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F4
  have F6 : IsP m (a + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F5
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F6)
  have F7 : ¬ IsP m (a + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    have hv : v2 ((2576 * u + 80) / 128) = 1 := by
      have : ((2576 * u + 80) / 128) % 4 = 2 := by omega
      rw [v2_even ((2576 * u + 80) / 128) (by omega) (by omega),
        v2_odd ((2576 * u + 80) / 128 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F8 : IsP m (a + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    refine (o_odd_iff m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F7
  have F9 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F9
  have F11 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F10
  have F12 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F11
  have F13 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 2) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F13
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F14)
  have F15 : IsP m (a + (10768 * u + 336) / 512) ((10768 * u + 336) / 512) := by
    have hv : v2 ((10768 * u + 336) / 512) = 0 := by
      have : ((10768 * u + 336) / 512) % 2 = 1 := by omega
      rw [v2_odd ((10768 * u + 336) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F16 : ¬ IsP m (a + (m + 2) + (2576 * u + 80) / 256) ((2576 * u + 80) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 80) / 256) / 2 = (10768 * u + 336) / 512 by omega]; exact F15
  have F17 : IsP m (a + (m + 2) + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    rw [show (2576 * u + 80) / 128 = 2 * ((2576 * u + 80) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F16
  have F18 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F17
  have F19 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F18
  have F20 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F19
  have F21 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F20
  have F22 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F21
  have F23 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F23
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hr3 (by rw [hh]; exact F24)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F44 : IsP m (a + (3632 * u + 112) / 128) ((3632 * u + 112) / 128) := by
    have hv : v2 ((3632 * u + 112) / 128) = 0 := by
      have : ((3632 * u + 112) / 128) % 2 = 1 := by omega
      rw [v2_odd ((3632 * u + 112) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F45 : ¬ IsP m (a + (m + 2) + (1584 * u + 48) / 64) ((1584 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1584 * u + 48) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1584 * u + 48) / 64) / 2 = (3632 * u + 112) / 128 by omega]; exact F44
  have F46 : IsP m (a + (m + 2) + (m + 2) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((560 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (560 * u + 16) / 32) / 2 = (1584 * u + 48) / 64 by omega]; exact F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F46
  have F48 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) (16 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F50
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F51)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F67 : IsP m (a + (3760 * u + 112) / 128) ((3760 * u + 112) / 128) := by
    have hv : v2 ((3760 * u + 112) / 128) = 4 := by
      have : ((3760 * u + 112) / 128) % 32 = 16 := by omega
      rw [v2_even ((3760 * u + 112) / 128) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2 / 2) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2 / 2 / 2) (by omega) (by omega),
        v2_odd ((3760 * u + 112) / 128 / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F68 : ¬ IsP m (a + (m + 2) + (1712 * u + 48) / 64) ((1712 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1712 * u + 48) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1712 * u + 48) / 64) / 2 = (3760 * u + 112) / 128 by omega]; exact F67
  have F69 : IsP m (a + (m + 2) + (m + 2) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((688 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (688 * u + 16) / 32) / 2 = (1712 * u + 48) / 64 by omega]; exact F68
  have F70 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F69
  have F71 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F70
  have F72 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F71
  have F73 : IsP m (a + (9840 * u + 304) / 512) ((9840 * u + 304) / 512) := by
    have hv : v2 ((9840 * u + 304) / 512) = 0 := by
      have : ((9840 * u + 304) / 512) % 2 = 1 := by omega
      rw [v2_odd ((9840 * u + 304) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F74 : ¬ IsP m (a + (m + 2) + (1648 * u + 48) / 256) ((1648 * u + 48) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1648 * u + 48) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1648 * u + 48) / 256) / 2 = (9840 * u + 304) / 512 by omega]; exact F73
  have F75 : IsP m (a + (m + 2) + (1648 * u + 48) / 128) ((1648 * u + 48) / 128) := by
    rw [show (1648 * u + 48) / 128 = 2 * ((1648 * u + 48) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((1648 * u + 48) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F74
  have F76 : ¬ IsP m (a + (m + 2) + (1648 * u + 48) / 64) ((1648 * u + 48) / 64) := by
    rw [show (1648 * u + 48) / 64 = 2 * ((1648 * u + 48) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((1648 * u + 48) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F75
  have F77 : IsP m (a + (m + 2) + (m + 2) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((624 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (624 * u + 16) / 32) / 2 = (1648 * u + 48) / 64 by omega]; exact F76
  have F78 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F77
  have F79 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F78
  have F80 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F79
  have F81 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 2) hmh hr3 hr4 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F72
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F80
  have F82 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F81
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hr5 (by rw [hh]; exact F82)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr4 hb4 hr5
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb3' hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F6, F14⟩

theorem k69g43_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 4 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k69g43_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g43

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 43 (mod 1024)（111000 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K69_43 (m : Nat) (hm : (m + 1) % 32768 = 1376) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 6 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g43_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht2⟩ := k69g43_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (6 * m + 9)) * (6 * m + 9) + n % (6 * m + 9) := by
    have := Nat.div_add_mod n (6 * m + 9)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (6 * m + 9) < 6 * m + 9 := Nat.mod_lt n (by omega)
  generalize hcc : n % (6 * m + 9) = c at hdiv hlt
  generalize ha : n / (6 * m + 9) * (6 * m + 9) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 ht0 ht1 ht2
  subst hdiv
  have hmh : m + 1 = 2 * (16 * ((m + 1) / 32)) := by omega
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
                · by_cases c4 : c ≤ 4 * m + 7 + m
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (4 * m + 7)) by omega] at hP
                    exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (c - (5 * m + 8)) by omega] at hP
                    exact not_isP_of_row m _ (c - (5 * m + 8)) 0 hq5 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]; exact hq5 0

section K69g139

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 1024 = 139)
include hmu hu

theorem k69g139_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (6 * m + 9)) p) ∧
    Blk m 4 (a + (6 * m + 9)) ∧
    IsP m (a + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
  have hmh : m + 1 = 2 * (16 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 16 * u := by omega
  have hv4u : v2 (16 * u) = 4 := by
    rw [show 16 * u = 2 * (2 * (2 * (2 * u))) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 16 * u) (16 * u) := by
    have hv : v2 (16 * u) = 4 := by
      have : (16 * u) % 32 = 16 := by omega
      rw [v2_even (16 * u) (by omega) (by omega),
        v2_even (16 * u / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2 / 2) (by omega) (by omega),
        v2_odd (16 * u / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    have hv : v2 ((528 * u + 16) / 32) = 1 := by
      have : ((528 * u + 16) / 32) % 4 = 2 := by omega
      rw [v2_even ((528 * u + 16) / 32) (by omega) (by omega),
        v2_odd ((528 * u + 16) / 32 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have F5 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F4
  have F6 : IsP m (a + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F5
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F6)
  have F7 : ¬ IsP m (a + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    have hv : v2 ((2576 * u + 80) / 128) = 1 := by
      have : ((2576 * u + 80) / 128) % 4 = 2 := by omega
      rw [v2_even ((2576 * u + 80) / 128) (by omega) (by omega),
        v2_odd ((2576 * u + 80) / 128 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F8 : IsP m (a + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    refine (o_odd_iff m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F7
  have F9 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F9
  have F11 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F10
  have F12 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F11
  have F13 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 2) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F13
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F14)
  have F15 : IsP m (a + (10768 * u + 336) / 512) ((10768 * u + 336) / 512) := by
    have hv : v2 ((10768 * u + 336) / 512) = 2 := by
      have : ((10768 * u + 336) / 512) % 8 = 4 := by omega
      rw [v2_even ((10768 * u + 336) / 512) (by omega) (by omega),
        v2_even ((10768 * u + 336) / 512 / 2) (by omega) (by omega),
        v2_odd ((10768 * u + 336) / 512 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F16 : ¬ IsP m (a + (m + 2) + (2576 * u + 80) / 256) ((2576 * u + 80) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 80) / 256) / 2 = (10768 * u + 336) / 512 by omega]; exact F15
  have F17 : IsP m (a + (m + 2) + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    rw [show (2576 * u + 80) / 128 = 2 * ((2576 * u + 80) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F16
  have F18 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F17
  have F19 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F18
  have F20 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F19
  have F21 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F20
  have F22 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F21
  have F23 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F23
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hr3 (by rw [hh]; exact F24)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F43 : IsP m (a + (3632 * u + 112) / 128) ((3632 * u + 112) / 128) := by
    have hv : v2 ((3632 * u + 112) / 128) = 0 := by
      have : ((3632 * u + 112) / 128) % 2 = 1 := by omega
      rw [v2_odd ((3632 * u + 112) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F44 : ¬ IsP m (a + (m + 2) + (1584 * u + 48) / 64) ((1584 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1584 * u + 48) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1584 * u + 48) / 64) / 2 = (3632 * u + 112) / 128 by omega]; exact F43
  have F45 : IsP m (a + (m + 2) + (m + 2) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((560 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (560 * u + 16) / 32) / 2 = (1584 * u + 48) / 64 by omega]; exact F44
  have F46 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F45
  have F47 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F46
  have F48 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F47
  have F49 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F48
  have F50 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) (16 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F49
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F50)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F68 : IsP m (a + (3760 * u + 112) / 128) ((3760 * u + 112) / 128) := by
    have hv : v2 ((3760 * u + 112) / 128) = 2 := by
      have : ((3760 * u + 112) / 128) % 8 = 4 := by omega
      rw [v2_even ((3760 * u + 112) / 128) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2) (by omega) (by omega),
        v2_odd ((3760 * u + 112) / 128 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F69 : ¬ IsP m (a + (m + 2) + (1712 * u + 48) / 64) ((1712 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1712 * u + 48) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1712 * u + 48) / 64) / 2 = (3760 * u + 112) / 128 by omega]; exact F68
  have F70 : IsP m (a + (m + 2) + (m + 2) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((688 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (688 * u + 16) / 32) / 2 = (1712 * u + 48) / 64 by omega]; exact F69
  have F71 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F70
  have F72 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F71
  have F73 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F72
  have F74 : IsP m (a + (9840 * u + 304) / 512) ((9840 * u + 304) / 512) := by
    have hv : v2 ((9840 * u + 304) / 512) = 4 := by
      have : ((9840 * u + 304) / 512) % 32 = 16 := by omega
      rw [v2_even ((9840 * u + 304) / 512) (by omega) (by omega),
        v2_even ((9840 * u + 304) / 512 / 2) (by omega) (by omega),
        v2_even ((9840 * u + 304) / 512 / 2 / 2) (by omega) (by omega),
        v2_even ((9840 * u + 304) / 512 / 2 / 2 / 2) (by omega) (by omega),
        v2_odd ((9840 * u + 304) / 512 / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F75 : ¬ IsP m (a + (m + 2) + (1648 * u + 48) / 256) ((1648 * u + 48) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1648 * u + 48) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1648 * u + 48) / 256) / 2 = (9840 * u + 304) / 512 by omega]; exact F74
  have F76 : IsP m (a + (m + 2) + (1648 * u + 48) / 128) ((1648 * u + 48) / 128) := by
    rw [show (1648 * u + 48) / 128 = 2 * ((1648 * u + 48) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((1648 * u + 48) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F75
  have F77 : ¬ IsP m (a + (m + 2) + (1648 * u + 48) / 64) ((1648 * u + 48) / 64) := by
    rw [show (1648 * u + 48) / 64 = 2 * ((1648 * u + 48) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((1648 * u + 48) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F76
  have F78 : IsP m (a + (m + 2) + (m + 2) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((624 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (624 * u + 16) / 32) / 2 = (1648 * u + 48) / 64 by omega]; exact F77
  have F79 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F78
  have F80 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F79
  have F81 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F80
  have F82 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 2) hmh hr3 hr4 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F73
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F81
  have F83 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F82
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hr5 (by rw [hh]; exact F83)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr4 hb4 hr5
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb3' hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F6, F14⟩

theorem k69g139_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 4 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k69g139_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g139

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 139 (mod 1024)（111000 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K69_139 (m : Nat) (hm : (m + 1) % 32768 = 4448) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 6 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g139_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht2⟩ := k69g139_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (6 * m + 9)) * (6 * m + 9) + n % (6 * m + 9) := by
    have := Nat.div_add_mod n (6 * m + 9)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (6 * m + 9) < 6 * m + 9 := Nat.mod_lt n (by omega)
  generalize hcc : n % (6 * m + 9) = c at hdiv hlt
  generalize ha : n / (6 * m + 9) * (6 * m + 9) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 ht0 ht1 ht2
  subst hdiv
  have hmh : m + 1 = 2 * (16 * ((m + 1) / 32)) := by omega
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
                · by_cases c4 : c ≤ 4 * m + 7 + m
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (4 * m + 7)) by omega] at hP
                    exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (c - (5 * m + 8)) by omega] at hP
                    exact not_isP_of_row m _ (c - (5 * m + 8)) 0 hq5 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]; exact hq5 0

section K69g267

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 1024 = 267)
include hmu hu

theorem k69g267_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (6 * m + 9)) p) ∧
    Blk m 4 (a + (6 * m + 9)) ∧
    IsP m (a + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
  have hmh : m + 1 = 2 * (16 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 16 * u := by omega
  have hv4u : v2 (16 * u) = 4 := by
    rw [show 16 * u = 2 * (2 * (2 * (2 * u))) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 16 * u) (16 * u) := by
    have hv : v2 (16 * u) = 4 := by
      have : (16 * u) % 32 = 16 := by omega
      rw [v2_even (16 * u) (by omega) (by omega),
        v2_even (16 * u / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2 / 2) (by omega) (by omega),
        v2_odd (16 * u / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    have hv : v2 ((528 * u + 16) / 32) = 1 := by
      have : ((528 * u + 16) / 32) % 4 = 2 := by omega
      rw [v2_even ((528 * u + 16) / 32) (by omega) (by omega),
        v2_odd ((528 * u + 16) / 32 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have F5 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F4
  have F6 : IsP m (a + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F5
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F6)
  have F7 : ¬ IsP m (a + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    have hv : v2 ((2576 * u + 80) / 128) = 1 := by
      have : ((2576 * u + 80) / 128) % 4 = 2 := by omega
      rw [v2_even ((2576 * u + 80) / 128) (by omega) (by omega),
        v2_odd ((2576 * u + 80) / 128 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F8 : IsP m (a + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    refine (o_odd_iff m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F7
  have F9 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F9
  have F11 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F10
  have F12 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F11
  have F13 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 2) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F13
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F14)
  have F15 : IsP m (a + (10768 * u + 336) / 512) ((10768 * u + 336) / 512) := by
    have hv : v2 ((10768 * u + 336) / 512) = 4 := by
      have : ((10768 * u + 336) / 512) % 32 = 16 := by omega
      rw [v2_even ((10768 * u + 336) / 512) (by omega) (by omega),
        v2_even ((10768 * u + 336) / 512 / 2) (by omega) (by omega),
        v2_even ((10768 * u + 336) / 512 / 2 / 2) (by omega) (by omega),
        v2_even ((10768 * u + 336) / 512 / 2 / 2 / 2) (by omega) (by omega),
        v2_odd ((10768 * u + 336) / 512 / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F16 : ¬ IsP m (a + (m + 2) + (2576 * u + 80) / 256) ((2576 * u + 80) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 80) / 256) / 2 = (10768 * u + 336) / 512 by omega]; exact F15
  have F17 : IsP m (a + (m + 2) + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    rw [show (2576 * u + 80) / 128 = 2 * ((2576 * u + 80) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F16
  have F18 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F17
  have F19 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F18
  have F20 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F19
  have F21 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F20
  have F22 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F21
  have F23 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F23
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hr3 (by rw [hh]; exact F24)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F43 : IsP m (a + (3632 * u + 112) / 128) ((3632 * u + 112) / 128) := by
    have hv : v2 ((3632 * u + 112) / 128) = 0 := by
      have : ((3632 * u + 112) / 128) % 2 = 1 := by omega
      rw [v2_odd ((3632 * u + 112) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F44 : ¬ IsP m (a + (m + 2) + (1584 * u + 48) / 64) ((1584 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1584 * u + 48) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1584 * u + 48) / 64) / 2 = (3632 * u + 112) / 128 by omega]; exact F43
  have F45 : IsP m (a + (m + 2) + (m + 2) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((560 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (560 * u + 16) / 32) / 2 = (1584 * u + 48) / 64 by omega]; exact F44
  have F46 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F45
  have F47 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F46
  have F48 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F47
  have F49 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F48
  have F50 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) (16 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F49
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F50)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F69 : IsP m (a + (3760 * u + 112) / 128) ((3760 * u + 112) / 128) := by
    have hv : v2 ((3760 * u + 112) / 128) = 2 := by
      have : ((3760 * u + 112) / 128) % 8 = 4 := by omega
      rw [v2_even ((3760 * u + 112) / 128) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2) (by omega) (by omega),
        v2_odd ((3760 * u + 112) / 128 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F70 : ¬ IsP m (a + (m + 2) + (1712 * u + 48) / 64) ((1712 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1712 * u + 48) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1712 * u + 48) / 64) / 2 = (3760 * u + 112) / 128 by omega]; exact F69
  have F71 : IsP m (a + (m + 2) + (m + 2) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((688 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (688 * u + 16) / 32) / 2 = (1712 * u + 48) / 64 by omega]; exact F70
  have F72 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F71
  have F73 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F72
  have F74 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F73
  have F75 : IsP m (a + (9840 * u + 304) / 512) ((9840 * u + 304) / 512) := by
    have hv : v2 ((9840 * u + 304) / 512) = 2 := by
      have : ((9840 * u + 304) / 512) % 8 = 4 := by omega
      rw [v2_even ((9840 * u + 304) / 512) (by omega) (by omega),
        v2_even ((9840 * u + 304) / 512 / 2) (by omega) (by omega),
        v2_odd ((9840 * u + 304) / 512 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F76 : ¬ IsP m (a + (m + 2) + (1648 * u + 48) / 256) ((1648 * u + 48) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1648 * u + 48) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1648 * u + 48) / 256) / 2 = (9840 * u + 304) / 512 by omega]; exact F75
  have F77 : IsP m (a + (m + 2) + (1648 * u + 48) / 128) ((1648 * u + 48) / 128) := by
    rw [show (1648 * u + 48) / 128 = 2 * ((1648 * u + 48) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((1648 * u + 48) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F76
  have F78 : ¬ IsP m (a + (m + 2) + (1648 * u + 48) / 64) ((1648 * u + 48) / 64) := by
    rw [show (1648 * u + 48) / 64 = 2 * ((1648 * u + 48) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((1648 * u + 48) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F77
  have F79 : IsP m (a + (m + 2) + (m + 2) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((624 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (624 * u + 16) / 32) / 2 = (1648 * u + 48) / 64 by omega]; exact F78
  have F80 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F79
  have F81 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F80
  have F82 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F81
  have F83 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 2) hmh hr3 hr4 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F74
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F82
  have F84 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F83
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hr5 (by rw [hh]; exact F84)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr4 hb4 hr5
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb3' hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F6, F14⟩

theorem k69g267_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 4 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k69g267_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g267

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 267 (mod 1024)（111000 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K69_267 (m : Nat) (hm : (m + 1) % 32768 = 8544) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 6 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g267_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht2⟩ := k69g267_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (6 * m + 9)) * (6 * m + 9) + n % (6 * m + 9) := by
    have := Nat.div_add_mod n (6 * m + 9)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (6 * m + 9) < 6 * m + 9 := Nat.mod_lt n (by omega)
  generalize hcc : n % (6 * m + 9) = c at hdiv hlt
  generalize ha : n / (6 * m + 9) * (6 * m + 9) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 ht0 ht1 ht2
  subst hdiv
  have hmh : m + 1 = 2 * (16 * ((m + 1) / 32)) := by omega
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
                · by_cases c4 : c ≤ 4 * m + 7 + m
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (4 * m + 7)) by omega] at hP
                    exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (c - (5 * m + 8)) by omega] at hP
                    exact not_isP_of_row m _ (c - (5 * m + 8)) 0 hq5 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]; exact hq5 0

section K69g299

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 1024 = 299)
include hmu hu

theorem k69g299_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (6 * m + 9)) p) ∧
    Blk m 4 (a + (6 * m + 9)) ∧
    IsP m (a + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
  have hmh : m + 1 = 2 * (16 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 16 * u := by omega
  have hv4u : v2 (16 * u) = 4 := by
    rw [show 16 * u = 2 * (2 * (2 * (2 * u))) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 16 * u) (16 * u) := by
    have hv : v2 (16 * u) = 4 := by
      have : (16 * u) % 32 = 16 := by omega
      rw [v2_even (16 * u) (by omega) (by omega),
        v2_even (16 * u / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2 / 2) (by omega) (by omega),
        v2_odd (16 * u / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    have hv : v2 ((528 * u + 16) / 32) = 1 := by
      have : ((528 * u + 16) / 32) % 4 = 2 := by omega
      rw [v2_even ((528 * u + 16) / 32) (by omega) (by omega),
        v2_odd ((528 * u + 16) / 32 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have F5 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F4
  have F6 : IsP m (a + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F5
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F6)
  have F7 : ¬ IsP m (a + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    have hv : v2 ((2576 * u + 80) / 128) = 1 := by
      have : ((2576 * u + 80) / 128) % 4 = 2 := by omega
      rw [v2_even ((2576 * u + 80) / 128) (by omega) (by omega),
        v2_odd ((2576 * u + 80) / 128 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F8 : IsP m (a + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    refine (o_odd_iff m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F7
  have F9 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F9
  have F11 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F10
  have F12 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F11
  have F13 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 2) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F13
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F14)
  have F15 : IsP m (a + (10768 * u + 336) / 512) ((10768 * u + 336) / 512) := by
    have hv : v2 ((10768 * u + 336) / 512) = 0 := by
      have : ((10768 * u + 336) / 512) % 2 = 1 := by omega
      rw [v2_odd ((10768 * u + 336) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F16 : ¬ IsP m (a + (m + 2) + (2576 * u + 80) / 256) ((2576 * u + 80) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 80) / 256) / 2 = (10768 * u + 336) / 512 by omega]; exact F15
  have F17 : IsP m (a + (m + 2) + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    rw [show (2576 * u + 80) / 128 = 2 * ((2576 * u + 80) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F16
  have F18 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F17
  have F19 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F18
  have F20 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F19
  have F21 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F20
  have F22 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F21
  have F23 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F23
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hr3 (by rw [hh]; exact F24)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F44 : IsP m (a + (3632 * u + 112) / 128) ((3632 * u + 112) / 128) := by
    have hv : v2 ((3632 * u + 112) / 128) = 0 := by
      have : ((3632 * u + 112) / 128) % 2 = 1 := by omega
      rw [v2_odd ((3632 * u + 112) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F45 : ¬ IsP m (a + (m + 2) + (1584 * u + 48) / 64) ((1584 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1584 * u + 48) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1584 * u + 48) / 64) / 2 = (3632 * u + 112) / 128 by omega]; exact F44
  have F46 : IsP m (a + (m + 2) + (m + 2) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((560 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (560 * u + 16) / 32) / 2 = (1584 * u + 48) / 64 by omega]; exact F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F46
  have F48 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) (16 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F50
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F51)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F67 : IsP m (a + (3760 * u + 112) / 128) ((3760 * u + 112) / 128) := by
    have hv : v2 ((3760 * u + 112) / 128) = 4 := by
      have : ((3760 * u + 112) / 128) % 32 = 16 := by omega
      rw [v2_even ((3760 * u + 112) / 128) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2 / 2) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2 / 2 / 2) (by omega) (by omega),
        v2_odd ((3760 * u + 112) / 128 / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F68 : ¬ IsP m (a + (m + 2) + (1712 * u + 48) / 64) ((1712 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1712 * u + 48) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1712 * u + 48) / 64) / 2 = (3760 * u + 112) / 128 by omega]; exact F67
  have F69 : IsP m (a + (m + 2) + (m + 2) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((688 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (688 * u + 16) / 32) / 2 = (1712 * u + 48) / 64 by omega]; exact F68
  have F70 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F69
  have F71 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F70
  have F72 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F71
  have F73 : IsP m (a + (9840 * u + 304) / 512) ((9840 * u + 304) / 512) := by
    have hv : v2 ((9840 * u + 304) / 512) = 0 := by
      have : ((9840 * u + 304) / 512) % 2 = 1 := by omega
      rw [v2_odd ((9840 * u + 304) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F74 : ¬ IsP m (a + (m + 2) + (1648 * u + 48) / 256) ((1648 * u + 48) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1648 * u + 48) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1648 * u + 48) / 256) / 2 = (9840 * u + 304) / 512 by omega]; exact F73
  have F75 : IsP m (a + (m + 2) + (1648 * u + 48) / 128) ((1648 * u + 48) / 128) := by
    rw [show (1648 * u + 48) / 128 = 2 * ((1648 * u + 48) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((1648 * u + 48) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F74
  have F76 : ¬ IsP m (a + (m + 2) + (1648 * u + 48) / 64) ((1648 * u + 48) / 64) := by
    rw [show (1648 * u + 48) / 64 = 2 * ((1648 * u + 48) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((1648 * u + 48) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F75
  have F77 : IsP m (a + (m + 2) + (m + 2) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((624 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (624 * u + 16) / 32) / 2 = (1648 * u + 48) / 64 by omega]; exact F76
  have F78 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F77
  have F79 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F78
  have F80 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F79
  have F81 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 2) hmh hr3 hr4 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F72
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F80
  have F82 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F81
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hr5 (by rw [hh]; exact F82)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr4 hb4 hr5
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb3' hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F6, F14⟩

theorem k69g299_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 4 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k69g299_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g299

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 299 (mod 1024)（111000 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K69_299 (m : Nat) (hm : (m + 1) % 32768 = 9568) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 6 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g299_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht2⟩ := k69g299_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (6 * m + 9)) * (6 * m + 9) + n % (6 * m + 9) := by
    have := Nat.div_add_mod n (6 * m + 9)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (6 * m + 9) < 6 * m + 9 := Nat.mod_lt n (by omega)
  generalize hcc : n % (6 * m + 9) = c at hdiv hlt
  generalize ha : n / (6 * m + 9) * (6 * m + 9) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 ht0 ht1 ht2
  subst hdiv
  have hmh : m + 1 = 2 * (16 * ((m + 1) / 32)) := by omega
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
                · by_cases c4 : c ≤ 4 * m + 7 + m
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (4 * m + 7)) by omega] at hP
                    exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (c - (5 * m + 8)) by omega] at hP
                    exact not_isP_of_row m _ (c - (5 * m + 8)) 0 hq5 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]; exact hq5 0

section K69g399

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 1024 = 399)
include hmu hu

theorem k69g399_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (7 * m + 10)) p) ∧
    Blk m 4 (a + (7 * m + 10)) ∧
    IsP m (a + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
  have hmh : m + 1 = 2 * (16 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 16 * u := by omega
  have hv4u : v2 (16 * u) = 4 := by
    rw [show 16 * u = 2 * (2 * (2 * (2 * u))) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 16 * u) (16 * u) := by
    have hv : v2 (16 * u) = 4 := by
      have : (16 * u) % 32 = 16 := by omega
      rw [v2_even (16 * u) (by omega) (by omega),
        v2_even (16 * u / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2 / 2) (by omega) (by omega),
        v2_odd (16 * u / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    have hv : v2 ((528 * u + 16) / 32) = 3 := by
      have : ((528 * u + 16) / 32) % 16 = 8 := by omega
      rw [v2_even ((528 * u + 16) / 32) (by omega) (by omega),
        v2_even ((528 * u + 16) / 32 / 2) (by omega) (by omega),
        v2_even ((528 * u + 16) / 32 / 2 / 2) (by omega) (by omega),
        v2_odd ((528 * u + 16) / 32 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have F5 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F4
  have F6 : IsP m (a + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F5
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F6)
  have F7 : IsP m (a + (8720 * u + 272) / 512) ((8720 * u + 272) / 512) := by
    have hv : v2 ((8720 * u + 272) / 512) = 2 := by
      have : ((8720 * u + 272) / 512) % 8 = 4 := by omega
      rw [v2_even ((8720 * u + 272) / 512) (by omega) (by omega),
        v2_even ((8720 * u + 272) / 512 / 2) (by omega) (by omega),
        v2_odd ((8720 * u + 272) / 512 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F8 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 256) ((528 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((528 * u + 16) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 256) / 2 = (8720 * u + 272) / 512 by omega]; exact F7
  have F9 : IsP m (a + (m + 2) + (528 * u + 16) / 128) ((528 * u + 16) / 128) := by
    rw [show (528 * u + 16) / 128 = 2 * ((528 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((528 * u + 16) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F8
  have F10 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    rw [show (528 * u + 16) / 64 = 2 * ((528 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F9
  have F11 : IsP m (a + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F10
  have F12 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F11
  have F13 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F12
  have F14 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F13
  have F15 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F14
  have F16 : ¬ IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 2) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F15
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2)) hr2 (by rw [hh]; exact F16)
  have hb3 := blk1_direct m _ hr3 (odd_of_rows m _ hmo hr3 (Or.inr ⟨_, rfl, hr2⟩))
  have F17 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    have hv : v2 ((16 * u + 0) / 8) = 1 := by
      have : ((16 * u + 0) / 8) % 4 = 2 := by omega
      rw [v2_even ((16 * u + 0) / 8) (by omega) (by omega),
        v2_odd ((16 * u + 0) / 8 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F18 : IsP m (a + (4752 * u + 144) / 256) ((4752 * u + 144) / 256) := by
    have hv : v2 ((4752 * u + 144) / 256) = 0 := by
      have : ((4752 * u + 144) / 256) % 2 = 1 := by omega
      rw [v2_odd ((4752 * u + 144) / 256) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F19 : ¬ IsP m (a + (m + 2) + (656 * u + 16) / 128) ((656 * u + 16) / 128) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((656 * u + 16) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (656 * u + 16) / 128) / 2 = (4752 * u + 144) / 256 by omega]; exact F18
  have F20 : IsP m (a + (m + 2) + (656 * u + 16) / 64) ((656 * u + 16) / 64) := by
    rw [show (656 * u + 16) / 64 = 2 * ((656 * u + 16) / 128) by omega]
    exact (o_half' m (16 * u) (a) ((656 * u + 16) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F19
  have F21 : ¬ IsP m (a + (m + 2) + (656 * u + 16) / 32) ((656 * u + 16) / 32) := by
    rw [show (656 * u + 16) / 32 = 2 * ((656 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((656 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F20
  have F22 : IsP m (a + (m + 2) + (m + 2) + (144 * u + 0) / 16) ((144 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((144 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (144 * u + 0) / 16) / 2 = (656 * u + 16) / 32 by omega]; exact F21
  have F23 : ¬ IsP m (a + (m + 2) + (m + 2) + (144 * u + 0) / 8) ((144 * u + 0) / 8) := by
    rw [show (144 * u + 0) / 8 = 2 * ((144 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((144 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (16 * u + 0) / 4 / 2 = (16 * u + 0) / 8 by omega]; exact F17
    · rw [show 16 * u + (16 * u + 0) / 4 / 2 = (144 * u + 0) / 8 by omega]; exact F23
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).1
    rw [show (16 * u + 0) / 2 / 2 = (16 * u + 0) / 4 by omega]; exact F24
  have F32 : IsP m (a + (1584 * u + 48) / 64) ((1584 * u + 48) / 64) := by
    have hv : v2 ((1584 * u + 48) / 64) = 2 := by
      have : ((1584 * u + 48) / 64) % 8 = 4 := by omega
      rw [v2_even ((1584 * u + 48) / 64) (by omega) (by omega),
        v2_even ((1584 * u + 48) / 64 / 2) (by omega) (by omega),
        v2_odd ((1584 * u + 48) / 64 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F33 : ¬ IsP m (a + (m + 2) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((560 * u + 16) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (560 * u + 16) / 32) / 2 = (1584 * u + 48) / 64 by omega]; exact F32
  have F34 : IsP m (a + (m + 2) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((48 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F33
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((48 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F34
  have F36 : IsP m (a + (m + 2) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((48 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F35
  have F37 : ¬ IsP m (a + (m + 2) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((48 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F36
  have F38 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2)) (16 * u) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show 16 * u / 2 = (16 * u + 0) / 2 by omega]; exact F31
    · rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F37
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) hr3 (by rw [hh]; exact F38)
  have F40 : IsP m (a + (141840 * u + 4368) / 8192) ((141840 * u + 4368) / 8192) := by
    have hv : v2 ((141840 * u + 4368) / 8192) = 0 := by
      have : ((141840 * u + 4368) / 8192) % 2 = 1 := by omega
      rw [v2_odd ((141840 * u + 4368) / 8192) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F41 : ¬ IsP m (a + (m + 2) + (10768 * u + 272) / 4096) ((10768 * u + 272) / 4096) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((10768 * u + 272) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (10768 * u + 272) / 4096) / 2 = (141840 * u + 4368) / 8192 by omega]; exact F40
  have F42 : IsP m (a + (m + 2) + (10768 * u + 272) / 2048) ((10768 * u + 272) / 2048) := by
    rw [show (10768 * u + 272) / 2048 = 2 * ((10768 * u + 272) / 4096) by omega]
    exact (o_half' m (16 * u) (a) ((10768 * u + 272) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F41
  have F43 : ¬ IsP m (a + (m + 2) + (10768 * u + 272) / 1024) ((10768 * u + 272) / 1024) := by
    rw [show (10768 * u + 272) / 1024 = 2 * ((10768 * u + 272) / 2048) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((10768 * u + 272) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F42
  have F44 : IsP m (a + (m + 2) + (10768 * u + 272) / 512) ((10768 * u + 272) / 512) := by
    rw [show (10768 * u + 272) / 512 = 2 * ((10768 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((10768 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F43
  have F45 : ¬ IsP m (a + (m + 2) + (m + 2) + (2576 * u + 16) / 256) ((2576 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((2576 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 16) / 256) / 2 = (10768 * u + 272) / 512 by omega]; exact F44
  have F46 : IsP m (a + (m + 2) + (m + 2) + (2576 * u + 16) / 128) ((2576 * u + 16) / 128) := by
    rw [show (2576 * u + 16) / 128 = 2 * ((2576 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((2576 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (528 * u + 16) / 64 / 2 = (2576 * u + 16) / 128 by omega]; exact F46
  have F48 : IsP m (a + (42512 * u + 1296) / 2048) ((42512 * u + 1296) / 2048) := by
    have hv : v2 ((42512 * u + 1296) / 2048) = 0 := by
      have : ((42512 * u + 1296) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((42512 * u + 1296) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F49 : ¬ IsP m (a + (m + 2) + (9744 * u + 272) / 1024) ((9744 * u + 272) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((9744 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (9744 * u + 272) / 1024) / 2 = (42512 * u + 1296) / 2048 by omega]; exact F48
  have F50 : IsP m (a + (m + 2) + (9744 * u + 272) / 512) ((9744 * u + 272) / 512) := by
    rw [show (9744 * u + 272) / 512 = 2 * ((9744 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((9744 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (1552 * u + 16) / 256) ((1552 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((1552 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1552 * u + 16) / 256) / 2 = (9744 * u + 272) / 512 by omega]; exact F50
  have F52 : IsP m (a + (m + 2) + (m + 2) + (1552 * u + 16) / 128) ((1552 * u + 16) / 128) := by
    rw [show (1552 * u + 16) / 128 = 2 * ((1552 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((1552 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F51
  have F53 : ¬ IsP m (a + (m + 2) + (m + 2) + (1552 * u + 16) / 64) ((1552 * u + 16) / 64) := by
    rw [show (1552 * u + 16) / 64 = 2 * ((1552 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((1552 * u + 16) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F52
  have F54 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 32) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (528 * u + 16) / 32 / 2 = (528 * u + 16) / 64 by omega]; exact F47
    · rw [show 16 * u + (528 * u + 16) / 32 / 2 = (1552 * u + 16) / 64 by omega]; exact F53
  have F55 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F54
  have F56 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F55
  have F57 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 8) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F56
  have F58 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 4) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F57
  have F59 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 2) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F58
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F59)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F75 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    have hv : v2 ((560 * u + 16) / 32) = 0 := by
      have : ((560 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((560 * u + 16) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F76 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F75
  have F77 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F76
  have F78 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 8) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F77
  have F79 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 4) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F78
  have F80 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F79
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F80)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F91 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    have hv : v2 ((688 * u + 16) / 32) = 0 := by
      have : ((688 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((688 * u + 16) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F92 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((176 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F91
  have F93 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((176 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F92
  have F94 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((48 * u + 0) / 4) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F93
  have F95 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    have hv : v2 ((624 * u + 16) / 32) = 0 := by
      have : ((624 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((624 * u + 16) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F96 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F95
  have F97 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F96
  have F98 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 8) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F97
  have F99 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((48 * u + 0) / 2) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F94
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F98
  have F100 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) (16 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F99
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) hr6 (by rw [hh]; exact F100)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb5 hr6
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr6 hb3' hr7
  rw [show a + (7 * m + 10) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F6, F38⟩

theorem k69g399_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 10)) p) ∧ Blk m 4 (i * (7 * m + 10)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k69g399_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g399

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 399 (mod 1024)（1101000 型）：(n, 0) が P ⇔ n mod (7 * m + 10) が各行の始まり。-/
theorem K69_399 (m : Nat) (hm : (m + 1) % 32768 = 12768) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 10) = 0 ∨ n % (7 * m + 10) = 1 * m + 2 ∨ n % (7 * m + 10) = 2 * m + 4 ∨ n % (7 * m + 10) = 3 * m + 5 ∨ n % (7 * m + 10) = 4 * m + 7 ∨ n % (7 * m + 10) = 5 * m + 8 ∨ n % (7 * m + 10) = 6 * m + 9) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g399_rows m _ hmu (by omega) (n / (7 * m + 10))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3⟩ := k69g399_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (7 * m + 10)) * (7 * m + 10) + n % (7 * m + 10) := by
    have := Nat.div_add_mod n (7 * m + 10)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (7 * m + 10) < 7 * m + 10 := Nat.mod_lt n (by omega)
  generalize hcc : n % (7 * m + 10) = c at hdiv hlt
  generalize ha : n / (7 * m + 10) * (7 * m + 10) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 hq6 ht0 ht1 ht3
  subst hdiv
  have hmh : m + 1 = 2 * (16 * ((m + 1) / 32)) := by omega
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
                  · by_cases c5 : c ≤ 5 * m + 8 + m
                    · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (c - (5 * m + 8)) by omega] at hP
                      exact not_isP_of_row m _ (c - (5 * m + 8)) 0 hq5 (by omega) (by omega) (by omega) hP
                    · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (c - (6 * m + 9)) by omega] at hP
                      exact not_isP_of_row m _ (c - (6 * m + 9)) 0 hq6 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 5) = a + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) by omega]; exact hq5 0
    · rw [h, show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]; exact hq6 0

section K69g527

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 1024 = 527)
include hmu hu

theorem k69g527_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (7 * m + 10)) p) ∧
    Blk m 4 (a + (7 * m + 10)) ∧
    IsP m (a + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
  have hmh : m + 1 = 2 * (16 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 16 * u := by omega
  have hv4u : v2 (16 * u) = 4 := by
    rw [show 16 * u = 2 * (2 * (2 * (2 * u))) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 16 * u) (16 * u) := by
    have hv : v2 (16 * u) = 4 := by
      have : (16 * u) % 32 = 16 := by omega
      rw [v2_even (16 * u) (by omega) (by omega),
        v2_even (16 * u / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2 / 2) (by omega) (by omega),
        v2_odd (16 * u / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    have hv : v2 ((528 * u + 16) / 32) = 3 := by
      have : ((528 * u + 16) / 32) % 16 = 8 := by omega
      rw [v2_even ((528 * u + 16) / 32) (by omega) (by omega),
        v2_even ((528 * u + 16) / 32 / 2) (by omega) (by omega),
        v2_even ((528 * u + 16) / 32 / 2 / 2) (by omega) (by omega),
        v2_odd ((528 * u + 16) / 32 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have F5 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F4
  have F6 : IsP m (a + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F5
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F6)
  have F7 : IsP m (a + (8720 * u + 272) / 512) ((8720 * u + 272) / 512) := by
    have hv : v2 ((8720 * u + 272) / 512) = 4 := by
      have : ((8720 * u + 272) / 512) % 32 = 16 := by omega
      rw [v2_even ((8720 * u + 272) / 512) (by omega) (by omega),
        v2_even ((8720 * u + 272) / 512 / 2) (by omega) (by omega),
        v2_even ((8720 * u + 272) / 512 / 2 / 2) (by omega) (by omega),
        v2_even ((8720 * u + 272) / 512 / 2 / 2 / 2) (by omega) (by omega),
        v2_odd ((8720 * u + 272) / 512 / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F8 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 256) ((528 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((528 * u + 16) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 256) / 2 = (8720 * u + 272) / 512 by omega]; exact F7
  have F9 : IsP m (a + (m + 2) + (528 * u + 16) / 128) ((528 * u + 16) / 128) := by
    rw [show (528 * u + 16) / 128 = 2 * ((528 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((528 * u + 16) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F8
  have F10 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    rw [show (528 * u + 16) / 64 = 2 * ((528 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F9
  have F11 : IsP m (a + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F10
  have F12 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F11
  have F13 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F12
  have F14 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F13
  have F15 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F14
  have F16 : ¬ IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 2) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F15
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2)) hr2 (by rw [hh]; exact F16)
  have hb3 := blk1_direct m _ hr3 (odd_of_rows m _ hmo hr3 (Or.inr ⟨_, rfl, hr2⟩))
  have F17 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    have hv : v2 ((16 * u + 0) / 8) = 1 := by
      have : ((16 * u + 0) / 8) % 4 = 2 := by omega
      rw [v2_even ((16 * u + 0) / 8) (by omega) (by omega),
        v2_odd ((16 * u + 0) / 8 / 2) (by omega)]
    intro h; have := (hb3 _ (by omega) (by omega) (by omega)).mp h; omega
  have F18 : IsP m (a + (4752 * u + 144) / 256) ((4752 * u + 144) / 256) := by
    have hv : v2 ((4752 * u + 144) / 256) = 0 := by
      have : ((4752 * u + 144) / 256) % 2 = 1 := by omega
      rw [v2_odd ((4752 * u + 144) / 256) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F19 : ¬ IsP m (a + (m + 2) + (656 * u + 16) / 128) ((656 * u + 16) / 128) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((656 * u + 16) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (656 * u + 16) / 128) / 2 = (4752 * u + 144) / 256 by omega]; exact F18
  have F20 : IsP m (a + (m + 2) + (656 * u + 16) / 64) ((656 * u + 16) / 64) := by
    rw [show (656 * u + 16) / 64 = 2 * ((656 * u + 16) / 128) by omega]
    exact (o_half' m (16 * u) (a) ((656 * u + 16) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F19
  have F21 : ¬ IsP m (a + (m + 2) + (656 * u + 16) / 32) ((656 * u + 16) / 32) := by
    rw [show (656 * u + 16) / 32 = 2 * ((656 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((656 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F20
  have F22 : IsP m (a + (m + 2) + (m + 2) + (144 * u + 0) / 16) ((144 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((144 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (144 * u + 0) / 16) / 2 = (656 * u + 16) / 32 by omega]; exact F21
  have F23 : ¬ IsP m (a + (m + 2) + (m + 2) + (144 * u + 0) / 8) ((144 * u + 0) / 8) := by
    rw [show (144 * u + 0) / 8 = 2 * ((144 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((144 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (16 * u + 0) / 4 / 2 = (16 * u + 0) / 8 by omega]; exact F17
    · rw [show 16 * u + (16 * u + 0) / 4 / 2 = (144 * u + 0) / 8 by omega]; exact F23
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).1
    rw [show (16 * u + 0) / 2 / 2 = (16 * u + 0) / 4 by omega]; exact F24
  have F32 : IsP m (a + (1584 * u + 48) / 64) ((1584 * u + 48) / 64) := by
    have hv : v2 ((1584 * u + 48) / 64) = 2 := by
      have : ((1584 * u + 48) / 64) % 8 = 4 := by omega
      rw [v2_even ((1584 * u + 48) / 64) (by omega) (by omega),
        v2_even ((1584 * u + 48) / 64 / 2) (by omega) (by omega),
        v2_odd ((1584 * u + 48) / 64 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F33 : ¬ IsP m (a + (m + 2) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((560 * u + 16) / 32) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (560 * u + 16) / 32) / 2 = (1584 * u + 48) / 64 by omega]; exact F32
  have F34 : IsP m (a + (m + 2) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((48 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F33
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((48 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F34
  have F36 : IsP m (a + (m + 2) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((48 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F35
  have F37 : ¬ IsP m (a + (m + 2) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((48 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F36
  have F38 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2)) (16 * u) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show 16 * u / 2 = (16 * u + 0) / 2 by omega]; exact F31
    · rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F37
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) hr3 (by rw [hh]; exact F38)
  have F40 : ¬ IsP m (a + (76304 * u + 2320) / 4096) ((76304 * u + 2320) / 4096) := by
    have hv : v2 ((76304 * u + 2320) / 4096) = 1 := by
      have : ((76304 * u + 2320) / 4096) % 4 = 2 := by omega
      rw [v2_even ((76304 * u + 2320) / 4096) (by omega) (by omega),
        v2_odd ((76304 * u + 2320) / 4096 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F41 : IsP m (a + (m + 2) + (10768 * u + 272) / 2048) ((10768 * u + 272) / 2048) := by
    refine (o_odd_iff m (16 * u) (a) ((10768 * u + 272) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (10768 * u + 272) / 2048) / 2 = (76304 * u + 2320) / 4096 by omega]; exact F40
  have F42 : ¬ IsP m (a + (m + 2) + (10768 * u + 272) / 1024) ((10768 * u + 272) / 1024) := by
    rw [show (10768 * u + 272) / 1024 = 2 * ((10768 * u + 272) / 2048) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((10768 * u + 272) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F41
  have F43 : IsP m (a + (m + 2) + (10768 * u + 272) / 512) ((10768 * u + 272) / 512) := by
    rw [show (10768 * u + 272) / 512 = 2 * ((10768 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((10768 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F42
  have F44 : ¬ IsP m (a + (m + 2) + (m + 2) + (2576 * u + 16) / 256) ((2576 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((2576 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 16) / 256) / 2 = (10768 * u + 272) / 512 by omega]; exact F43
  have F45 : IsP m (a + (m + 2) + (m + 2) + (2576 * u + 16) / 128) ((2576 * u + 16) / 128) := by
    rw [show (2576 * u + 16) / 128 = 2 * ((2576 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((2576 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F44
  have F46 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (528 * u + 16) / 64 / 2 = (2576 * u + 16) / 128 by omega]; exact F45
  have F47 : IsP m (a + (42512 * u + 1296) / 2048) ((42512 * u + 1296) / 2048) := by
    have hv : v2 ((42512 * u + 1296) / 2048) = 2 := by
      have : ((42512 * u + 1296) / 2048) % 8 = 4 := by omega
      rw [v2_even ((42512 * u + 1296) / 2048) (by omega) (by omega),
        v2_even ((42512 * u + 1296) / 2048 / 2) (by omega) (by omega),
        v2_odd ((42512 * u + 1296) / 2048 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F48 : ¬ IsP m (a + (m + 2) + (9744 * u + 272) / 1024) ((9744 * u + 272) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((9744 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (9744 * u + 272) / 1024) / 2 = (42512 * u + 1296) / 2048 by omega]; exact F47
  have F49 : IsP m (a + (m + 2) + (9744 * u + 272) / 512) ((9744 * u + 272) / 512) := by
    rw [show (9744 * u + 272) / 512 = 2 * ((9744 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((9744 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F48
  have F50 : ¬ IsP m (a + (m + 2) + (m + 2) + (1552 * u + 16) / 256) ((1552 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((1552 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1552 * u + 16) / 256) / 2 = (9744 * u + 272) / 512 by omega]; exact F49
  have F51 : IsP m (a + (m + 2) + (m + 2) + (1552 * u + 16) / 128) ((1552 * u + 16) / 128) := by
    rw [show (1552 * u + 16) / 128 = 2 * ((1552 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((1552 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F50
  have F52 : ¬ IsP m (a + (m + 2) + (m + 2) + (1552 * u + 16) / 64) ((1552 * u + 16) / 64) := by
    rw [show (1552 * u + 16) / 64 = 2 * ((1552 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((1552 * u + 16) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F51
  have F53 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 32) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (528 * u + 16) / 32 / 2 = (528 * u + 16) / 64 by omega]; exact F46
    · rw [show 16 * u + (528 * u + 16) / 32 / 2 = (1552 * u + 16) / 64 by omega]; exact F52
  have F54 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F53
  have F55 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F54
  have F56 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 8) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F55
  have F57 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 4) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F56
  have F58 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 2) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F57
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F58)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F74 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    have hv : v2 ((560 * u + 16) / 32) = 0 := by
      have : ((560 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((560 * u + 16) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F75 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F74
  have F76 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F75
  have F77 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 8) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F76
  have F78 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 4) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F77
  have F79 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F78
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F79)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F90 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    have hv : v2 ((688 * u + 16) / 32) = 0 := by
      have : ((688 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((688 * u + 16) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F91 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((176 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F90
  have F92 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((176 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F91
  have F93 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((48 * u + 0) / 4) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F92
  have F94 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    have hv : v2 ((624 * u + 16) / 32) = 0 := by
      have : ((624 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((624 * u + 16) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F95 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F94
  have F96 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F95
  have F97 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 8) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F96
  have F98 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((48 * u + 0) / 2) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F93
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F97
  have F99 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) (16 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F98
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) hr6 (by rw [hh]; exact F99)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb5 hr6
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr6 hb3' hr7
  rw [show a + (7 * m + 10) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F6, F38⟩

theorem k69g527_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 10)) p) ∧ Blk m 4 (i * (7 * m + 10)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k69g527_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g527

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 527 (mod 1024)（1101000 型）：(n, 0) が P ⇔ n mod (7 * m + 10) が各行の始まり。-/
theorem K69_527 (m : Nat) (hm : (m + 1) % 32768 = 16864) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 10) = 0 ∨ n % (7 * m + 10) = 1 * m + 2 ∨ n % (7 * m + 10) = 2 * m + 4 ∨ n % (7 * m + 10) = 3 * m + 5 ∨ n % (7 * m + 10) = 4 * m + 7 ∨ n % (7 * m + 10) = 5 * m + 8 ∨ n % (7 * m + 10) = 6 * m + 9) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g527_rows m _ hmu (by omega) (n / (7 * m + 10))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3⟩ := k69g527_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (7 * m + 10)) * (7 * m + 10) + n % (7 * m + 10) := by
    have := Nat.div_add_mod n (7 * m + 10)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (7 * m + 10) < 7 * m + 10 := Nat.mod_lt n (by omega)
  generalize hcc : n % (7 * m + 10) = c at hdiv hlt
  generalize ha : n / (7 * m + 10) * (7 * m + 10) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 hq6 ht0 ht1 ht3
  subst hdiv
  have hmh : m + 1 = 2 * (16 * ((m + 1) / 32)) := by omega
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
                  · by_cases c5 : c ≤ 5 * m + 8 + m
                    · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (c - (5 * m + 8)) by omega] at hP
                      exact not_isP_of_row m _ (c - (5 * m + 8)) 0 hq5 (by omega) (by omega) (by omega) hP
                    · rw [show a + c = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (c - (6 * m + 9)) by omega] at hP
                      exact not_isP_of_row m _ (c - (6 * m + 9)) 0 hq6 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 5) = a + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) by omega]; exact hq5 0
    · rw [h, show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]; exact hq6 0

section K69g555

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 1024 = 555)
include hmu hu

theorem k69g555_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (6 * m + 9)) p) ∧
    Blk m 4 (a + (6 * m + 9)) ∧
    IsP m (a + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
  have hmh : m + 1 = 2 * (16 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 16 * u := by omega
  have hv4u : v2 (16 * u) = 4 := by
    rw [show 16 * u = 2 * (2 * (2 * (2 * u))) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 16 * u) (16 * u) := by
    have hv : v2 (16 * u) = 4 := by
      have : (16 * u) % 32 = 16 := by omega
      rw [v2_even (16 * u) (by omega) (by omega),
        v2_even (16 * u / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2 / 2) (by omega) (by omega),
        v2_odd (16 * u / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    have hv : v2 ((528 * u + 16) / 32) = 1 := by
      have : ((528 * u + 16) / 32) % 4 = 2 := by omega
      rw [v2_even ((528 * u + 16) / 32) (by omega) (by omega),
        v2_odd ((528 * u + 16) / 32 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have F5 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F4
  have F6 : IsP m (a + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F5
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F6)
  have F7 : ¬ IsP m (a + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    have hv : v2 ((2576 * u + 80) / 128) = 1 := by
      have : ((2576 * u + 80) / 128) % 4 = 2 := by omega
      rw [v2_even ((2576 * u + 80) / 128) (by omega) (by omega),
        v2_odd ((2576 * u + 80) / 128 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F8 : IsP m (a + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    refine (o_odd_iff m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F7
  have F9 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F9
  have F11 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F10
  have F12 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F11
  have F13 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 2) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F13
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F14)
  have F15 : IsP m (a + (10768 * u + 336) / 512) ((10768 * u + 336) / 512) := by
    have hv : v2 ((10768 * u + 336) / 512) = 0 := by
      have : ((10768 * u + 336) / 512) % 2 = 1 := by omega
      rw [v2_odd ((10768 * u + 336) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F16 : ¬ IsP m (a + (m + 2) + (2576 * u + 80) / 256) ((2576 * u + 80) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 80) / 256) / 2 = (10768 * u + 336) / 512 by omega]; exact F15
  have F17 : IsP m (a + (m + 2) + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    rw [show (2576 * u + 80) / 128 = 2 * ((2576 * u + 80) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F16
  have F18 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F17
  have F19 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F18
  have F20 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F19
  have F21 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F20
  have F22 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F21
  have F23 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F23
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hr3 (by rw [hh]; exact F24)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F44 : IsP m (a + (3632 * u + 112) / 128) ((3632 * u + 112) / 128) := by
    have hv : v2 ((3632 * u + 112) / 128) = 0 := by
      have : ((3632 * u + 112) / 128) % 2 = 1 := by omega
      rw [v2_odd ((3632 * u + 112) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F45 : ¬ IsP m (a + (m + 2) + (1584 * u + 48) / 64) ((1584 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1584 * u + 48) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1584 * u + 48) / 64) / 2 = (3632 * u + 112) / 128 by omega]; exact F44
  have F46 : IsP m (a + (m + 2) + (m + 2) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((560 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (560 * u + 16) / 32) / 2 = (1584 * u + 48) / 64 by omega]; exact F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F46
  have F48 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) (16 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F50
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F51)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F67 : IsP m (a + (3760 * u + 112) / 128) ((3760 * u + 112) / 128) := by
    have hv : v2 ((3760 * u + 112) / 128) = 4 := by
      have : ((3760 * u + 112) / 128) % 32 = 16 := by omega
      rw [v2_even ((3760 * u + 112) / 128) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2 / 2) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2 / 2 / 2) (by omega) (by omega),
        v2_odd ((3760 * u + 112) / 128 / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F68 : ¬ IsP m (a + (m + 2) + (1712 * u + 48) / 64) ((1712 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1712 * u + 48) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1712 * u + 48) / 64) / 2 = (3760 * u + 112) / 128 by omega]; exact F67
  have F69 : IsP m (a + (m + 2) + (m + 2) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((688 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (688 * u + 16) / 32) / 2 = (1712 * u + 48) / 64 by omega]; exact F68
  have F70 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F69
  have F71 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F70
  have F72 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F71
  have F73 : IsP m (a + (9840 * u + 304) / 512) ((9840 * u + 304) / 512) := by
    have hv : v2 ((9840 * u + 304) / 512) = 0 := by
      have : ((9840 * u + 304) / 512) % 2 = 1 := by omega
      rw [v2_odd ((9840 * u + 304) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F74 : ¬ IsP m (a + (m + 2) + (1648 * u + 48) / 256) ((1648 * u + 48) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1648 * u + 48) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1648 * u + 48) / 256) / 2 = (9840 * u + 304) / 512 by omega]; exact F73
  have F75 : IsP m (a + (m + 2) + (1648 * u + 48) / 128) ((1648 * u + 48) / 128) := by
    rw [show (1648 * u + 48) / 128 = 2 * ((1648 * u + 48) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((1648 * u + 48) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F74
  have F76 : ¬ IsP m (a + (m + 2) + (1648 * u + 48) / 64) ((1648 * u + 48) / 64) := by
    rw [show (1648 * u + 48) / 64 = 2 * ((1648 * u + 48) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((1648 * u + 48) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F75
  have F77 : IsP m (a + (m + 2) + (m + 2) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((624 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (624 * u + 16) / 32) / 2 = (1648 * u + 48) / 64 by omega]; exact F76
  have F78 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F77
  have F79 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F78
  have F80 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F79
  have F81 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 2) hmh hr3 hr4 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F72
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F80
  have F82 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F81
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hr5 (by rw [hh]; exact F82)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr4 hb4 hr5
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb3' hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F6, F14⟩

theorem k69g555_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 4 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k69g555_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g555

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 555 (mod 1024)（111000 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K69_555 (m : Nat) (hm : (m + 1) % 32768 = 17760) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 6 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g555_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht2⟩ := k69g555_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (6 * m + 9)) * (6 * m + 9) + n % (6 * m + 9) := by
    have := Nat.div_add_mod n (6 * m + 9)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (6 * m + 9) < 6 * m + 9 := Nat.mod_lt n (by omega)
  generalize hcc : n % (6 * m + 9) = c at hdiv hlt
  generalize ha : n / (6 * m + 9) * (6 * m + 9) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 ht0 ht1 ht2
  subst hdiv
  have hmh : m + 1 = 2 * (16 * ((m + 1) / 32)) := by omega
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
                · by_cases c4 : c ≤ 4 * m + 7 + m
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (4 * m + 7)) by omega] at hP
                    exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (c - (5 * m + 8)) by omega] at hP
                    exact not_isP_of_row m _ (c - (5 * m + 8)) 0 hq5 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]; exact hq5 0

section K69g811

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 1024 = 811)
include hmu hu

theorem k69g811_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (6 * m + 9)) p) ∧
    Blk m 4 (a + (6 * m + 9)) ∧
    IsP m (a + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
  have hmh : m + 1 = 2 * (16 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 16 * u := by omega
  have hv4u : v2 (16 * u) = 4 := by
    rw [show 16 * u = 2 * (2 * (2 * (2 * u))) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 16 * u) (16 * u) := by
    have hv : v2 (16 * u) = 4 := by
      have : (16 * u) % 32 = 16 := by omega
      rw [v2_even (16 * u) (by omega) (by omega),
        v2_even (16 * u / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2 / 2) (by omega) (by omega),
        v2_odd (16 * u / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    have hv : v2 ((528 * u + 16) / 32) = 1 := by
      have : ((528 * u + 16) / 32) % 4 = 2 := by omega
      rw [v2_even ((528 * u + 16) / 32) (by omega) (by omega),
        v2_odd ((528 * u + 16) / 32 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have F5 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F4
  have F6 : IsP m (a + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F5
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F6)
  have F7 : ¬ IsP m (a + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    have hv : v2 ((2576 * u + 80) / 128) = 1 := by
      have : ((2576 * u + 80) / 128) % 4 = 2 := by omega
      rw [v2_even ((2576 * u + 80) / 128) (by omega) (by omega),
        v2_odd ((2576 * u + 80) / 128 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F8 : IsP m (a + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    refine (o_odd_iff m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F7
  have F9 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F9
  have F11 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F10
  have F12 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F11
  have F13 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 2) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F13
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F14)
  have F15 : IsP m (a + (10768 * u + 336) / 512) ((10768 * u + 336) / 512) := by
    have hv : v2 ((10768 * u + 336) / 512) = 0 := by
      have : ((10768 * u + 336) / 512) % 2 = 1 := by omega
      rw [v2_odd ((10768 * u + 336) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F16 : ¬ IsP m (a + (m + 2) + (2576 * u + 80) / 256) ((2576 * u + 80) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 80) / 256) / 2 = (10768 * u + 336) / 512 by omega]; exact F15
  have F17 : IsP m (a + (m + 2) + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    rw [show (2576 * u + 80) / 128 = 2 * ((2576 * u + 80) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F16
  have F18 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F17
  have F19 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F18
  have F20 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F19
  have F21 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F20
  have F22 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F21
  have F23 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F22
  have F24 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F23
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hr3 (by rw [hh]; exact F24)
  have hb4 := blk1_direct m _ hr4 (odd_of_rows m _ hmo hr4 (Or.inr ⟨_, rfl, hr3⟩))
  have F44 : IsP m (a + (3632 * u + 112) / 128) ((3632 * u + 112) / 128) := by
    have hv : v2 ((3632 * u + 112) / 128) = 0 := by
      have : ((3632 * u + 112) / 128) % 2 = 1 := by omega
      rw [v2_odd ((3632 * u + 112) / 128) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F45 : ¬ IsP m (a + (m + 2) + (1584 * u + 48) / 64) ((1584 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1584 * u + 48) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1584 * u + 48) / 64) / 2 = (3632 * u + 112) / 128 by omega]; exact F44
  have F46 : IsP m (a + (m + 2) + (m + 2) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((560 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (560 * u + 16) / 32) / 2 = (1584 * u + 48) / 64 by omega]; exact F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F46
  have F48 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) (16 * u) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F50
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr4 (by rw [hh]; exact F51)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F67 : IsP m (a + (3760 * u + 112) / 128) ((3760 * u + 112) / 128) := by
    have hv : v2 ((3760 * u + 112) / 128) = 4 := by
      have : ((3760 * u + 112) / 128) % 32 = 16 := by omega
      rw [v2_even ((3760 * u + 112) / 128) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2 / 2) (by omega) (by omega),
        v2_even ((3760 * u + 112) / 128 / 2 / 2 / 2) (by omega) (by omega),
        v2_odd ((3760 * u + 112) / 128 / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F68 : ¬ IsP m (a + (m + 2) + (1712 * u + 48) / 64) ((1712 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1712 * u + 48) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1712 * u + 48) / 64) / 2 = (3760 * u + 112) / 128 by omega]; exact F67
  have F69 : IsP m (a + (m + 2) + (m + 2) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((688 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (688 * u + 16) / 32) / 2 = (1712 * u + 48) / 64 by omega]; exact F68
  have F70 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F69
  have F71 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F70
  have F72 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr3 hr4 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F71
  have F73 : IsP m (a + (9840 * u + 304) / 512) ((9840 * u + 304) / 512) := by
    have hv : v2 ((9840 * u + 304) / 512) = 0 := by
      have : ((9840 * u + 304) / 512) % 2 = 1 := by omega
      rw [v2_odd ((9840 * u + 304) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F74 : ¬ IsP m (a + (m + 2) + (1648 * u + 48) / 256) ((1648 * u + 48) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((1648 * u + 48) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1648 * u + 48) / 256) / 2 = (9840 * u + 304) / 512 by omega]; exact F73
  have F75 : IsP m (a + (m + 2) + (1648 * u + 48) / 128) ((1648 * u + 48) / 128) := by
    rw [show (1648 * u + 48) / 128 = 2 * ((1648 * u + 48) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((1648 * u + 48) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F74
  have F76 : ¬ IsP m (a + (m + 2) + (1648 * u + 48) / 64) ((1648 * u + 48) / 64) := by
    rw [show (1648 * u + 48) / 64 = 2 * ((1648 * u + 48) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((1648 * u + 48) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F75
  have F77 : IsP m (a + (m + 2) + (m + 2) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((624 * u + 16) / 32) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (624 * u + 16) / 32) / 2 = (1648 * u + 48) / 64 by omega]; exact F76
  have F78 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F77
  have F79 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F78
  have F80 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((112 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F79
  have F81 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 2) hmh hr3 hr4 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F72
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F80
  have F82 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F81
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hr5 (by rw [hh]; exact F82)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr4 hb4 hr5
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb3' hr6
  rw [show a + (6 * m + 9) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hblk', F0, F6, F14⟩

theorem k69g811_rows : ∀ i, (∀ p, IsP m (i * (6 * m + 9)) p) ∧ Blk m 4 (i * (6 * m + 9)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, ha, hb, _⟩ := k69g811_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g811

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 811 (mod 1024)（111000 型）：(n, 0) が P ⇔ n mod (6 * m + 9) が各行の始まり。-/
theorem K69_811 (m : Nat) (hm : (m + 1) % 32768 = 25952) (n : Nat) :
    IsP m n 0 ↔ (n % (6 * m + 9) = 0 ∨ n % (6 * m + 9) = 1 * m + 2 ∨ n % (6 * m + 9) = 2 * m + 4 ∨ n % (6 * m + 9) = 3 * m + 6 ∨ n % (6 * m + 9) = 4 * m + 7 ∨ n % (6 * m + 9) = 5 * m + 8) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g811_rows m _ hmu (by omega) (n / (6 * m + 9))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, _, _, ht0, ht1, ht2⟩ := k69g811_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (6 * m + 9)) * (6 * m + 9) + n % (6 * m + 9) := by
    have := Nat.div_add_mod n (6 * m + 9)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (6 * m + 9) < 6 * m + 9 := Nat.mod_lt n (by omega)
  generalize hcc : n % (6 * m + 9) = c at hdiv hlt
  generalize ha : n / (6 * m + 9) * (6 * m + 9) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 ht0 ht1 ht2
  subst hdiv
  have hmh : m + 1 = 2 * (16 * ((m + 1) / 32)) := by omega
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
                · by_cases c4 : c ≤ 4 * m + 7 + m
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (4 * m + 7)) by omega] at hP
                    exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hq4 (by omega) (by omega) (by omega) hP
                  · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (c - (5 * m + 8)) by omega] at hP
                    exact not_isP_of_row m _ (c - (5 * m + 8)) 0 hq5 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]; exact hq5 0

section K69g843

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 1024 = 843)
include hmu hu

theorem k69g843_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (7 * m + 11)) p) ∧
    Blk m 4 (a + (7 * m + 11)) ∧
    IsP m (a + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
  have hmh : m + 1 = 2 * (16 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 16 * u := by omega
  have hv4u : v2 (16 * u) = 4 := by
    rw [show 16 * u = 2 * (2 * (2 * (2 * u))) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hr0 := hrow
  have F0 : IsP m (a + 16 * u) (16 * u) := by
    have hv : v2 (16 * u) = 4 := by
      have : (16 * u) % 32 = 16 := by omega
      rw [v2_even (16 * u) (by omega) (by omega),
        v2_even (16 * u / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2) (by omega) (by omega),
        v2_even (16 * u / 2 / 2 / 2) (by omega) (by omega),
        v2_odd (16 * u / 2 / 2 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hr1 : ∀ p, IsP m (a + (m + 2)) p := row_long m (a) hmo (by omega) hr0 (by rw [hh]; exact F0)
  have F1 : ¬ IsP m (a + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    have hv : v2 ((528 * u + 16) / 32) = 1 := by
      have : ((528 * u + 16) / 32) % 4 = 2 := by omega
      rw [v2_even ((528 * u + 16) / 32) (by omega) (by omega),
        v2_odd ((528 * u + 16) / 32 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F2 : IsP m (a + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F1
  have F3 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 16) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F2
  have F4 : IsP m (a + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 8) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F3
  have F5 : ¬ IsP m (a + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((16 * u + 0) / 4) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F4
  have F6 : IsP m (a + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a) ((16 * u + 0) / 2) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F5
  have hr2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m (a + (m + 2)) hmo (by omega) hr1 (by rw [hh]; exact F6)
  have F7 : ¬ IsP m (a + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    have hv : v2 ((2576 * u + 80) / 128) = 1 := by
      have : ((2576 * u + 80) / 128) % 4 = 2 := by omega
      rw [v2_even ((2576 * u + 80) / 128) (by omega) (by omega),
        v2_odd ((2576 * u + 80) / 128 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F8 : IsP m (a + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    refine (o_odd_iff m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F7
  have F9 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F9
  have F11 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F10
  have F12 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F11
  have F13 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 2) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F13
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F14)
  have F15 : ¬ IsP m (a + (10768 * u + 336) / 512) ((10768 * u + 336) / 512) := by
    have hv : v2 ((10768 * u + 336) / 512) = 1 := by
      have : ((10768 * u + 336) / 512) % 4 = 2 := by omega
      rw [v2_even ((10768 * u + 336) / 512) (by omega) (by omega),
        v2_odd ((10768 * u + 336) / 512 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F16 : IsP m (a + (m + 2) + (2576 * u + 80) / 256) ((2576 * u + 80) / 256) := by
    refine (o_odd_iff m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (2576 * u + 80) / 256) / 2 = (10768 * u + 336) / 512 by omega]; exact F15
  have F17 : ¬ IsP m (a + (m + 2) + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    rw [show (2576 * u + 80) / 128 = 2 * ((2576 * u + 80) / 256) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((2576 * u + 80) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F16
  have F18 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F17
  have F19 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F18
  have F20 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F19
  have F21 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F20
  have F22 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F23
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 2)) hmo (by omega) hr3 (by rw [hh]; exact F24)
  have F25 : IsP m (a + (43536 * u + 1360) / 2048) ((43536 * u + 1360) / 2048) := by
    have hv : v2 ((43536 * u + 1360) / 2048) = 0 := by
      have : ((43536 * u + 1360) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((43536 * u + 1360) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F26 : ¬ IsP m (a + (m + 2) + (10768 * u + 336) / 1024) ((10768 * u + 336) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((10768 * u + 336) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (10768 * u + 336) / 1024) / 2 = (43536 * u + 1360) / 2048 by omega]; exact F25
  have F27 : IsP m (a + (m + 2) + (10768 * u + 336) / 512) ((10768 * u + 336) / 512) := by
    rw [show (10768 * u + 336) / 512 = 2 * ((10768 * u + 336) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((10768 * u + 336) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F26
  have F28 : ¬ IsP m (a + (m + 2) + (m + 2) + (2576 * u + 80) / 256) ((2576 * u + 80) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((2576 * u + 80) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 80) / 256) / 2 = (10768 * u + 336) / 512 by omega]; exact F27
  have F29 : IsP m (a + (m + 2) + (m + 2) + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    rw [show (2576 * u + 80) / 128 = 2 * ((2576 * u + 80) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((2576 * u + 80) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F28
  have F30 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F29
  have F31 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr3 hr4 F24 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mpr F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mp h F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mpr F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mp h F35
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hr4 (by rw [hh]; exact F36)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F38 : IsP m (a + (14992 * u + 464) / 512) ((14992 * u + 464) / 512) := by
    have hv : v2 ((14992 * u + 464) / 512) = 0 := by
      have : ((14992 * u + 464) / 512) % 2 = 1 := by omega
      rw [v2_odd ((14992 * u + 464) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F39 : ¬ IsP m (a + (m + 2) + (6800 * u + 208) / 256) ((6800 * u + 208) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((6800 * u + 208) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (6800 * u + 208) / 256) / 2 = (14992 * u + 464) / 512 by omega]; exact F38
  have F40 : IsP m (a + (m + 2) + (m + 2) + (2704 * u + 80) / 128) ((2704 * u + 80) / 128) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((2704 * u + 80) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (2704 * u + 80) / 128) / 2 = (6800 * u + 208) / 256 by omega]; exact F39
  have F41 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (656 * u + 16) / 64) ((656 * u + 16) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((656 * u + 16) / 64) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (656 * u + 16) / 64) / 2 = (2704 * u + 80) / 128 by omega]; exact F40
  have F42 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (656 * u + 16) / 32) ((656 * u + 16) / 32) := by
    rw [show (656 * u + 16) / 32 = 2 * ((656 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((656 * u + 16) / 64) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F41
  have F43 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (144 * u + 0) / 16) ((144 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((144 * u + 0) / 16) hmh hr3 hr4 F24 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (144 * u + 0) / 16) / 2 = (656 * u + 16) / 32 by omega]; exact F42
  have F44 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (144 * u + 0) / 8) ((144 * u + 0) / 8) := by
    rw [show (144 * u + 0) / 8 = 2 * ((144 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((144 * u + 0) / 16) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mpr F43
  have F45 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (16 * u + 0) / 4 / 2 = (144 * u + 0) / 8 by omega]; exact F44
  have F46 : IsP m (a + (152144 * u + 4752) / 8192) ((152144 * u + 4752) / 8192) := by
    have hv : v2 ((152144 * u + 4752) / 8192) = 0 := by
      have : ((152144 * u + 4752) / 8192) % 2 = 1 := by omega
      rw [v2_odd ((152144 * u + 4752) / 8192) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F47 : ¬ IsP m (a + (m + 2) + (21072 * u + 656) / 4096) ((21072 * u + 656) / 4096) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((21072 * u + 656) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (21072 * u + 656) / 4096) / 2 = (152144 * u + 4752) / 8192 by omega]; exact F46
  have F48 : IsP m (a + (m + 2) + (21072 * u + 656) / 2048) ((21072 * u + 656) / 2048) := by
    rw [show (21072 * u + 656) / 2048 = 2 * ((21072 * u + 656) / 4096) by omega]
    exact (o_half' m (16 * u) (a) ((21072 * u + 656) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F47
  have F49 : ¬ IsP m (a + (m + 2) + (21072 * u + 656) / 1024) ((21072 * u + 656) / 1024) := by
    rw [show (21072 * u + 656) / 1024 = 2 * ((21072 * u + 656) / 2048) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((21072 * u + 656) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (4688 * u + 144) / 512) ((4688 * u + 144) / 512) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((4688 * u + 144) / 512) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (4688 * u + 144) / 512) / 2 = (21072 * u + 656) / 1024 by omega]; exact F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (4688 * u + 144) / 256) ((4688 * u + 144) / 256) := by
    rw [show (4688 * u + 144) / 256 = 2 * ((4688 * u + 144) / 512) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((4688 * u + 144) / 512) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F50
  have F52 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (592 * u + 16) / 128) ((592 * u + 16) / 128) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((592 * u + 16) / 128) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (592 * u + 16) / 128) / 2 = (4688 * u + 144) / 256 by omega]; exact F51
  have F53 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (592 * u + 16) / 64) ((592 * u + 16) / 64) := by
    rw [show (592 * u + 16) / 64 = 2 * ((592 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((592 * u + 16) / 128) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F52
  have F54 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (592 * u + 16) / 32) ((592 * u + 16) / 32) := by
    rw [show (592 * u + 16) / 32 = 2 * ((592 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((592 * u + 16) / 64) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F53
  have F55 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (80 * u + 0) / 16) ((80 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((80 * u + 0) / 16) hmh hr3 hr4 F24 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (80 * u + 0) / 16) / 2 = (592 * u + 16) / 32 by omega]; exact F54
  have F56 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (80 * u + 0) / 8) ((80 * u + 0) / 8) := by
    rw [show (80 * u + 0) / 8 = 2 * ((80 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((80 * u + 0) / 16) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mpr F55
  have F57 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (80 * u + 0) / 4) ((80 * u + 0) / 4) := by
    rw [show (80 * u + 0) / 4 = 2 * ((80 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((80 * u + 0) / 8) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mp h F56
  have F58 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (16 * u + 0) / 2 / 2 = (16 * u + 0) / 4 by omega]; exact F45
    · rw [show 16 * u + (16 * u + 0) / 2 / 2 = (80 * u + 0) / 4 by omega]; exact F57
  have F67 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).1
    rw [show 16 * u / 2 = (16 * u + 0) / 2 by omega]; exact F58
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F67)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F85 : ¬ IsP m (a + (20144 * u + 624) / 1024) ((20144 * u + 624) / 1024) := by
    have hv : v2 ((20144 * u + 624) / 1024) = 3 := by
      have : ((20144 * u + 624) / 1024) % 16 = 8 := by omega
      rw [v2_even ((20144 * u + 624) / 1024) (by omega) (by omega),
        v2_even ((20144 * u + 624) / 1024 / 2) (by omega) (by omega),
        v2_even ((20144 * u + 624) / 1024 / 2 / 2) (by omega) (by omega),
        v2_odd ((20144 * u + 624) / 1024 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F86 : IsP m (a + (m + 2) + (3760 * u + 112) / 512) ((3760 * u + 112) / 512) := by
    refine (o_odd_iff m (16 * u) (a) ((3760 * u + 112) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (3760 * u + 112) / 512) / 2 = (20144 * u + 624) / 1024 by omega]; exact F85
  have F87 : ¬ IsP m (a + (m + 2) + (3760 * u + 112) / 256) ((3760 * u + 112) / 256) := by
    rw [show (3760 * u + 112) / 256 = 2 * ((3760 * u + 112) / 512) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((3760 * u + 112) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F86
  have F88 : IsP m (a + (m + 2) + (3760 * u + 112) / 128) ((3760 * u + 112) / 128) := by
    rw [show (3760 * u + 112) / 128 = 2 * ((3760 * u + 112) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((3760 * u + 112) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F87
  have F89 : ¬ IsP m (a + (m + 2) + (m + 2) + (1712 * u + 48) / 64) ((1712 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((1712 * u + 48) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1712 * u + 48) / 64) / 2 = (3760 * u + 112) / 128 by omega]; exact F88
  have F90 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((688 * u + 16) / 32) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (688 * u + 16) / 32) / 2 = (1712 * u + 48) / 64 by omega]; exact F89
  have F91 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr3 hr4 F24 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F90
  have F92 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mpr F91
  have F93 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F92
  have F94 : IsP m (a + (42608 * u + 1328) / 2048) ((42608 * u + 1328) / 2048) := by
    have hv : v2 ((42608 * u + 1328) / 2048) = 0 := by
      have : ((42608 * u + 1328) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((42608 * u + 1328) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F95 : ¬ IsP m (a + (m + 2) + (9840 * u + 304) / 1024) ((9840 * u + 304) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((9840 * u + 304) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (9840 * u + 304) / 1024) / 2 = (42608 * u + 1328) / 2048 by omega]; exact F94
  have F96 : IsP m (a + (m + 2) + (9840 * u + 304) / 512) ((9840 * u + 304) / 512) := by
    rw [show (9840 * u + 304) / 512 = 2 * ((9840 * u + 304) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((9840 * u + 304) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F95
  have F97 : ¬ IsP m (a + (m + 2) + (m + 2) + (1648 * u + 48) / 256) ((1648 * u + 48) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((1648 * u + 48) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1648 * u + 48) / 256) / 2 = (9840 * u + 304) / 512 by omega]; exact F96
  have F98 : IsP m (a + (m + 2) + (m + 2) + (1648 * u + 48) / 128) ((1648 * u + 48) / 128) := by
    rw [show (1648 * u + 48) / 128 = 2 * ((1648 * u + 48) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((1648 * u + 48) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F97
  have F99 : ¬ IsP m (a + (m + 2) + (m + 2) + (1648 * u + 48) / 64) ((1648 * u + 48) / 64) := by
    rw [show (1648 * u + 48) / 64 = 2 * ((1648 * u + 48) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((1648 * u + 48) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F98
  have F100 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((624 * u + 16) / 32) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (624 * u + 16) / 32) / 2 = (1648 * u + 48) / 64 by omega]; exact F99
  have F101 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr3 hr4 F24 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F100
  have F102 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mpr F101
  have F103 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((112 * u + 0) / 8) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mp h F102
  have F104 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 2) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F93
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F103
  have F105 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) (16 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F104
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hr6 (by rw [hh]; exact F105)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb5 hr6
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr6 hb3' hr7
  rw [show a + (7 * m + 11) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F6, F14, F24⟩

theorem k69g843_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 11)) p) ∧ Blk m 4 (i * (7 * m + 11)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k69g843_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g843

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 843 (mod 1024)（1111000 型）：(n, 0) が P ⇔ n mod (7 * m + 11) が各行の始まり。-/
theorem K69_843 (m : Nat) (hm : (m + 1) % 32768 = 26976) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 11) = 0 ∨ n % (7 * m + 11) = 1 * m + 2 ∨ n % (7 * m + 11) = 2 * m + 4 ∨ n % (7 * m + 11) = 3 * m + 6 ∨ n % (7 * m + 11) = 4 * m + 8 ∨ n % (7 * m + 11) = 5 * m + 9 ∨ n % (7 * m + 11) = 6 * m + 10) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g843_rows m _ hmu (by omega) (n / (7 * m + 11))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht2, ht3⟩ := k69g843_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (7 * m + 11)) * (7 * m + 11) + n % (7 * m + 11) := by
    have := Nat.div_add_mod n (7 * m + 11)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (7 * m + 11) < 7 * m + 11 := Nat.mod_lt n (by omega)
  generalize hcc : n % (7 * m + 11) = c at hdiv hlt
  generalize ha : n / (7 * m + 11) * (7 * m + 11) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 hq6 ht0 ht1 ht2 ht3
  subst hdiv
  have hmh : m + 1 = 2 * (16 * ((m + 1) / 32)) := by omega
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
                      · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (c - (6 * m + 10)) by omega] at hP
                        exact not_isP_of_row m _ (c - (6 * m + 10)) 0 hq6 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 9) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq5 0
    · rw [h, show a + (6 * m + 10) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]; exact hq6 0

end Rubidium
