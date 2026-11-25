/-
  Rubidium.K69b1 — v2(m+1) = 5（m + 1 = 32u）の類（u mod 4096）の型の証明（code/k69_gen.js で生成、code/k69_search.js 4096 の結果のうち K69a にない類の第 1 組）

  証明の方法は K69a と同じ（始まりの行の不変量 Blk m 4）。
-/
import Rubidium.K67b

namespace Rubidium

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

section K69g971

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 4096 = 971)
include hmu hu

theorem k69g971_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (8 * m + 13)) p) ∧
    Blk m 4 (a + (8 * m + 13)) ∧
    IsP m (a + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
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
  have F25 : ¬ IsP m (a + (43536 * u + 1360) / 2048) ((43536 * u + 1360) / 2048) := by
    have hv : v2 ((43536 * u + 1360) / 2048) = 1 := by
      have : ((43536 * u + 1360) / 2048) % 4 = 2 := by omega
      rw [v2_even ((43536 * u + 1360) / 2048) (by omega) (by omega),
        v2_odd ((43536 * u + 1360) / 2048 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F26 : IsP m (a + (m + 2) + (10768 * u + 336) / 1024) ((10768 * u + 336) / 1024) := by
    refine (o_odd_iff m (16 * u) (a) ((10768 * u + 336) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (10768 * u + 336) / 1024) / 2 = (43536 * u + 1360) / 2048 by omega]; exact F25
  have F27 : ¬ IsP m (a + (m + 2) + (10768 * u + 336) / 512) ((10768 * u + 336) / 512) := by
    rw [show (10768 * u + 336) / 512 = 2 * ((10768 * u + 336) / 1024) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((10768 * u + 336) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (2576 * u + 80) / 256) ((2576 * u + 80) / 256) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((2576 * u + 80) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (2576 * u + 80) / 256) / 2 = (10768 * u + 336) / 512 by omega]; exact F27
  have F29 : ¬ IsP m (a + (m + 2) + (m + 2) + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    rw [show (2576 * u + 80) / 128 = 2 * ((2576 * u + 80) / 256) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((2576 * u + 80) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F28
  have F30 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F29
  have F31 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F30
  have F32 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr3 hr4 F24 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F31
  have F33 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mp h F32
  have F34 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mpr F33
  have F35 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mp h F34
  have F36 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mpr F35
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hmo (by omega) hr4 (by rw [hh]; exact F36)
  have F37 : IsP m (a + (174608 * u + 5456) / 8192) ((174608 * u + 5456) / 8192) := by
    have hv : v2 ((174608 * u + 5456) / 8192) = 0 := by
      have : ((174608 * u + 5456) / 8192) % 2 = 1 := by omega
      rw [v2_odd ((174608 * u + 5456) / 8192) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F38 : ¬ IsP m (a + (m + 2) + (43536 * u + 1360) / 4096) ((43536 * u + 1360) / 4096) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((43536 * u + 1360) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (43536 * u + 1360) / 4096) / 2 = (174608 * u + 5456) / 8192 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (43536 * u + 1360) / 2048) ((43536 * u + 1360) / 2048) := by
    rw [show (43536 * u + 1360) / 2048 = 2 * ((43536 * u + 1360) / 4096) by omega]
    exact (o_half' m (16 * u) (a) ((43536 * u + 1360) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (10768 * u + 336) / 1024) ((10768 * u + 336) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((10768 * u + 336) / 1024) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (10768 * u + 336) / 1024) / 2 = (43536 * u + 1360) / 2048 by omega]; exact F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (10768 * u + 336) / 512) ((10768 * u + 336) / 512) := by
    rw [show (10768 * u + 336) / 512 = 2 * ((10768 * u + 336) / 1024) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((10768 * u + 336) / 1024) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (2576 * u + 80) / 256) ((2576 * u + 80) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((2576 * u + 80) / 256) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 80) / 256) / 2 = (10768 * u + 336) / 512 by omega]; exact F41
  have F43 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (2576 * u + 80) / 128) ((2576 * u + 80) / 128) := by
    rw [show (2576 * u + 80) / 128 = 2 * ((2576 * u + 80) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((2576 * u + 80) / 256) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F42
  have F44 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr3 hr4 F24 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 64) / 2 = (2576 * u + 80) / 128 by omega]; exact F43
  have F45 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr3 hr4 F24 (by omega) (by omega) (by omega)).mpr F44
  have F46 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr4 hr5 F36 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F45
  have F47 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mpr F46
  have F48 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mp h F47
  have F49 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mpr F48
  have F50 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mp h F49
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hr5 (by rw [hh]; exact F50)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F76 : IsP m (a + (15920 * u + 496) / 512) ((15920 * u + 496) / 512) := by
    have hv : v2 ((15920 * u + 496) / 512) = 0 := by
      have : ((15920 * u + 496) / 512) % 2 = 1 := by omega
      rw [v2_odd ((15920 * u + 496) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F77 : ¬ IsP m (a + (m + 2) + (7728 * u + 240) / 256) ((7728 * u + 240) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((7728 * u + 240) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (7728 * u + 240) / 256) / 2 = (15920 * u + 496) / 512 by omega]; exact F76
  have F78 : IsP m (a + (m + 2) + (m + 2) + (3632 * u + 112) / 128) ((3632 * u + 112) / 128) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((3632 * u + 112) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (3632 * u + 112) / 128) / 2 = (7728 * u + 240) / 256 by omega]; exact F77
  have F79 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (1584 * u + 48) / 64) ((1584 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((1584 * u + 48) / 64) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1584 * u + 48) / 64) / 2 = (3632 * u + 112) / 128 by omega]; exact F78
  have F80 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((560 * u + 16) / 32) hmh hr3 hr4 F24 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (560 * u + 16) / 32) / 2 = (1584 * u + 48) / 64 by omega]; exact F79
  have F81 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr4 hr5 F36 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F80
  have F82 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mpr F81
  have F83 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 8) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mp h F82
  have F84 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mpr F83
  have F85 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) (16 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F84
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr6 (by rw [hh]; exact F85)
  have hb7 := blk1_direct m _ hr7 (odd_of_rows m _ hmo hr7 (Or.inr ⟨_, rfl, hr6⟩))
  have F105 : ¬ IsP m (a + (85680 * u + 2672) / 4096) ((85680 * u + 2672) / 4096) := by
    have hv : v2 ((85680 * u + 2672) / 4096) = 3 := by
      have : ((85680 * u + 2672) / 4096) % 16 = 8 := by omega
      rw [v2_even ((85680 * u + 2672) / 4096) (by omega) (by omega),
        v2_even ((85680 * u + 2672) / 4096 / 2) (by omega) (by omega),
        v2_even ((85680 * u + 2672) / 4096 / 2 / 2) (by omega) (by omega),
        v2_odd ((85680 * u + 2672) / 4096 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F106 : IsP m (a + (m + 2) + (20144 * u + 624) / 2048) ((20144 * u + 624) / 2048) := by
    refine (o_odd_iff m (16 * u) (a) ((20144 * u + 624) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (20144 * u + 624) / 2048) / 2 = (85680 * u + 2672) / 4096 by omega]; exact F105
  have F107 : ¬ IsP m (a + (m + 2) + (20144 * u + 624) / 1024) ((20144 * u + 624) / 1024) := by
    rw [show (20144 * u + 624) / 1024 = 2 * ((20144 * u + 624) / 2048) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((20144 * u + 624) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F106
  have F108 : IsP m (a + (m + 2) + (m + 2) + (3760 * u + 112) / 512) ((3760 * u + 112) / 512) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((3760 * u + 112) / 512) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (3760 * u + 112) / 512) / 2 = (20144 * u + 624) / 1024 by omega]; exact F107
  have F109 : ¬ IsP m (a + (m + 2) + (m + 2) + (3760 * u + 112) / 256) ((3760 * u + 112) / 256) := by
    rw [show (3760 * u + 112) / 256 = 2 * ((3760 * u + 112) / 512) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((3760 * u + 112) / 512) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F108
  have F110 : IsP m (a + (m + 2) + (m + 2) + (3760 * u + 112) / 128) ((3760 * u + 112) / 128) := by
    rw [show (3760 * u + 112) / 128 = 2 * ((3760 * u + 112) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((3760 * u + 112) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F109
  have F111 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (1712 * u + 48) / 64) ((1712 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((1712 * u + 48) / 64) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1712 * u + 48) / 64) / 2 = (3760 * u + 112) / 128 by omega]; exact F110
  have F112 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((688 * u + 16) / 32) hmh hr3 hr4 F24 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (688 * u + 16) / 32) / 2 = (1712 * u + 48) / 64 by omega]; exact F111
  have F113 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr4 hr5 F36 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F112
  have F114 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mpr F113
  have F115 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F114
  have F116 : IsP m (a + (173680 * u + 5424) / 8192) ((173680 * u + 5424) / 8192) := by
    have hv : v2 ((173680 * u + 5424) / 8192) = 0 := by
      have : ((173680 * u + 5424) / 8192) % 2 = 1 := by omega
      rw [v2_odd ((173680 * u + 5424) / 8192) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F117 : ¬ IsP m (a + (m + 2) + (42608 * u + 1328) / 4096) ((42608 * u + 1328) / 4096) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((42608 * u + 1328) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (42608 * u + 1328) / 4096) / 2 = (173680 * u + 5424) / 8192 by omega]; exact F116
  have F118 : IsP m (a + (m + 2) + (42608 * u + 1328) / 2048) ((42608 * u + 1328) / 2048) := by
    rw [show (42608 * u + 1328) / 2048 = 2 * ((42608 * u + 1328) / 4096) by omega]
    exact (o_half' m (16 * u) (a) ((42608 * u + 1328) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F117
  have F119 : ¬ IsP m (a + (m + 2) + (m + 2) + (9840 * u + 304) / 1024) ((9840 * u + 304) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((9840 * u + 304) / 1024) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (9840 * u + 304) / 1024) / 2 = (42608 * u + 1328) / 2048 by omega]; exact F118
  have F120 : IsP m (a + (m + 2) + (m + 2) + (9840 * u + 304) / 512) ((9840 * u + 304) / 512) := by
    rw [show (9840 * u + 304) / 512 = 2 * ((9840 * u + 304) / 1024) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((9840 * u + 304) / 1024) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F119
  have F121 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (1648 * u + 48) / 256) ((1648 * u + 48) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((1648 * u + 48) / 256) hmh hr2 hr3 F14 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1648 * u + 48) / 256) / 2 = (9840 * u + 304) / 512 by omega]; exact F120
  have F122 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (1648 * u + 48) / 128) ((1648 * u + 48) / 128) := by
    rw [show (1648 * u + 48) / 128 = 2 * ((1648 * u + 48) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((1648 * u + 48) / 256) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mpr F121
  have F123 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (1648 * u + 48) / 64) ((1648 * u + 48) / 64) := by
    rw [show (1648 * u + 48) / 64 = 2 * ((1648 * u + 48) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((1648 * u + 48) / 128) hmh hr2 hr3 F14 (by omega) (by omega) (by omega)).mp h F122
  have F124 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((624 * u + 16) / 32) hmh hr3 hr4 F24 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (624 * u + 16) / 32) / 2 = (1648 * u + 48) / 64 by omega]; exact F123
  have F125 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr4 hr5 F36 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F124
  have F126 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mpr F125
  have F127 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((112 * u + 0) / 8) hmh hr4 hr5 F36 (by omega) (by omega) (by omega)).mp h F126
  have F128 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 2) hmh hr5 hr6 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F115
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F127
  have F129 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) (16 * u) hmh hr6 hr7 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F128
  have hr8 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hr7 (by rw [hh]; exact F129)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr6 hb6 hr7
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr7 hb3' hr8
  rw [show a + (8 * m + 13) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hblk', F0, F6, F14, F24, F36⟩

theorem k69g971_rows : ∀ i, (∀ p, IsP m (i * (8 * m + 13)) p) ∧ Blk m 4 (i * (8 * m + 13)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, _, ha, hb, _⟩ := k69g971_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g971

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 971 (mod 4096)（11111000 型）：(n, 0) が P ⇔ n mod (8 * m + 13) が各行の始まり。-/
theorem K69_971 (m : Nat) (hm : (m + 1) % 131072 = 31072) (n : Nat) :
    IsP m n 0 ↔ (n % (8 * m + 13) = 0 ∨ n % (8 * m + 13) = 1 * m + 2 ∨ n % (8 * m + 13) = 2 * m + 4 ∨ n % (8 * m + 13) = 3 * m + 6 ∨ n % (8 * m + 13) = 4 * m + 8 ∨ n % (8 * m + 13) = 5 * m + 10 ∨ n % (8 * m + 13) = 6 * m + 11 ∨ n % (8 * m + 13) = 7 * m + 12) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g971_rows m _ hmu (by omega) (n / (8 * m + 13))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7, _, _, ht0, ht1, ht2, ht3, ht4⟩ := k69g971_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (8 * m + 13)) * (8 * m + 13) + n % (8 * m + 13) := by
    have := Nat.div_add_mod n (8 * m + 13)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (8 * m + 13) < 8 * m + 13 := Nat.mod_lt n (by omega)
  generalize hcc : n % (8 * m + 13) = c at hdiv hlt
  generalize ha : n / (8 * m + 13) * (8 * m + 13) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 hq6 hq7 ht0 ht1 ht2 ht3 ht4
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
                    · by_cases d4 : c = 4 * m + 8 + (m + 1)
                      · rw [d4, show a + (4 * m + 8 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega] at hP
                        exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht4 (by omega) hP
                      · by_cases c5 : c ≤ 5 * m + 10 + m
                        · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (c - (5 * m + 10)) by omega] at hP
                          exact not_isP_of_row m _ (c - (5 * m + 10)) 0 hq5 (by omega) (by omega) (by omega) hP
                        · by_cases c6 : c ≤ 6 * m + 11 + m
                          · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (c - (6 * m + 11)) by omega] at hP
                            exact not_isP_of_row m _ (c - (6 * m + 11)) 0 hq6 (by omega) (by omega) (by omega) hP
                          · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (c - (7 * m + 12)) by omega] at hP
                            exact not_isP_of_row m _ (c - (7 * m + 12)) 0 hq7 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 10) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq5 0
    · rw [h, show a + (6 * m + 11) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq6 0
    · rw [h, show a + (7 * m + 12) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega]; exact hq7 0

section K69g1231

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 4096 = 1231)
include hmu hu

theorem k69g1231_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
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
  have F7 : ¬ IsP m (a + (8720 * u + 272) / 512) ((8720 * u + 272) / 512) := by
    have hv : v2 ((8720 * u + 272) / 512) = 1 := by
      have : ((8720 * u + 272) / 512) % 4 = 2 := by omega
      rw [v2_even ((8720 * u + 272) / 512) (by omega) (by omega),
        v2_odd ((8720 * u + 272) / 512 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F8 : IsP m (a + (m + 2) + (528 * u + 16) / 256) ((528 * u + 16) / 256) := by
    refine (o_odd_iff m (16 * u) (a) ((528 * u + 16) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 256) / 2 = (8720 * u + 272) / 512 by omega]; exact F7
  have F9 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 128) ((528 * u + 16) / 128) := by
    rw [show (528 * u + 16) / 128 = 2 * ((528 * u + 16) / 256) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    rw [show (528 * u + 16) / 64 = 2 * ((528 * u + 16) / 128) by omega]
    exact (o_half' m (16 * u) (a) ((528 * u + 16) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F9
  have F11 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F10
  have F12 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F11
  have F13 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F13
  have F15 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F14
  have F16 : IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 2) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F15
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F16)
  have F17 : ¬ IsP m (a + (41488 * u + 1296) / 2048) ((41488 * u + 1296) / 2048) := by
    have hv : v2 ((41488 * u + 1296) / 2048) = 1 := by
      have : ((41488 * u + 1296) / 2048) % 4 = 2 := by omega
      rw [v2_even ((41488 * u + 1296) / 2048) (by omega) (by omega),
        v2_odd ((41488 * u + 1296) / 2048 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F18 : IsP m (a + (m + 2) + (8720 * u + 272) / 1024) ((8720 * u + 272) / 1024) := by
    refine (o_odd_iff m (16 * u) (a) ((8720 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (8720 * u + 272) / 1024) / 2 = (41488 * u + 1296) / 2048 by omega]; exact F17
  have F19 : ¬ IsP m (a + (m + 2) + (8720 * u + 272) / 512) ((8720 * u + 272) / 512) := by
    rw [show (8720 * u + 272) / 512 = 2 * ((8720 * u + 272) / 1024) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((8720 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F18
  have F20 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 256) ((528 * u + 16) / 256) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((528 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 256) / 2 = (8720 * u + 272) / 512 by omega]; exact F19
  have F21 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 128) ((528 * u + 16) / 128) := by
    rw [show (528 * u + 16) / 128 = 2 * ((528 * u + 16) / 256) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F20
  have F22 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    rw [show (528 * u + 16) / 64 = 2 * ((528 * u + 16) / 128) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F23
  have F25 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F27
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 2)) hmo (by omega) hr3 (by rw [hh]; exact F28)
  have F29 : IsP m (a + (172560 * u + 5392) / 8192) ((172560 * u + 5392) / 8192) := by
    have hv : v2 ((172560 * u + 5392) / 8192) = 0 := by
      have : ((172560 * u + 5392) / 8192) % 2 = 1 := by omega
      rw [v2_odd ((172560 * u + 5392) / 8192) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F30 : ¬ IsP m (a + (m + 2) + (41488 * u + 1296) / 4096) ((41488 * u + 1296) / 4096) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((41488 * u + 1296) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (41488 * u + 1296) / 4096) / 2 = (172560 * u + 5392) / 8192 by omega]; exact F29
  have F31 : IsP m (a + (m + 2) + (41488 * u + 1296) / 2048) ((41488 * u + 1296) / 2048) := by
    rw [show (41488 * u + 1296) / 2048 = 2 * ((41488 * u + 1296) / 4096) by omega]
    exact (o_half' m (16 * u) (a) ((41488 * u + 1296) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (8720 * u + 272) / 1024) ((8720 * u + 272) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((8720 * u + 272) / 1024) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (8720 * u + 272) / 1024) / 2 = (41488 * u + 1296) / 2048 by omega]; exact F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (8720 * u + 272) / 512) ((8720 * u + 272) / 512) := by
    rw [show (8720 * u + 272) / 512 = 2 * ((8720 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((8720 * u + 272) / 1024) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 256) ((528 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 256) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 256) / 2 = (8720 * u + 272) / 512 by omega]; exact F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 128) ((528 * u + 16) / 128) := by
    rw [show (528 * u + 16) / 128 = 2 * ((528 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 256) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    rw [show (528 * u + 16) / 64 = 2 * ((528 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 128) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F36
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F41
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hr4 (by rw [hh]; exact F42)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F44 : IsP m (a + (45712 * u + 1424) / 2048) ((45712 * u + 1424) / 2048) := by
    have hv : v2 ((45712 * u + 1424) / 2048) = 0 := by
      have : ((45712 * u + 1424) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((45712 * u + 1424) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F45 : ¬ IsP m (a + (m + 2) + (12944 * u + 400) / 1024) ((12944 * u + 400) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((12944 * u + 400) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12944 * u + 400) / 1024) / 2 = (45712 * u + 1424) / 2048 by omega]; exact F44
  have F46 : IsP m (a + (m + 2) + (12944 * u + 400) / 512) ((12944 * u + 400) / 512) := by
    rw [show (12944 * u + 400) / 512 = 2 * ((12944 * u + 400) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((12944 * u + 400) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (4752 * u + 144) / 256) ((4752 * u + 144) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((4752 * u + 144) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4752 * u + 144) / 256) / 2 = (12944 * u + 400) / 512 by omega]; exact F46
  have F48 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (656 * u + 16) / 128) ((656 * u + 16) / 128) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((656 * u + 16) / 128) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (656 * u + 16) / 128) / 2 = (4752 * u + 144) / 256 by omega]; exact F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (656 * u + 16) / 64) ((656 * u + 16) / 64) := by
    rw [show (656 * u + 16) / 64 = 2 * ((656 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((656 * u + 16) / 128) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (656 * u + 16) / 32) ((656 * u + 16) / 32) := by
    rw [show (656 * u + 16) / 32 = 2 * ((656 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((656 * u + 16) / 64) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (144 * u + 0) / 16) ((144 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((144 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (144 * u + 0) / 16) / 2 = (656 * u + 16) / 32 by omega]; exact F50
  have F52 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (144 * u + 0) / 8) ((144 * u + 0) / 8) := by
    rw [show (144 * u + 0) / 8 = 2 * ((144 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((144 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F51
  have F53 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (16 * u + 0) / 4 / 2 = (144 * u + 0) / 8 by omega]; exact F52
  have F54 : ¬ IsP m (a + (76368 * u + 2384) / 4096) ((76368 * u + 2384) / 4096) := by
    have hv : v2 ((76368 * u + 2384) / 4096) = 3 := by
      have : ((76368 * u + 2384) / 4096) % 16 = 8 := by omega
      rw [v2_even ((76368 * u + 2384) / 4096) (by omega) (by omega),
        v2_even ((76368 * u + 2384) / 4096 / 2) (by omega) (by omega),
        v2_even ((76368 * u + 2384) / 4096 / 2 / 2) (by omega) (by omega),
        v2_odd ((76368 * u + 2384) / 4096 / 2 / 2 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F55 : IsP m (a + (m + 2) + (10832 * u + 336) / 2048) ((10832 * u + 336) / 2048) := by
    refine (o_odd_iff m (16 * u) (a) ((10832 * u + 336) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (10832 * u + 336) / 2048) / 2 = (76368 * u + 2384) / 4096 by omega]; exact F54
  have F56 : ¬ IsP m (a + (m + 2) + (10832 * u + 336) / 1024) ((10832 * u + 336) / 1024) := by
    rw [show (10832 * u + 336) / 1024 = 2 * ((10832 * u + 336) / 2048) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((10832 * u + 336) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F55
  have F57 : IsP m (a + (m + 2) + (10832 * u + 336) / 512) ((10832 * u + 336) / 512) := by
    rw [show (10832 * u + 336) / 512 = 2 * ((10832 * u + 336) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((10832 * u + 336) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F56
  have F58 : ¬ IsP m (a + (m + 2) + (m + 2) + (2640 * u + 80) / 256) ((2640 * u + 80) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((2640 * u + 80) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2640 * u + 80) / 256) / 2 = (10832 * u + 336) / 512 by omega]; exact F57
  have F59 : IsP m (a + (m + 2) + (m + 2) + (2640 * u + 80) / 128) ((2640 * u + 80) / 128) := by
    rw [show (2640 * u + 80) / 128 = 2 * ((2640 * u + 80) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((2640 * u + 80) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F58
  have F60 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (592 * u + 16) / 64) ((592 * u + 16) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((592 * u + 16) / 64) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (592 * u + 16) / 64) / 2 = (2640 * u + 80) / 128 by omega]; exact F59
  have F61 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (592 * u + 16) / 32) ((592 * u + 16) / 32) := by
    rw [show (592 * u + 16) / 32 = 2 * ((592 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((592 * u + 16) / 64) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F60
  have F62 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (80 * u + 0) / 16) ((80 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((80 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (80 * u + 0) / 16) / 2 = (592 * u + 16) / 32 by omega]; exact F61
  have F63 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (80 * u + 0) / 8) ((80 * u + 0) / 8) := by
    rw [show (80 * u + 0) / 8 = 2 * ((80 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((80 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F62
  have F64 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (80 * u + 0) / 4) ((80 * u + 0) / 4) := by
    rw [show (80 * u + 0) / 4 = 2 * ((80 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((80 * u + 0) / 8) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F63
  have F65 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (16 * u + 0) / 2 / 2 = (16 * u + 0) / 4 by omega]; exact F53
    · rw [show 16 * u + (16 * u + 0) / 2 / 2 = (80 * u + 0) / 4 by omega]; exact F64
  have F76 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).1
    rw [show 16 * u / 2 = (16 * u + 0) / 2 by omega]; exact F65
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F76)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F91 : IsP m (a + (14000 * u + 432) / 512) ((14000 * u + 432) / 512) := by
    have hv : v2 ((14000 * u + 432) / 512) = 0 := by
      have : ((14000 * u + 432) / 512) % 2 = 1 := by omega
      rw [v2_odd ((14000 * u + 432) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F92 : ¬ IsP m (a + (m + 2) + (5808 * u + 176) / 256) ((5808 * u + 176) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((5808 * u + 176) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (5808 * u + 176) / 256) / 2 = (14000 * u + 432) / 512 by omega]; exact F91
  have F93 : IsP m (a + (m + 2) + (m + 2) + (1712 * u + 48) / 128) ((1712 * u + 48) / 128) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((1712 * u + 48) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (1712 * u + 48) / 128) / 2 = (5808 * u + 176) / 256 by omega]; exact F92
  have F94 : ¬ IsP m (a + (m + 2) + (m + 2) + (1712 * u + 48) / 64) ((1712 * u + 48) / 64) := by
    rw [show (1712 * u + 48) / 64 = 2 * ((1712 * u + 48) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((1712 * u + 48) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F93
  have F95 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((688 * u + 16) / 32) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (688 * u + 16) / 32) / 2 = (1712 * u + 48) / 64 by omega]; exact F94
  have F96 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F95
  have F97 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F96
  have F98 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F97
  have F99 : IsP m (a + (11888 * u + 368) / 512) ((11888 * u + 368) / 512) := by
    have hv : v2 ((11888 * u + 368) / 512) = 0 := by
      have : ((11888 * u + 368) / 512) % 2 = 1 := by omega
      rw [v2_odd ((11888 * u + 368) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F100 : ¬ IsP m (a + (m + 2) + (3696 * u + 112) / 256) ((3696 * u + 112) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((3696 * u + 112) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (3696 * u + 112) / 256) / 2 = (11888 * u + 368) / 512 by omega]; exact F99
  have F101 : IsP m (a + (m + 2) + (3696 * u + 112) / 128) ((3696 * u + 112) / 128) := by
    rw [show (3696 * u + 112) / 128 = 2 * ((3696 * u + 112) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((3696 * u + 112) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F100
  have F102 : ¬ IsP m (a + (m + 2) + (m + 2) + (1648 * u + 48) / 64) ((1648 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((1648 * u + 48) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1648 * u + 48) / 64) / 2 = (3696 * u + 112) / 128 by omega]; exact F101
  have F103 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((624 * u + 16) / 32) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (624 * u + 16) / 32) / 2 = (1648 * u + 48) / 64 by omega]; exact F102
  have F104 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F103
  have F105 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F104
  have F106 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((112 * u + 0) / 8) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F105
  have F107 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 2) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F98
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F106
  have F108 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) (16 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F107
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hr6 (by rw [hh]; exact F108)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb5 hr6
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr6 hb3' hr7
  rw [show a + (7 * m + 11) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F6, F16, F28⟩

theorem k69g1231_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 11)) p) ∧ Blk m 4 (i * (7 * m + 11)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k69g1231_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g1231

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 1231 (mod 4096)（1111000 型）：(n, 0) が P ⇔ n mod (7 * m + 11) が各行の始まり。-/
theorem K69_1231 (m : Nat) (hm : (m + 1) % 131072 = 39392) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 11) = 0 ∨ n % (7 * m + 11) = 1 * m + 2 ∨ n % (7 * m + 11) = 2 * m + 4 ∨ n % (7 * m + 11) = 3 * m + 6 ∨ n % (7 * m + 11) = 4 * m + 8 ∨ n % (7 * m + 11) = 5 * m + 9 ∨ n % (7 * m + 11) = 6 * m + 10) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g1231_rows m _ hmu (by omega) (n / (7 * m + 11))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht2, ht3⟩ := k69g1231_step m _ hmu (by omega) _ hrow hblk
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

section K69g1743

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 4096 = 1743)
include hmu hu

theorem k69g1743_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
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
  have F7 : ¬ IsP m (a + (8720 * u + 272) / 512) ((8720 * u + 272) / 512) := by
    have hv : v2 ((8720 * u + 272) / 512) = 1 := by
      have : ((8720 * u + 272) / 512) % 4 = 2 := by omega
      rw [v2_even ((8720 * u + 272) / 512) (by omega) (by omega),
        v2_odd ((8720 * u + 272) / 512 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F8 : IsP m (a + (m + 2) + (528 * u + 16) / 256) ((528 * u + 16) / 256) := by
    refine (o_odd_iff m (16 * u) (a) ((528 * u + 16) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 256) / 2 = (8720 * u + 272) / 512 by omega]; exact F7
  have F9 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 128) ((528 * u + 16) / 128) := by
    rw [show (528 * u + 16) / 128 = 2 * ((528 * u + 16) / 256) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    rw [show (528 * u + 16) / 64 = 2 * ((528 * u + 16) / 128) by omega]
    exact (o_half' m (16 * u) (a) ((528 * u + 16) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F9
  have F11 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F10
  have F12 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F11
  have F13 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F13
  have F15 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F14
  have F16 : IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 2) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F15
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F16)
  have F17 : ¬ IsP m (a + (41488 * u + 1296) / 2048) ((41488 * u + 1296) / 2048) := by
    have hv : v2 ((41488 * u + 1296) / 2048) = 1 := by
      have : ((41488 * u + 1296) / 2048) % 4 = 2 := by omega
      rw [v2_even ((41488 * u + 1296) / 2048) (by omega) (by omega),
        v2_odd ((41488 * u + 1296) / 2048 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F18 : IsP m (a + (m + 2) + (8720 * u + 272) / 1024) ((8720 * u + 272) / 1024) := by
    refine (o_odd_iff m (16 * u) (a) ((8720 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (8720 * u + 272) / 1024) / 2 = (41488 * u + 1296) / 2048 by omega]; exact F17
  have F19 : ¬ IsP m (a + (m + 2) + (8720 * u + 272) / 512) ((8720 * u + 272) / 512) := by
    rw [show (8720 * u + 272) / 512 = 2 * ((8720 * u + 272) / 1024) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((8720 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F18
  have F20 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 256) ((528 * u + 16) / 256) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((528 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 256) / 2 = (8720 * u + 272) / 512 by omega]; exact F19
  have F21 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 128) ((528 * u + 16) / 128) := by
    rw [show (528 * u + 16) / 128 = 2 * ((528 * u + 16) / 256) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F20
  have F22 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    rw [show (528 * u + 16) / 64 = 2 * ((528 * u + 16) / 128) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F23
  have F25 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F27
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 2)) hmo (by omega) hr3 (by rw [hh]; exact F28)
  have F29 : IsP m (a + (172560 * u + 5392) / 8192) ((172560 * u + 5392) / 8192) := by
    have hv : v2 ((172560 * u + 5392) / 8192) = 2 := by
      have : ((172560 * u + 5392) / 8192) % 8 = 4 := by omega
      rw [v2_even ((172560 * u + 5392) / 8192) (by omega) (by omega),
        v2_even ((172560 * u + 5392) / 8192 / 2) (by omega) (by omega),
        v2_odd ((172560 * u + 5392) / 8192 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F30 : ¬ IsP m (a + (m + 2) + (41488 * u + 1296) / 4096) ((41488 * u + 1296) / 4096) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((41488 * u + 1296) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (41488 * u + 1296) / 4096) / 2 = (172560 * u + 5392) / 8192 by omega]; exact F29
  have F31 : IsP m (a + (m + 2) + (41488 * u + 1296) / 2048) ((41488 * u + 1296) / 2048) := by
    rw [show (41488 * u + 1296) / 2048 = 2 * ((41488 * u + 1296) / 4096) by omega]
    exact (o_half' m (16 * u) (a) ((41488 * u + 1296) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (8720 * u + 272) / 1024) ((8720 * u + 272) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((8720 * u + 272) / 1024) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (8720 * u + 272) / 1024) / 2 = (41488 * u + 1296) / 2048 by omega]; exact F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (8720 * u + 272) / 512) ((8720 * u + 272) / 512) := by
    rw [show (8720 * u + 272) / 512 = 2 * ((8720 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((8720 * u + 272) / 1024) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 256) ((528 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 256) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 256) / 2 = (8720 * u + 272) / 512 by omega]; exact F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 128) ((528 * u + 16) / 128) := by
    rw [show (528 * u + 16) / 128 = 2 * ((528 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 256) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    rw [show (528 * u + 16) / 64 = 2 * ((528 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 128) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F36
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F41
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hr4 (by rw [hh]; exact F42)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F44 : IsP m (a + (45712 * u + 1424) / 2048) ((45712 * u + 1424) / 2048) := by
    have hv : v2 ((45712 * u + 1424) / 2048) = 0 := by
      have : ((45712 * u + 1424) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((45712 * u + 1424) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F45 : ¬ IsP m (a + (m + 2) + (12944 * u + 400) / 1024) ((12944 * u + 400) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((12944 * u + 400) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (12944 * u + 400) / 1024) / 2 = (45712 * u + 1424) / 2048 by omega]; exact F44
  have F46 : IsP m (a + (m + 2) + (12944 * u + 400) / 512) ((12944 * u + 400) / 512) := by
    rw [show (12944 * u + 400) / 512 = 2 * ((12944 * u + 400) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((12944 * u + 400) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (4752 * u + 144) / 256) ((4752 * u + 144) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((4752 * u + 144) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (4752 * u + 144) / 256) / 2 = (12944 * u + 400) / 512 by omega]; exact F46
  have F48 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (656 * u + 16) / 128) ((656 * u + 16) / 128) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((656 * u + 16) / 128) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (656 * u + 16) / 128) / 2 = (4752 * u + 144) / 256 by omega]; exact F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (656 * u + 16) / 64) ((656 * u + 16) / 64) := by
    rw [show (656 * u + 16) / 64 = 2 * ((656 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((656 * u + 16) / 128) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F48
  have F50 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (656 * u + 16) / 32) ((656 * u + 16) / 32) := by
    rw [show (656 * u + 16) / 32 = 2 * ((656 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((656 * u + 16) / 64) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F49
  have F51 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (144 * u + 0) / 16) ((144 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((144 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (144 * u + 0) / 16) / 2 = (656 * u + 16) / 32 by omega]; exact F50
  have F52 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (144 * u + 0) / 8) ((144 * u + 0) / 8) := by
    rw [show (144 * u + 0) / 8 = 2 * ((144 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((144 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F51
  have F53 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (16 * u + 0) / 4 / 2 = (144 * u + 0) / 8 by omega]; exact F52
  have F54 : ¬ IsP m (a + (76368 * u + 2384) / 4096) ((76368 * u + 2384) / 4096) := by
    have hv : v2 ((76368 * u + 2384) / 4096) = 1 := by
      have : ((76368 * u + 2384) / 4096) % 4 = 2 := by omega
      rw [v2_even ((76368 * u + 2384) / 4096) (by omega) (by omega),
        v2_odd ((76368 * u + 2384) / 4096 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F55 : IsP m (a + (m + 2) + (10832 * u + 336) / 2048) ((10832 * u + 336) / 2048) := by
    refine (o_odd_iff m (16 * u) (a) ((10832 * u + 336) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (10832 * u + 336) / 2048) / 2 = (76368 * u + 2384) / 4096 by omega]; exact F54
  have F56 : ¬ IsP m (a + (m + 2) + (10832 * u + 336) / 1024) ((10832 * u + 336) / 1024) := by
    rw [show (10832 * u + 336) / 1024 = 2 * ((10832 * u + 336) / 2048) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((10832 * u + 336) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F55
  have F57 : IsP m (a + (m + 2) + (10832 * u + 336) / 512) ((10832 * u + 336) / 512) := by
    rw [show (10832 * u + 336) / 512 = 2 * ((10832 * u + 336) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((10832 * u + 336) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F56
  have F58 : ¬ IsP m (a + (m + 2) + (m + 2) + (2640 * u + 80) / 256) ((2640 * u + 80) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((2640 * u + 80) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2640 * u + 80) / 256) / 2 = (10832 * u + 336) / 512 by omega]; exact F57
  have F59 : IsP m (a + (m + 2) + (m + 2) + (2640 * u + 80) / 128) ((2640 * u + 80) / 128) := by
    rw [show (2640 * u + 80) / 128 = 2 * ((2640 * u + 80) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((2640 * u + 80) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F58
  have F60 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (592 * u + 16) / 64) ((592 * u + 16) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((592 * u + 16) / 64) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (592 * u + 16) / 64) / 2 = (2640 * u + 80) / 128 by omega]; exact F59
  have F61 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (592 * u + 16) / 32) ((592 * u + 16) / 32) := by
    rw [show (592 * u + 16) / 32 = 2 * ((592 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((592 * u + 16) / 64) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F60
  have F62 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (80 * u + 0) / 16) ((80 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((80 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (80 * u + 0) / 16) / 2 = (592 * u + 16) / 32 by omega]; exact F61
  have F63 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (80 * u + 0) / 8) ((80 * u + 0) / 8) := by
    rw [show (80 * u + 0) / 8 = 2 * ((80 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((80 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F62
  have F64 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (80 * u + 0) / 4) ((80 * u + 0) / 4) := by
    rw [show (80 * u + 0) / 4 = 2 * ((80 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((80 * u + 0) / 8) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F63
  have F65 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (16 * u + 0) / 2 / 2 = (16 * u + 0) / 4 by omega]; exact F53
    · rw [show 16 * u + (16 * u + 0) / 2 / 2 = (80 * u + 0) / 4 by omega]; exact F64
  have F76 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).1
    rw [show 16 * u / 2 = (16 * u + 0) / 2 by omega]; exact F65
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F76)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F91 : IsP m (a + (14000 * u + 432) / 512) ((14000 * u + 432) / 512) := by
    have hv : v2 ((14000 * u + 432) / 512) = 0 := by
      have : ((14000 * u + 432) / 512) % 2 = 1 := by omega
      rw [v2_odd ((14000 * u + 432) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F92 : ¬ IsP m (a + (m + 2) + (5808 * u + 176) / 256) ((5808 * u + 176) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((5808 * u + 176) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (5808 * u + 176) / 256) / 2 = (14000 * u + 432) / 512 by omega]; exact F91
  have F93 : IsP m (a + (m + 2) + (m + 2) + (1712 * u + 48) / 128) ((1712 * u + 48) / 128) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((1712 * u + 48) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (1712 * u + 48) / 128) / 2 = (5808 * u + 176) / 256 by omega]; exact F92
  have F94 : ¬ IsP m (a + (m + 2) + (m + 2) + (1712 * u + 48) / 64) ((1712 * u + 48) / 64) := by
    rw [show (1712 * u + 48) / 64 = 2 * ((1712 * u + 48) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((1712 * u + 48) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F93
  have F95 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((688 * u + 16) / 32) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (688 * u + 16) / 32) / 2 = (1712 * u + 48) / 64 by omega]; exact F94
  have F96 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F95
  have F97 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((176 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F96
  have F98 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F97
  have F99 : IsP m (a + (11888 * u + 368) / 512) ((11888 * u + 368) / 512) := by
    have hv : v2 ((11888 * u + 368) / 512) = 0 := by
      have : ((11888 * u + 368) / 512) % 2 = 1 := by omega
      rw [v2_odd ((11888 * u + 368) / 512) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F100 : ¬ IsP m (a + (m + 2) + (3696 * u + 112) / 256) ((3696 * u + 112) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((3696 * u + 112) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (3696 * u + 112) / 256) / 2 = (11888 * u + 368) / 512 by omega]; exact F99
  have F101 : IsP m (a + (m + 2) + (3696 * u + 112) / 128) ((3696 * u + 112) / 128) := by
    rw [show (3696 * u + 112) / 128 = 2 * ((3696 * u + 112) / 256) by omega]
    exact (o_half' m (16 * u) (a) ((3696 * u + 112) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F100
  have F102 : ¬ IsP m (a + (m + 2) + (m + 2) + (1648 * u + 48) / 64) ((1648 * u + 48) / 64) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((1648 * u + 48) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1648 * u + 48) / 64) / 2 = (3696 * u + 112) / 128 by omega]; exact F101
  have F103 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((624 * u + 16) / 32) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (624 * u + 16) / 32) / 2 = (1648 * u + 48) / 64 by omega]; exact F102
  have F104 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F103
  have F105 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((112 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F104
  have F106 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((112 * u + 0) / 8) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F105
  have F107 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 2) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F98
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F106
  have F108 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) (16 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F107
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hr6 (by rw [hh]; exact F108)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb5 hr6
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr6 hb3' hr7
  rw [show a + (7 * m + 11) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F6, F16, F28⟩

theorem k69g1743_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 11)) p) ∧ Blk m 4 (i * (7 * m + 11)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k69g1743_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g1743

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 1743 (mod 4096)（1111000 型）：(n, 0) が P ⇔ n mod (7 * m + 11) が各行の始まり。-/
theorem K69_1743 (m : Nat) (hm : (m + 1) % 131072 = 55776) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 11) = 0 ∨ n % (7 * m + 11) = 1 * m + 2 ∨ n % (7 * m + 11) = 2 * m + 4 ∨ n % (7 * m + 11) = 3 * m + 6 ∨ n % (7 * m + 11) = 4 * m + 8 ∨ n % (7 * m + 11) = 5 * m + 9 ∨ n % (7 * m + 11) = 6 * m + 10) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g1743_rows m _ hmu (by omega) (n / (7 * m + 11))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht2, ht3⟩ := k69g1743_step m _ hmu (by omega) _ hrow hblk
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

section K69g2255

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 4096 = 2255)
include hmu hu

theorem k69g2255_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p) ∧
    (∀ p, IsP m (a + (9 * m + 14)) p) ∧
    Blk m 4 (a + (9 * m + 14)) ∧
    IsP m (a + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) ∧
    IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
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
  have F7 : ¬ IsP m (a + (8720 * u + 272) / 512) ((8720 * u + 272) / 512) := by
    have hv : v2 ((8720 * u + 272) / 512) = 1 := by
      have : ((8720 * u + 272) / 512) % 4 = 2 := by omega
      rw [v2_even ((8720 * u + 272) / 512) (by omega) (by omega),
        v2_odd ((8720 * u + 272) / 512 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F8 : IsP m (a + (m + 2) + (528 * u + 16) / 256) ((528 * u + 16) / 256) := by
    refine (o_odd_iff m (16 * u) (a) ((528 * u + 16) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 256) / 2 = (8720 * u + 272) / 512 by omega]; exact F7
  have F9 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 128) ((528 * u + 16) / 128) := by
    rw [show (528 * u + 16) / 128 = 2 * ((528 * u + 16) / 256) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 256) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F8
  have F10 : IsP m (a + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    rw [show (528 * u + 16) / 64 = 2 * ((528 * u + 16) / 128) by omega]
    exact (o_half' m (16 * u) (a) ((528 * u + 16) / 128) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F9
  have F11 : ¬ IsP m (a + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((528 * u + 16) / 64) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F10
  have F12 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F11
  have F13 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 16) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F12
  have F14 : IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 8) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F13
  have F15 : ¬ IsP m (a + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 4) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F14
  have F16 : IsP m (a + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((16 * u + 0) / 2) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F15
  have hr3 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hr2 (by rw [hh]; exact F16)
  have F17 : ¬ IsP m (a + (41488 * u + 1296) / 2048) ((41488 * u + 1296) / 2048) := by
    have hv : v2 ((41488 * u + 1296) / 2048) = 1 := by
      have : ((41488 * u + 1296) / 2048) % 4 = 2 := by omega
      rw [v2_even ((41488 * u + 1296) / 2048) (by omega) (by omega),
        v2_odd ((41488 * u + 1296) / 2048 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F18 : IsP m (a + (m + 2) + (8720 * u + 272) / 1024) ((8720 * u + 272) / 1024) := by
    refine (o_odd_iff m (16 * u) (a) ((8720 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (8720 * u + 272) / 1024) / 2 = (41488 * u + 1296) / 2048 by omega]; exact F17
  have F19 : ¬ IsP m (a + (m + 2) + (8720 * u + 272) / 512) ((8720 * u + 272) / 512) := by
    rw [show (8720 * u + 272) / 512 = 2 * ((8720 * u + 272) / 1024) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((8720 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F18
  have F20 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 256) ((528 * u + 16) / 256) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((528 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (528 * u + 16) / 256) / 2 = (8720 * u + 272) / 512 by omega]; exact F19
  have F21 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 128) ((528 * u + 16) / 128) := by
    rw [show (528 * u + 16) / 128 = 2 * ((528 * u + 16) / 256) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F20
  have F22 : IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    rw [show (528 * u + 16) / 64 = 2 * ((528 * u + 16) / 128) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F21
  have F23 : ¬ IsP m (a + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((528 * u + 16) / 64) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F22
  have F24 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F23
  have F25 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F24
  have F26 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F25
  have F27 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F26
  have F28 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F27
  have hr4 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 2)) hmo (by omega) hr3 (by rw [hh]; exact F28)
  have F29 : IsP m (a + (172560 * u + 5392) / 8192) ((172560 * u + 5392) / 8192) := by
    have hv : v2 ((172560 * u + 5392) / 8192) = 0 := by
      have : ((172560 * u + 5392) / 8192) % 2 = 1 := by omega
      rw [v2_odd ((172560 * u + 5392) / 8192) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F30 : ¬ IsP m (a + (m + 2) + (41488 * u + 1296) / 4096) ((41488 * u + 1296) / 4096) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((41488 * u + 1296) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (41488 * u + 1296) / 4096) / 2 = (172560 * u + 5392) / 8192 by omega]; exact F29
  have F31 : IsP m (a + (m + 2) + (41488 * u + 1296) / 2048) ((41488 * u + 1296) / 2048) := by
    rw [show (41488 * u + 1296) / 2048 = 2 * ((41488 * u + 1296) / 4096) by omega]
    exact (o_half' m (16 * u) (a) ((41488 * u + 1296) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F30
  have F32 : ¬ IsP m (a + (m + 2) + (m + 2) + (8720 * u + 272) / 1024) ((8720 * u + 272) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((8720 * u + 272) / 1024) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (8720 * u + 272) / 1024) / 2 = (41488 * u + 1296) / 2048 by omega]; exact F31
  have F33 : IsP m (a + (m + 2) + (m + 2) + (8720 * u + 272) / 512) ((8720 * u + 272) / 512) := by
    rw [show (8720 * u + 272) / 512 = 2 * ((8720 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((8720 * u + 272) / 1024) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F32
  have F34 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 256) ((528 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 256) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (528 * u + 16) / 256) / 2 = (8720 * u + 272) / 512 by omega]; exact F33
  have F35 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 128) ((528 * u + 16) / 128) := by
    rw [show (528 * u + 16) / 128 = 2 * ((528 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 256) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F34
  have F36 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    rw [show (528 * u + 16) / 64 = 2 * ((528 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 128) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F35
  have F37 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    rw [show (528 * u + 16) / 32 = 2 * ((528 * u + 16) / 64) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F36
  have F38 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F37
  have F39 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F38
  have F40 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 8) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F39
  have F41 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 4) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F40
  have F42 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F41
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) hr4 (by rw [hh]; exact F42)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F54 : IsP m (a + (76368 * u + 2384) / 4096) ((76368 * u + 2384) / 4096) := by
    have hv : v2 ((76368 * u + 2384) / 4096) = 2 := by
      have : ((76368 * u + 2384) / 4096) % 8 = 4 := by omega
      rw [v2_even ((76368 * u + 2384) / 4096) (by omega) (by omega),
        v2_even ((76368 * u + 2384) / 4096 / 2) (by omega) (by omega),
        v2_odd ((76368 * u + 2384) / 4096 / 2 / 2) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F55 : ¬ IsP m (a + (m + 2) + (10832 * u + 336) / 2048) ((10832 * u + 336) / 2048) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((10832 * u + 336) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (10832 * u + 336) / 2048) / 2 = (76368 * u + 2384) / 4096 by omega]; exact F54
  have F56 : IsP m (a + (m + 2) + (10832 * u + 336) / 1024) ((10832 * u + 336) / 1024) := by
    rw [show (10832 * u + 336) / 1024 = 2 * ((10832 * u + 336) / 2048) by omega]
    exact (o_half' m (16 * u) (a) ((10832 * u + 336) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F55
  have F57 : ¬ IsP m (a + (m + 2) + (10832 * u + 336) / 512) ((10832 * u + 336) / 512) := by
    rw [show (10832 * u + 336) / 512 = 2 * ((10832 * u + 336) / 1024) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((10832 * u + 336) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F56
  have F58 : IsP m (a + (m + 2) + (m + 2) + (2640 * u + 80) / 256) ((2640 * u + 80) / 256) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((2640 * u + 80) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (2640 * u + 80) / 256) / 2 = (10832 * u + 336) / 512 by omega]; exact F57
  have F59 : ¬ IsP m (a + (m + 2) + (m + 2) + (2640 * u + 80) / 128) ((2640 * u + 80) / 128) := by
    rw [show (2640 * u + 80) / 128 = 2 * ((2640 * u + 80) / 256) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((2640 * u + 80) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F58
  have F60 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (592 * u + 16) / 64) ((592 * u + 16) / 64) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((592 * u + 16) / 64) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (592 * u + 16) / 64) / 2 = (2640 * u + 80) / 128 by omega]; exact F59
  have F61 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (592 * u + 16) / 32) ((592 * u + 16) / 32) := by
    rw [show (592 * u + 16) / 32 = 2 * ((592 * u + 16) / 64) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((592 * u + 16) / 64) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F60
  have F62 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (80 * u + 0) / 16) ((80 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((80 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (80 * u + 0) / 16) / 2 = (592 * u + 16) / 32 by omega]; exact F61
  have F63 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (80 * u + 0) / 8) ((80 * u + 0) / 8) := by
    rw [show (80 * u + 0) / 8 = 2 * ((80 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((80 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F62
  have F64 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (80 * u + 0) / 4) ((80 * u + 0) / 4) := by
    rw [show (80 * u + 0) / 4 = 2 * ((80 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((80 * u + 0) / 8) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F63
  have F65 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((16 * u + 0) / 2) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (16 * u + 0) / 2 / 2 = (80 * u + 0) / 4 by omega]; exact F64
  have F66 : IsP m (a + (26160 * u + 816) / 1024) ((26160 * u + 816) / 1024) := by
    have hv : v2 ((26160 * u + 816) / 1024) = 0 := by
      have : ((26160 * u + 816) / 1024) % 2 = 1 := by omega
      rw [v2_odd ((26160 * u + 816) / 1024) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F67 : ¬ IsP m (a + (m + 2) + (9776 * u + 304) / 512) ((9776 * u + 304) / 512) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((9776 * u + 304) / 512) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (9776 * u + 304) / 512) / 2 = (26160 * u + 816) / 1024 by omega]; exact F66
  have F68 : IsP m (a + (m + 2) + (m + 2) + (1584 * u + 48) / 256) ((1584 * u + 48) / 256) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((1584 * u + 48) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (1584 * u + 48) / 256) / 2 = (9776 * u + 304) / 512 by omega]; exact F67
  have F69 : ¬ IsP m (a + (m + 2) + (m + 2) + (1584 * u + 48) / 128) ((1584 * u + 48) / 128) := by
    rw [show (1584 * u + 48) / 128 = 2 * ((1584 * u + 48) / 256) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((1584 * u + 48) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F68
  have F70 : IsP m (a + (m + 2) + (m + 2) + (1584 * u + 48) / 64) ((1584 * u + 48) / 64) := by
    rw [show (1584 * u + 48) / 64 = 2 * ((1584 * u + 48) / 128) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((1584 * u + 48) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F69
  have F71 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((560 * u + 16) / 32) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (560 * u + 16) / 32) / 2 = (1584 * u + 48) / 64 by omega]; exact F70
  have F72 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F71
  have F73 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 16) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F72
  have F74 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 8) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F73
  have F75 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((48 * u + 0) / 4) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F74
  have F76 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show 16 * u / 2 = (16 * u + 0) / 2 by omega]; exact F65
    · rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F75
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2)) p := row_long m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) hmo (by omega) hr5 (by rw [hh]; exact F76)
  have F78 : IsP m (a + (240144 * u + 7440) / 8192) ((240144 * u + 7440) / 8192) := by
    have hv : v2 ((240144 * u + 7440) / 8192) = 0 := by
      have : ((240144 * u + 7440) / 8192) % 2 = 1 := by omega
      rw [v2_odd ((240144 * u + 7440) / 8192) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F79 : ¬ IsP m (a + (m + 2) + (109072 * u + 3344) / 4096) ((109072 * u + 3344) / 4096) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((109072 * u + 3344) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (109072 * u + 3344) / 4096) / 2 = (240144 * u + 7440) / 8192 by omega]; exact F78
  have F80 : IsP m (a + (m + 2) + (m + 2) + (43536 * u + 1296) / 2048) ((43536 * u + 1296) / 2048) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2)) ((43536 * u + 1296) / 2048) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (43536 * u + 1296) / 2048) / 2 = (109072 * u + 3344) / 4096 by omega]; exact F79
  have F81 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (10768 * u + 272) / 1024) ((10768 * u + 272) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((10768 * u + 272) / 1024) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (10768 * u + 272) / 1024) / 2 = (43536 * u + 1296) / 2048 by omega]; exact F80
  have F82 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (10768 * u + 272) / 512) ((10768 * u + 272) / 512) := by
    rw [show (10768 * u + 272) / 512 = 2 * ((10768 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((10768 * u + 272) / 1024) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F81
  have F83 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (2576 * u + 16) / 256) ((2576 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((2576 * u + 16) / 256) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 16) / 256) / 2 = (10768 * u + 272) / 512 by omega]; exact F82
  have F84 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (2576 * u + 16) / 128) ((2576 * u + 16) / 128) := by
    rw [show (2576 * u + 16) / 128 = 2 * ((2576 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((2576 * u + 16) / 256) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F83
  have F85 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (528 * u + 16) / 64 / 2 = (2576 * u + 16) / 128 by omega]; exact F84
  have F86 : ¬ IsP m (a + (468496 * u + 14608) / 16384) ((468496 * u + 14608) / 16384) := by
    have hv : v2 ((468496 * u + 14608) / 16384) = 1 := by
      have : ((468496 * u + 14608) / 16384) % 4 = 2 := by omega
      rw [v2_even ((468496 * u + 14608) / 16384) (by omega) (by omega),
        v2_odd ((468496 * u + 14608) / 16384 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F87 : IsP m (a + (m + 2) + (206352 * u + 6416) / 8192) ((206352 * u + 6416) / 8192) := by
    refine (o_odd_iff m (16 * u) (a) ((206352 * u + 6416) / 8192) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (206352 * u + 6416) / 8192) / 2 = (468496 * u + 14608) / 16384 by omega]; exact F86
  have F88 : ¬ IsP m (a + (m + 2) + (m + 2) + (75280 * u + 2320) / 4096) ((75280 * u + 2320) / 4096) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((75280 * u + 2320) / 4096) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (75280 * u + 2320) / 4096) / 2 = (206352 * u + 6416) / 8192 by omega]; exact F87
  have F89 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (9744 * u + 272) / 2048) ((9744 * u + 272) / 2048) := by
    refine (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2)) ((9744 * u + 272) / 2048) hmh hr2 hr3 F16 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (9744 * u + 272) / 2048) / 2 = (75280 * u + 2320) / 4096 by omega]; exact F88
  have F90 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (9744 * u + 272) / 1024) ((9744 * u + 272) / 1024) := by
    rw [show (9744 * u + 272) / 1024 = 2 * ((9744 * u + 272) / 2048) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((9744 * u + 272) / 2048) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mp h F89
  have F91 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (9744 * u + 272) / 512) ((9744 * u + 272) / 512) := by
    rw [show (9744 * u + 272) / 512 = 2 * ((9744 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2)) ((9744 * u + 272) / 1024) hmh hr2 hr3 F16 (by omega) (by omega) (by omega)).mpr F90
  have F92 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (1552 * u + 16) / 256) ((1552 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((1552 * u + 16) / 256) hmh hr3 hr4 F28 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1552 * u + 16) / 256) / 2 = (9744 * u + 272) / 512 by omega]; exact F91
  have F93 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (1552 * u + 16) / 128) ((1552 * u + 16) / 128) := by
    rw [show (1552 * u + 16) / 128 = 2 * ((1552 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((1552 * u + 16) / 256) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mpr F92
  have F94 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (1552 * u + 16) / 64) ((1552 * u + 16) / 64) := by
    rw [show (1552 * u + 16) / 64 = 2 * ((1552 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2)) ((1552 * u + 16) / 128) hmh hr3 hr4 F28 (by omega) (by omega) (by omega)).mp h F93
  have F95 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2)) ((528 * u + 16) / 32) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (528 * u + 16) / 32 / 2 = (528 * u + 16) / 64 by omega]; exact F85
    · rw [show 16 * u + (528 * u + 16) / 32 / 2 = (1552 * u + 16) / 64 by omega]; exact F94
  have F96 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 16) hmh hr5 hr6 F76 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F95
  have F97 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 16) hmh hr5 hr6 F76 (by omega) (by omega) (by omega)).mpr F96
  have F98 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 8) hmh hr5 hr6 F76 (by omega) (by omega) (by omega)).mp h F97
  have F99 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 4) hmh hr5 hr6 F76 (by omega) (by omega) (by omega)).mpr F98
  have F100 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 2) hmh hr5 hr6 F76 (by omega) (by omega) (by omega)).mp h F99
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr6 (by rw [hh]; exact F100)
  have hb7 := blk1_direct m _ hr7 (odd_of_rows m _ hmo hr7 (Or.inr ⟨_, rfl, hr6⟩))
  have F122 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    have hv : v2 ((560 * u + 16) / 32) = 0 := by
      have : ((560 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((560 * u + 16) / 32) (by omega)]
    exact (hb5 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F123 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 16) hmh hr5 hr6 F76 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F122
  have F124 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 16) hmh hr5 hr6 F76 (by omega) (by omega) (by omega)).mpr F123
  have F125 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 8) hmh hr5 hr6 F76 (by omega) (by omega) (by omega)).mp h F124
  have F126 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 4) hmh hr5 hr6 F76 (by omega) (by omega) (by omega)).mpr F125
  have F127 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (16 * u) hmh hr6 hr7 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F126
  have hr8 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr7 (by rw [hh]; exact F127)
  have hb8 := blk1_direct m _ hr8 (odd_of_rows m _ hmo hr8 (Or.inr ⟨_, rfl, hr7⟩))
  have F138 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    have hv : v2 ((688 * u + 16) / 32) = 0 := by
      have : ((688 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((688 * u + 16) / 32) (by omega)]
    exact (hb5 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F139 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((176 * u + 0) / 16) hmh hr5 hr6 F76 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F138
  have F140 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((176 * u + 0) / 16) hmh hr5 hr6 F76 (by omega) (by omega) (by omega)).mpr F139
  have F141 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((48 * u + 0) / 4) hmh hr6 hr7 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F140
  have F142 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    have hv : v2 ((624 * u + 16) / 32) = 0 := by
      have : ((624 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((624 * u + 16) / 32) (by omega)]
    exact (hb5 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F143 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 16) hmh hr5 hr6 F76 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F142
  have F144 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 16) hmh hr5 hr6 F76 (by omega) (by omega) (by omega)).mpr F143
  have F145 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 8) hmh hr5 hr6 F76 (by omega) (by omega) (by omega)).mp h F144
  have F146 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((48 * u + 0) / 2) hmh hr6 hr7 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F141
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F145
  have F147 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) (16 * u) hmh hr7 hr8 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F146
  have hr9 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) hr8 (by rw [hh]; exact F147)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr7 hb7 hr8
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr8 hb3' hr9
  rw [show a + (9 * m + 14) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hblk', F0, F6, F16, F28, F76⟩

theorem k69g2255_rows : ∀ i, (∀ p, IsP m (i * (9 * m + 14)) p) ∧ Blk m 4 (i * (9 * m + 14)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, _, _, ha, hb, _⟩ := k69g2255_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g2255

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 2255 (mod 4096)（111101000 型）：(n, 0) が P ⇔ n mod (9 * m + 14) が各行の始まり。-/
theorem K69_2255 (m : Nat) (hm : (m + 1) % 131072 = 72160) (n : Nat) :
    IsP m n 0 ↔ (n % (9 * m + 14) = 0 ∨ n % (9 * m + 14) = 1 * m + 2 ∨ n % (9 * m + 14) = 2 * m + 4 ∨ n % (9 * m + 14) = 3 * m + 6 ∨ n % (9 * m + 14) = 4 * m + 8 ∨ n % (9 * m + 14) = 5 * m + 9 ∨ n % (9 * m + 14) = 6 * m + 11 ∨ n % (9 * m + 14) = 7 * m + 12 ∨ n % (9 * m + 14) = 8 * m + 13) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g2255_rows m _ hmu (by omega) (n / (9 * m + 14))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, _, _, ht0, ht1, ht2, ht3, ht5⟩ := k69g2255_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (9 * m + 14)) * (9 * m + 14) + n % (9 * m + 14) := by
    have := Nat.div_add_mod n (9 * m + 14)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (9 * m + 14) < 9 * m + 14 := Nat.mod_lt n (by omega)
  generalize hcc : n % (9 * m + 14) = c at hdiv hlt
  generalize ha : n / (9 * m + 14) * (9 * m + 14) = a at hdiv hrow hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 ht0 ht1 ht2 ht3 ht5
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
                      · by_cases d5 : c = 5 * m + 9 + (m + 1)
                        · rw [d5, show a + (5 * m + 9 + (m + 1)) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) by omega] at hP
                          exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht5 (by omega) hP
                        · by_cases c6 : c ≤ 6 * m + 11 + m
                          · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (c - (6 * m + 11)) by omega] at hP
                            exact not_isP_of_row m _ (c - (6 * m + 11)) 0 hq6 (by omega) (by omega) (by omega) hP
                          · by_cases c7 : c ≤ 7 * m + 12 + m
                            · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (c - (7 * m + 12)) by omega] at hP
                              exact not_isP_of_row m _ (c - (7 * m + 12)) 0 hq7 (by omega) (by omega) (by omega) hP
                            · rw [show a + c = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (c - (8 * m + 13)) by omega] at hP
                              exact not_isP_of_row m _ (c - (8 * m + 13)) 0 hq8 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h, show a + (1 * m + 2) = a + (m + 2) by omega]; exact hq1 0
    · rw [h, show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hq2 0
    · rw [h, show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq3 0
    · rw [h, show a + (4 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) by omega]; exact hq4 0
    · rw [h, show a + (5 * m + 9) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hq5 0
    · rw [h, show a + (6 * m + 11) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) by omega]; exact hq6 0
    · rw [h, show a + (7 * m + 12) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) by omega]; exact hq7 0
    · rw [h, show a + (8 * m + 13) = a + (m + 2) + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) by omega]; exact hq8 0

section K69g3215

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 4096 = 3215)
include hmu hu

theorem k69g3215_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
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
  have F40 : IsP m (a + (535056 * u + 16656) / 32768) ((535056 * u + 16656) / 32768) := by
    have hv : v2 ((535056 * u + 16656) / 32768) = 0 := by
      have : ((535056 * u + 16656) / 32768) % 2 = 1 := by omega
      rw [v2_odd ((535056 * u + 16656) / 32768) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F41 : ¬ IsP m (a + (m + 2) + (10768 * u + 272) / 16384) ((10768 * u + 272) / 16384) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((10768 * u + 272) / 16384) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (10768 * u + 272) / 16384) / 2 = (535056 * u + 16656) / 32768 by omega]; exact F40
  have F42 : IsP m (a + (m + 2) + (10768 * u + 272) / 8192) ((10768 * u + 272) / 8192) := by
    rw [show (10768 * u + 272) / 8192 = 2 * ((10768 * u + 272) / 16384) by omega]
    exact (o_half' m (16 * u) (a) ((10768 * u + 272) / 16384) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F41
  have F43 : ¬ IsP m (a + (m + 2) + (10768 * u + 272) / 4096) ((10768 * u + 272) / 4096) := by
    rw [show (10768 * u + 272) / 4096 = 2 * ((10768 * u + 272) / 8192) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((10768 * u + 272) / 8192) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F42
  have F44 : IsP m (a + (m + 2) + (10768 * u + 272) / 2048) ((10768 * u + 272) / 2048) := by
    rw [show (10768 * u + 272) / 2048 = 2 * ((10768 * u + 272) / 4096) by omega]
    exact (o_half' m (16 * u) (a) ((10768 * u + 272) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F43
  have F45 : ¬ IsP m (a + (m + 2) + (10768 * u + 272) / 1024) ((10768 * u + 272) / 1024) := by
    rw [show (10768 * u + 272) / 1024 = 2 * ((10768 * u + 272) / 2048) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((10768 * u + 272) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F44
  have F46 : IsP m (a + (m + 2) + (10768 * u + 272) / 512) ((10768 * u + 272) / 512) := by
    rw [show (10768 * u + 272) / 512 = 2 * ((10768 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((10768 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F45
  have F47 : ¬ IsP m (a + (m + 2) + (m + 2) + (2576 * u + 16) / 256) ((2576 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((2576 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 16) / 256) / 2 = (10768 * u + 272) / 512 by omega]; exact F46
  have F48 : IsP m (a + (m + 2) + (m + 2) + (2576 * u + 16) / 128) ((2576 * u + 16) / 128) := by
    rw [show (2576 * u + 16) / 128 = 2 * ((2576 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((2576 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F47
  have F49 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (528 * u + 16) / 64 / 2 = (2576 * u + 16) / 128 by omega]; exact F48
  have F50 : IsP m (a + (42512 * u + 1296) / 2048) ((42512 * u + 1296) / 2048) := by
    have hv : v2 ((42512 * u + 1296) / 2048) = 0 := by
      have : ((42512 * u + 1296) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((42512 * u + 1296) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F51 : ¬ IsP m (a + (m + 2) + (9744 * u + 272) / 1024) ((9744 * u + 272) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((9744 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (9744 * u + 272) / 1024) / 2 = (42512 * u + 1296) / 2048 by omega]; exact F50
  have F52 : IsP m (a + (m + 2) + (9744 * u + 272) / 512) ((9744 * u + 272) / 512) := by
    rw [show (9744 * u + 272) / 512 = 2 * ((9744 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((9744 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F51
  have F53 : ¬ IsP m (a + (m + 2) + (m + 2) + (1552 * u + 16) / 256) ((1552 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((1552 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1552 * u + 16) / 256) / 2 = (9744 * u + 272) / 512 by omega]; exact F52
  have F54 : IsP m (a + (m + 2) + (m + 2) + (1552 * u + 16) / 128) ((1552 * u + 16) / 128) := by
    rw [show (1552 * u + 16) / 128 = 2 * ((1552 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((1552 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F53
  have F55 : ¬ IsP m (a + (m + 2) + (m + 2) + (1552 * u + 16) / 64) ((1552 * u + 16) / 64) := by
    rw [show (1552 * u + 16) / 64 = 2 * ((1552 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((1552 * u + 16) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F54
  have F56 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 32) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (528 * u + 16) / 32 / 2 = (528 * u + 16) / 64 by omega]; exact F49
    · rw [show 16 * u + (528 * u + 16) / 32 / 2 = (1552 * u + 16) / 64 by omega]; exact F55
  have F57 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F56
  have F58 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F57
  have F59 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 8) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F58
  have F60 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 4) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F59
  have F61 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 2) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F60
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F61)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F77 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    have hv : v2 ((560 * u + 16) / 32) = 0 := by
      have : ((560 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((560 * u + 16) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F78 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F77
  have F79 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F78
  have F80 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 8) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F79
  have F81 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 4) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F80
  have F82 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F81
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F82)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F93 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    have hv : v2 ((688 * u + 16) / 32) = 0 := by
      have : ((688 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((688 * u + 16) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F94 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((176 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F93
  have F95 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((176 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F94
  have F96 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((48 * u + 0) / 4) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F95
  have F97 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    have hv : v2 ((624 * u + 16) / 32) = 0 := by
      have : ((624 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((624 * u + 16) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F98 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F97
  have F99 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F98
  have F100 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 8) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F99
  have F101 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((48 * u + 0) / 2) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F96
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F100
  have F102 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) (16 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F101
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) hr6 (by rw [hh]; exact F102)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb5 hr6
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr6 hb3' hr7
  rw [show a + (7 * m + 10) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F6, F38⟩

theorem k69g3215_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 10)) p) ∧ Blk m 4 (i * (7 * m + 10)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k69g3215_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g3215

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 3215 (mod 4096)（1101000 型）：(n, 0) が P ⇔ n mod (7 * m + 10) が各行の始まり。-/
theorem K69_3215 (m : Nat) (hm : (m + 1) % 131072 = 102880) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 10) = 0 ∨ n % (7 * m + 10) = 1 * m + 2 ∨ n % (7 * m + 10) = 2 * m + 4 ∨ n % (7 * m + 10) = 3 * m + 5 ∨ n % (7 * m + 10) = 4 * m + 7 ∨ n % (7 * m + 10) = 5 * m + 8 ∨ n % (7 * m + 10) = 6 * m + 9) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g3215_rows m _ hmu (by omega) (n / (7 * m + 10))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3⟩ := k69g3215_step m _ hmu (by omega) _ hrow hblk
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

section K69g3727

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 4096 = 3727)
include hmu hu

theorem k69g3727_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
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
  have F40 : ¬ IsP m (a + (272912 * u + 8464) / 16384) ((272912 * u + 8464) / 16384) := by
    have hv : v2 ((272912 * u + 8464) / 16384) = 1 := by
      have : ((272912 * u + 8464) / 16384) % 4 = 2 := by omega
      rw [v2_even ((272912 * u + 8464) / 16384) (by omega) (by omega),
        v2_odd ((272912 * u + 8464) / 16384 / 2) (by omega)]
    intro h; have := (hblk _ (by omega) (by omega) (by omega)).mp h; omega
  have F41 : IsP m (a + (m + 2) + (10768 * u + 272) / 8192) ((10768 * u + 272) / 8192) := by
    refine (o_odd_iff m (16 * u) (a) ((10768 * u + 272) / 8192) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mpr ?_
    rw [show (m + 2 + (10768 * u + 272) / 8192) / 2 = (272912 * u + 8464) / 16384 by omega]; exact F40
  have F42 : ¬ IsP m (a + (m + 2) + (10768 * u + 272) / 4096) ((10768 * u + 272) / 4096) := by
    rw [show (10768 * u + 272) / 4096 = 2 * ((10768 * u + 272) / 8192) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((10768 * u + 272) / 8192) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F41
  have F43 : IsP m (a + (m + 2) + (10768 * u + 272) / 2048) ((10768 * u + 272) / 2048) := by
    rw [show (10768 * u + 272) / 2048 = 2 * ((10768 * u + 272) / 4096) by omega]
    exact (o_half' m (16 * u) (a) ((10768 * u + 272) / 4096) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F42
  have F44 : ¬ IsP m (a + (m + 2) + (10768 * u + 272) / 1024) ((10768 * u + 272) / 1024) := by
    rw [show (10768 * u + 272) / 1024 = 2 * ((10768 * u + 272) / 2048) by omega]
    exact fun h => (o_half' m (16 * u) (a) ((10768 * u + 272) / 2048) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mp h F43
  have F45 : IsP m (a + (m + 2) + (10768 * u + 272) / 512) ((10768 * u + 272) / 512) := by
    rw [show (10768 * u + 272) / 512 = 2 * ((10768 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((10768 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F44
  have F46 : ¬ IsP m (a + (m + 2) + (m + 2) + (2576 * u + 16) / 256) ((2576 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((2576 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (2576 * u + 16) / 256) / 2 = (10768 * u + 272) / 512 by omega]; exact F45
  have F47 : IsP m (a + (m + 2) + (m + 2) + (2576 * u + 16) / 128) ((2576 * u + 16) / 128) := by
    rw [show (2576 * u + 16) / 128 = 2 * ((2576 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((2576 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F46
  have F48 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (528 * u + 16) / 64) ((528 * u + 16) / 64) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 64) hmh hr2 hr3 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (528 * u + 16) / 64 / 2 = (2576 * u + 16) / 128 by omega]; exact F47
  have F49 : IsP m (a + (42512 * u + 1296) / 2048) ((42512 * u + 1296) / 2048) := by
    have hv : v2 ((42512 * u + 1296) / 2048) = 0 := by
      have : ((42512 * u + 1296) / 2048) % 2 = 1 := by omega
      rw [v2_odd ((42512 * u + 1296) / 2048) (by omega)]
    exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F50 : ¬ IsP m (a + (m + 2) + (9744 * u + 272) / 1024) ((9744 * u + 272) / 1024) := by
    intro h; apply (o_odd_iff m (16 * u) (a) ((9744 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (9744 * u + 272) / 1024) / 2 = (42512 * u + 1296) / 2048 by omega]; exact F49
  have F51 : IsP m (a + (m + 2) + (9744 * u + 272) / 512) ((9744 * u + 272) / 512) := by
    rw [show (9744 * u + 272) / 512 = 2 * ((9744 * u + 272) / 1024) by omega]
    exact (o_half' m (16 * u) (a) ((9744 * u + 272) / 1024) hmh hr0 hr1 F0 (by omega) (by omega) (by omega)).mpr F50
  have F52 : ¬ IsP m (a + (m + 2) + (m + 2) + (1552 * u + 16) / 256) ((1552 * u + 16) / 256) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2)) ((1552 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (1552 * u + 16) / 256) / 2 = (9744 * u + 272) / 512 by omega]; exact F51
  have F53 : IsP m (a + (m + 2) + (m + 2) + (1552 * u + 16) / 128) ((1552 * u + 16) / 128) := by
    rw [show (1552 * u + 16) / 128 = 2 * ((1552 * u + 16) / 256) by omega]
    exact (o_half' m (16 * u) (a + (m + 2)) ((1552 * u + 16) / 256) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mpr F52
  have F54 : ¬ IsP m (a + (m + 2) + (m + 2) + (1552 * u + 16) / 64) ((1552 * u + 16) / 64) := by
    rw [show (1552 * u + 16) / 64 = 2 * ((1552 * u + 16) / 128) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2)) ((1552 * u + 16) / 128) hmh hr1 hr2 F6 (by omega) (by omega) (by omega)).mp h F53
  have F55 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (528 * u + 16) / 32) ((528 * u + 16) / 32) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2)) ((528 * u + 16) / 32) hmh hr2 hr3 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (528 * u + 16) / 32 / 2 = (528 * u + 16) / 64 by omega]; exact F48
    · rw [show 16 * u + (528 * u + 16) / 32 / 2 = (1552 * u + 16) / 64 by omega]; exact F54
  have F56 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 16) ((16 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (16 * u + 0) / 16) / 2 = (528 * u + 16) / 32 by omega]; exact F55
  have F57 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 8) ((16 * u + 0) / 8) := by
    rw [show (16 * u + 0) / 8 = 2 * ((16 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F56
  have F58 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 4) ((16 * u + 0) / 4) := by
    rw [show (16 * u + 0) / 4 = 2 * ((16 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 8) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F57
  have F59 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (16 * u + 0) / 2) ((16 * u + 0) / 2) := by
    rw [show (16 * u + 0) / 2 = 2 * ((16 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 4) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F58
  have F60 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + 16 * u) (16 * u) := by
    rw [show 16 * u = 2 * ((16 * u + 0) / 2) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((16 * u + 0) / 2) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F59
  have hr5 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) hr4 (by rw [hh]; exact F60)
  have hb5 := blk1_direct m _ hr5 (odd_of_rows m _ hmo hr5 (Or.inr ⟨_, rfl, hr4⟩))
  have F76 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (560 * u + 16) / 32) ((560 * u + 16) / 32) := by
    have hv : v2 ((560 * u + 16) / 32) = 0 := by
      have : ((560 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((560 * u + 16) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F77 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 16) ((48 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (48 * u + 0) / 16) / 2 = (560 * u + 16) / 32 by omega]; exact F76
  have F78 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 8) ((48 * u + 0) / 8) := by
    rw [show (48 * u + 0) / 8 = 2 * ((48 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F77
  have F79 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    rw [show (48 * u + 0) / 4 = 2 * ((48 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 8) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F78
  have F80 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    rw [show (48 * u + 0) / 2 = 2 * ((48 * u + 0) / 4) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((48 * u + 0) / 4) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F79
  have F81 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) (16 * u) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F80
  have hr6 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hr5 (by rw [hh]; exact F81)
  have hb6 := blk1_direct m _ hr6 (odd_of_rows m _ hmo hr6 (Or.inr ⟨_, rfl, hr5⟩))
  have F92 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (688 * u + 16) / 32) ((688 * u + 16) / 32) := by
    have hv : v2 ((688 * u + 16) / 32) = 0 := by
      have : ((688 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((688 * u + 16) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F93 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (176 * u + 0) / 16) ((176 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((176 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (176 * u + 0) / 16) / 2 = (688 * u + 16) / 32 by omega]; exact F92
  have F94 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (176 * u + 0) / 8) ((176 * u + 0) / 8) := by
    rw [show (176 * u + 0) / 8 = 2 * ((176 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((176 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F93
  have F95 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (48 * u + 0) / 4) ((48 * u + 0) / 4) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((48 * u + 0) / 4) hmh hr4 hr5 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + (48 * u + 0) / 4 / 2 = (176 * u + 0) / 8 by omega]; exact F94
  have F96 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (624 * u + 16) / 32) ((624 * u + 16) / 32) := by
    have hv : v2 ((624 * u + 16) / 32) = 0 := by
      have : ((624 * u + 16) / 32) % 2 = 1 := by omega
      rw [v2_odd ((624 * u + 16) / 32) (by omega)]
    exact (hb3 _ (by omega) (by omega) (by omega)).mpr (by omega)
  have F97 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 16) ((112 * u + 0) / 16) := by
    intro h; apply (o_odd_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega) (by omega)).mp h
    rw [show (m + 2 + (112 * u + 0) / 16) / 2 = (624 * u + 16) / 32 by omega]; exact F96
  have F98 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 8) ((112 * u + 0) / 8) := by
    rw [show (112 * u + 0) / 8 = 2 * ((112 * u + 0) / 16) by omega]
    exact (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 16) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mpr F97
  have F99 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (112 * u + 0) / 4) ((112 * u + 0) / 4) := by
    rw [show (112 * u + 0) / 4 = 2 * ((112 * u + 0) / 8) by omega]
    exact fun h => (o_half' m (16 * u) (a + (m + 2) + (m + 2) + (m + 1)) ((112 * u + 0) / 8) hmh hr3 hr4 F38 (by omega) (by omega) (by omega)).mp h F98
  have F100 : IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (48 * u + 0) / 2) ((48 * u + 0) / 2) := by
    refine (e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2)) ((48 * u + 0) / 2) hmh hr4 hr5 (by omega) (by omega) (by omega)).mpr ⟨?_, ?_⟩
    · rw [show (48 * u + 0) / 2 / 2 = (48 * u + 0) / 4 by omega]; exact F95
    · rw [show 16 * u + (48 * u + 0) / 2 / 2 = (112 * u + 0) / 4 by omega]; exact F99
  have F101 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) := by
    intro h; apply ((e_iff m (16 * u) (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) (16 * u) hmh hr5 hr6 (by omega) (by omega) (by omega)).mp h).2
    rw [show 16 * u + 16 * u / 2 = (48 * u + 0) / 2 by omega]; exact F100
  have hr7 : ∀ p, IsP m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) p := row_next m (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) hr6 (by rw [hh]; exact F101)
  have hb3' : Blk m 3 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) := blk_step2 m 1 3 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr5 hb5 hr6
  have hblk' : Blk m 4 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1)) := blk_step2 m 3 4 (a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1)) hmo (by omega) (by omega) (by rw [hh, hv4u]; omega) hr6 hb3' hr7
  rw [show a + (7 * m + 10) = a + (m + 2) + (m + 2) + (m + 1) + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hblk', F0, F6, F38⟩

theorem k69g3727_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 10)) p) ∧ Blk m 4 (i * (7 * m + 10)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k69g3727_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g3727

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 3727 (mod 4096)（1101000 型）：(n, 0) が P ⇔ n mod (7 * m + 10) が各行の始まり。-/
theorem K69_3727 (m : Nat) (hm : (m + 1) % 131072 = 119264) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 10) = 0 ∨ n % (7 * m + 10) = 1 * m + 2 ∨ n % (7 * m + 10) = 2 * m + 4 ∨ n % (7 * m + 10) = 3 * m + 5 ∨ n % (7 * m + 10) = 4 * m + 7 ∨ n % (7 * m + 10) = 5 * m + 8 ∨ n % (7 * m + 10) = 6 * m + 9) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g3727_rows m _ hmu (by omega) (n / (7 * m + 10))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3⟩ := k69g3727_step m _ hmu (by omega) _ hrow hblk
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

section K69g3983

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 4096 = 3983)
include hmu hu

theorem k69g3983_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
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
    have hv : v2 ((141840 * u + 4368) / 8192) = 2 := by
      have : ((141840 * u + 4368) / 8192) % 8 = 4 := by omega
      rw [v2_even ((141840 * u + 4368) / 8192) (by omega) (by omega),
        v2_even ((141840 * u + 4368) / 8192 / 2) (by omega) (by omega),
        v2_odd ((141840 * u + 4368) / 8192 / 2 / 2) (by omega)]
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

theorem k69g3983_rows : ∀ i, (∀ p, IsP m (i * (7 * m + 10)) p) ∧ Blk m 4 (i * (7 * m + 10)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 4⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := k69g3983_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K69g3983

/-- v2(m+1) = 5、m + 1 = 32u、u ≡ 3983 (mod 4096)（1101000 型）：(n, 0) が P ⇔ n mod (7 * m + 10) が各行の始まり。-/
theorem K69_3983 (m : Nat) (hm : (m + 1) % 131072 = 127456) (n : Nat) :
    IsP m n 0 ↔ (n % (7 * m + 10) = 0 ∨ n % (7 * m + 10) = 1 * m + 2 ∨ n % (7 * m + 10) = 2 * m + 4 ∨ n % (7 * m + 10) = 3 * m + 5 ∨ n % (7 * m + 10) = 4 * m + 7 ∨ n % (7 * m + 10) = 5 * m + 8 ∨ n % (7 * m + 10) = 6 * m + 9) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  obtain ⟨hrow, hblk⟩ := k69g3983_rows m _ hmu (by omega) (n / (7 * m + 10))
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, _, _, ht0, ht1, ht3⟩ := k69g3983_step m _ hmu (by omega) _ hrow hblk
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

end Rubidium
