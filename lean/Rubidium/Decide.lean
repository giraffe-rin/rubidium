/-
  Rubidium.Decide — ゲームの定義 IsP の計算できる版 isPb と、その同値性

  isPb m r p：「1 ≤ k ≤ min(m, r)、k ≠ p のどの k でも、isPb m (r − k) k が false」を、Nat.all で計算する。
  定理 isPb_iff：isPb m r p = true ↔ IsP m r p。
  これで IsP の値を #eval で計算でき、全探索（code/ の JavaScript）と照合できる。
-/
import Rubidium.Game

namespace Rubidium

/-- Nat.all の言い換え。-/
theorem nat_all_iff (n : Nat) (f : (i : Nat) → i < n → Bool) :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true, ih]
    constructor
    · intro ⟨h1, h2⟩ i hi
      by_cases hin : i < n
      · exact h1 i hin
      · have : i = n := by omega
        subst this; exact h2
    · intro h; exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

/-- IsP の計算できる版。i = 0..r−1 について k = i + 1 を調べる。-/
def isPb (m : Nat) (r p : Nat) : Bool :=
  Nat.all r fun i _ => !(decide (i + 1 ≤ m) && decide (i + 1 ≠ p)) || !isPb m (r - (i + 1)) (i + 1)
termination_by r
decreasing_by omega

theorem isPb_iff (m : Nat) : ∀ r p, isPb m r p = true ↔ IsP m r p := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro p
    rw [isPb, nat_all_iff, isP_iff]
    constructor
    · intro h k hk1 hkm hkr hkp hP
      have hi : k - 1 < r := by omega
      have := h (k - 1) hi
      have hk : k - 1 + 1 = k := by omega
      rw [hk] at this
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
      rcases this with (h1 | h1) | h1
      · exact h1 hkm
      · exact h1 hkp
      · have := (ih (r - k) (by omega) k).mpr hP
        rw [this] at h1; exact absurd h1 (by simp)
    · intro h i hi
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases hm : i + 1 ≤ m
      · by_cases hp : i + 1 = p
        · left; right; exact fun hne => hne hp
        · right
          have hn := h (i + 1) (by omega) hm (by omega) hp
          cases hb : isPb m (r - (i + 1)) (i + 1)
          · rfl
          · exact absurd ((ih (r - (i + 1)) (by omega) (i + 1)).mp hb) hn
      · left; left; exact hm

end Rubidium
