/-
  Rubidium.K3 — 定理 K3 の形式化

  定理 K3（gemini-2 が査読済み）：1 ≤ r ≤ m のとき、局面 (r, p) が P 局面 ⇔ p = r かつ v2(r) が偶数。

  証明：r についての強い帰納法。
  - p ≠ r なら、r 個全部取って (0, r) に移せる。(0, r) は P 局面なので (r, p) は N 局面。
  - p = r なら、取れるのは 1 ≤ k ≤ r − 1 で、移った先 (r − k, k) は 1 ≤ r − k < r ≤ m。
    帰納法の仮定から、(r − k, k) が P ⇔ k = r − k かつ v2(r − k) が偶数。
    よって (r, r) が P ⇔「r が偶数で v2(r/2) が偶数」でない ⇔ v2(r) が偶数。
-/
import Rubidium.Game

namespace Rubidium

/-- v2(r) が偶数 ⇔ 「r が偶数で v2(r/2) が偶数」でない（r ≥ 1）。-/
theorem ev2_iff (r : Nat) (h : 1 ≤ r) :
    ev2 r = true ↔ ¬ (r % 2 = 0 ∧ ev2 (r / 2) = true) := by
  by_cases hp : r % 2 = 1
  · rw [ev2_odd r hp]
    constructor
    · intro _ ⟨h2, _⟩; omega
    · intro _; rfl
  · have h0 : r % 2 = 0 := by omega
    rw [ev2_even r (by omega) h0]
    cases ev2 (r / 2) <;> simp [h0]

/-- 定理 K3。-/
theorem K3 (m : Nat) : ∀ r p, 1 ≤ r → r ≤ m → (IsP m r p ↔ p = r ∧ ev2 r = true) := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro p h1 hrm
    by_cases hpr : p = r
    · subst hpr
      simp only [true_and]
      rw [isP_iff, ev2_iff p h1]
      constructor
      · -- (p, p) が P なら、「p が偶数で v2(p/2) が偶数」でない
        intro hP ⟨heven, hev⟩
        have hk1 : 1 ≤ p / 2 := by omega
        have hlt : p - p / 2 < p := by omega
        have hsub : p - p / 2 = p / 2 := by omega
        apply hP (p / 2) hk1 (by omega) (by omega) (by omega)
        rw [ih (p - p / 2) hlt (p / 2) (by omega) (by omega), hsub]
        exact ⟨rfl, hev⟩
      · -- 逆向き：どの手 k で移った先も P でない
        intro hnot k hk1 hkm hkr hkp hPk
        have hlt : p - k < p := by omega
        have hk' : k ≤ p - 1 := by omega
        rw [ih (p - k) hlt k (by omega) (by omega)] at hPk
        obtain ⟨hkeq, hev⟩ := hPk
        apply hnot
        refine ⟨by omega, ?_⟩
        have : p / 2 = p - k := by omega
        rw [this]; exact hev
    · -- p ≠ r：r 個全部取れば (0, r) で、これは P 局面
      constructor
      · intro hP
        rw [isP_iff] at hP
        have h0 := hP r h1 hrm (Nat.le_refl r) (fun h => hpr h.symm)
        rw [Nat.sub_self] at h0
        exact absurd (isP_zero m r) h0
      · intro ⟨h, _⟩; exact absurd h hpr

end Rubidium
