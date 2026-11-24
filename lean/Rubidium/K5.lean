/-
  Rubidium.K5 — 定理 K5 と、定理 K4 の「最初の P 局面」の部分の形式化

  定理 K4（gemini-2 が査読済み）の一部：(m+1, 0) が P 局面 ⇔ v2(m+1) が偶数。
  定理 K5（gemini-2 が査読済み）：m ≥ 2 で v2(m+1) が奇数なら、(m+2, 0) は P 局面。
  あわせて、1 ≤ n ≤ m の (n, 0) はどれも N 局面（全部取れる）。
  よって、開始局面 (n, 0) が最初に後手必勝になる n は、v2(m+1) が偶数なら m+1、奇数（m ≥ 2）なら m+2。
-/
import Rubidium.K3

namespace Rubidium

/-- 1 ≤ r ≤ m なら、(r, p)（p ≠ r）は N 局面。とくに 1 ≤ n ≤ m の (n, 0) は N 局面。-/
theorem not_isP_small (m n : Nat) (h1 : 1 ≤ n) (hn : n ≤ m) : ¬ IsP m n 0 := by
  rw [K3 m n 0 h1 hn]
  intro ⟨h, _⟩; omega

/-- (m+1, p) の P/N（p = 0 または p = 1）：移った先 (m+1−k, k) は K3 の範囲にある。
    (m+1, p) が P ⇔ 「m+1 が偶数、(m+1)/2 ≠ p、v2((m+1)/2) が偶数」でない。-/
theorem isP_succ (m p : Nat) (hm : 1 ≤ m) (hp : p ≤ 1) :
    IsP m (m + 1) p ↔ ¬ ((m + 1) % 2 = 0 ∧ (m + 1) / 2 ≠ p ∧ ev2 ((m + 1) / 2) = true) := by
  rw [isP_iff]
  constructor
  · intro hP ⟨heven, hne, hev⟩
    have hk1 : 1 ≤ (m + 1) / 2 := by omega
    apply hP ((m + 1) / 2) hk1 (by omega) (by omega) hne
    have hsub : m + 1 - (m + 1) / 2 = (m + 1) / 2 := by omega
    rw [K3 m (m + 1 - (m + 1) / 2) ((m + 1) / 2) (by omega) (by omega), hsub]
    exact ⟨rfl, hev⟩
  · intro hnot k hk1 hkm _ hkp hPk
    rw [K3 m (m + 1 - k) k (by omega) (by omega)] at hPk
    obtain ⟨hkeq, hev⟩ := hPk
    apply hnot
    have h2 : (m + 1) / 2 = m + 1 - k := by omega
    refine ⟨by omega, by omega, ?_⟩
    rw [h2]; exact hev

/-- 定理 K4 の一部：(m+1, 0) が P 局面 ⇔ v2(m+1) が偶数。-/
theorem K4_first (m : Nat) (hm : 1 ≤ m) : IsP m (m + 1) 0 ↔ ev2 (m + 1) = true := by
  rw [isP_succ m 0 hm (by omega), ev2_iff (m + 1) (by omega)]
  constructor
  · intro h ⟨he, hv⟩; exact h ⟨he, by omega, hv⟩
  · intro h ⟨he, _, hv⟩; exact h ⟨he, hv⟩

/-- 定理 K5：m ≥ 2 で v2(m+1) が奇数なら、(m+2, 0) は P 局面。-/
theorem K5 (m : Nat) (hm : 2 ≤ m) (hodd : ev2 (m + 1) = false) : IsP m (m + 2) 0 := by
  -- v2(m+1) が奇数なので m+1 は偶数、v2((m+1)/2) は偶数
  have hev := ev2_iff (m + 1) (by omega)
  rw [hodd] at hev
  have hboth : (m + 1) % 2 = 0 ∧ ev2 ((m + 1) / 2) = true :=
    Classical.byContradiction fun hc => absurd (hev.mpr hc) (by simp)
  obtain ⟨heven, hhalf⟩ := hboth
  rw [isP_iff]
  intro k hk1 hkm _ _ hPk
  by_cases hk : k = 1
  · -- k = 1：(m+1, 1) は N 局面（(m+1)/2 ≠ 1 なので、k' = (m+1)/2 で P に移れる）
    subst hk
    have hrw : m + 2 - 1 = m + 1 := by omega
    rw [hrw, isP_succ m 1 (by omega) (by omega)] at hPk
    exact hPk ⟨heven, by omega, hhalf⟩
  · -- k ≥ 2：移った先 (m+2−k, k) は K3 の範囲。P なら k = m+2−k だが、m+2 は奇数
    rw [K3 m (m + 2 - k) k (by omega) (by omega)] at hPk
    omega

/-- 1 ≤ n ≤ m+1 で、v2(m+1) が奇数なら (n, 0) は N 局面（K5 の「最初」の部分）。-/
theorem K5_before (m n : Nat) (hm : 1 ≤ m) (hodd : ev2 (m + 1) = false) (h1 : 1 ≤ n) (hn : n ≤ m + 1) :
    ¬ IsP m n 0 := by
  by_cases h : n = m + 1
  · subst h; rw [K4_first m hm, hodd]; simp
  · exact not_isP_small m n h1 (by omega)

end Rubidium
