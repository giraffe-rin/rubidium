/-
  Rubidium.K4Even — 定理 K4 の m が偶数の場合の形式化

  定理 K4（gemini-2 が査読済み）のうち m が偶数の場合：すべての n で「(n, 0) が P 局面 ⇔ (m+1) | n」。
  ブロック全体の理論を使わない直接の証明：
  - `not_isP_of_row`：行 r がすべての p で P なら、1 ≤ d ≤ m、p ≠ d の (r + d, p) は N 局面（手 d で (r, d) に移れる）。
  - `row_all`：m が偶数なら、行 j(m+1) はすべての p で P 局面。(j(m+1) + (m+1), p) からの手 k の行き先は
    (j(m+1) + (m+1−k), k) で、これが P になりうるのは k = m+1−k のときだけだが、m+1 は奇数なのでそうならない。
  - `K4_even`：m が偶数なら、IsP m n 0 ↔ n % (m+1) = 0。
-/
import Rubidium.Game

namespace Rubidium

/-- 行 r がすべての p で P 局面なら、1 ≤ d ≤ m、p ≠ d の (r + d, p) は N 局面。-/
theorem not_isP_of_row (m r d p : Nat) (hrow : ∀ p', IsP m r p') (hd1 : 1 ≤ d) (hdm : d ≤ m) (hpd : p ≠ d) :
    ¬ IsP m (r + d) p := by
  rw [isP_iff]
  intro h
  apply h d hd1 hdm (by omega) (fun e => hpd e.symm)
  have hs : r + d - d = r := by omega
  rw [hs]; exact hrow d

/-- m が偶数なら、行 j(m+1) はすべての p で P 局面。-/
theorem row_all (m : Nat) (hm : m % 2 = 0) : ∀ j p, IsP m (j * (m + 1)) p := by
  intro j
  induction j with
  | zero => intro p; rw [Nat.zero_mul]; exact isP_zero m p
  | succ j ih =>
    intro p
    rw [isP_iff]
    intro k hk1 hkm _ _ hPk
    have hs : (j + 1) * (m + 1) - k = j * (m + 1) + (m + 1 - k) := by
      rw [Nat.succ_mul]; omega
    rw [hs] at hPk
    exact not_isP_of_row m (j * (m + 1)) (m + 1 - k) k ih (by omega) (by omega) (by omega) hPk

/-- 定理 K4 の m が偶数の場合：IsP m n 0 ↔ (m+1) | n。-/
theorem K4_even (m : Nat) (hm : m % 2 = 0) (n : Nat) : IsP m n 0 ↔ n % (m + 1) = 0 := by
  have hdiv : n = (n / (m + 1)) * (m + 1) + n % (m + 1) := by
    have := Nat.div_add_mod n (m + 1)
    rw [Nat.mul_comm] at this; omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    have hlt : n % (m + 1) < m + 1 := Nat.mod_lt n (by omega)
    rw [hdiv] at hP
    exact not_isP_of_row m _ (n % (m + 1)) 0 (row_all m hm (n / (m + 1))) (by omega) (by omega) (by omega) hP
  · intro h0
    rw [hdiv, h0, Nat.add_zero]
    exact row_all m hm (n / (m + 1)) 0

end Rubidium
