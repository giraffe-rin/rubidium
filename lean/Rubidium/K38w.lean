/-
  Rubidium.K38w — 定理 K38 をもとの仮定（w = v2(u+1)）の形で述べる

  `v2_decomp`：x ≥ 1 なら x = 2^{v2 x}·t（t は奇数）。
  `k38_hyp`：m + 1 = 2^v·u、w = v2(u+1) が奇数で 3 ≤ w ≤ v − 2、または w ≥ v + 1 なら、v2((m+2+u)/2) は偶数で v − 1 以下。
    u + 1 = 2^w·t とすると、m + 2 + u = 2^v·u + 2^w·t。w < v なら 2^w·(2^{v−w}·u + t)（括弧は奇数）で v2 = w。
    w ≥ v + 1 なら 2^v·(u + 2^{w−v}·t)（括弧は奇数）で v2 = v。
  `K38`：もとの形の定理 K38。
-/
import Rubidium.K38gen

namespace Rubidium

theorem v2_decomp : ∀ x, 1 ≤ x → ∃ t, t % 2 = 1 ∧ x = 2 ^ v2 x * t := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx
    by_cases ho : x % 2 = 1
    · exact ⟨x, ho, by rw [v2_odd x ho, Nat.pow_zero, Nat.one_mul]⟩
    · obtain ⟨t, ht, he⟩ := ih (x / 2) (by omega) (by omega)
      refine ⟨t, ht, ?_⟩
      rw [v2_even x (by omega) (by omega), Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2, ← Nat.mul_assoc, ← he]
      omega

/-- 奇数 y について v2(2^k·y) = k。-/
theorem v2_pow_odd (k y : Nat) (hy : y % 2 = 1) : v2 (2 ^ k * y) = k := by
  rw [v2_pow_mul y (by omega), v2_odd y hy, Nat.add_zero]

theorem k38_hyp (m v u : Nat) (hv5 : 5 ≤ v) (hvo : v % 2 = 1) (hmu : m + 1 = 2 ^ v * u) (hu : u % 4 = 3)
    (hw : (v2 (u + 1) % 2 = 1 ∧ 3 ≤ v2 (u + 1) ∧ v2 (u + 1) ≤ v - 2) ∨ v + 1 ≤ v2 (u + 1)) :
    v2 ((m + 2 + u) / 2) % 2 = 0 ∧ v2 ((m + 2 + u) / 2) ≤ v - 1 := by
  obtain ⟨t, ht, hut⟩ := v2_decomp (u + 1) (by omega)
  generalize hW : v2 (u + 1) = w at hw hut
  have hsum : m + 2 + u = 2 ^ v * u + 2 ^ w * t := by omega
  have hpos : 1 ≤ m + 2 + u := by omega
  have hev : (m + 2 + u) % 2 = 0 := by
    have : (2 ^ v * u) % 2 = 0 := by
      rw [show v = (v - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm (2 ^ (v - 1)) 2, Nat.mul_assoc]; simp
    omega
  have hhalf : v2 (m + 2 + u) = v2 ((m + 2 + u) / 2) + 1 := v2_even _ (by omega) hev
  rcases hw with ⟨hwo, hw3, hwv⟩ | hwv
  · -- w < v：2^w·(2^{v−w}·u + t)
    have hsplit : 2 ^ v = 2 ^ w * 2 ^ (v - w) := by rw [← Nat.pow_add]; congr 1; omega
    have hinner : (2 ^ (v - w) * u + t) % 2 = 1 := by
      have : (2 ^ (v - w) * u) % 2 = 0 := by
        rw [show v - w = (v - w - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm (2 ^ (v - w - 1)) 2, Nat.mul_assoc]; simp
      omega
    have : m + 2 + u = 2 ^ w * (2 ^ (v - w) * u + t) := by
      rw [hsum, hsplit, Nat.mul_assoc, ← Nat.mul_add]
    have h2 : v2 (m + 2 + u) = w := by rw [this, v2_pow_odd w _ hinner]
    omega
  · -- w ≥ v + 1：2^v·(u + 2^{w−v}·t)
    have hsplit : 2 ^ w = 2 ^ v * 2 ^ (w - v) := by rw [← Nat.pow_add]; congr 1; omega
    have hinner : (u + 2 ^ (w - v) * t) % 2 = 1 := by
      have : (2 ^ (w - v) * t) % 2 = 0 := by
        rw [show w - v = (w - v - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm (2 ^ (w - v - 1)) 2, Nat.mul_assoc]; simp
      omega
    have : m + 2 + u = 2 ^ v * (u + 2 ^ (w - v) * t) := by
      rw [hsum, hsplit, Nat.mul_assoc, ← Nat.mul_add]
    have h2 : v2 (m + 2 + u) = v := by rw [this, v2_pow_odd v _ hinner]
    omega

/-- 定理 K38（もとの形）：v ≥ 5 を奇数、m + 1 = 2^v·u（u ≡ 3 (mod 4)）、w = v2(u+1) とする。
    w が奇数で 3 ≤ w ≤ v − 2、または w ≥ v + 1 なら、型は前周期なし、周期 1 0^{(v+1)/2}。-/
theorem K38 (m v u : Nat) (hv5 : 5 ≤ v) (hvo : v % 2 = 1) (hmu : m + 1 = 2 ^ v * u) (hu : u % 4 = 3)
    (hw : (v2 (u + 1) % 2 = 1 ∧ 3 ≤ v2 (u + 1) ∧ v2 (u + 1) ≤ v - 2) ∨ v + 1 ≤ v2 (u + 1)) (n : Nat) :
    IsP m n 0 ↔ (n % ((m + 2) + ((v + 1) / 2) * (m + 1)) = 0 ∨
      (m + 2 ≤ n % ((m + 2) + ((v + 1) / 2) * (m + 1)) ∧
        (n % ((m + 2) + ((v + 1) / 2) * (m + 1)) - (m + 2)) % (m + 1) = 0)) :=
  K38_gen m v u hv5 hvo hmu hu (k38_hyp m v u hv5 hvo hmu hu hw) n

end Rubidium
