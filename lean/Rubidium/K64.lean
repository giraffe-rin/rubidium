/-
  Rubidium.K64 — 予想 K64（1^{j+2} 0 型）の証明

  定理 K64：m + 1 = 2h、3h + 1 = 4w（w 奇数）、X₀ = (m+2+w)/2、X_{t+1} = (m+2 + X_t/2)/2 とする。
    X_t ≡ 2 (mod 4)（t < j）、X_j が奇数なら、型は前周期なしで 1^{j+2} 0：
    L = (j+2)(m+2) + (m+1) として、(n, 0) が P ⇔ n mod L が (m+2) の倍数（で (j+2)(m+2) 以下）。
  行：a（始まり、Blk m 1）、B_r = a + r(m+2)（r = 1..j+2、O 型）、a' = B_{j+2} + (m+1)（次の始まり）。
  - O 型の B_r（r ≥ 1）で、偶数 X_s（≡ 2 (mod 4)）は「半分」→「奇数の相手」で 1 つ前のブロックの X_{s+1} に移る：
    (B_r + X_s) が P ⇔ (B_{r−1} + X_{s+1}) が P（`k64_shift`）。
  - h ∈ S_i（i ≥ 2）⇔ (B_{i−1} + 2w) が N ⇔ (B_{i−1} + w) が P ⇔ (B_{i−2} + X₀) が N ⇔ (a + X_{i−2}) が N ⇔ X_{i−2} が偶数。
-/
import Rubidium.K15gen

namespace Rubidium

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-- K64 の列 X。-/
def k64X (m w : Nat) : Nat → Nat
  | 0 => (m + 2 + w) / 2
  | t + 1 => (m + 2 + k64X m w t / 2) / 2

section K64

variable (m h w j : Nat) (hmh : m + 1 = 2 * h) (hW : 3 * h + 1 = 4 * w) (hwo : w % 2 = 1) (hm9 : 9 ≤ m)
  (hX : ∀ t, t < j → k64X m w t % 4 = 2) (hXj : k64X m w j % 2 = 1)
include hmh hW hwo hm9 hX hXj

theorem k64_h4 : h % 4 = 1 := by omega

/-- X_t の範囲：4 ≤ ... 、X_t ≤ (3m+5)/4 くらい（ここでは 2 ≤ X_t かつ 4·X_t ≤ 3m + 6）。-/
theorem k64_X_bound : ∀ t, 2 ≤ k64X m w t ∧ 4 * k64X m w t ≤ 3 * m + 6 := by
  intro t
  induction t with
  | zero => simp only [k64X]; omega
  | succ t ih => simp only [k64X]; omega

/-- O 型の B_r = p + (m+2)（行 p・行 B_r がすべての p で P、(p + h) が P）で、偶数 X_s（s < j）について
    (B_r + X_s) が P ⇔ (p + X_{s+1}) が P。-/
theorem k64_shift (p s : Nat) (hs : s < j) (hrowp : ∀ q, IsP m p q) (hrowb : ∀ q, IsP m (p + (m + 2)) q)
    (hph : IsP m (p + h) h) :
    IsP m (p + (m + 2) + k64X m w s) (k64X m w s) ↔ IsP m (p + k64X m w (s + 1)) (k64X m w (s + 1)) := by
  have hb := k64_X_bound m h w j hmh hW hwo hm9 hX hXj s
  have h4 := hX s hs
  have hh4 := k64_h4 m h w j hmh hW hwo hm9 hX hXj
  generalize hx : k64X m w s = x at hb h4 ⊢
  have hx1 : k64X m w (s + 1) = (m + 2 + x / 2) / 2 := by simp only [k64X]; rw [hx]
  rw [hx1]
  -- 半分
  rw [show x = 2 * (x / 2) by omega, o_half' m h p (x / 2) hmh hrowp hrowb hph (by omega) (by omega) (by omega),
    show 2 * (x / 2) / 2 = x / 2 by omega]
  -- 奇数の相手
  rw [o_odd_iff m h p (x / 2) hmh hrowp hrowb hph (by omega) (by omega) (by omega) (by omega)]
  constructor
  · intro h1; exact Classical.byContradiction h1
  · intro h1 h2; exact h2 h1


/-- 鎖：行 B_t = a + t(m+2)（t ≤ r）がすべての p で P、(B_t + h) が P（t < r）なら、
    s + r ≤ j で (B_r + X_s) が P ⇔ (a + X_{s+r}) が P。-/
theorem k64_chain (a : Nat) : ∀ r s, s + r ≤ j → (∀ t, t ≤ r → ∀ q, IsP m (a + t * (m + 2)) q) →
    (∀ t, t < r → IsP m (a + t * (m + 2) + h) h) →
    (IsP m (a + r * (m + 2) + k64X m w s) (k64X m w s) ↔ IsP m (a + k64X m w (s + r)) (k64X m w (s + r))) := by
  intro r
  induction r with
  | zero => intro s _ _ _; rw [Nat.zero_mul, Nat.add_zero, Nat.add_zero]
  | succ r ih =>
    intro s hsr hrows hh
    have e : a + (r + 1) * (m + 2) = a + r * (m + 2) + (m + 2) := by rw [Nat.succ_mul]; omega
    rw [e, k64_shift m h w j hmh hW hwo hm9 hX hXj _ s (by omega) (hrows r (by omega)) (by rw [← e]; exact hrows _ (Nat.le_refl _))
      (hh r (by omega)), ih (s + 1) (by omega) (fun t ht => hrows t (by omega)) (fun t ht => hh t (by omega)),
      show s + 1 + r = s + (r + 1) by omega]

/-- (B_i + h) が P ⇔ i ≤ j + 1（i ≥ 1）。行 B_t（t ≤ i）がすべての p で P、(B_t + h) が P（t < i）、Blk m 1 a を仮定。-/
theorem k64_hfact (a : Nat) (hblk : Blk m 1 a) (i : Nat) (hi1 : 1 ≤ i) (hij : i ≤ j + 2)
    (hrows : ∀ t, t ≤ i → ∀ q, IsP m (a + t * (m + 2)) q) (hh : ∀ t, t < i → IsP m (a + t * (m + 2) + h) h) :
    (IsP m (a + i * (m + 2) + h) h ↔ i ≤ j + 1) := by
  have h4 := k64_h4 m h w j hmh hW hwo hm9 hX hXj
  have hw2 : (m + 2 + h) / 2 = 2 * w := by omega
  have e : ∀ t, a + (t + 1) * (m + 2) = a + t * (m + 2) + (m + 2) := by intro t; rw [Nat.succ_mul]; omega
  obtain ⟨i1, rfl⟩ : ∃ i1, i = i1 + 1 := ⟨i - 1, by omega⟩
  -- (B_i + h) は、相手 (B_{i−1} + 2w) が N のとき P
  rw [e i1, o_odd_iff m h _ h hmh (hrows i1 (by omega)) (by rw [← e]; exact hrows _ (Nat.le_refl _))
    (hh i1 (by omega)) (by omega) (by omega) (by omega) (by omega), hw2]
  by_cases hi0 : i1 = 0
  · subst hi0
    rw [Nat.zero_mul, Nat.add_zero]
    have hv : v2 (2 * w) = 1 := by rw [v2_two_mul w (by omega), v2_odd w hwo]
    rw [hblk (2 * w) (by omega) (by omega) (by omega), hv]
    omega
  · obtain ⟨i2, rfl⟩ : ∃ i2, i1 = i2 + 1 := ⟨i1 - 1, by omega⟩
    have hX0 : (m + 2 + w) / 2 = k64X m w 0 := rfl
    -- (B_{i−1} + 2w) が P ⇔ (B_{i−1} + w) が N
    rw [e i2, o_half' m h _ w hmh (hrows i2 (by omega)) (by rw [← e]; exact hrows _ (by omega)) (hh i2 (by omega))
      (by omega) (by omega) (by omega)]
    -- (B_{i−1} + w) が P ⇔ (B_{i−2} + X₀) が N
    rw [o_odd_iff m h _ w hmh (hrows i2 (by omega)) (by rw [← e]; exact hrows _ (by omega)) (hh i2 (by omega))
      (by omega) hwo (by omega) (by omega), hX0]
    rw [k64_chain m h w j hmh hW hwo hm9 hX hXj a i2 0 (by omega) (fun t ht => hrows t (by omega))
      (fun t ht => hh t (by omega)), Nat.zero_add]
    have hb := k64_X_bound m h w j hmh hW hwo hm9 hX hXj i2
    by_cases hlt : i2 < j
    · have h42 := hX i2 hlt
      have hv : v2 (k64X m w i2) = 1 := v2_of_mod4 _ h42
      rw [hblk _ (by omega) (by omega) (by omega), hv]
      omega
    · have heq : i2 = j := by omega
      subst heq
      rw [hblk _ (by omega) (by omega) (by rw [v2_odd _ hXj]; omega), v2_odd _ hXj]
      omega

/-- K64 の 1 周期分。 -/
theorem k64_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 1 a) :
    (∀ t, t ≤ j + 2 → ∀ q, IsP m (a + t * (m + 2)) q) ∧ (∀ t, t ≤ j + 1 → IsP m (a + t * (m + 2) + h) h) ∧
    (∀ q, IsP m (a + (j + 2) * (m + 2) + (m + 1)) q) ∧ Blk m 1 (a + (j + 2) * (m + 2) + (m + 1)) := by
  have hmo : m % 2 = 1 := by omega
  have hhm : (m + 1) / 2 = h := by omega
  have e : ∀ t, a + (t + 1) * (m + 2) = a + t * (m + 2) + (m + 2) := by intro t; rw [Nat.succ_mul]; omega
  have hah : IsP m (a + h) h := (hblk h (by omega) (by omega) (by rw [v2_odd h (by omega)]; omega)).mpr
    (by rw [v2_odd h (by omega)])
  have G : ∀ i, i ≤ j + 2 → (∀ t, t ≤ i → ∀ q, IsP m (a + t * (m + 2)) q) ∧
      (∀ t, t ≤ i → t ≤ j + 1 → IsP m (a + t * (m + 2) + h) h) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨fun t ht => ?_, fun t ht _ => ?_⟩
      · rw [show t = 0 by omega, Nat.zero_mul, Nat.add_zero]; exact hrow
      · rw [show t = 0 by omega, Nat.zero_mul, Nat.add_zero]; exact hah
    | succ i ih =>
      intro hi
      obtain ⟨hr, hh⟩ := ih (by omega)
      have hri : ∀ q, IsP m (a + (i + 1) * (m + 2)) q := by
        rw [e i]; exact row_long m _ hmo (by omega) (hr i (Nat.le_refl _)) (by rw [hhm]; exact hh i (Nat.le_refl _) (by omega))
      have hr' : ∀ t, t ≤ i + 1 → ∀ q, IsP m (a + t * (m + 2)) q := by
        intro t ht; by_cases htt : t = i + 1
        · rw [htt]; exact hri
        · exact hr t (by omega)
      refine ⟨hr', fun t ht htj => ?_⟩
      by_cases htt : t = i + 1
      · rw [htt]
        exact (k64_hfact m h w j hmh hW hwo hm9 hX hXj a hblk (i + 1) (by omega) (by omega) hr'
          (fun t ht => hh t (by omega) (by omega))).mpr (by omega)
      · exact hh t (by omega) htj
  obtain ⟨hr, hh⟩ := G (j + 2) (Nat.le_refl _)
  have hN := (k64_hfact m h w j hmh hW hwo hm9 hX hXj a hblk (j + 2) (by omega) (Nat.le_refl _) hr
    (fun t ht => hh t (by omega) (by omega)))
  have hN' : ¬ IsP m (a + (j + 2) * (m + 2) + h) h := fun hP => by have := hN.mp hP; omega
  have ha' := row_next m _ (hr (j + 2) (Nat.le_refl _)) (by rw [hhm]; exact hN')
  have hodd := odd_of_rows m _ hmo ha' (Or.inr ⟨_, rfl, hr (j + 2) (Nat.le_refl _)⟩)
  exact ⟨hr, fun t ht => hh t (by omega) ht, ha', blk1_direct m _ ha' hodd⟩

theorem k64_rows : ∀ i, (∀ q, IsP m (i * ((j + 2) * (m + 2) + (m + 1))) q) ∧
    Blk m 1 (i * ((j + 2) * (m + 2) + (m + 1))) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 1⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, ha', hb'⟩ := k64_step m h w j hmh hW hwo hm9 hX hXj _ hrow hblk
    rw [Nat.succ_mul, show i * ((j + 2) * (m + 2) + (m + 1)) + ((j + 2) * (m + 2) + (m + 1))
      = i * ((j + 2) * (m + 2) + (m + 1)) + (j + 2) * (m + 2) + (m + 1) by omega]
    exact ⟨ha', hb'⟩

end K64

/-- 定理 K64：m + 1 = 2h、3h + 1 = 4w（w 奇数）、m ≥ 9、X_t ≡ 2 (mod 4)（t < j）、X_j 奇数なら、
    L = (j+2)(m+2) + (m+1) として、(n, 0) が P ⇔ n mod L が (m+2) の倍数で (j+2)(m+2) 以下。-/
theorem K64 (m h w j : Nat) (hmh : m + 1 = 2 * h) (hW : 3 * h + 1 = 4 * w) (hwo : w % 2 = 1) (hm9 : 9 ≤ m)
    (hX : ∀ t, t < j → k64X m w t % 4 = 2) (hXj : k64X m w j % 2 = 1) (n : Nat) :
    IsP m n 0 ↔ (n % ((j + 2) * (m + 2) + (m + 1)) % (m + 2) = 0 ∧
      n % ((j + 2) * (m + 2) + (m + 1)) ≤ (j + 2) * (m + 2)) := by
  obtain ⟨hrowA, hblkA⟩ := k64_rows m h w j hmh hW hwo hm9 hX hXj (n / ((j + 2) * (m + 2) + (m + 1)))
  obtain ⟨hr, hh, _, _⟩ := k64_step m h w j hmh hW hwo hm9 hX hXj _ hrowA hblkA
  generalize hLL : (j + 2) * (m + 2) + (m + 1) = L at hrowA hr hh
  have hLpos : 0 < L := by omega
  have hdiv : n = (n / L) * L + n % L := by
    have := Nat.div_add_mod n L; rw [Nat.mul_comm] at this; omega
  have hlt : n % L < L := Nat.mod_lt n hLpos
  generalize hc : n % L = c at hdiv hlt
  generalize ha : n / L * L = A at hdiv hrowA hr hh
  subst hdiv
  have hcd : A + c = A + c / (m + 2) * (m + 2) + c % (m + 2) := by
    have := Nat.div_add_mod c (m + 2); rw [Nat.mul_comm] at this; omega
  have hcj : c / (m + 2) ≤ j + 2 := by
    apply Nat.le_of_lt_succ; rw [Nat.div_lt_iff_lt_mul (by omega), Nat.succ_mul]
    have := Nat.mul_le_mul_right (m + 2) (Nat.le_refl (j + 2)); omega
  have hdl : c % (m + 2) < m + 2 := Nat.mod_lt _ (by omega)
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    rw [hcd] at hP
    by_cases hd0 : c % (m + 2) = 0
    · -- c > (j+2)(m+2) で余り 0 はありえない
      have : c / (m + 2) * (m + 2) = c := by have := Nat.div_add_mod c (m + 2); rw [Nat.mul_comm] at this; omega
      have h2 : (j + 2 + 1) * (m + 2) ≤ c := by
        have h3 : j + 2 < c / (m + 2) := by
          apply Decidable.byContradiction; intro h4
          have := Nat.mul_le_mul_right (m + 2) (show c / (m + 2) ≤ j + 2 by omega); omega
        exact Nat.le_trans (Nat.mul_le_mul_right _ h3) (by omega)
      rw [Nat.succ_mul] at h2; omega
    · by_cases hdm : c % (m + 2) ≤ m
      · exact not_isP_of_row m _ _ 0 (hr _ hcj) (by omega) hdm (by omega) hP
      · -- 余り m + 1：行 c/(m+2) の次の局面。c/(m+2) ≤ j+1 なら (B + h) が P なので N
        have hj1 : c / (m + 2) ≤ j + 1 := by
          apply Decidable.byContradiction; intro h4
          have h5 : c / (m + 2) = j + 2 := by omega
          have := Nat.div_add_mod c (m + 2); rw [h5, Nat.mul_comm] at this; omega
        rw [show c % (m + 2) = m + 1 by omega] at hP
        exact not_isP_near m _ h 0 hmh (by omega) (by omega) (hh _ hj1) (by omega) hP
  · intro ⟨h1, h2⟩
    rw [hcd, h1, Nat.add_zero]
    exact hr _ hcj 0

end Rubidium
