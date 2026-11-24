/-
  Rubidium.K29gen — 定理 K29（すべての奇数 v ≥ 5）の形式化

  定理 K29：v ≥ 5 を奇数、m + 1 = 2^v·u、u ≡ 1 (mod 4) なら、型は前周期なし、周期 1 0^{(v−1)/2}。
  K38 の一般の形式化（Rubidium.K38gen）と同じ道具を使う。違いは次のとおり。
  - 追う q（「よい q」）：q ≡ 1 (mod 4)（S₁[q] = F）と qu ≡ 3 (mod 8)（S₁[q] = T）。T(q) := (qu mod 8 = 3)。
    ブロック 1（行 b）で S₁[2^b q] = (T(q) ↔ b が偶数)（`k29_S0`）。E 型のブロック c_j でも、2j ≤ b ≤ v − 3 なら同じ値（`k29_istep`）。
  - h の所属：c_j（1 ≤ j ≤ (v−3)/2）では H/2 = 2^{v−2}u が P（q = 1, 5 の値が F）なので、手 H/2 で h は N。
    最後の c_{(v−1)/2} では、H/2 は N（Blk）、3H/2 は 1 つ前のブロックで N（u ≡ 1 (mod 8) なら T(3)、u ≡ 5 (mod 8) なら T(7)）なので h は P。
  - 周期の始まりの行で使うのは、Blk m 1 と (a + h) が P であることだけ。
-/
import Rubidium.K38w

namespace Rubidium

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-- Blk の範囲を狭めてもよい。-/
theorem blk_mono (m s t r : Nat) (hts : t ≤ s) (h : Blk m s r) : Blk m t r :=
  fun d hd1 hdm hdt => h d hd1 hdm (by omega)

section K29g

variable (m v u : Nat) (hv5 : 5 ≤ v) (hvo : v % 2 = 1) (hmu : m + 1 = 2 ^ v * u) (hu : u % 4 = 1)
include hv5 hvo hmu hu

theorem k29_le (x : Nat) (hx : x < 2 ^ v) : x * u + u ≤ m + 1 := by
  rw [hmu, ← Nat.succ_mul]; exact Nat.mul_le_mul_right u hx

theorem k29_hdef : m + 1 = 2 * (2 ^ (v - 1) * u) := by
  rw [hmu, ← Nat.mul_assoc, ← Nat.pow_succ']; congr 2; omega

theorem k29_m8 : (m + 1) % 8 = 0 := by
  rw [hmu, show v = (v - 3) + 3 by omega, Nat.pow_add]; simp [Nat.mul_mod, Nat.mul_assoc]

/-- 行 b の事実 S0：よい q（q ≡ 1 (mod 4) か qu ≡ 3 (mod 8)）で 2^b·q < 2^v なら、
    (b + 2^b·qu) が P ⇔ (qu ≡ 3 (mod 8) ⇔ b が偶数)。-/
theorem k29_S0 (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 1 a)
    (hrowb : ∀ p, IsP m (a + (m + 2)) p) (hah : IsP m (a + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u)) :
    ∀ q b, (q % 4 = 1 ∨ (q * u) % 8 = 3) → 2 ^ b * q < 2 ^ v →
      (IsP m (a + (m + 2) + 2 ^ b * (q * u)) (2 ^ b * (q * u)) ↔ ((q * u) % 8 = 3 ↔ b % 2 = 0)) := by
  have hh := k29_hdef m v u hv5 hvo hmu hu
  have hm8 := k29_m8 m v u hv5 hvo hmu hu
  have hhe : (2 ^ (v - 1) * u) % 2 = 0 := by omega
  intro q b hq hlt
  have hq1 : 1 ≤ q := by
    rcases hq with h | h
    · omega
    · apply Nat.pos_of_ne_zero; intro h0; rw [h0, Nat.zero_mul] at h; simp at h
  have hqlt : q < 2 ^ v := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left q (Nat.pow_pos (by omega))) hlt
  have hle := k29_le m v u hv5 hvo hmu hu q hqlt
  have hqu1 : 1 ≤ q * u := Nat.mul_pos (by omega) (by omega)
  -- qu ≡ 3 (mod 8) なら qu + 1 ≠ h（h = 2^(v-1)·u ≡ 0 (mod 8)）
  have hH8 : (2 ^ (v - 1) * u) % 8 = 0 := by
    rw [show v - 1 = (v - 4) + 3 by omega, Nat.pow_add]; simp [Nat.mul_mod, Nat.mul_assoc]
  have hne : (q * u) % 8 = 3 → q * u + 1 ≠ 2 ^ (v - 1) * u := fun h3 he => by omega
  have hmod4 : q % 4 = 1 → (q * u) % 4 = 1 := fun h => by rw [Nat.mul_mod, h, hu]
  -- (b + qu) が P ⇔ T(q)
  have hbase : IsP m (a + (m + 2) + q * u) (q * u) ↔ (q * u) % 8 = 3 := by
    have hcase : (q * u) % 4 = 1 ∨ (q * u) % 8 = 3 := by
      rcases hq with h | h
      · left; exact hmod4 h
      · right; exact h
    generalize hX : q * u = X at hle hqu1 hne hcase ⊢
    rcases hcase with h1 | h3
    · have heo : ((m + 2 + X) / 2) % 2 = 1 := by omega
      have hpe : IsP m (a + (m + 2 + X) / 2) ((m + 2 + X) / 2) :=
        (hblk _ (by omega) (by omega) (by rw [v2_odd _ heo]; omega)).mpr (by rw [v2_odd _ heo])
      constructor
      · intro hP
        exfalso
        exact not_isP_move m _ _ ((m + 2 + X) / 2) (by omega) (by omega) (by omega) (by omega)
          (by rw [show a + (m + 2) + X - (m + 2 + X) / 2 = a + (m + 2 + X) / 2 by omega]; exact hpe) hP
      · intro h; omega
    · have hv1 : v2 ((m + 2 + X) / 2) = 1 := v2_of_mod4 _ (by omega)
      have hN : ¬ IsP m (a + (m + 2 + X) / 2) ((m + 2 + X) / 2) := by
        rw [hblk _ (by omega) (by omega) (by omega), hv1]; omega
      constructor
      · intro _; exact h3
      · intro _
        exact p_oddb m (2 ^ (v - 1) * u) a X hh (by omega) hrow hrowb hah hqu1 (by omega) (hne h3) (by omega) hN
  have hle2 := k29_le m v u hv5 hvo hmu hu (2 ^ b * q) hlt
  rw [Nat.mul_assoc] at hle2
  rw [o_iter m (2 ^ (v - 1) * u) a (q * u) hh hhe hrow hrowb hah hqu1 b (by omega), hbase]


/-- E 型のブロック c = p + (m+1) での補題 Inh の 1 段（値 V(q, b) = (qu ≡ 3 (mod 8) ↔ b が偶数)）。-/
theorem k29_istep (p c : Nat) (hc : c = p + (m + 1)) (hrowp : ∀ q, IsP m p q) (hrowc : ∀ q, IsP m c q)
    (j : Nat) (hj : 1 ≤ j) (hblk : Blk m (2 * j - 1) c)
    (hprev : ∀ q b, (q % 4 = 1 ∨ (q * u) % 8 = 3) → 2 * (j - 1) ≤ b → b + 3 ≤ v → 2 ^ b * q < 2 ^ v →
      (IsP m (p + 2 ^ b * (q * u)) (2 ^ b * (q * u)) ↔ ((q * u) % 8 = 3 ↔ b % 2 = 0))) :
    ∀ q b, (q % 4 = 1 ∨ (q * u) % 8 = 3) → 2 * j ≤ b → b + 3 ≤ v → 2 ^ b * q < 2 ^ v →
      (IsP m (c + 2 ^ b * (q * u)) (2 ^ b * (q * u)) ↔ ((q * u) % 8 = 3 ↔ b % 2 = 0)) := by
  intro q b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro hq hb hbv hlt
    obtain ⟨b1, rfl⟩ : ∃ b1, b = b1 + 1 := ⟨b - 1, by omega⟩
    have hq1 : 1 ≤ q := by
      rcases hq with h | h
      · omega
      · apply Nat.pos_of_ne_zero; intro h0; rw [h0, Nat.zero_mul] at h; simp at h
    have hqu1 : 1 ≤ q * u := Nat.mul_pos (by omega) (by omega)
    have hquo : (q * u) % 2 = 1 := by
      rw [Nat.mul_mod]
      have : q % 2 = 1 := by
        rcases hq with h | h
        · omega
        · apply Decidable.byContradiction; intro hne
          have h0 : q % 2 = 0 := by omega
          have : (q * u) % 2 = 0 := by rw [Nat.mul_mod, h0, Nat.zero_mul]
          omega
      rw [this, show u % 2 = 1 by omega]
    have hx1 : 1 ≤ 2 ^ b1 * (q * u) := Nat.mul_pos (Nat.pow_pos (by omega)) hqu1
    have hD : 2 ^ (b1 + 1) * (q * u) = 2 * (2 ^ b1 * (q * u)) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ b1) 2, Nat.mul_assoc]
    have hle := k29_le m v u hv5 hvo hmu hu (2 ^ (b1 + 1) * q) hlt
    rw [Nat.mul_assoc, hD] at hle
    have hh := k29_hdef m v u hv5 hvo hmu hu
    have hsplit : 2 ^ (v - 1) = 2 ^ b1 * 2 ^ (v - (b1 + 1)) := by rw [← Nat.pow_add]; congr 1; omega
    have hq' : 2 ^ (v - 1) * u + 2 ^ b1 * (q * u) = 2 ^ b1 * ((q + 2 ^ (v - (b1 + 1))) * u) := by
      rw [hsplit, Nat.mul_assoc, ← Nat.mul_add, Nat.add_mul, Nat.add_comm]
    have hpow8 : 2 ^ (v - (b1 + 1)) % 8 = 0 := by
      rw [show v - (b1 + 1) = (v - (b1 + 1) - 3) + 3 by omega, Nat.pow_add]; simp [Nat.mul_mod_left]
    have hq'u : ((q + 2 ^ (v - (b1 + 1))) * u) % 8 = (q * u) % 8 := by
      rw [Nat.add_mul, Nat.add_mod, Nat.mul_mod (2 ^ (v - (b1 + 1))), hpow8]; simp
    have hq'G : (q + 2 ^ (v - (b1 + 1))) % 4 = 1 ∨ ((q + 2 ^ (v - (b1 + 1))) * u) % 8 = 3 := by
      rcases hq with h | h
      · left; omega
      · right; rw [hq'u]; exact h
    have hq'lt : 2 ^ b1 * (q + 2 ^ (v - (b1 + 1))) < 2 ^ v := by
      rw [Nat.mul_add, ← Nat.pow_add, show b1 + (v - (b1 + 1)) = v - 1 by omega]
      have h1 : 2 ^ (b1 + 1) * q = 2 * (2 ^ b1 * q) := by rw [Nat.pow_succ, Nat.mul_comm (2 ^ b1) 2, Nat.mul_assoc]
      have h2 : 2 ^ v = 2 * 2 ^ (v - 1) := by rw [← Nat.pow_succ']; congr 1; omega
      omega
    rw [hc, e_iff m (2 ^ (v - 1) * u) p _ hh hrowp (by rw [← hc]; exact hrowc) (by omega) (by omega) (by omega),
      ← hc, show 2 ^ (b1 + 1) * (q * u) / 2 = 2 ^ b1 * (q * u) by omega, hq']
    have hT2 := hprev (q + 2 ^ (v - (b1 + 1))) b1 hq'G (by omega) (by omega) hq'lt
    rw [hT2, hq'u]
    by_cases hbj : b1 + 1 = 2 * j
    · have hv2 : v2 (2 ^ b1 * (q * u)) = b1 := by rw [v2_pow_mul _ hqu1, v2_odd _ hquo, Nat.add_zero]
      have hT1 : ¬ IsP m (c + 2 ^ b1 * (q * u)) (2 ^ b1 * (q * u)) := by
        rw [hblk _ hx1 (by omega) (by omega), hv2]; omega
      constructor
      · intro ⟨_, h2⟩; omega
      · intro hv; exact ⟨hT1, by omega⟩
    · have hT1 := ih b1 (by omega) hq (by omega) (by omega)
        (by have : 2 ^ (b1 + 1) * q = 2 * (2 ^ b1 * q) := by
              rw [Nat.pow_succ, Nat.mul_comm (2 ^ b1) 2, Nat.mul_assoc]
            omega)
      rw [hT1]; omega


/-- c = p + (m+1)、D = 2^(v-2)·(k·u)（k = 1, 3）について、e_iff を 2^(v-3) の形で書いたもの。-/
theorem k29_eD (p c k : Nat) (hc : c = p + (m + 1)) (hrowp : ∀ q, IsP m p q) (hrowc : ∀ q, IsP m c q)
    (hk : k = 1 ∨ k = 3) :
    IsP m (c + 2 ^ (v - 2) * (k * u)) (2 ^ (v - 2) * (k * u)) ↔
      (¬ IsP m (c + 2 ^ (v - 3) * (k * u)) (2 ^ (v - 3) * (k * u)) ∧
       ¬ IsP m (p + 2 ^ (v - 3) * ((k + 4) * u)) (2 ^ (v - 3) * ((k + 4) * u))) := by
  have hh := k29_hdef m v u hv5 hvo hmu hu
  have e2 : 2 ^ (v - 2) = 2 * 2 ^ (v - 3) := by rw [← Nat.pow_succ']; congr 1; omega
  have e1 : 2 ^ (v - 1) = 4 * 2 ^ (v - 3) := by
    rw [show v - 1 = (v - 3) + 2 by omega, Nat.pow_add, Nat.mul_comm]
  have hy1 : 1 ≤ 2 ^ (v - 3) * u := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  have hH : 2 ^ (v - 1) * u = 4 * (2 ^ (v - 3) * u) := by rw [e1, Nat.mul_assoc]
  have hDk : 2 ^ (v - 2) * (k * u) = 2 * k * (2 ^ (v - 3) * u) := by
    rw [e2, Nat.mul_assoc 2, Nat.mul_left_comm (2 ^ (v - 3)) k u, ← Nat.mul_assoc]
  have hk1 : 2 ^ (v - 3) * (k * u) = k * (2 ^ (v - 3) * u) := Nat.mul_left_comm _ _ _
  have hk4 : 2 ^ (v - 3) * ((k + 4) * u) = (k + 4) * (2 ^ (v - 3) * u) := Nat.mul_left_comm _ _ _
  have hle : 2 ^ (v - 2) * (k * u) ≤ m := by
    have := k29_le m v u hv5 hvo hmu hu (2 ^ (v - 2) * k) (by
      have h4 : 2 ^ v = 4 * 2 ^ (v - 2) := by
        rw [show 2 ^ v = 2 ^ ((v - 2) + 2) by congr 1; omega, Nat.pow_add, Nat.mul_comm]
      have hp : 0 < 2 ^ (v - 2) := Nat.pow_pos (by omega)
      rcases hk with rfl | rfl <;> omega)
    rw [Nat.mul_assoc] at this; omega
  rw [hDk] at hle ⊢; rw [hk1, hk4]; rw [hH] at hh
  generalize hy : 2 ^ (v - 3) * u = y at hh hy1 hle ⊢
  rw [hc, e_iff m (4 * y) p (2 * k * y) hh hrowp (by rw [← hc]; exact hrowc)
      (by rcases hk with rfl | rfl <;> omega) hle (by rcases hk with rfl | rfl <;> omega), ← hc,
    show 2 * k * y / 2 = k * y by rcases hk with rfl | rfl <;> omega,
    show 4 * y + k * y = (k + 4) * y by rcases hk with rfl | rfl <;> omega]

/-- K29 の 1 周期分（v = 2s + 5）。行 a・Blk m 1 a・(a + h) が P から、行 b + j(m+1)（j ≤ s+2）がすべての p で P、
    行 a' = b + (s+2)(m+1) で Blk m 1 と (a' + h) が P。-/
theorem k29g_step (s : Nat) (hs : v = 2 * s + 5) (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 1 a)
    (hah : IsP m (a + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u)) :
    (∀ j, j ≤ s + 2 → ∀ p, IsP m (a + (m + 2) + j * (m + 1)) p) ∧
    Blk m 1 (a + (m + 2) + (s + 2) * (m + 1)) ∧
    IsP m (a + (m + 2) + (s + 2) * (m + 1) + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u) := by
  have hh := k29_hdef m v u hv5 hvo hmu hu
  have hmo : m % 2 = 1 := by omega
  have hh2 : (m + 1) / 2 = 2 ^ (v - 1) * u := by omega
  have hvh : v2 (2 ^ (v - 1) * u) = v - 1 := by rw [v2_pow_mul u (by omega), v2_odd u (by omega), Nat.add_zero]
  have h2v : 2 ≤ 2 ^ (v - 1) := by
    rw [show v - 1 = (v - 2) + 1 by omega, Nat.pow_succ]
    have : 0 < 2 ^ (v - 2) := Nat.pow_pos (by omega)
    omega
  have hH2 : 2 ≤ 2 ^ (v - 1) * u := Nat.le_trans h2v (Nat.le_mul_of_pos_right _ (by omega))
  have hb := row_long m a hmo (by omega) hrow (by rw [hh2]; exact hah)
  have S0 := k29_S0 m v u hv5 hvo hmu hu a hrow hblk hb hah
  have hpos : ∀ j, a + (m + 2) + (j + 1) * (m + 1) = a + (m + 2) + j * (m + 1) + (m + 1) := by
    intro j; rw [Nat.succ_mul]; omega
  have hpos0 : a + (m + 2) + 0 * (m + 1) = a + (m + 2) := by rw [Nat.zero_mul, Nat.add_zero]
  have hb0 : ∀ p, IsP m (a + (m + 2) + 0 * (m + 1)) p := by rw [hpos0]; exact hb
  let I : Nat → Prop := fun j => ∀ q b, (q % 4 = 1 ∨ (q * u) % 8 = 3) → 2 * j ≤ b → b + 3 ≤ v → 2 ^ b * q < 2 ^ v →
    (IsP m (a + (m + 2) + j * (m + 1) + 2 ^ b * (q * u)) (2 ^ b * (q * u)) ↔ ((q * u) % 8 = 3 ↔ b % 2 = 0))
  have I0 : I 0 := by intro q b hq _ _ hlt; rw [hpos0]; exact S0 q b hq hlt
  have p8 : 2 ^ v = 8 * 2 ^ (v - 3) := by
    rw [show 2 ^ v = 2 ^ ((v - 3) + 3) by congr 1; omega, Nat.pow_add, Nat.mul_comm]
  have hp3 : 0 < 2 ^ (v - 3) := Nat.pow_pos (by omega)
  have hu1 : (1 * u) % 8 ≠ 3 := by omega
  have hu5' : (5 * u) % 8 ≠ 3 := by omega
  -- (c_j + h) は N：H/2 = 2^(v-2)·u が P（I j の q = 1 と I (j-1) の q = 5）
  have Nof : ∀ j, I j → I (j + 1) → 2 * (j + 1) + 3 ≤ v →
      (∀ p, IsP m (a + (m + 2) + j * (m + 1)) p) → (∀ p, IsP m (a + (m + 2) + (j + 1) * (m + 1)) p) →
      ¬ IsP m (a + (m + 2) + (j + 1) * (m + 1) + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u) := by
    intro j Ij Ij1 hjv hrj hrj1
    have hhalf : IsP m (a + (m + 2) + (j + 1) * (m + 1) + 2 ^ (v - 2) * (1 * u)) (2 ^ (v - 2) * (1 * u)) := by
      rw [k29_eD m v u hv5 hvo hmu hu _ _ 1 (hpos j) hrj hrj1 (Or.inl rfl)]
      constructor
      · rw [Ij1 1 (v - 3) (Or.inl rfl) (by omega) (by omega) (by omega)]; omega
      · rw [Ij 5 (v - 3) (Or.inl rfl) (by omega) (by omega) (by omega)]; omega
    rw [Nat.one_mul] at hhalf
    have e1 : 2 ^ (v - 1) * u = 2 * (2 ^ (v - 2) * u) := by
      rw [show 2 ^ (v - 1) = 2 * 2 ^ (v - 2) by rw [← Nat.pow_succ']; congr 1; omega, Nat.mul_assoc]
    rw [e1]
    exact not_isP_move m _ _ (2 ^ (v - 2) * u) (Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)) (by omega)
      (by omega) (by omega)
      (by rw [show a + (m + 2) + (j + 1) * (m + 1) + 2 * (2 ^ (v - 2) * u) - 2 ^ (v - 2) * u
              = a + (m + 2) + (j + 1) * (m + 1) + 2 ^ (v - 2) * u by omega]; exact hhalf)
  have Nb : ¬ IsP m (a + (m + 2) + 0 * (m + 1) + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u) := by
    rw [hpos0]
    have := S0 1 (v - 1) (Or.inl rfl) (by
      rw [Nat.mul_one, show 2 ^ v = 2 * 2 ^ (v - 1) by rw [← Nat.pow_succ']; congr 1; omega]
      have : 0 < 2 ^ (v - 1) := Nat.pow_pos (by omega)
      omega)
    rw [Nat.one_mul] at this; rw [this]; omega
  have bundle : ∀ j, 1 ≤ j → j ≤ s + 2 →
      (∀ p, IsP m (a + (m + 2) + j * (m + 1)) p) ∧ Blk m (2 * j - 1) (a + (m + 2) + j * (m + 1)) ∧
      (j ≤ s + 1 → I j ∧ ¬ IsP m (a + (m + 2) + j * (m + 1) + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u)) ∧
      I (j - 1) := by
    intro j hj1 hj2
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hj0 : j = 0
      · subst hj0
        have hr1 : ∀ p, IsP m (a + (m + 2) + (0 + 1) * (m + 1)) p := by
          rw [hpos 0]; exact row_next m _ hb0 (by rw [hh2]; exact Nb)
        have hodd1 := odd_of_rows m _ hmo hr1 (Or.inr ⟨_, hpos 0, hb0⟩)
        have hblk1 := blk1_direct m _ hr1 hodd1
        have I1 : I 1 := k29_istep m v u hv5 hvo hmu hu _ _ (hpos 0) hb0 hr1 1 (Nat.le_refl 1) hblk1 I0
        exact ⟨hr1, hblk1, fun _ => ⟨I1, Nof 0 I0 I1 (by omega) hb0 hr1⟩, I0⟩
      · obtain ⟨hrj, hblkj, hIN, _⟩ := ih (by omega) (by omega)
        obtain ⟨Ij, hNj⟩ := hIN (by omega)
        have hr : ∀ p, IsP m (a + (m + 2) + (j + 1) * (m + 1)) p := by
          rw [hpos j]; exact row_next m _ hrj (by rw [hh2]; exact hNj)
        have hblk' : Blk m (2 * (j + 1) - 1) (a + (m + 2) + (j + 1) * (m + 1)) := by
          rw [hpos j]
          exact blk_step2 m (2 * j - 1) (2 * (j + 1) - 1) _ hmo (by omega) (by omega) (by rw [hh2, hvh]; omega)
            hrj hblkj (by rw [← hpos j]; exact hr)
        refine ⟨hr, hblk', ?_, by rw [show j + 1 - 1 = j by omega]; exact Ij⟩
        intro hjs
        have Ij1 : I (j + 1) := k29_istep m v u hv5 hvo hmu hu _ _ (hpos j) hrj hr (j + 1) (by omega) hblk'
          (by intro q b hq hb hbv hlt; exact Ij q b hq (by omega) hbv hlt)
        exact ⟨Ij1, Nof j Ij Ij1 (by omega) hrj hr⟩
  -- 最後の行 c_{s+2}
  obtain ⟨hrL, hblkL, _, IL1⟩ := bundle (s + 2) (by omega) (Nat.le_refl _)
  obtain ⟨hrL1, _, hIN1, _⟩ := bundle (s + 1) (by omega) (by omega)
  obtain ⟨Is1, _⟩ := hIN1 (by omega)
  have Is : I s := by
    by_cases hs0 : s = 0
    · subst hs0; exact I0
    · exact ((bundle s (by omega) (by omega)).2.2.1 (by omega)).1
  have hrs : ∀ p, IsP m (a + (m + 2) + s * (m + 1)) p := by
    by_cases hs0 : s = 0
    · subst hs0; exact hb0
    · exact (bundle s (by omega) (by omega)).1
  -- (c_{s+1} + 3H/2) は N
  have h3N : ¬ IsP m (a + (m + 2) + (s + 1) * (m + 1) + 2 ^ (v - 2) * (3 * u)) (2 ^ (v - 2) * (3 * u)) := by
    rw [k29_eD m v u hv5 hvo hmu hu _ _ 3 (hpos s) hrs hrL1 (Or.inr rfl)]
    intro ⟨hA, hB⟩
    by_cases hu8 : u % 8 = 1
    · apply hA
      rw [Is1 3 (v - 3) (Or.inr (by omega)) (by omega) (by omega) (by omega)]; omega
    · apply hB
      rw [show 3 + 4 = 7 from rfl, Is 7 (v - 3) (Or.inr (by omega)) (by omega) (by omega) (by omega)]; omega
  -- (c_{s+2} + h) は P
  have hlast : IsP m (a + (m + 2) + (s + 2) * (m + 1) + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u) := by
    have e1 : 2 ^ (v - 1) * u = 2 * (2 ^ (v - 2) * u) := by
      rw [show 2 ^ (v - 1) = 2 * 2 ^ (v - 2) by rw [← Nat.pow_succ']; congr 1; omega, Nat.mul_assoc]
    have hy1 : 1 ≤ 2 ^ (v - 2) * u := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
    have hv2 : v2 (2 ^ (v - 2) * u) = v - 2 := by rw [v2_pow_mul u (by omega), v2_odd u (by omega), Nat.add_zero]
    have hhalfN : ¬ IsP m (a + (m + 2) + (s + 2) * (m + 1) + 2 ^ (v - 2) * u) (2 ^ (v - 2) * u) := by
      rw [hblkL _ hy1 (by omega) (by rw [hv2]; omega), hv2]; omega
    have h3 : 2 ^ (v - 2) * (3 * u) = 3 * (2 ^ (v - 2) * u) := Nat.mul_left_comm _ _ _
    rw [h3] at h3N
    rw [hpos (s + 1), e1, e_iff m (2 * (2 ^ (v - 2) * u)) _ _ (by rw [← e1]; exact hh) hrL1
      (by rw [← hpos (s + 1)]; exact hrL) (by omega) (by omega) (by omega),
      show 2 * (2 ^ (v - 2) * u) / 2 = 2 ^ (v - 2) * u by omega,
      show 2 * (2 ^ (v - 2) * u) + 2 ^ (v - 2) * u = 3 * (2 ^ (v - 2) * u) by omega, ← hpos (s + 1)]
    exact ⟨hhalfN, h3N⟩
  refine ⟨?_, blk_mono m _ 1 _ (by omega) hblkL, hlast⟩
  intro j hj
  by_cases hj0 : j = 0
  · subst hj0; exact hb0
  · exact (bundle j (by omega) hj).1


theorem k29g_rows (s : Nat) (hs : v = 2 * s + 5) :
    ∀ i, (∀ p, IsP m (i * ((m + 2) + (s + 2) * (m + 1))) p) ∧ Blk m 1 (i * ((m + 2) + (s + 2) * (m + 1))) ∧
      IsP m (i * ((m + 2) + (s + 2) * (m + 1)) + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u) := by
  intro i
  induction i with
  | zero =>
    rw [Nat.zero_mul, Nat.zero_add]
    refine ⟨isP_zero m, blk_zero m 1, ?_⟩
    have hh := k29_hdef m v u hv5 hvo hmu hu
    rw [K3 m _ _ (Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)) (by omega), ev2_iff_v2 _
      (Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)), v2_pow_mul u (by omega), v2_odd u (by omega)]
    exact ⟨rfl, by omega⟩
  | succ i ih =>
    obtain ⟨hrow, hblk, hah⟩ := ih
    obtain ⟨hrows, hb, hh'⟩ := k29g_step m v u hv5 hvo hmu hu s hs _ hrow hblk hah
    have e : (i + 1) * ((m + 2) + (s + 2) * (m + 1)) = i * ((m + 2) + (s + 2) * (m + 1)) + (m + 2) + (s + 2) * (m + 1) := by
      rw [Nat.succ_mul]; omega
    rw [e]
    exact ⟨hrows (s + 2) (Nat.le_refl _), hb, hh'⟩

end K29g

/-- 定理 K29（すべての奇数 v ≥ 5）：m + 1 = 2^v·u、u ≡ 1 (mod 4) なら、型は 1 0^{(v−1)/2}：
    L = (m+2) + ((v−1)/2)(m+1) として、(n, 0) が P ⇔ n mod L = 0、または n mod L ≥ m+2 かつ (n mod L − (m+2)) が m+1 の倍数。-/
theorem K29_gen (m v u : Nat) (hv5 : 5 ≤ v) (hvo : v % 2 = 1) (hmu : m + 1 = 2 ^ v * u) (hu : u % 4 = 1) (n : Nat) :
    IsP m n 0 ↔ (n % ((m + 2) + ((v - 1) / 2) * (m + 1)) = 0 ∨
      (m + 2 ≤ n % ((m + 2) + ((v - 1) / 2) * (m + 1)) ∧
        (n % ((m + 2) + ((v - 1) / 2) * (m + 1)) - (m + 2)) % (m + 1) = 0)) := by
  obtain ⟨s, hs⟩ : ∃ s, v = 2 * s + 5 := ⟨(v - 5) / 2, by omega⟩
  have hL : (v - 1) / 2 = s + 2 := by omega
  rw [hL]
  have hh := k29_hdef m v u hv5 hvo hmu hu
  obtain ⟨hrowA, hblkA, hahA⟩ := k29g_rows m v u hv5 hvo hmu hu s hs (n / ((m + 2) + (s + 2) * (m + 1)))
  obtain ⟨hrows, _, _⟩ := k29g_step m v u hv5 hvo hmu hu s hs _ hrowA hblkA hahA
  generalize hLL : (m + 2) + (s + 2) * (m + 1) = L at hrowA hblkA hahA hrows
  have hLpos : 0 < L := by omega
  have hdiv : n = (n / L) * L + n % L := by
    have := Nat.div_add_mod n L; rw [Nat.mul_comm] at this; omega
  have hlt : n % L < L := Nat.mod_lt n hLpos
  generalize hc : n % L = c at hdiv hlt
  generalize ha : n / L * L = A at hdiv hrowA hrows hahA
  subst hdiv
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases h1 : c ≤ m
    · exact not_isP_of_row m A c 0 hrowA (by omega) h1 (by omega) hP
    · by_cases h2 : c = m + 1
      · subst h2
        exact not_isP_near m A (2 ^ (v - 1) * u) 0 hh (by omega) (by omega) hahA (by omega) hP
      · have hj : (c - (m + 2)) / (m + 1) ≤ s + 1 := by
          apply Nat.le_of_lt_succ
          rw [Nat.div_lt_iff_lt_mul (by omega), Nat.succ_mul]
          rw [Nat.succ_mul] at hLL
          omega
        have hd : (c - (m + 2)) % (m + 1) ≠ 0 := by omega
        have hdlt : (c - (m + 2)) % (m + 1) < m + 1 := Nat.mod_lt _ (by omega)
        have hcd : A + c = A + (m + 2) + (c - (m + 2)) / (m + 1) * (m + 1) + (c - (m + 2)) % (m + 1) := by
          have := Nat.div_add_mod (c - (m + 2)) (m + 1)
          rw [Nat.mul_comm] at this; omega
        rw [hcd] at hP
        exact not_isP_of_row m _ _ 0 (hrows _ (by omega)) (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | ⟨h1, h2⟩
    · rw [h, Nat.add_zero]; exact hrowA 0
    · have hj : (c - (m + 2)) / (m + 1) ≤ s + 1 := by
        apply Nat.le_of_lt_succ
        rw [Nat.div_lt_iff_lt_mul (by omega), Nat.succ_mul]
        rw [Nat.succ_mul] at hLL
        omega
      have hcd : A + c = A + (m + 2) + (c - (m + 2)) / (m + 1) * (m + 1) := by
        have := Nat.div_add_mod (c - (m + 2)) (m + 1)
        rw [Nat.mul_comm, h2, Nat.add_zero] at this; omega
      rw [hcd]; exact hrows _ (by omega) 0

end Rubidium
