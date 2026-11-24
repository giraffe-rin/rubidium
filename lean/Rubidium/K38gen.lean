/-
  Rubidium.K38gen — 定理 K38 のすべての奇数 v ≥ 5 の場合の形式化（汎用の補題）

  記号：m + 1 = 2h（h は偶数）、行 a はすべての p で P、b = a + (m+2)、行 b もすべての p で P、(a + h, h) は P。
  - `o_half`：(b + 2z, 2z) が P ⇔ (b + z, z) が N（2z + 1 ≤ m）。
  - `o_iter`：(b + 2^i·x, 2^i·x) が P ⇔ ((b + x, x) が P ⇔ i が偶数)。
  - `e_iff`：c = p + (m+1)（行 p・行 c がすべての p' で P）の偶数 D について、
    (c + D, D) が P ⇔ (c + D/2, D/2) が N かつ (p + h + D/2, h + D/2) が N。
  - `v2_pow_mul`：v2(2^b·x) = b + v2(x)（x ≥ 1）。
-/
import Rubidium.K38v7

namespace Rubidium

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

theorem o_half (m h a z : Nat) (hmh : m + 1 = 2 * h) (hhe : h % 2 = 0) (hrow : ∀ p, IsP m a p)
    (hrowb : ∀ p, IsP m (a + (m + 2)) p) (hah : IsP m (a + h) h) (hz1 : 1 ≤ z) (hzm : 2 * z + 1 ≤ m) :
    IsP m (a + (m + 2) + 2 * z) (2 * z) ↔ ¬ IsP m (a + (m + 2) + z) z := by
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = h := by omega
  constructor
  · intro hP hz
    exact not_isP_move m _ _ z (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + 2 * z - z = a + (m + 2) + z by omega]; exact hz) hP
  · intro hN
    exact p_two m a z hmo hz1 hzm (by rw [hh]; omega) (by omega) hrow hrowb (by rw [hh]; exact hah) hN

theorem o_iter (m h a x : Nat) (hmh : m + 1 = 2 * h) (hhe : h % 2 = 0) (hrow : ∀ p, IsP m a p)
    (hrowb : ∀ p, IsP m (a + (m + 2)) p) (hah : IsP m (a + h) h) (hx : 1 ≤ x) :
    ∀ i, 2 ^ i * x ≤ m →
      (IsP m (a + (m + 2) + 2 ^ i * x) (2 ^ i * x) ↔ (IsP m (a + (m + 2) + x) x ↔ i % 2 = 0)) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [Nat.pow_zero, Nat.one_mul]
    exact ⟨fun hp => ⟨fun _ => rfl, fun _ => hp⟩, fun hh => hh.mpr rfl⟩
  | succ i ih =>
    intro hle
    have hd : 2 ^ (i + 1) * x = 2 * (2 ^ i * x) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, Nat.mul_assoc]
    have hpos : 1 ≤ 2 ^ i * x := Nat.mul_pos (Nat.pow_pos (by omega)) hx
    rw [hd] at hle ⊢
    have hm2 : 2 * (2 ^ i * x) + 1 ≤ m := by omega
    rw [o_half m h a _ hmh hhe hrow hrowb hah hpos hm2, ih (by omega)]
    have hpar : (i + 1) % 2 = 0 ↔ ¬ (i % 2 = 0) := by omega
    rw [hpar]
    constructor
    · intro hn
      constructor
      · intro ha hb; exact hn ⟨fun _ => hb, fun _ => ha⟩
      · intro hnb
        exact Classical.byContradiction fun hna => hn ⟨fun ha => absurd ha hna, fun hb => absurd hb hnb⟩
    · intro hiff hiff'
      by_cases hb : i % 2 = 0
      · exact (hiff.mp (hiff'.mpr hb)) hb
      · exact hb (hiff'.mp (hiff.mpr hb))

theorem e_iff (m h p D : Nat) (hmh : m + 1 = 2 * h) (hrowp : ∀ q, IsP m p q) (hrowc : ∀ q, IsP m (p + (m + 1)) q)
    (hD2 : 2 ≤ D) (hDm : D ≤ m) (hDe : D % 2 = 0) :
    IsP m (p + (m + 1) + D) D ↔ (¬ IsP m (p + (m + 1) + D / 2) (D / 2) ∧ ¬ IsP m (p + (h + D / 2)) (h + D / 2)) := by
  constructor
  · intro hP
    constructor
    · intro h1
      exact not_isP_move m _ _ (D / 2) (by omega) (by omega) (by omega) (by omega)
        (by rw [show p + (m + 1) + D - D / 2 = p + (m + 1) + D / 2 by omega]; exact h1) hP
    · intro h2
      exact not_isP_move m _ _ (h + D / 2) (by omega) (by omega) (by omega) (by omega)
        (by rw [show p + (m + 1) + D - (h + D / 2) = p + (h + D / 2) by omega]; exact h2) hP
  · intro ⟨h1, h2⟩
    exact e_even m h p D hmh hrowp hrowc hD2 hDm hDe h1 h2

theorem v2_pow_mul (x : Nat) (hx : 1 ≤ x) : ∀ b, v2 (2 ^ b * x) = b + v2 x := by
  intro b
  induction b with
  | zero => rw [Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | succ b ih =>
    have hpos : 1 ≤ 2 ^ b * x := Nat.mul_pos (Nat.pow_pos (by omega)) hx
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ b) 2, Nat.mul_assoc, v2_two_mul _ hpos, ih]
    omega


/-! ### 一般の v での記号と算術 -/

section Gen

variable (m v u : Nat) (hv5 : 5 ≤ v) (hvo : v % 2 = 1) (hmu : m + 1 = 2 ^ v * u) (hu : u % 4 = 3)
include hv5 hvo hmu hu

theorem g_le (x : Nat) (hx : x < 2 ^ v) : x * u + u ≤ m + 1 := by
  rw [hmu, ← Nat.succ_mul]; exact Nat.mul_le_mul_right u hx

theorem g_pow_split (b : Nat) (hb1 : 1 ≤ b) (hbv : b ≤ v) : 2 ^ (v - 1) = 2 ^ (b - 1) * 2 ^ (v - b) := by
  rw [← Nat.pow_add]; congr 1; omega

theorem g_hdef : m + 1 = 2 * (2 ^ (v - 1) * u) := by
  rw [hmu, ← Nat.mul_assoc, ← Nat.pow_succ']; congr 2; omega

/-- E 型のブロック c = p + (m+1) での補題 Inh′ の 1 段。-/
theorem k38_istep (p c : Nat) (hc : c = p + (m + 1)) (hrowp : ∀ q, IsP m p q) (hrowc : ∀ q, IsP m c q)
    (j : Nat) (hj : 1 ≤ j) (hblk : Blk m (2 * j - 1) c)
    (hprev : ∀ q b, q % 4 = 3 → 2 * (j - 1) ≤ b → b + 3 ≤ v → 2 ^ b * q < 2 ^ v →
      (IsP m (p + 2 ^ b * (q * u)) (2 ^ b * (q * u)) ↔ b % 2 = 1)) :
    ∀ q b, q % 4 = 3 → 2 * j ≤ b → b + 3 ≤ v → 2 ^ b * q < 2 ^ v →
      (IsP m (c + 2 ^ b * (q * u)) (2 ^ b * (q * u)) ↔ b % 2 = 1) := by
  intro q b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro hq hb hbv hlt
    obtain ⟨b1, rfl⟩ : ∃ b1, b = b1 + 1 := ⟨b - 1, by omega⟩
    have hqu1 : 1 ≤ q * u := Nat.mul_pos (by omega) (by omega)
    have hquo : (q * u) % 2 = 1 := by rw [Nat.mul_mod]; have : q % 2 = 1 := by omega
                                      rw [this, show u % 2 = 1 by omega]
    have hx1 : 1 ≤ 2 ^ b1 * (q * u) := Nat.mul_pos (Nat.pow_pos (by omega)) hqu1
    have hD : 2 ^ (b1 + 1) * (q * u) = 2 * (2 ^ b1 * (q * u)) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ b1) 2, Nat.mul_assoc]
    have hle := g_le m v u hv5 hvo hmu hu (2 ^ (b1 + 1) * q) hlt
    rw [Nat.mul_assoc, hD] at hle
    have hh := g_hdef m v u hv5 hvo hmu hu
    -- q' = q + 2^(v - b)
    have hsplit := g_pow_split m v u hv5 hvo hmu hu (b1 + 1) (by omega) (by omega)
    rw [show b1 + 1 - 1 = b1 by omega] at hsplit
    have hq' : 2 ^ (v - 1) * u + 2 ^ b1 * (q * u) = 2 ^ b1 * ((q + 2 ^ (v - (b1 + 1))) * u) := by
      rw [hsplit, Nat.mul_assoc, ← Nat.mul_add, Nat.add_mul, Nat.add_comm]
    have hpow4 : 2 ^ (v - (b1 + 1)) % 4 = 0 := by
      rw [show v - (b1 + 1) = (v - (b1 + 1) - 2) + 2 by omega, Nat.pow_add]; simp [Nat.mul_mod_left]
    have hq'4 : (q + 2 ^ (v - (b1 + 1))) % 4 = 3 := by omega
    have hq'lt : 2 ^ b1 * (q + 2 ^ (v - (b1 + 1))) < 2 ^ v := by
      rw [Nat.mul_add, ← Nat.pow_add, show b1 + (v - (b1 + 1)) = v - 1 by omega]
      have h1 : 2 ^ (b1 + 1) * q = 2 * (2 ^ b1 * q) := by rw [Nat.pow_succ, Nat.mul_comm (2 ^ b1) 2, Nat.mul_assoc]
      have h2 : 2 ^ v = 2 * 2 ^ (v - 1) := by rw [← Nat.pow_succ']; congr 1; omega
      omega
    -- e_iff
    rw [hc, e_iff m (2 ^ (v - 1) * u) p _ hh hrowp (by rw [← hc]; exact hrowc) (by omega) (by omega) (by omega),
      ← hc, show 2 ^ (b1 + 1) * (q * u) / 2 = 2 ^ b1 * (q * u) by omega, hq']
    have hT2 := hprev (q + 2 ^ (v - (b1 + 1))) b1 hq'4 (by omega) (by omega) hq'lt
    rw [hT2]
    by_cases hbj : b1 + 1 = 2 * j
    · -- 項 1 は Blk で N
      have hv2 : v2 (2 ^ b1 * (q * u)) = b1 := by rw [v2_pow_mul _ hqu1, v2_odd _ hquo, Nat.add_zero]
      have hT1 : ¬ IsP m (c + 2 ^ b1 * (q * u)) (2 ^ b1 * (q * u)) := by
        rw [hblk _ hx1 (by omega) (by omega), hv2]; omega
      constructor
      · intro ⟨_, h2⟩; omega
      · intro hodd; exact ⟨hT1, by omega⟩
    · have hT1 := ih b1 (by omega) hq (by omega) (by omega)
        (by have : 2 ^ (b1 + 1) * q = 2 * (2 ^ b1 * q) := by
              rw [Nat.pow_succ, Nat.mul_comm (2 ^ b1) 2, Nat.mul_assoc]
            omega)
      rw [hT1]; omega


/-- 行 b（O 型）の事実 S0：q ≡ 3 (mod 4) か q = 1 で 2^b·q < 2^v なら、(b + 2^b·qu) が P ⇔ b が奇数。-/
theorem k38_S0 (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m (v - 1) a)
    (he1 : v2 ((m + 2 + u) / 2) % 2 = 0 ∧ v2 ((m + 2 + u) / 2) ≤ v - 1)
    (hrowb : ∀ p, IsP m (a + (m + 2)) p) (hah : IsP m (a + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u)) :
    ∀ q b, (q % 4 = 3 ∨ q = 1) → 2 ^ b * q < 2 ^ v →
      (IsP m (a + (m + 2) + 2 ^ b * (q * u)) (2 ^ b * (q * u)) ↔ b % 2 = 1) := by
  have hh := g_hdef m v u hv5 hvo hmu hu
  have hm4 : (m + 1) % 4 = 0 := by
    rw [hmu, show v = (v - 2) + 2 by omega, Nat.pow_add]; simp [Nat.mul_mod, Nat.mul_assoc]
  have hhe : (2 ^ (v - 1) * u) % 2 = 0 := by omega
  intro q b hq hlt
  have hq1 : 1 ≤ q := by omega
  have hqlt : q < 2 ^ v := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left q (Nat.pow_pos (by omega))) hlt
  have hle := g_le m v u hv5 hvo hmu hu q hqlt
  have hqu1 : 1 ≤ q * u := Nat.mul_pos (by omega) (by omega)
  -- (b + qu, qu) は N
  have hN : ¬ IsP m (a + (m + 2) + q * u) (q * u) := by
    have hcase : q = 1 ∨ (q * u) % 4 = 1 := by
      rcases hq with h3 | h1
      · right; rw [Nat.mul_mod, h3, hu]
      · left; exact h1
    have hX1 : q = 1 → q * u = u := fun h => by rw [h, Nat.one_mul]
    generalize hX : q * u = X at hle hqu1 hX1 hcase ⊢
    have hpe : IsP m (a + (m + 2 + X) / 2) ((m + 2 + X) / 2) := by
      rcases hcase with h1 | h3
      · rw [hX1 h1]
        exact (hblk _ (by omega) (by omega) he1.2).mpr he1.1
      · have heo : ((m + 2 + X) / 2) % 2 = 1 := by omega
        exact (hblk _ (by omega) (by omega) (by rw [v2_odd _ heo]; omega)).mpr (by rw [v2_odd _ heo])
    exact not_isP_move m _ _ ((m + 2 + X) / 2) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + X - (m + 2 + X) / 2 = a + (m + 2 + X) / 2 by omega]; exact hpe)
  have hle2 := g_le m v u hv5 hvo hmu hu (2 ^ b * q) hlt
  rw [Nat.mul_assoc] at hle2
  rw [o_iter m (2 ^ (v - 1) * u) a (q * u) hh hhe hrow hrowb hah hqu1 b (by omega)]
  constructor
  · intro hiff; apply Decidable.byContradiction; intro hb; exact hN (hiff.mpr (by omega))
  · intro hb; exact ⟨fun hP => absurd hP hN, fun h0 => by omega⟩


/-- 3H/2 = 2^(v-2)·3u の所属：(c + 2^(v-3)·3u) と (p + 2^(v-3)·7u) が N なら (c + 3H/2) は P（c = p + (m+1)）。-/
theorem k38_K (p c : Nat) (hc : c = p + (m + 1)) (hrowp : ∀ q, IsP m p q) (hrowc : ∀ q, IsP m c q)
    (h1 : ¬ IsP m (c + 2 ^ (v - 3) * (3 * u)) (2 ^ (v - 3) * (3 * u)))
    (h2 : ¬ IsP m (p + 2 ^ (v - 3) * (7 * u)) (2 ^ (v - 3) * (7 * u))) :
    IsP m (c + 2 ^ (v - 2) * (3 * u)) (2 ^ (v - 2) * (3 * u)) := by
  have hh := g_hdef m v u hv5 hvo hmu hu
  have e2 : 2 ^ (v - 2) = 2 * 2 ^ (v - 3) := by rw [← Nat.pow_succ']; congr 1; omega
  have e1 : 2 ^ (v - 1) = 4 * 2 ^ (v - 3) := by
    rw [show v - 1 = (v - 3) + 2 by omega, Nat.pow_add, Nat.mul_comm]
  have hle := g_le m v u hv5 hvo hmu hu (2 ^ (v - 2) * 3) (by
    have : 2 ^ v = 4 * 2 ^ (v - 2) := by
      rw [show 2 ^ v = 2 ^ ((v - 2) + 2) by congr 1; omega, Nat.pow_add, Nat.mul_comm]
    have hp : 0 < 2 ^ (v - 2) := Nat.pow_pos (by omega)
    rw [this]; omega)
  rw [Nat.mul_assoc] at hle
  have hy1 : 1 ≤ 2 ^ (v - 3) * u := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  have hD : 2 ^ (v - 2) * (3 * u) = 6 * (2 ^ (v - 3) * u) := by
    rw [e2, Nat.mul_assoc 2 (2 ^ (v - 3)) (3 * u), Nat.mul_left_comm (2 ^ (v - 3)) 3 u]; omega
  have hD3 : 2 ^ (v - 3) * (3 * u) = 3 * (2 ^ (v - 3) * u) := Nat.mul_left_comm _ _ _
  have hD7 : 2 ^ (v - 3) * (7 * u) = 7 * (2 ^ (v - 3) * u) := Nat.mul_left_comm _ _ _
  have hH : 2 ^ (v - 1) * u = 4 * (2 ^ (v - 3) * u) := by rw [e1, Nat.mul_assoc]
  rw [hD3] at h1; rw [hD7] at h2; rw [hD]
  rw [hD] at hle; rw [hH] at hh
  generalize hy : 2 ^ (v - 3) * u = y at h1 h2 hle hh hy1 ⊢
  rw [hc, e_iff m (4 * y) p (6 * y) hh hrowp (by rw [← hc]; exact hrowc) (by omega) (by omega) (by omega), ← hc,
    show 6 * y / 2 = 3 * y by omega, show 4 * y + 3 * y = 7 * y by omega]
  exact ⟨h1, h2⟩

/-- (c + h, h) は N：手 3H/2 で (p + 3H/2) に移れる（c = p + (m+1)）。-/
theorem k38_N (p c : Nat) (hc : c = p + (m + 1)) (hP : IsP m (p + 2 ^ (v - 2) * (3 * u)) (2 ^ (v - 2) * (3 * u))) :
    ¬ IsP m (c + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u) := by
  have hh := g_hdef m v u hv5 hvo hmu hu
  have e1 : 2 ^ (v - 1) = 2 * 2 ^ (v - 2) := by rw [← Nat.pow_succ']; congr 1; omega
  have hH : 2 ^ (v - 1) * u = 2 * (2 ^ (v - 2) * u) := by rw [e1, Nat.mul_assoc]
  have hD : 2 ^ (v - 2) * (3 * u) = 3 * (2 ^ (v - 2) * u) := Nat.mul_left_comm _ _ _
  have hy1 : 1 ≤ 2 ^ (v - 2) * u := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  rw [hD] at hP; rw [hH] at hh ⊢
  generalize hy : 2 ^ (v - 2) * u = y at hP hh hy1 ⊢
  exact not_isP_move m _ _ (3 * y) (by omega) (by omega) (by omega) (by omega)
    (by rw [hc, show p + (m + 1) + 2 * y - 3 * y = p + 3 * y by omega]; exact hP)


/-- K38 の 1 周期分（v = 2s + 5）。行 a・Blk m (v−1) a から、行 b + j(m+1)（j ≤ s+2）がすべての p で P、
    行 a + L（L = (m+2) + (s+3)(m+1)）がすべての p で P かつ Blk m (v−1)、(a + h, h) が P。-/
theorem k38g_step (s : Nat) (hs : v = 2 * s + 5)
    (he1 : v2 ((m + 2 + u) / 2) % 2 = 0 ∧ v2 ((m + 2 + u) / 2) ≤ v - 1)
    (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m (v - 1) a) :
    (∀ j, j ≤ s + 2 → ∀ p, IsP m (a + (m + 2) + j * (m + 1)) p) ∧
    (∀ p, IsP m (a + (m + 2) + (s + 3) * (m + 1)) p) ∧ Blk m (v - 1) (a + (m + 2) + (s + 3) * (m + 1)) ∧
    IsP m (a + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u) := by
  have hmo : m % 2 = 1 := by have := g_hdef m v u hv5 hvo hmu hu; omega
  have hh := g_hdef m v u hv5 hvo hmu hu
  have hh2 : (m + 1) / 2 = 2 ^ (v - 1) * u := by omega
  have hvh : v2 (2 ^ (v - 1) * u) = v - 1 := by rw [v2_pow_mul u (by omega), v2_odd u (by omega), Nat.add_zero]
  have hah : IsP m (a + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u) :=
    (hblk _ (Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)) (by omega) (by omega)).mpr (by rw [hvh]; omega)
  have h2v : 2 ≤ 2 ^ (v - 1) := by
    rw [show v - 1 = (v - 2) + 1 by omega, Nat.pow_succ]
    have : 0 < 2 ^ (v - 2) := Nat.pow_pos (by omega)
    omega
  have hH2 : 2 ≤ 2 ^ (v - 1) * u := Nat.le_trans h2v (Nat.le_mul_of_pos_right _ (by omega))
  have hb := row_long m a hmo (by omega) hrow (by rw [hh2]; exact hah)
  have S0 := k38_S0 m v u hv5 hvo hmu hu a hrow hblk he1 hb hah
  -- 位置
  have hpos : ∀ j, a + (m + 2) + (j + 1) * (m + 1) = a + (m + 2) + j * (m + 1) + (m + 1) := by
    intro j; rw [Nat.succ_mul]; omega
  have hpos0 : a + (m + 2) + 0 * (m + 1) = a + (m + 2) := by rw [Nat.zero_mul, Nat.add_zero]
  have hb0 : ∀ p, IsP m (a + (m + 2) + 0 * (m + 1)) p := by rw [hpos0]; exact hb
  -- I の形
  let I : Nat → Prop := fun j => ∀ q b, q % 4 = 3 → 2 * j ≤ b → b + 3 ≤ v → 2 ^ b * q < 2 ^ v →
    (IsP m (a + (m + 2) + j * (m + 1) + 2 ^ b * (q * u)) (2 ^ b * (q * u)) ↔ b % 2 = 1)
  have I0 : I 0 := by
    intro q b hq _ _ hlt; rw [hpos0]; exact S0 q b (Or.inl hq) hlt
  have p8 : 2 ^ v = 8 * 2 ^ (v - 3) := by
    rw [show 2 ^ v = 2 ^ ((v - 3) + 3) by congr 1; omega, Nat.pow_add, Nat.mul_comm]
  have hp3 : 0 < 2 ^ (v - 3) := Nat.pow_pos (by omega)
  -- K の計算：I j と I (j+1) から K (j+1)
  have Kof : ∀ j, I j → I (j + 1) → 2 * (j + 1) + 3 ≤ v - 3 + 3 → (∀ p, IsP m (a + (m + 2) + j * (m + 1)) p) →
      (∀ p, IsP m (a + (m + 2) + (j + 1) * (m + 1)) p) →
      IsP m (a + (m + 2) + (j + 1) * (m + 1) + 2 ^ (v - 2) * (3 * u)) (2 ^ (v - 2) * (3 * u)) := by
    intro j Ij Ij1 hjv hrj hrj1
    apply k38_K m v u hv5 hvo hmu hu _ _ (hpos j) hrj hrj1
    · rw [Ij1 3 (v - 3) rfl (by omega) (by omega) (by omega)]; omega
    · rw [Ij 7 (v - 3) rfl (by omega) (by omega) (by omega)]; omega
  have K0 : IsP m (a + (m + 2) + 0 * (m + 1) + 2 ^ (v - 2) * (3 * u)) (2 ^ (v - 2) * (3 * u)) := by
    rw [hpos0, S0 3 (v - 2) (Or.inl rfl) (by
      have : 2 ^ v = 4 * 2 ^ (v - 2) := by
        rw [show 2 ^ v = 2 ^ ((v - 2) + 2) by congr 1; omega, Nat.pow_add, Nat.mul_comm]
      have hp : 0 < 2 ^ (v - 2) := Nat.pow_pos (by omega)
      omega)]
    omega
  have Nb : ¬ IsP m (a + (m + 2) + 0 * (m + 1) + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u) := by
    rw [hpos0]
    have := S0 1 (v - 1) (Or.inr rfl) (by
      rw [Nat.mul_one, show 2 ^ v = 2 * 2 ^ (v - 1) by rw [← Nat.pow_succ']; congr 1; omega]
      have : 0 < 2 ^ (v - 1) := Nat.pow_pos (by omega)
      omega)
    rw [Nat.one_mul] at this; rw [this]; omega
  -- 束ねた帰納法
  have bundle : ∀ j, 1 ≤ j → j ≤ s + 2 →
      (∀ p, IsP m (a + (m + 2) + j * (m + 1)) p) ∧ Blk m (2 * j - 1) (a + (m + 2) + j * (m + 1)) ∧
      (j ≤ s + 1 → I j ∧ IsP m (a + (m + 2) + j * (m + 1) + 2 ^ (v - 2) * (3 * u)) (2 ^ (v - 2) * (3 * u))) ∧
      ¬ IsP m (a + (m + 2) + j * (m + 1) + 2 ^ (v - 1) * u) (2 ^ (v - 1) * u) := by
    intro j hj1 hj2
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hj0 : j = 0
      · subst hj0
        -- j + 1 = 1
        have hr1 : ∀ p, IsP m (a + (m + 2) + (0 + 1) * (m + 1)) p := by
          rw [hpos 0]; exact row_next m _ hb0 (by rw [hh2]; exact Nb)
        have hodd1 := odd_of_rows m _ hmo hr1 (Or.inr ⟨_, hpos 0, hb0⟩)
        have hblk1 := blk1_direct m _ hr1 hodd1
        have I1 : I 1 := k38_istep m v u hv5 hvo hmu hu _ _ (hpos 0) hb0 hr1 1 (Nat.le_refl 1) hblk1 I0
        refine ⟨hr1, hblk1, fun _ => ⟨I1, Kof 0 I0 I1 (by omega) hb0 hr1⟩, ?_⟩
        exact k38_N m v u hv5 hvo hmu hu _ _ (hpos 0) K0
      · obtain ⟨hrj, hblkj, hIK, hNj⟩ := ih (by omega) (by omega)
        obtain ⟨Ij, Kj⟩ := hIK (by omega)
        have hr : ∀ p, IsP m (a + (m + 2) + (j + 1) * (m + 1)) p := by
          rw [hpos j]; exact row_next m _ hrj (by rw [hh2]; exact hNj)
        have hblk' : Blk m (2 * (j + 1) - 1) (a + (m + 2) + (j + 1) * (m + 1)) := by
          rw [hpos j]
          exact blk_step2 m (2 * j - 1) (2 * (j + 1) - 1) _ hmo (by omega) (by omega) (by rw [hh2, hvh]; omega)
            hrj hblkj (by rw [← hpos j]; exact hr)
        refine ⟨hr, hblk', ?_, k38_N m v u hv5 hvo hmu hu _ _ (hpos j) Kj⟩
        intro hjs
        have Ij1 : I (j + 1) := k38_istep m v u hv5 hvo hmu hu _ _ (hpos j) hrj hr (j + 1) (by omega) hblk'
          (by intro q b hq hb hbv hlt; exact Ij q b hq (by omega) hbv hlt)
        exact ⟨Ij1, Kof j Ij Ij1 (by omega) hrj hr⟩
  obtain ⟨hrL, hblkL, _, hNL⟩ := bundle (s + 2) (by omega) (Nat.le_refl _)
  have hr3 : ∀ p, IsP m (a + (m + 2) + (s + 3) * (m + 1)) p := by
    rw [hpos (s + 2)]; exact row_next m _ hrL (by rw [hh2]; exact hNL)
  have hblk3 : Blk m (v - 1) (a + (m + 2) + (s + 3) * (m + 1)) := by
    rw [hpos (s + 2)]
    exact blk_step2 m (2 * (s + 2) - 1) (v - 1) _ hmo (by omega) (by omega) (by rw [hh2, hvh]; exact Nat.le_refl _) hrL hblkL
      (by rw [← hpos (s + 2)]; exact hr3)
  refine ⟨?_, hr3, hblk3, hah⟩
  intro j hj
  by_cases hj0 : j = 0
  · subst hj0; exact hb0
  · exact (bundle j (by omega) hj).1


theorem k38g_rows (s : Nat) (hs : v = 2 * s + 5)
    (he1 : v2 ((m + 2 + u) / 2) % 2 = 0 ∧ v2 ((m + 2 + u) / 2) ≤ v - 1) :
    ∀ i, (∀ p, IsP m (i * ((m + 2) + (s + 3) * (m + 1))) p) ∧ Blk m (v - 1) (i * ((m + 2) + (s + 3) * (m + 1))) := by
  intro i
  induction i with
  | zero =>
    rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m (v - 1)⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, hr, hb, _⟩ := k38g_step m v u hv5 hvo hmu hu s hs he1 _ hrow hblk
    rw [Nat.succ_mul, show i * ((m + 2) + (s + 3) * (m + 1)) + ((m + 2) + (s + 3) * (m + 1))
      = i * ((m + 2) + (s + 3) * (m + 1)) + (m + 2) + (s + 3) * (m + 1) by omega]
    exact ⟨hr, hb⟩

end Gen

/-- 定理 K38（すべての奇数 v ≥ 5）：m + 1 = 2^v·u、u ≡ 3 (mod 4)、e₁ = (m+2+u)/2 の v2 が偶数で v − 1 以下なら、
    型は 1 0^{(v+1)/2}：L = (m+2) + ((v+1)/2)(m+1) として、
    (n, 0) が P ⇔ n mod L = 0、または n mod L ≥ m+2 かつ (n mod L − (m+2)) が m+1 の倍数。-/
theorem K38_gen (m v u : Nat) (hv5 : 5 ≤ v) (hvo : v % 2 = 1) (hmu : m + 1 = 2 ^ v * u) (hu : u % 4 = 3)
    (he1 : v2 ((m + 2 + u) / 2) % 2 = 0 ∧ v2 ((m + 2 + u) / 2) ≤ v - 1) (n : Nat) :
    IsP m n 0 ↔ (n % ((m + 2) + ((v + 1) / 2) * (m + 1)) = 0 ∨
      (m + 2 ≤ n % ((m + 2) + ((v + 1) / 2) * (m + 1)) ∧
        (n % ((m + 2) + ((v + 1) / 2) * (m + 1)) - (m + 2)) % (m + 1) = 0)) := by
  obtain ⟨s, hs⟩ : ∃ s, v = 2 * s + 5 := ⟨(v - 5) / 2, by omega⟩
  have hL : (v + 1) / 2 = s + 3 := by omega
  rw [hL]
  generalize hLL : (m + 2) + (s + 3) * (m + 1) = L
  have hLpos : 0 < L := by omega
  obtain ⟨hrowA, hblkA⟩ := k38g_rows m v u hv5 hvo hmu hu s hs he1 (n / L)
  rw [hLL] at hrowA hblkA
  obtain ⟨hrows, _, _, hah⟩ := k38g_step m v u hv5 hvo hmu hu s hs he1 _ hrowA hblkA
  have hh := g_hdef m v u hv5 hvo hmu hu
  have hdiv : n = (n / L) * L + n % L := by
    have := Nat.div_add_mod n L; rw [Nat.mul_comm] at this; omega
  have hlt : n % L < L := Nat.mod_lt n hLpos
  generalize hc : n % L = c at hdiv hlt
  generalize ha : n / L * L = A at hdiv hrowA hrows hah
  subst hdiv
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases h1 : c ≤ m
    · exact not_isP_of_row m A c 0 hrowA (by omega) h1 (by omega) hP
    · by_cases h2 : c = m + 1
      · subst h2
        exact not_isP_near m A (2 ^ (v - 1) * u) 0 hh (by omega) (by omega) hah (by omega) hP
      · -- c = (m+2) + j(m+1) + d、1 ≤ d ≤ m
        have hj : (c - (m + 2)) / (m + 1) ≤ s + 2 := by
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
        exact not_isP_of_row m _ _ 0 (hrows _ hj) (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | ⟨h1, h2⟩
    · rw [h, Nat.add_zero]; exact hrowA 0
    · have hj : (c - (m + 2)) / (m + 1) ≤ s + 2 := by
        apply Nat.le_of_lt_succ
        rw [Nat.div_lt_iff_lt_mul (by omega), Nat.succ_mul]
        rw [Nat.succ_mul] at hLL
        omega
      have hcd : A + c = A + (m + 2) + (c - (m + 2)) / (m + 1) * (m + 1) := by
        have := Nat.div_add_mod (c - (m + 2)) (m + 1)
        rw [Nat.mul_comm, h2, Nat.add_zero] at this; omega
      rw [hcd]; exact hrows _ hj 0

end Rubidium
