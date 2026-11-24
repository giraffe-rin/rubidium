/-
  Rubidium.K15gen — 定理 K15（1(10)^k 型）の一般の k ≥ 2 での形式化

  定理 K15：m + 1 = 2h（h 奇数）、3h + 1 = 4^k·w（k ≥ 2、w ≡ 3 (mod 4)。これは Q = (m+2+w)/2 が奇数と同じ）なら、
    型は 1(10)^k：周期 L = (m+2) + k(2m+3)、P の行は 0、m+2、そのあと (m+2) + i(2m+3)、2(m+2) + (i−1)(2m+3)。
  ブロック：R₀（始まり）、R₁ = R₀ + (m+2)（O）、R₂ = R₁ + (m+2)（O）、E_i = R₂ + (m+1) + (i−1)(2m+3)（E）、
    O_i = E_{i−1} + (m+2)（O、i ≥ 2）。E_k が次の始まり。e* = (3h+1)/2 = 2^{2k−1}·w。
  - (iii) の例外：k ≥ 2 で h ≡ 5 (mod 16)。q ≡ 3 (mod 4) なら 2·2^j·q + 1 ≢ 5 (mod 16) なので、半分にする規則が使える。
  - E 型の Inh：2i ≤ b ≤ 2k−1、q ≡ 3 (mod 4)、3·2^b·q + 5·4^i ≤ 2·4^k·w なら、(E_i + 2^b q) が P ⇔ b が奇数。
  - Blk：E_i で Blk m (2i−1)。O 型をはさんで 2 ずつ伸びる（`blk_EO`）。
-/
import Rubidium.K29gen

namespace Rubidium

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-- h が奇数でも使える半分にする規則：2z + 1 ≠ h なら、(b + 2z) が P ⇔ (b + z) が N（b = a + (m+2)）。-/
theorem o_half' (m h a z : Nat) (hmh : m + 1 = 2 * h) (hrow : ∀ p, IsP m a p)
    (hrowb : ∀ p, IsP m (a + (m + 2)) p) (hah : IsP m (a + h) h) (hz1 : 1 ≤ z) (hzm : 2 * z + 1 ≤ m)
    (hzh : 2 * z + 1 ≠ h) :
    IsP m (a + (m + 2) + 2 * z) (2 * z) ↔ ¬ IsP m (a + (m + 2) + z) z := by
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = h := by omega
  constructor
  · intro hP hz
    exact not_isP_move m _ _ z (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + 2 * z - z = a + (m + 2) + z by omega]; exact hz) hP
  · intro hN
    exact p_two m a z hmo hz1 hzm (by rw [hh]; exact hzh) (by omega) hrow hrowb (by rw [hh]; exact hah) hN

/-- h ≡ 5 (mod 16)、x ≡ 3 (mod 4) なら、半分にする規則のくり返し。-/
theorem o_iter3 (m h a x : Nat) (hmh : m + 1 = 2 * h) (h16 : h % 16 = 5) (hrow : ∀ p, IsP m a p)
    (hrowb : ∀ p, IsP m (a + (m + 2)) p) (hah : IsP m (a + h) h) (hx : x % 4 = 3) :
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
    have hpos : 1 ≤ 2 ^ i * x := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
    -- 2·(2^i x) + 1 ≠ h
    have hne : 2 * (2 ^ i * x) + 1 ≠ h := by
      rcases i with _ | _ | i
      · rw [Nat.pow_zero, Nat.one_mul]; omega
      · rw [show 2 ^ (0 + 1) = 2 by rfl]; omega
      · have : 2 ^ (i + 2) * x = 4 * (2 ^ i * x) := by
          rw [Nat.pow_add, Nat.mul_comm (2 ^ i) (2 ^ 2), Nat.mul_assoc]
        rw [this]; omega
    rw [hd] at hle ⊢
    rw [o_half' m h a _ hmh hrow hrowb hah hpos (by omega) hne, ih (by omega)]
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


/-- O 型の行 o = e + (m+2) の奇数 x：(o + x) が P ⇔ (e + (m+2+x)/2) が N。-/
theorem o_odd_iff (m h e x : Nat) (hmh : m + 1 = 2 * h) (hrow : ∀ p, IsP m e p)
    (hrowo : ∀ p, IsP m (e + (m + 2)) p) (heh : IsP m (e + h) h) (hx1 : 1 ≤ x) (hxo : x % 2 = 1)
    (hxh : x + 1 ≠ h) (hxm : (m + 2 + x) / 2 ≤ m) :
    IsP m (e + (m + 2) + x) x ↔ ¬ IsP m (e + (m + 2 + x) / 2) ((m + 2 + x) / 2) := by
  constructor
  · intro hP hQ
    exact not_isP_move m _ _ ((m + 2 + x) / 2) (by omega) hxm (by omega) (by omega)
      (by rw [show e + (m + 2) + x - (m + 2 + x) / 2 = e + (m + 2 + x) / 2 by omega]; exact hQ) hP
  · intro hN
    exact p_oddb m h e x hmh (by omega) hrow hrowo heh hx1 hxo hxh hxm hN

/-- Blk は O 型をはさんで 2 伸びる：Blk m s e、o = e + (m+2)、c = o + (m+1)（どれもすべての p で P）、
    h 奇数、v2((m+2+h)/2) = V、s < V、m − 1 の v2 は奇数なら、Blk m (s+2) c。-/
theorem blk_EO (m h e s V : Nat) (hmh : m + 1 = 2 * h) (hho : h % 2 = 1) (hrow : ∀ p, IsP m e p)
    (hrowo : ∀ p, IsP m (e + (m + 2)) p) (hrowc : ∀ p, IsP m (e + (m + 2) + (m + 1)) p)
    (heh : IsP m (e + h) h) (hblk : Blk m s e) (hV : v2 ((m + 2 + h) / 2) = V) (hsV : s < V)
    (hm1 : v2 (m - 1) % 2 = 1) (hm5 : 5 ≤ m) :
    Blk m (s + 2) (e + (m + 2) + (m + 1)) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro hd1 hdm hds
    constructor
    · intro hP
      apply Decidable.byContradiction
      intro hodd
      have hde : d % 2 = 0 := even_of_v2_pos d (by omega)
      have hv : v2 d = v2 (d / 2) + 1 := v2_even d (by omega) hde
      rw [isP_iff] at hP
      apply hP (d / 2) (by omega) (by omega) (by omega) (by omega)
      rw [show e + (m + 2) + (m + 1) + d - d / 2 = e + (m + 2) + (m + 1) + d / 2 by omega]
      exact (ih (d / 2) (by omega) (by omega) (by omega) (by omega)).mpr (by omega)
    · intro hev
      rw [isP_iff]
      intro k hk1 hkm hkr hkd hPk
      by_cases hlt : k < d
      · rw [show e + (m + 2) + (m + 1) + d - k = e + (m + 2) + (m + 1) + (d - k) by omega] at hPk
        by_cases hk : k = d - k
        · have hde : d % 2 = 0 := by omega
          have hd2 : d / 2 = k := by omega
          have hv : v2 d = v2 k + 1 := by rw [v2_even d (by omega) hde, hd2]
          rw [← hk] at hPk
          have := (ih k hlt hk1 (by omega) (by omega)).mp hPk
          omega
        · exact not_isP_of_row m _ (d - k) k hrowc (by omega) (by omega) hk hPk
      · rw [show e + (m + 2) + (m + 1) + d - k = e + (m + 2) + (m + 1 + d - k) by omega] at hPk
        by_cases hk : k = m + 1 + d - k
        · -- k = h + d/2（奇数）。相手 e* + d/4 は v2 が v2(d) − 2（偶数、≤ s）で、行 e で P
          have hde : d % 2 = 0 := by omega
          have hv1 : v2 d = v2 (d / 2) + 1 := v2_even d (by omega) hde
          have hd4 : (d / 2) % 2 = 0 := even_of_v2_pos (d / 2) (by omega)
          have hv2 : v2 (d / 2) = v2 (d / 4) + 1 := by
            rw [v2_even (d / 2) (by omega) hd4, show d / 2 / 2 = d / 4 by omega]
          have hdm1 : d ≠ m - 1 := fun h' => by rw [h'] at hev; omega
          have hkx : k = h + d / 2 := by omega
          rw [← hk, hkx] at hPk
          have hpart : (m + 2 + (h + d / 2)) / 2 = d / 4 + (m + 2 + h) / 2 := by omega
          have hvp : v2 (d / 4 + (m + 2 + h) / 2) = v2 (d / 4) :=
            v2_add (d / 4) ((m + 2 + h) / 2) (by omega) (by omega) (by omega)
          have hPe : IsP m (e + (m + 2 + (h + d / 2)) / 2) ((m + 2 + (h + d / 2)) / 2) := by
            rw [hpart]; exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
          exact ((o_odd_iff m h e (h + d / 2) hmh hrow hrowo heh (by omega) (by omega) (by omega) (by omega)).mp hPk) hPe
        · exact not_isP_of_row m _ (m + 1 + d - k) k hrowo (by omega) (by omega) hk hPk


section K15g

variable (m h k w : Nat) (hmh : m + 1 = 2 * h) (hW : 3 * h + 1 = 2 ^ (2 * k) * w) (hw : w % 4 = 3) (hk : 2 ≤ k)
include hmh hW hw hk

theorem k15_h16 : h % 16 = 5 := by
  have : (2 ^ (2 * k) * w) % 16 = 0 := by
    rw [show 2 * k = (2 * k - 4) + 4 by omega, Nat.pow_add]; simp [Nat.mul_mod, Nat.mul_assoc]
  omega

theorem k15_estar : (m + 2 + h) / 2 = 2 ^ (2 * k - 1) * w := by
  have : 2 ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  rw [this, Nat.mul_assoc] at hW; omega

theorem k15_vstar : v2 ((m + 2 + h) / 2) = 2 * k - 1 := by
  rw [k15_estar m h k w hmh hW hw hk, v2_pow_mul w (by omega), v2_odd w (by omega), Nat.add_zero]

theorem k15_vm1 : v2 (m - 1) % 2 = 1 := by
  have h16 := k15_h16 m h k w hmh hW hw hk
  rw [v2_even (m - 1) (by omega) (by omega), v2_even ((m - 1) / 2) (by omega) (by omega),
    v2_even ((m - 1) / 2 / 2) (by omega) (by omega), v2_odd _ (by omega)]

/-- 値の型：行 r で、q ≡ 3 (mod 4)、2i ≤ b ≤ 2k−1、3·2^b q + 5·4^i ≤ 2·4^k w なら、(r + 2^b q) が P ⇔ b が奇数。-/
def K15I (r i : Nat) : Prop := ∀ q b, q % 4 = 3 → 2 * i ≤ b → b ≤ 2 * k - 1 →
  3 * (2 ^ b * q) + 5 * 4 ^ i ≤ 2 * (2 ^ (2 * k) * w) → (IsP m (r + 2 ^ b * q) (2 ^ b * q) ↔ b % 2 = 1)

/-- E 型の行 c = o + (m+1)（o = p + (m+2)）での Inh の 1 段。-/
theorem k15_istep (p i : Nat) (hi : 1 ≤ i) (hrowp : ∀ x, IsP m p x) (hrowo : ∀ x, IsP m (p + (m + 2)) x)
    (hrowc : ∀ x, IsP m (p + (m + 2) + (m + 1)) x) (hph : IsP m (p + h) h)
    (hblk : Blk m (2 * i - 1) (p + (m + 2) + (m + 1))) (hprev : K15I m k w p (i - 1)) :
    K15I m k w (p + (m + 2) + (m + 1)) i := by
  have h16 := k15_h16 m h k w hmh hW hw hk
  have hst := k15_estar m h k w hmh hW hw hk
  intro q b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro hq hb hbk hbd
    obtain ⟨b2, rfl⟩ : ∃ b2, b = b2 + 2 := ⟨b - 2, by omega⟩
    have hq1 : 1 ≤ q := by omega
    have hp4 : 4 ^ i = 4 * 4 ^ (i - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    have hp41 : 1 ≤ 4 ^ (i - 1) := Nat.pow_pos (by omega)
    have hA : 2 ^ (b2 + 2) * q = 4 * (2 ^ b2 * q) := by
      rw [Nat.pow_add, Nat.mul_comm (2 ^ b2) (2 ^ 2), Nat.mul_assoc]
    have hB : 2 ^ (b2 + 1) * q = 2 * (2 ^ b2 * q) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ b2) 2, Nat.mul_assoc]
    have hA1 : 1 ≤ 2 ^ b2 * q := Nat.mul_pos (Nat.pow_pos (by omega)) hq1
    have hW2 : 2 ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    have hWE : 2 ^ (2 * k) * w = 2 * (2 ^ (2 * k - 1) * w) := by rw [hW2, Nat.mul_assoc]
    rw [hA] at hbd ⊢; rw [hp4] at hbd
    -- q' = q + 2^(2k−1−b2) w
    have hsplit : 2 ^ (2 * k - 1) = 2 ^ b2 * 2 ^ (2 * k - 1 - b2) := by rw [← Nat.pow_add]; congr 1; omega
    have hq' : 2 ^ b2 * q + 2 ^ (2 * k - 1) * w = 2 ^ b2 * (q + 2 ^ (2 * k - 1 - b2) * w) := by
      rw [hsplit, Nat.mul_assoc, ← Nat.mul_add]
    have hpw4 : (2 ^ (2 * k - 1 - b2) * w) % 4 = 0 := by
      rw [show 2 * k - 1 - b2 = (2 * k - 1 - b2 - 2) + 2 by omega, Nat.pow_add]; simp [Nat.mul_mod, Nat.mul_assoc]
    have hq'4 : (q + 2 ^ (2 * k - 1 - b2) * w) % 4 = 3 := by omega
    -- e_iff
    have hD : 4 * (2 ^ b2 * q) ≤ m := by omega
    rw [e_iff m h (p + (m + 2)) (4 * (2 ^ b2 * q)) hmh hrowo hrowc (by omega) hD (by omega),
      show 4 * (2 ^ b2 * q) / 2 = 2 * (2 ^ b2 * q) by omega]
    -- 項 2：O 型の奇数 h + 2·(2^b2 q)
    have hx := o_odd_iff m h p (h + 2 * (2 ^ b2 * q)) hmh hrowp hrowo hph (by omega) (by omega) (by omega) (by omega)
    rw [show (m + 2 + (h + 2 * (2 ^ b2 * q))) / 2 = 2 ^ b2 * q + 2 ^ (2 * k - 1) * w by omega, hq'] at hx
    rw [hx]
    have hT2 := hprev (q + 2 ^ (2 * k - 1 - b2) * w) b2 hq'4 (by omega) (by omega) (by rw [← hq']; omega)
    rw [hT2]
    by_cases hbi : b2 + 2 = 2 * i
    · -- 項 1 は Blk で N（v2 = b2 + 1 = 2i − 1）
      have hv2 : v2 (2 * (2 ^ b2 * q)) = b2 + 1 := by
        rw [← hB, v2_pow_mul q hq1, v2_odd q (by omega), Nat.add_zero]
      have hT1 : ¬ IsP m (p + (m + 2) + (m + 1) + 2 * (2 ^ b2 * q)) (2 * (2 ^ b2 * q)) := by
        rw [hblk _ (by omega) (by omega) (by omega), hv2]; omega
      constructor
      · intro ⟨_, h2⟩; omega
      · intro hodd; exact ⟨hT1, by omega⟩
    · have hT1 := ih (b2 + 1) (by omega) hq (by omega) (by omega) (by rw [hB, hp4]; omega)
      rw [hB] at hT1
      rw [hT1]; omega


/-- 5·4^i ≤ 2^(2k−1)·w（i ≤ k − 1、w ≥ 3）。-/
theorem k15_bound (i : Nat) (hi : i + 1 ≤ k) : 5 * 4 ^ i ≤ 2 ^ (2 * k - 1) * w := by
  have h1 : 4 ^ i ≤ 4 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 4 ^ (k - 1) = 2 ^ (2 * k - 2) := by rw [show 2 * k - 2 = 2 * (k - 1) by omega, Nat.pow_mul]
  have h3 : 2 ^ (2 * k - 1) = 2 * 2 ^ (2 * k - 2) := by rw [← Nat.pow_succ']; congr 1; omega
  have h4 : 2 ^ (2 * k - 1) * 3 ≤ 2 ^ (2 * k - 1) * w := Nat.mul_le_mul_left _ (by omega)
  omega

/-- K15 の 1 周期分。行 a・Blk m (2k−1) a から、各行がすべての p で P、行 posE k で Blk m (2k−1)。
    posE i = a + (m+2) + i(2m+3)、posO i = posE i + (m+2)。-/
theorem k15_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m (2 * k - 1) a) :
    (∀ i, i ≤ k → ∀ p, IsP m (a + (m + 2) + i * (2 * m + 3)) p) ∧
    (∀ i, i + 1 ≤ k → ∀ p, IsP m (a + (m + 2) + i * (2 * m + 3) + (m + 2)) p) ∧
    (∀ i, i ≤ k → IsP m (a + (m + 2) + i * (2 * m + 3) + h) h) ∧
    Blk m (2 * k - 1) (a + (m + 2) + k * (2 * m + 3)) ∧ IsP m (a + h) h := by
  have h16 := k15_h16 m h k w hmh hW hw hk
  have hst := k15_estar m h k w hmh hW hw hk
  have hvst := k15_vstar m h k w hmh hW hw hk
  have hvm1 := k15_vm1 m h k w hmh hW hw hk
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = h := by omega
  have hE5 : 5 ≤ 2 ^ (2 * k - 1) * w := by have := k15_bound m h k w hmh hW hw hk 0 (by omega); simpa using this
  have hWE : 2 ^ (2 * k) * w = 2 * (2 ^ (2 * k - 1) * w) := by
    rw [show 2 ^ (2 * k) = 2 * 2 ^ (2 * k - 1) by rw [← Nat.pow_succ']; congr 1; omega, Nat.mul_assoc]
  have hoddA : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d :=
    fun d hd1 hdm hdo => (hblk d hd1 hdm (by rw [v2_odd d hdo]; omega)).mpr (by rw [v2_odd d hdo])
  have hah : IsP m (a + h) h := hoddA h (by omega) (by omega) (by omega)
  have hpos : ∀ i, a + (m + 2) + (i + 1) * (2 * m + 3) = a + (m + 2) + i * (2 * m + 3) + (m + 2) + (m + 1) := by
    intro i; rw [Nat.succ_mul]; omega
  have hpos0 : a + (m + 2) + 0 * (2 * m + 3) = a + (m + 2) := by rw [Nat.zero_mul, Nat.add_zero]
  -- R₁
  have hR1 : ∀ p, IsP m (a + (m + 2)) p := row_long m a hmo (by omega) hrow (by rw [hh]; exact hah)
  have I0 : K15I m k w (a + (m + 2) + 0 * (2 * m + 3)) 0 := by
    intro q b hq _ _ hbd
    rw [hpos0]
    have hle : 2 ^ b * q ≤ m := by omega
    have hq1 : 1 ≤ q := by omega
    have hqb : q ≤ 2 ^ b * q := Nat.le_mul_of_pos_left q (Nat.pow_pos (by omega))
    have hqN : ¬ IsP m (a + (m + 2) + q) q :=
      not_isP_move m _ _ ((m + 2 + q) / 2) (by omega) (by omega) (by omega) (by omega)
        (by rw [show a + (m + 2) + q - (m + 2 + q) / 2 = a + (m + 2 + q) / 2 by omega]
            exact hoddA _ (by omega) (by omega) (by omega))
    rw [o_iter3 m h a q hmh h16 hrow hR1 hah hq b hle]
    exact ⟨fun hiff => by apply Decidable.byContradiction; intro hb; exact hqN (hiff.mpr (by omega)),
      fun hb => ⟨fun hP => absurd hP hqN, fun _ => by omega⟩⟩
  -- (A) (R₁ + h) は P
  have hA : IsP m (a + (m + 2) + h) h := by
    have hN : ¬ IsP m (a + (m + 2 + h) / 2) ((m + 2 + h) / 2) := by
      rw [hblk _ (by omega) (by omega) (by omega), hvst]; omega
    exact p_oddb m h a h hmh (by omega) hrow hR1 hah (by omega) (by omega) (by omega) (by omega) hN
  have hR2 : ∀ p, IsP m (a + (m + 2) + (m + 2)) p := row_long m _ hmo (by omega) hR1 (by rw [hh]; exact hA)
  -- (B) (R₂ + h) は N
  have hB : ¬ IsP m (a + (m + 2) + (m + 2) + h) h := by
    have hv := I0 w (2 * k - 1) hw (by omega) (Nat.le_refl _) (by rw [hWE, Nat.pow_zero]; omega)
    rw [hpos0] at hv
    exact not_isP_move m _ _ (2 ^ (2 * k - 1) * w) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + (m + 2) + h - 2 ^ (2 * k - 1) * w = a + (m + 2) + 2 ^ (2 * k - 1) * w by omega]
          exact hv.mpr (by omega))
  -- 束ねた帰納法
  have bundle : ∀ i, 1 ≤ i → i ≤ k →
      (∀ p, IsP m (a + (m + 2) + i * (2 * m + 3)) p) ∧ Blk m (2 * i - 1) (a + (m + 2) + i * (2 * m + 3)) ∧
      K15I m k w (a + (m + 2) + i * (2 * m + 3)) i := by
    intro i hi1 hik
    induction i with
    | zero => omega
    | succ i ih =>
      by_cases hi0 : i = 0
      · subst hi0
        have hr : ∀ p, IsP m (a + (m + 2) + (0 + 1) * (2 * m + 3)) p := by
          rw [hpos 0, hpos0]; exact row_next m _ hR2 (by rw [hh]; exact hB)
        have hodd := odd_of_rows m _ hmo hr (Or.inr ⟨a + (m + 2) + (m + 2), by rw [hpos 0, hpos0], hR2⟩)
        have hb1 := blk1_direct m _ hr hodd
        refine ⟨hr, hb1, ?_⟩
        have := k15_istep m h k w hmh hW hw hk (a + (m + 2)) 1 (Nat.le_refl 1) hR1 hR2
          (by rw [← hpos0, ← hpos 0]; exact hr) hA (by rw [← hpos0, ← hpos 0]; exact hb1) (by have h0 := I0; rw [hpos0] at h0; exact h0)
        rw [← hpos0, ← hpos 0] at this; exact this
      · obtain ⟨hr, hb, hI⟩ := ih (by omega) (by omega)
        have hodd : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + (m + 2) + i * (2 * m + 3) + d) d :=
          fun d hd1 hdm hdo => (hb d hd1 hdm (by rw [v2_odd d hdo]; omega)).mpr (by rw [v2_odd d hdo])
        have heh := hodd h (by omega) (by omega) (by omega)
        have hro := row_long m _ hmo (by omega) hr (by rw [hh]; exact heh)
        have hNo : ¬ IsP m (a + (m + 2) + i * (2 * m + 3) + (m + 2) + h) h := by
          have hv := hI w (2 * k - 1) hw (by omega) (Nat.le_refl _)
            (by have := k15_bound m h k w hmh hW hw hk i (by omega); rw [hWE]; omega)
          exact not_isP_move m _ _ (2 ^ (2 * k - 1) * w) (by omega) (by omega) (by omega) (by omega)
            (by rw [show a + (m + 2) + i * (2 * m + 3) + (m + 2) + h - 2 ^ (2 * k - 1) * w
                    = a + (m + 2) + i * (2 * m + 3) + 2 ^ (2 * k - 1) * w by omega]
                exact hv.mpr (by omega))
        have hr' : ∀ p, IsP m (a + (m + 2) + (i + 1) * (2 * m + 3)) p := by
          rw [hpos i]; exact row_next m _ hro (by rw [hh]; exact hNo)
        have hb' : Blk m (2 * (i + 1) - 1) (a + (m + 2) + (i + 1) * (2 * m + 3)) := by
          rw [hpos i, show 2 * (i + 1) - 1 = (2 * i - 1) + 2 by omega]
          exact blk_EO m h _ (2 * i - 1) (2 * k - 1) hmh (by omega) hr hro (by rw [← hpos i]; exact hr') heh hb
            hvst (by omega) hvm1 (by omega)
        refine ⟨hr', hb', ?_⟩
        have := k15_istep m h k w hmh hW hw hk _ (i + 1) (by omega) hr hro (by rw [← hpos i]; exact hr') heh
          (by rw [← hpos i]; exact hb') (by rw [show i + 1 - 1 = i by omega]; exact hI)
        rw [← hpos i] at this; exact this
  refine ⟨?_, ?_, ?_, ?_, hah⟩
  · intro i hi
    by_cases hi0 : i = 0
    · subst hi0; rw [hpos0]; exact hR1
    · exact (bundle i (by omega) hi).1
  · intro i hi
    by_cases hi0 : i = 0
    · subst hi0; rw [hpos0]; exact hR2
    · obtain ⟨hr, hb, _⟩ := bundle i (by omega) (by omega)
      have heh : IsP m (a + (m + 2) + i * (2 * m + 3) + h) h :=
        (hb h (by omega) (by omega) (by rw [v2_odd h (by omega)]; omega)).mpr (by rw [v2_odd h (by omega)])
      exact row_long m _ hmo (by omega) hr (by rw [hh]; exact heh)
  · intro i hi
    by_cases hi0 : i = 0
    · subst hi0; rw [hpos0]; exact hA
    · obtain ⟨_, hb, _⟩ := bundle i (by omega) hi
      exact (hb h (by omega) (by omega) (by rw [v2_odd h (by omega)]; omega)).mpr (by rw [v2_odd h (by omega)])
  · exact (bundle k (by omega) (Nat.le_refl _)).2.1


theorem k15_rows : ∀ i, (∀ p, IsP m (i * ((m + 2) + k * (2 * m + 3))) p) ∧
    Blk m (2 * k - 1) (i * ((m + 2) + k * (2 * m + 3))) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m _⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨hr, _, _, hb, _⟩ := k15_step m h k w hmh hW hw hk _ hrow hblk
    rw [Nat.succ_mul, show i * ((m + 2) + k * (2 * m + 3)) + ((m + 2) + k * (2 * m + 3))
      = i * ((m + 2) + k * (2 * m + 3)) + (m + 2) + k * (2 * m + 3) by omega]
    exact ⟨hr k (Nat.le_refl _), hb⟩

end K15g

/-- 定理 K15（k ≥ 2）：m + 1 = 2h、3h + 1 = 4^k·w（w ≡ 3 (mod 4)、k ≥ 2）なら、型は 1(10)^k：
    L = (m+2) + k(2m+3) として、(n, 0) が P ⇔ r = n mod L が 0、または r ≥ m+2 かつ (r − (m+2)) mod (2m+3) ∈ {0, m+2}。-/
theorem K15_gen (m h k w : Nat) (hmh : m + 1 = 2 * h) (hW : 3 * h + 1 = 4 ^ k * w) (hw : w % 4 = 3) (hk : 2 ≤ k)
    (n : Nat) :
    IsP m n 0 ↔ (n % ((m + 2) + k * (2 * m + 3)) = 0 ∨
      (m + 2 ≤ n % ((m + 2) + k * (2 * m + 3)) ∧
        ((n % ((m + 2) + k * (2 * m + 3)) - (m + 2)) % (2 * m + 3) = 0 ∨
         (n % ((m + 2) + k * (2 * m + 3)) - (m + 2)) % (2 * m + 3) = m + 2))) := by
  have hW' : 3 * h + 1 = 2 ^ (2 * k) * w := by rw [hW, Nat.pow_mul]
  have h16 := k15_h16 m h k w hmh hW' hw hk
  obtain ⟨hrowA, hblkA⟩ := k15_rows m h k w hmh hW' hw hk (n / ((m + 2) + k * (2 * m + 3)))
  obtain ⟨hE, hO, hEh, _, hAh⟩ := k15_step m h k w hmh hW' hw hk _ hrowA hblkA
  generalize hLL : (m + 2) + k * (2 * m + 3) = L at hrowA hE hO hEh hAh
  have hLpos : 0 < L := by omega
  have hdiv : n = (n / L) * L + n % L := by
    have := Nat.div_add_mod n L; rw [Nat.mul_comm] at this; omega
  have hlt : n % L < L := Nat.mod_lt n hLpos
  generalize hc : n % L = c at hdiv hlt
  generalize ha : n / L * L = A at hdiv hrowA hE hO hEh hAh
  subst hdiv
  -- c ≥ m+2 なら c − (m+2) = j(2m+3) + d（j < k）
  have hdec : m + 2 ≤ c → (c - (m + 2)) / (2 * m + 3) < k ∧
      A + c = A + (m + 2) + (c - (m + 2)) / (2 * m + 3) * (2 * m + 3) + (c - (m + 2)) % (2 * m + 3) := by
    intro h2
    constructor
    · rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    · have := Nat.div_add_mod (c - (m + 2)) (2 * m + 3); rw [Nat.mul_comm] at this; omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases h1 : c ≤ m
    · exact not_isP_of_row m A c 0 hrowA (by omega) h1 (by omega) hP
    · by_cases h2 : c = m + 1
      · subst h2; exact not_isP_near m A h 0 hmh (by omega) (by omega) hAh (by omega) hP
      · obtain ⟨hj, hcd⟩ := hdec (by omega)
        have hdl : (c - (m + 2)) % (2 * m + 3) < 2 * m + 3 := Nat.mod_lt _ (by omega)
        rw [hcd] at hP
        generalize hd : (c - (m + 2)) % (2 * m + 3) = d at hP hdl hne
        generalize hJ : (c - (m + 2)) / (2 * m + 3) = j at hP hj
        by_cases hd1 : d ≤ m
        · exact not_isP_of_row m _ d 0 (hE j (by omega)) (by omega) hd1 (by omega) hP
        · by_cases hd2 : d = m + 1
          · subst hd2
            exact not_isP_near m _ h 0 hmh (by omega) (by omega) (hEh j (by omega)) (by omega) hP
          · rw [show A + (m + 2) + j * (2 * m + 3) + d = A + (m + 2) + j * (2 * m + 3) + (m + 2) + (d - (m + 2)) by omega] at hP
            exact not_isP_of_row m _ (d - (m + 2)) 0 (hO j (by omega)) (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | ⟨h1, h2⟩
    · rw [h, Nat.add_zero]; exact hrowA 0
    · obtain ⟨hj, hcd⟩ := hdec h1
      rw [hcd]
      rcases h2 with h2 | h2
      · rw [h2, Nat.add_zero]; exact hE _ (by omega) 0
      · rw [h2]; exact hO _ (by omega) 0

end Rubidium
