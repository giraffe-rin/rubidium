/-
  Rubidium.K38v7 — 定理 K38 の v = 7 の場合の形式化

  定理 K38（v = 7）：m + 1 = 128u、w = v2(u+1) ∈ {3, 5} または w ≥ 8 なら「10000 型」：
    (n, 0) が P ⇔ n mod (5m+6) ∈ {0, m+2, 2m+3, 3m+4, 4m+5}。
  h = 64u、e₁ = (129u+1)/2（v2(e₁) ∈ {2, 4, 6}）。行は a、b = a + (m+2)、c₁ = b + (m+1)、c₂、c₃、a' = c₃ + (m+1)。
  - 行 a：Blk m 6 a。
  - 行 b（O 型）：q ∈ {1, 3, 7, 11, 15, 27, 43} の (b + qu) は N（相手 (m+2+qu)/2 は v2 が偶数か奇数）。
    半分にする鎖：u から 2u・8u・32u が P、4u・16u・64u が N。3u から 6u・24u・96u が P、12u・48u が N。
    7u から 14u・56u が P、28u・112u が N。11u から 22u・88u が P、44u が N。15u から 30u・120u が P、60u が N。
    27u から 54u が P、108u が N。43u から 86u が P。
  - 行 c₁：(c₁ + 64u)・(c₁ + 48u)・(c₁ + 112u)・(c₁ + 44u) は N（手 96u・88u・120u・86u）、(c₁ + 96u)・(c₁ + 88u) は P（`e_even`）。
  - 行 c₂：Blk m 3。(c₂ + 64u)・(c₂ + 48u) は N（手 96u・88u）、(c₂ + 96u) は P（`e_even`）。
  - 行 c₃：Blk m 5。(c₃ + 64u) は N（手 96u）。行 a'：Blk m 6。
-/
import Rubidium.K38

namespace Rubidium

set_option maxHeartbeats 8000000

section K38v7

variable (m u : Nat) (hmu : m + 1 = 128 * u) (hu : u % 4 = 3)
  (he1 : v2 ((129 * u + 1) / 2) = 2 ∨ v2 ((129 * u + 1) / 2) = 4 ∨ v2 ((129 * u + 1) / 2) = 6)
include hmu hu he1

theorem k38v7_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 6 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧ (∀ p, IsP m (a + (2 * m + 3)) p) ∧ (∀ p, IsP m (a + (3 * m + 4)) p) ∧
    (∀ p, IsP m (a + (4 * m + 5)) p) ∧ (∀ p, IsP m (a + (5 * m + 6)) p) ∧ Blk m 6 (a + (5 * m + 6)) ∧
    IsP m (a + 64 * u) (64 * u) := by
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 64 * u := by omega
  have hmh : m + 1 = 2 * (64 * u) := by omega
  have hv64 : v2 (64 * u) = 6 := by
    rw [show 64 * u = 2 * (2 * (2 * (2 * (2 * (2 * u))))) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega),
      v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_two_mul _ (by omega),
      v2_odd u (by omega)]
  have hah : IsP m (a + 64 * u) (64 * u) := (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hah' : IsP m (a + (m + 1) / 2) ((m + 1) / 2) := by rw [hh]; exact hah
  have hb := row_long m a hmo (by omega) hrow hah'
  have hoddA : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d :=
    fun d hd1 hdm hdo => (hblk d hd1 hdm (by rw [v2_odd d hdo]; omega)).mpr (by rw [v2_odd d hdo])
  have mv : ∀ d e, (m + 2 + d) = 2 * e → e ≤ m → e ≠ d → 1 ≤ d → IsP m (a + e) e → ¬ IsP m (a + (m + 2) + d) d :=
    fun d e hde hem hed hd1 hP => not_isP_move m _ d e (by omega) hem (by omega) hed
      (by rw [show a + (m + 2) + d - e = a + e by omega]; exact hP)
  have mvq : ∀ q, q % 4 = 3 → q ≤ 43 → ¬ IsP m (a + (m + 2) + q * u) (q * u) := by
    intro q hq hq43
    have hqu : (q * u) % 4 = 1 := by
      rw [Nat.mul_mod, hq, hu]
    have hqu1 : 1 ≤ q * u := Nat.mul_pos (by omega) (by omega)
    have hqum : q * u ≤ 43 * u := Nat.mul_le_mul_right u hq43
    exact mv (q * u) ((m + 2 + q * u) / 2) (by omega) (by omega) (by omega) hqu1
      (hoddA _ (by omega) (by omega) (by omega))
  have hbu := mv u ((129 * u + 1) / 2) (by omega) (by omega) (by omega) (by omega)
    ((hblk _ (by omega) (by omega) (by omega)).mpr (by omega))
  have p2 : ∀ z, 1 ≤ z → 2 * z + 1 ≤ m → ¬ IsP m (a + (m + 2) + z) z → IsP m (a + (m + 2) + 2 * z) (2 * z) :=
    fun z hz1 hzm hbz => p_two m a z hmo hz1 hzm (by rw [hh]; omega) (by omega) hrow hb hah' hbz
  have nh : ∀ z, 1 ≤ z → 2 * z ≤ m → IsP m (a + (m + 2) + z) z → ¬ IsP m (a + (m + 2) + 2 * z) (2 * z) :=
    fun z hz1 hzm hP => not_isP_move m _ _ z (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + 2 * z - z = a + (m + 2) + z by omega]; exact hP)
  -- 半分にする鎖（距離を c·u の形に直す）
  have P2 : ∀ c, 1 ≤ c → 2 * c ≤ 127 → ¬ IsP m (a + (m + 2) + c * u) (c * u) →
      IsP m (a + (m + 2) + (2 * c) * u) ((2 * c) * u) := by
    intro c hc1 hc hN
    have h1 : 1 ≤ c * u := Nat.mul_pos (by omega) (by omega)
    have h2 : (2 * c) * u ≤ 127 * u := Nat.mul_le_mul_right u hc
    rw [Nat.mul_assoc]; exact p2 (c * u) h1 (by rw [Nat.mul_assoc] at h2; omega) hN
  have N2 : ∀ c, 1 ≤ c → 2 * c ≤ 127 → IsP m (a + (m + 2) + c * u) (c * u) →
      ¬ IsP m (a + (m + 2) + (2 * c) * u) ((2 * c) * u) := by
    intro c hc1 hc hP
    have h1 : 1 ≤ c * u := Nat.mul_pos (by omega) (by omega)
    have h2 : (2 * c) * u ≤ 127 * u := Nat.mul_le_mul_right u hc
    rw [Nat.mul_assoc]; exact nh (c * u) h1 (by rw [Nat.mul_assoc] at h2; omega) hP
  have hbu' : ¬ IsP m (a + (m + 2) + 1 * u) (1 * u) := by rw [Nat.one_mul]; exact hbu
  have b2 := P2 1 (by omega) (by omega) hbu'
  have b4 := N2 2 (by omega) (by omega) b2
  have b8 := P2 4 (by omega) (by omega) b4
  have b16 := N2 8 (by omega) (by omega) b8
  have b32 := P2 16 (by omega) (by omega) b16
  have b64 := N2 32 (by omega) (by omega) b32
  have b3 := mvq 3 rfl (by omega)
  have b6 := P2 3 (by omega) (by omega) b3
  have b12 := N2 6 (by omega) (by omega) b6
  have b24 := P2 12 (by omega) (by omega) b12
  have b48 := N2 24 (by omega) (by omega) b24
  have b96 := P2 48 (by omega) (by omega) b48
  have b7 := mvq 7 rfl (by omega)
  have b14 := P2 7 (by omega) (by omega) b7
  have b28 := N2 14 (by omega) (by omega) b14
  have b56 := P2 28 (by omega) (by omega) b28
  have b112 := N2 56 (by omega) (by omega) b56
  have b11 := mvq 11 rfl (by omega)
  have b22 := P2 11 (by omega) (by omega) b11
  have b44 := N2 22 (by omega) (by omega) b22
  have b88 := P2 44 (by omega) (by omega) b44
  have b15 := mvq 15 rfl (by omega)
  have b30 := P2 15 (by omega) (by omega) b15
  have b60 := N2 30 (by omega) (by omega) b30
  have b120 := P2 60 (by omega) (by omega) b60
  have b27 := mvq 27 rfl (by omega)
  have b54 := P2 27 (by omega) (by omega) b27
  have b108 := N2 54 (by omega) (by omega) b54
  have b43 := mvq 43 rfl (by omega)
  have b86 := P2 43 (by omega) (by omega) b43
  simp only [show 2 * 32 = 64 from rfl, show 2 * 48 = 96 from rfl, show 2 * 56 = 112 from rfl,
    show 2 * 44 = 88 from rfl, show 2 * 60 = 120 from rfl, show 2 * 54 = 108 from rfl,
    show 2 * 43 = 86 from rfl] at b64 b96 b112 b88 b120 b108 b86
  -- 行 c₁
  have hc1 := row_next m (a + (m + 2)) hb (by rw [hh]; exact b64)
  have hc1odd := odd_of_rows m (a + (m + 2) + (m + 1)) hmo hc1 (Or.inr ⟨a + (m + 2), rfl, hb⟩)
  have hblk1 := blk1_direct m _ hc1 hc1odd
  -- c₁ の N：手 k で (b + k) に移る（c₁ + d − k = b + (128u + d − k)）
  have mvc1 : ∀ d k, d * u + 128 * u = 2 * (k * u) → k * u ≤ m → 1 ≤ d * u → d * u ≤ m →
      IsP m (a + (m + 2) + k * u) (k * u) → ¬ IsP m (a + (m + 2) + (m + 1) + d * u) (d * u) := by
    intro d k hdk hkm hd1 hdm hP
    exact not_isP_move m _ _ (k * u) (by omega) hkm (by omega) (by omega)
      (by rw [show a + (m + 2) + (m + 1) + d * u - k * u = a + (m + 2) + k * u by omega]; exact hP)
  have c64 := mvc1 64 96 (by omega) (by omega) (by omega) (by omega) b96
  have c48 := mvc1 48 88 (by omega) (by omega) (by omega) (by omega) b88
  have c112 := mvc1 112 120 (by omega) (by omega) (by omega) (by omega) b120
  have c44 := mvc1 44 86 (by omega) (by omega) (by omega) (by omega) b86
  have c96 : IsP m (a + (m + 2) + (m + 1) + 96 * u) (96 * u) :=
    e_even m (64 * u) (a + (m + 2)) (96 * u) hmh hb hc1 (by omega) (by omega) (by omega)
      (by rw [show 96 * u / 2 = 48 * u by omega]; exact c48)
      (by rw [show 64 * u + 96 * u / 2 = 112 * u by omega]; exact b112)
  have c88 : IsP m (a + (m + 2) + (m + 1) + 88 * u) (88 * u) :=
    e_even m (64 * u) (a + (m + 2)) (88 * u) hmh hb hc1 (by omega) (by omega) (by omega)
      (by rw [show 88 * u / 2 = 44 * u by omega]; exact c44)
      (by rw [show 64 * u + 88 * u / 2 = 108 * u by omega]; exact b108)
  -- 行 c₂
  have hc2 := row_next m (a + (m + 2) + (m + 1)) hc1 (by rw [hh]; exact c64)
  have hblk2 := blk_step2 m 1 3 _ hmo rfl (by omega) (by rw [hh, hv64]; omega) hc1 hblk1 hc2
  have mvc2 : ∀ d k, d * u + 128 * u = 2 * (k * u) → k * u ≤ m → 1 ≤ d * u → d * u ≤ m →
      IsP m (a + (m + 2) + (m + 1) + k * u) (k * u) → ¬ IsP m (a + (m + 2) + (m + 1) + (m + 1) + d * u) (d * u) := by
    intro d k hdk hkm hd1 hdm hP
    exact not_isP_move m _ _ (k * u) (by omega) hkm (by omega) (by omega)
      (by rw [show a + (m + 2) + (m + 1) + (m + 1) + d * u - k * u = a + (m + 2) + (m + 1) + k * u by omega]; exact hP)
  have d64 := mvc2 64 96 (by omega) (by omega) (by omega) (by omega) c96
  have d48 := mvc2 48 88 (by omega) (by omega) (by omega) (by omega) c88
  have d96 : IsP m (a + (m + 2) + (m + 1) + (m + 1) + 96 * u) (96 * u) :=
    e_even m (64 * u) (a + (m + 2) + (m + 1)) (96 * u) hmh hc1 hc2 (by omega) (by omega) (by omega)
      (by rw [show 96 * u / 2 = 48 * u by omega]; exact d48)
      (by rw [show 64 * u + 96 * u / 2 = 112 * u by omega]; exact c112)
  -- 行 c₃
  have hc3 := row_next m (a + (m + 2) + (m + 1) + (m + 1)) hc2 (by rw [hh]; exact d64)
  have hblk3 := blk_step2 m 3 5 _ hmo rfl (by omega) (by rw [hh, hv64]; omega) hc2 hblk2 hc3
  have e64 : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 1) + (m + 1) + 64 * u) (64 * u) :=
    not_isP_move m _ _ (96 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + (m + 1) + (m + 1) + (m + 1) + 64 * u - 96 * u
              = a + (m + 2) + (m + 1) + (m + 1) + 96 * u by omega]; exact d96)
  -- 行 a'
  have ha' := row_next m (a + (m + 2) + (m + 1) + (m + 1) + (m + 1)) hc3 (by rw [hh]; exact e64)
  have hblk' := blk_step2 m 5 6 _ hmo rfl (by omega) (by rw [hh, hv64]; exact Nat.le_refl 6) hc3 hblk3 ha'
  have e1 : a + (5 * m + 6) = a + (m + 2) + (m + 1) + (m + 1) + (m + 1) + (m + 1) := by omega
  refine ⟨hb, ?_, ?_, ?_, ?_, ?_, hah⟩
  · intro p; rw [show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega]; exact hc1 p
  · intro p; rw [show a + (3 * m + 4) = a + (m + 2) + (m + 1) + (m + 1) by omega]; exact hc2 p
  · intro p; rw [show a + (4 * m + 5) = a + (m + 2) + (m + 1) + (m + 1) + (m + 1) by omega]; exact hc3 p
  · intro p; rw [e1]; exact ha' p
  · rw [e1]; exact hblk'

theorem k38v7_rows :
    ∀ i, (∀ p, IsP m (i * (5 * m + 6)) p) ∧ (∀ p, IsP m (i * (5 * m + 6) + (m + 2)) p) ∧
      (∀ p, IsP m (i * (5 * m + 6) + (2 * m + 3)) p) ∧ (∀ p, IsP m (i * (5 * m + 6) + (3 * m + 4)) p) ∧
      (∀ p, IsP m (i * (5 * m + 6) + (4 * m + 5)) p) ∧
      IsP m (i * (5 * m + 6) + 64 * u) (64 * u) ∧ Blk m 6 (i * (5 * m + 6)) := by
  intro i
  induction i with
  | zero =>
    have hrow : ∀ p, IsP m (0 * (5 * m + 6)) p := by intro p; rw [Nat.zero_mul]; exact isP_zero m p
    have hblk : Blk m 6 (0 * (5 * m + 6)) := by rw [Nat.zero_mul]; exact blk_zero m 6
    obtain ⟨hb, hc1, hc2, hc3, _, _, hah⟩ := k38v7_step m u hmu hu he1 _ hrow hblk
    exact ⟨hrow, hb, hc1, hc2, hc3, hah, hblk⟩
  | succ i ih =>
    obtain ⟨hrow, _, _, _, _, _, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha', hblk', _⟩ := k38v7_step m u hmu hu he1 _ hrow hblk
    obtain ⟨hb', hc1', hc2', hc3', _, _, hah'⟩ := k38v7_step m u hmu hu he1 _ ha' hblk'
    rw [Nat.succ_mul]
    exact ⟨ha', hb', hc1', hc2', hc3', hah', hblk'⟩

end K38v7

/-- 定理 K38（v = 7）：m + 1 = 128u で u ≡ 7 (mod 16)、u ≡ 31 (mod 64)、u ≡ 255 (mod 256) のどれかなら、
    (n, 0) が P ⇔ n mod (5m+6) ∈ {0, m+2, 2m+3, 3m+4, 4m+5}。-/
theorem K38_v7 (m : Nat) (hm : (m + 1) % 128 = 0)
    (hu : (m + 1) / 128 % 16 = 7 ∨ (m + 1) / 128 % 64 = 31 ∨ (m + 1) / 128 % 256 = 255) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 6) = 0 ∨ n % (5 * m + 6) = m + 2 ∨ n % (5 * m + 6) = 2 * m + 3 ∨
      n % (5 * m + 6) = 3 * m + 4 ∨ n % (5 * m + 6) = 4 * m + 5) := by
  obtain ⟨u, hu'⟩ : ∃ u, (m + 1) / 128 = u := ⟨_, rfl⟩
  rw [hu'] at hu
  have hmu : m + 1 = 128 * u := by omega
  have he1 : v2 ((129 * u + 1) / 2) = 2 ∨ v2 ((129 * u + 1) / 2) = 4 ∨ v2 ((129 * u + 1) / 2) = 6 := by
    rcases hu with h | h | h
    · left; rw [v2_even _ (by omega) (by omega), v2_of_mod4 _ (by omega)]
    · right; left
      rw [v2_even _ (by omega) (by omega), v2_even _ (by omega) (by omega), v2_even _ (by omega) (by omega),
        v2_of_mod4 _ (by omega)]
    · right; right
      rw [v2_even _ (by omega) (by omega), v2_even _ (by omega) (by omega), v2_even _ (by omega) (by omega),
        v2_even _ (by omega) (by omega), v2_even _ (by omega) (by omega), v2_of_mod4 _ (by omega)]
  obtain ⟨hrow, hrowb, hrowc, hrowd, hrowe, hah, _⟩ := k38v7_rows m u hmu (by omega) he1 (n / (5 * m + 6))
  have hdiv : n = (n / (5 * m + 6)) * (5 * m + 6) + n % (5 * m + 6) := by
    have := Nat.div_add_mod n (5 * m + 6)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (5 * m + 6) < 5 * m + 6 := Nat.mod_lt n (by omega)
  generalize hcc : n % (5 * m + 6) = c at hdiv hlt
  generalize ha : n / (5 * m + 6) * (5 * m + 6) = a at hdiv hrow hrowb hrowc hrowd hrowe hah
  subst hdiv
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases h1 : c ≤ m
    · exact not_isP_of_row m a c 0 hrow (by omega) h1 (by omega) hP
    · by_cases h2 : c = m + 1
      · subst h2
        exact not_isP_near m a (64 * u) 0 (by omega) (by omega) (by omega) hah (by omega) hP
      · by_cases h3 : c ≤ 2 * m + 2
        · rw [show a + c = a + (m + 2) + (c - (m + 2)) by omega] at hP
          exact not_isP_of_row m _ (c - (m + 2)) 0 hrowb (by omega) (by omega) (by omega) hP
        · by_cases h4 : c ≤ 3 * m + 3
          · rw [show a + c = a + (2 * m + 3) + (c - (2 * m + 3)) by omega] at hP
            exact not_isP_of_row m _ (c - (2 * m + 3)) 0 hrowc (by omega) (by omega) (by omega) hP
          · by_cases h5 : c ≤ 4 * m + 4
            · rw [show a + c = a + (3 * m + 4) + (c - (3 * m + 4)) by omega] at hP
              exact not_isP_of_row m _ (c - (3 * m + 4)) 0 hrowd (by omega) (by omega) (by omega) hP
            · rw [show a + c = a + (4 * m + 5) + (c - (4 * m + 5)) by omega] at hP
              exact not_isP_of_row m _ (c - (4 * m + 5)) 0 hrowe (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h]; exact hrowb 0
    · rw [h]; exact hrowc 0
    · rw [h]; exact hrowd 0
    · rw [h]; exact hrowe 0

end Rubidium
