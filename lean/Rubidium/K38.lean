/-
  Rubidium.K38 — 定理 K38 の v = 5 の場合の形式化

  定理 K38（v = 5）：m + 1 = 32u、w = v2(u+1) が 3 または 6 以上なら「1000 型」：
    (n, 0) が P ⇔ n mod (4m+5) ∈ {0, m+2, 2m+3, 3m+4}。
  条件は m % 512 = 223（w = 3）または m % 2048 = 2015（w ≥ 6）と同じ。
  h = 16u、e₁ = (33u+1)/2（v2(e₁) は 2 または 4）。L = 4m+5、a = iL、b = a + (m+2)、c₁ = b + (m+1)、c₂ = c₁ + (m+1)。
  - 行 a：Blk m 4 a（v2(d) ≤ 4 なら (a+d, d) が P ⇔ v2(d) が偶数。K4 の形式化の `Blk`）。
  - 行 b（O 型）：(b + u)・(b + 3u)・(b + 7u)・(b + 11u) は N（手 e₁、(35u+1)/2、(39u+1)/2、(43u+1)/2）。
    半分にする鎖で (b + 2u)・(b + 6u)・(b + 8u)・(b + 14u)・(b + 22u)・(b + 24u) は P、(b + 4u)・(b + 12u)・(b + 16u)・(b + 28u) は N。
  - 行 c₁：Blk m 1（`blk1_direct`）。(c₁ + h) は N（手 24u）、(c₁ + 12u) は N（手 22u）、(c₁ + 24u) は P（`e_even`）。
  - 行 c₂：Blk m 3（`blk_step2`）。(c₂ + h) は N（手 24u）。
  - 行 a + L：Blk m 4（`blk_step2`）。
  `blk_step2`：s が奇数、t ≤ s + 2、t ≤ v2(h) のとき、Blk m s r' から Blk m t (r' + (m+1))（K4 の `blk_step` の変形）。
-/
import Rubidium.K29

namespace Rubidium

set_option maxHeartbeats 4000000

theorem v2_two_mul (x : Nat) (hx : 1 ≤ x) : v2 (2 * x) = v2 x + 1 := by
  rw [v2_even (2 * x) (by omega) (by omega), show 2 * x / 2 = x by omega]

/-- 行 r がすべての p で P、奇数 d の (r + d, d) が P なら、Blk m 1 r。-/
theorem blk1_direct (m r : Nat) (_hrow : ∀ p, IsP m r p) (hodd : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (r + d) d) :
    Blk m 1 r := by
  intro d hd1 hdm hds
  by_cases hdo : d % 2 = 1
  · rw [v2_odd d hdo]; exact ⟨fun _ => rfl, fun _ => hodd d hd1 hdm hdo⟩
  · have hv : v2 d = v2 (d / 2) + 1 := v2_even d (by omega) (by omega)
    have hd2 : v2 (d / 2) = 0 := by omega
    have hho : (d / 2) % 2 = 1 := by
      apply Decidable.byContradiction; intro h
      have := v2_even (d / 2) (by omega) (by omega); omega
    constructor
    · intro hP
      exfalso
      exact not_isP_move m _ d (d / 2) (by omega) (by omega) (by omega) (by omega)
        (by rw [show r + d - d / 2 = r + d / 2 by omega]; exact hodd _ (by omega) (by omega) hho) hP
    · intro h; omega

/-- K4 の blk_step の変形：s が奇数、t ≤ s + 2、t ≤ v2(h) なら、Blk m s r' と行 r'・行 r = r' + (m+1) から Blk m t r。-/
theorem blk_step2 (m s t r' : Nat) (hmo : m % 2 = 1) (hso : s % 2 = 1) (hts : t ≤ s + 2)
    (htv : t ≤ v2 ((m + 1) / 2)) (hrow' : ∀ p, IsP m r' p) (hblk' : Blk m s r')
    (hrow : ∀ p, IsP m (r' + (m + 1)) p) : Blk m t (r' + (m + 1)) := by
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
      rw [show r' + (m + 1) + d - d / 2 = r' + (m + 1) + d / 2 by omega]
      exact (ih (d / 2) (by omega) (by omega) (by omega) (by omega)).mpr (by omega)
    · intro hev
      rw [isP_iff]
      intro k hk1 hkm hkr hkd hPk
      by_cases hlt : k < d
      · rw [show r' + (m + 1) + d - k = r' + (m + 1) + (d - k) by omega] at hPk
        by_cases hk : k = d - k
        · have hde : d % 2 = 0 := by omega
          have hd2 : d / 2 = k := by omega
          have hv : v2 d = v2 k + 1 := by rw [v2_even d (by omega) hde, hd2]
          rw [← hk] at hPk
          have := (ih k hlt hk1 (by omega) (by omega)).mp hPk
          omega
        · exact not_isP_of_row m _ (d - k) k hrow (by omega) (by omega) hk hPk
      · rw [show r' + (m + 1) + d - k = r' + (m + 1 + d - k) by omega] at hPk
        by_cases hk : k = m + 1 + d - k
        · have hde : d % 2 = 0 := by omega
          have hv : v2 d = v2 (d / 2) + 1 := v2_even d (by omega) hde
          have hkh : k = d / 2 + (m + 1) / 2 := by omega
          have hvk : v2 k = v2 (d / 2) := by
            rw [hkh]; exact v2_add (d / 2) ((m + 1) / 2) (by omega) (by omega) (by omega)
          rw [← hk] at hPk
          have := (hblk' k hk1 hkm (by omega)).mp hPk
          omega
        · exact not_isP_of_row m r' (m + 1 + d - k) k hrow' (by omega) (by omega) hk hPk

/-- 行 0 では Blk m s 0（K3）。-/
theorem blk_zero (m s : Nat) : Blk m s 0 := by
  intro d hd1 hdm _
  rw [Nat.zero_add, K3 m d d hd1 hdm, ev2_iff_v2 d hd1]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

section K38

variable (m u : Nat) (hmu : m + 1 = 32 * u) (hu : u % 4 = 3)
  (he1 : v2 ((33 * u + 1) / 2) = 2 ∨ v2 ((33 * u + 1) / 2) = 4)
include hmu hu he1

theorem k38_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 4 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧ (∀ p, IsP m (a + (2 * m + 3)) p) ∧ (∀ p, IsP m (a + (3 * m + 4)) p) ∧
    (∀ p, IsP m (a + (4 * m + 5)) p) ∧ Blk m 4 (a + (4 * m + 5)) ∧ IsP m (a + 16 * u) (16 * u) := by
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 16 * u := by omega
  have hmh : m + 1 = 2 * (16 * u) := by omega
  have hv16 : v2 (16 * u) = 4 := by
    rw [show 16 * u = 2 * (2 * (2 * (2 * u))) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega),
      v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hah : IsP m (a + 16 * u) (16 * u) := (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  have hah' : IsP m (a + (m + 1) / 2) ((m + 1) / 2) := by rw [hh]; exact hah
  have hb := row_long m a hmo (by omega) hrow hah'
  -- 行 a の奇数は P
  have hoddA : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d :=
    fun d hd1 hdm hdo => (hblk d hd1 hdm (by rw [v2_odd d hdo]; omega)).mpr (by rw [v2_odd d hdo])
  -- 行 b の奇数 cu（相手 (m+2+cu)/2 が P）は N
  have mv : ∀ d e, (m + 2 + d) = 2 * e → e ≤ m → e ≠ d → 1 ≤ d → IsP m (a + e) e → ¬ IsP m (a + (m + 2) + d) d :=
    fun d e hde hem hed hd1 hP => not_isP_move m _ d e (by omega) hem (by omega) hed
      (by rw [show a + (m + 2) + d - e = a + e by omega]; exact hP)
  have hbu := mv u ((33 * u + 1) / 2) (by omega) (by omega) (by omega) (by omega)
    ((hblk _ (by omega) (by omega) (by omega)).mpr (by omega))
  have hb3 := mv (3 * u) ((35 * u + 1) / 2) (by omega) (by omega) (by omega) (by omega)
    (hoddA _ (by omega) (by omega) (by omega))
  have hb7 := mv (7 * u) ((39 * u + 1) / 2) (by omega) (by omega) (by omega) (by omega)
    (hoddA _ (by omega) (by omega) (by omega))
  have hb11 := mv (11 * u) ((43 * u + 1) / 2) (by omega) (by omega) (by omega) (by omega)
    (hoddA _ (by omega) (by omega) (by omega))
  have p2 : ∀ z, 1 ≤ z → 2 * z + 1 ≤ m → 2 * z + 1 ≠ 16 * u → ¬ IsP m (a + (m + 2) + z) z →
      IsP m (a + (m + 2) + 2 * z) (2 * z) :=
    fun z hz1 hzm hzh hbz => p_two m a z hmo hz1 hzm (by rw [hh]; exact hzh) (by omega) hrow hb hah' hbz
  have nh : ∀ z, 1 ≤ z → 2 * z ≤ m → IsP m (a + (m + 2) + z) z → ¬ IsP m (a + (m + 2) + 2 * z) (2 * z) :=
    fun z hz1 hzm hP => not_isP_move m _ _ z (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + 2 * z - z = a + (m + 2) + z by omega]; exact hP)
  have hb2 := p2 u (by omega) (by omega) (by omega) hbu
  have hb4 := nh (2 * u) (by omega) (by omega) hb2
  have hb8 := p2 (2 * (2 * u)) (by omega) (by omega) (by omega) hb4
  have hb16 := nh (2 * (2 * (2 * u))) (by omega) (by omega) hb8
  have hb6 := p2 (3 * u) (by omega) (by omega) (by omega) hb3
  have hb12 := nh (2 * (3 * u)) (by omega) (by omega) hb6
  have hb24 := p2 (2 * (2 * (3 * u))) (by omega) (by omega) (by omega) hb12
  have hb14 := p2 (7 * u) (by omega) (by omega) (by omega) hb7
  have hb28 := nh (2 * (7 * u)) (by omega) (by omega) hb14
  have hb22 := p2 (11 * u) (by omega) (by omega) (by omega) hb11
  rw [show 2 * (2 * (2 * (2 * u))) = 16 * u by omega] at hb16
  rw [show 2 * (2 * (2 * (3 * u))) = 24 * u by omega] at hb24
  rw [show 2 * (2 * (7 * u)) = 28 * u by omega] at hb28
  rw [show 2 * (11 * u) = 22 * u by omega] at hb22
  -- 行 c₁ = b + (m+1)
  have hc1 := row_next m (a + (m + 2)) hb (by rw [hh]; exact hb16)
  have hc1odd := odd_of_rows m (a + (m + 2) + (m + 1)) hmo hc1 (Or.inr ⟨a + (m + 2), rfl, hb⟩)
  have hblk1 := blk1_direct m _ hc1 hc1odd
  have hc1h : ¬ IsP m (a + (m + 2) + (m + 1) + 16 * u) (16 * u) :=
    not_isP_move m _ _ (24 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + (m + 1) + 16 * u - 24 * u = a + (m + 2) + 24 * u by omega]; exact hb24)
  have hc1_12 : ¬ IsP m (a + (m + 2) + (m + 1) + 12 * u) (12 * u) :=
    not_isP_move m _ _ (22 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + (m + 1) + 12 * u - 22 * u = a + (m + 2) + 22 * u by omega]; exact hb22)
  have hc1_24 : IsP m (a + (m + 2) + (m + 1) + 24 * u) (24 * u) :=
    e_even m (16 * u) (a + (m + 2)) (24 * u) hmh hb hc1 (by omega) (by omega) (by omega)
      (by rw [show 24 * u / 2 = 12 * u by omega]; exact hc1_12)
      (by rw [show 16 * u + 24 * u / 2 = 28 * u by omega]; exact hb28)
  -- 行 c₂ = c₁ + (m+1)
  have hc2 := row_next m (a + (m + 2) + (m + 1)) hc1 (by rw [hh]; exact hc1h)
  have hblk2 := blk_step2 m 1 3 _ hmo rfl (by omega) (by rw [hh, hv16]; omega) hc1 hblk1 hc2
  have hc2h : ¬ IsP m (a + (m + 2) + (m + 1) + (m + 1) + 16 * u) (16 * u) :=
    not_isP_move m _ _ (24 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + (m + 1) + (m + 1) + 16 * u - 24 * u = a + (m + 2) + (m + 1) + 24 * u by omega]
          exact hc1_24)
  -- 行 a' = c₂ + (m+1)
  have ha' := row_next m (a + (m + 2) + (m + 1) + (m + 1)) hc2 (by rw [hh]; exact hc2h)
  have hblk' := blk_step2 m 3 4 _ hmo rfl (by omega) (by rw [hh, hv16]; exact Nat.le_refl 4) hc2 hblk2 ha'
  have e1 : a + (4 * m + 5) = a + (m + 2) + (m + 1) + (m + 1) + (m + 1) := by omega
  refine ⟨hb, ?_, ?_, ?_, ?_, hah⟩
  · intro p; rw [show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega]; exact hc1 p
  · intro p; rw [show a + (3 * m + 4) = a + (m + 2) + (m + 1) + (m + 1) by omega]; exact hc2 p
  · intro p; rw [e1]; exact ha' p
  · rw [e1]; exact hblk'

theorem k38_rows :
    ∀ i, (∀ p, IsP m (i * (4 * m + 5)) p) ∧ (∀ p, IsP m (i * (4 * m + 5) + (m + 2)) p) ∧
      (∀ p, IsP m (i * (4 * m + 5) + (2 * m + 3)) p) ∧ (∀ p, IsP m (i * (4 * m + 5) + (3 * m + 4)) p) ∧
      IsP m (i * (4 * m + 5) + 16 * u) (16 * u) ∧ Blk m 4 (i * (4 * m + 5)) := by
  intro i
  induction i with
  | zero =>
    have hrow : ∀ p, IsP m (0 * (4 * m + 5)) p := by intro p; rw [Nat.zero_mul]; exact isP_zero m p
    have hblk : Blk m 4 (0 * (4 * m + 5)) := by rw [Nat.zero_mul]; exact blk_zero m 4
    obtain ⟨hb, hc1, hc2, _, _, hah⟩ := k38_step m u hmu hu he1 _ hrow hblk
    exact ⟨hrow, hb, hc1, hc2, hah, hblk⟩
  | succ i ih =>
    obtain ⟨hrow, _, _, _, _, hblk⟩ := ih
    obtain ⟨_, _, _, ha', hblk', _⟩ := k38_step m u hmu hu he1 _ hrow hblk
    obtain ⟨hb', hc1', hc2', _, _, hah'⟩ := k38_step m u hmu hu he1 _ ha' hblk'
    rw [Nat.succ_mul]
    exact ⟨ha', hb', hc1', hc2', hah', hblk'⟩

end K38

/-- 定理 K38（v = 5）：m % 512 = 223 または m % 2048 = 2015 なら、(n, 0) が P ⇔ n mod (4m+5) ∈ {0, m+2, 2m+3, 3m+4}。-/
theorem K38_v5 (m : Nat) (hm : m % 512 = 223 ∨ m % 2048 = 2015) (n : Nat) :
    IsP m n 0 ↔ (n % (4 * m + 5) = 0 ∨ n % (4 * m + 5) = m + 2 ∨ n % (4 * m + 5) = 2 * m + 3 ∨
      n % (4 * m + 5) = 3 * m + 4) := by
  have hmu : m + 1 = 32 * ((m + 1) / 32) := by omega
  have he1 : v2 ((33 * ((m + 1) / 32) + 1) / 2) = 2 ∨ v2 ((33 * ((m + 1) / 32) + 1) / 2) = 4 := by
    rcases hm with h | h
    · left
      rw [v2_even _ (by omega) (by omega), v2_of_mod4 _ (by omega)]
    · right
      rw [v2_even _ (by omega) (by omega), v2_even _ (by omega) (by omega), v2_even _ (by omega) (by omega),
        v2_of_mod4 _ (by omega)]
  obtain ⟨hrow, hrowb, hrowc, hrowd, hah, _⟩ := k38_rows m ((m + 1) / 32) hmu (by omega) he1 (n / (4 * m + 5))
  have hdiv : n = (n / (4 * m + 5)) * (4 * m + 5) + n % (4 * m + 5) := by
    have := Nat.div_add_mod n (4 * m + 5)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (4 * m + 5) < 4 * m + 5 := Nat.mod_lt n (by omega)
  generalize hcc : n % (4 * m + 5) = c at hdiv hlt
  generalize ha : n / (4 * m + 5) * (4 * m + 5) = a at hdiv hrow hrowb hrowc hrowd hah
  subst hdiv
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases h1 : c ≤ m
    · exact not_isP_of_row m a c 0 hrow (by omega) h1 (by omega) hP
    · by_cases h2 : c = m + 1
      · subst h2
        exact not_isP_near m a (16 * ((m + 1) / 32)) 0 (by omega) (by omega) (by omega) hah (by omega) hP
      · by_cases h3 : c ≤ 2 * m + 2
        · rw [show a + c = a + (m + 2) + (c - (m + 2)) by omega] at hP
          exact not_isP_of_row m (a + (m + 2)) (c - (m + 2)) 0 hrowb (by omega) (by omega) (by omega) hP
        · by_cases h4 : c ≤ 3 * m + 3
          · rw [show a + c = a + (2 * m + 3) + (c - (2 * m + 3)) by omega] at hP
            exact not_isP_of_row m (a + (2 * m + 3)) (c - (2 * m + 3)) 0 hrowc (by omega) (by omega) (by omega) hP
          · rw [show a + c = a + (3 * m + 4) + (c - (3 * m + 4)) by omega] at hP
            exact not_isP_of_row m (a + (3 * m + 4)) (c - (3 * m + 4)) 0 hrowd (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h]; exact hrowb 0
    · rw [h]; exact hrowc 0
    · rw [h]; exact hrowd 0

end Rubidium
