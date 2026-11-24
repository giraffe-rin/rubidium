/-
  Rubidium.K4Full — 定理 K4 全体の形式化

  定理 K4（gemini-2 が査読済み）：m ≥ 1 のとき、
    「すべての n で (n, 0) が P 局面 ⇔ (m+1) | n」⇔ v2(m+1) が偶数。
  - ⇒：n = m+1 とおくと K4_first（Rubidium.K5）。
  - ⇐、m が偶数：K4_even（Rubidium.K4Even）。
  - ⇐、m が奇数：h = (m+1)/2、s = v2(h)（奇数）。各行 r = j(m+1) について、次の 2 つを j の帰納法で同時に示す。
      Row r：すべての p で (r, p) は P。
      Blk r：1 ≤ d ≤ m、v2(d) ≤ s なら、(r + d, d) が P ⇔ v2(d) が偶数。
    Blk r は d についての強い帰納法で示す（下の `blk_step` の説明）。h は v2(h) = s が奇数なので (r + h, h) は N で、
    次の行 r + (m+1) からの手はどれも N 局面に移る（`row_next`）。
-/
import Rubidium.K5
import Rubidium.K4Even

namespace Rubidium

/-! ### 2 の付値 v2 -/

/-- 2 の付値。v2 0 = 0 とする（使わない）。-/
def v2 (n : Nat) : Nat := if n ≠ 0 ∧ n % 2 = 0 then v2 (n / 2) + 1 else 0
termination_by n
decreasing_by omega

theorem v2_odd (n : Nat) (h : n % 2 = 1) : v2 n = 0 := by
  rw [v2]; simp; omega

theorem v2_even (n : Nat) (h0 : n ≠ 0) (h : n % 2 = 0) : v2 n = v2 (n / 2) + 1 := by
  rw [v2]; simp [h0, h]

/-- v2 が正なら偶数。-/
theorem even_of_v2_pos (n : Nat) (h : 0 < v2 n) : n % 2 = 0 := by
  apply Decidable.byContradiction
  intro hn
  rw [v2_odd n (by omega)] at h
  omega

/-- ev2 は v2 の偶奇。-/
theorem ev2_iff_v2 : ∀ n, 1 ≤ n → (ev2 n = true ↔ v2 n % 2 = 0) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro h1
    by_cases hp : n % 2 = 1
    · rw [ev2_odd n hp, v2_odd n hp]; simp
    · have h0 : n % 2 = 0 := by omega
      rw [ev2_even n (by omega) h0, v2_even n (by omega) h0]
      have := ih (n / 2) (by omega) (by omega)
      cases hb : ev2 (n / 2) <;> simp [hb] at this ⊢ <;> omega

/-- v2 x < v2 y なら v2 (x + y) = v2 x。-/
theorem v2_add : ∀ x y, 1 ≤ x → 1 ≤ y → v2 x < v2 y → v2 (x + y) = v2 x := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro y hx hy hlt
    have hye : y % 2 = 0 := even_of_v2_pos y (by omega)
    by_cases hxo : x % 2 = 1
    · rw [v2_odd x hxo, v2_odd (x + y) (by omega)]
    · have hxe : x % 2 = 0 := by omega
      have hx2 : 1 ≤ x / 2 := by omega
      have hy2 : 1 ≤ y / 2 := by omega
      rw [v2_even x (by omega) hxe] at hlt ⊢
      rw [v2_even y (by omega) hye] at hlt
      rw [v2_even (x + y) (by omega) (by omega)]
      have hs : (x + y) / 2 = x / 2 + y / 2 := by omega
      rw [hs, ih (x / 2) (by omega) (y / 2) hx2 hy2 (by omega)]

/-! ### m が奇数の場合 -/

/-- 行 r の次の行：(r + h, h) が N なら、行 r + (m+1) はすべての p で P（m が奇数、h = (m+1)/2）。-/
theorem row_next (m r : Nat) (hrow : ∀ p, IsP m r p) (hh : ¬ IsP m (r + (m + 1) / 2) ((m + 1) / 2)) :
    ∀ p, IsP m (r + (m + 1)) p := by
  intro p
  rw [isP_iff]
  intro k hk1 hkm _ _ hPk
  have hs : r + (m + 1) - k = r + (m + 1 - k) := by omega
  rw [hs] at hPk
  by_cases hk : k = m + 1 - k
  · have hkh : k = (m + 1) / 2 := by omega
    rw [hkh, show m + 1 - (m + 1) / 2 = (m + 1) / 2 by omega] at hPk
    exact hh hPk
  · exact not_isP_of_row m r (m + 1 - k) k hrow (by omega) (by omega) hk hPk

/-- 行 r の性質 Blk：1 ≤ d ≤ m、v2 d ≤ s なら、(r + d, d) が P ⇔ v2 d が偶数。-/
def Blk (m s r : Nat) : Prop :=
  ∀ d, 1 ≤ d → d ≤ m → v2 d ≤ s → (IsP m (r + d) d ↔ v2 d % 2 = 0)

/-- Blk の 1 段。m が奇数、h = (m+1)/2、s = v2 h。行 r がすべての p で P で、
    r = 0 か、r = r' + (m+1) で行 r' がすべての p で P かつ Blk r' なら、Blk r。
    d についての強い帰納法：
    - v2 d が奇数：手 d/2 で (r + d/2, d/2) に移れ、v2(d/2) は偶数なので帰納法の仮定より P。
    - v2 d が偶数：手 k < d の行き先 (r + (d−k), k) は、k = d − k（d = 2k、v2 k は奇数）のときだけ P になりうるが、帰納法の仮定より N。
      手 k > d の行き先は (r' + (m+1+d−k), k)（r = 0 では k ≤ d なので起こらない）。k = m+1+d−k のときだけ P になりうる。
      そのとき d は偶数で k = h + d/2、v2(d/2) = v2 d − 1 < s = v2 h なので v2 k = v2(d/2) は奇数で、Blk r' より N。-/
theorem blk_step (m s r : Nat) (hmo : m % 2 = 1) (hs : v2 ((m + 1) / 2) = s)
    (hrow : ∀ p, IsP m r p)
    (hprev : r = 0 ∨ ∃ r', r = r' + (m + 1) ∧ (∀ p, IsP m r' p) ∧ Blk m s r') :
    Blk m s r := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro hd1 hdm hds
    constructor
    · -- P なら v2 d は偶数
      intro hP
      apply Decidable.byContradiction
      intro hodd
      have hde : d % 2 = 0 := even_of_v2_pos d (by omega)
      have hv : v2 d = v2 (d / 2) + 1 := v2_even d (by omega) hde
      rw [isP_iff] at hP
      apply hP (d / 2) (by omega) (by omega) (by omega) (by omega)
      rw [show r + d - d / 2 = r + d / 2 by omega]
      exact (ih (d / 2) (by omega) (by omega) (by omega) (by omega)).mpr (by omega)
    · -- v2 d が偶数なら P
      intro hev
      rw [isP_iff]
      intro k hk1 hkm hkr hkd hPk
      by_cases hlt : k < d
      · rw [show r + d - k = r + (d - k) by omega] at hPk
        by_cases hk : k = d - k
        · -- d = 2k
          have hde : d % 2 = 0 := by omega
          have hd2 : d / 2 = k := by omega
          have hv : v2 d = v2 k + 1 := by rw [v2_even d (by omega) hde, hd2]
          rw [← hk] at hPk
          have := (ih k hlt hk1 (by omega) (by omega)).mp hPk
          omega
        · exact not_isP_of_row m r (d - k) k hrow (by omega) (by omega) hk hPk
      · have hgt : d < k := by omega
        rcases hprev with h0 | ⟨r', hr', hrow', hblk'⟩
        · omega
        · rw [show r + d - k = r' + (m + 1 + d - k) by omega] at hPk
          by_cases hk : k = m + 1 + d - k
          · -- d は偶数で k = h + d/2
            have hde : d % 2 = 0 := by omega
            have hv : v2 d = v2 (d / 2) + 1 := v2_even d (by omega) hde
            have hkh : k = d / 2 + (m + 1) / 2 := by omega
            have hvk : v2 k = v2 (d / 2) := by
              rw [hkh]; exact v2_add (d / 2) ((m + 1) / 2) (by omega) (by omega) (by omega)
            rw [← hk] at hPk
            have := (hblk' k hk1 hkm (by omega)).mp hPk
            omega
          · exact not_isP_of_row m r' (m + 1 + d - k) k hrow' (by omega) (by omega) hk hPk

/-- m が奇数で v2(m+1) が偶数なら、すべての j で、行 j(m+1) はすべての p で P、かつ Blk。-/
theorem row_all_odd (m : Nat) (hmo : m % 2 = 1) (hev : ev2 (m + 1) = true) :
    ∀ j, (∀ p, IsP m (j * (m + 1)) p) ∧ Blk m (v2 ((m + 1) / 2)) (j * (m + 1)) := by
  have hv : v2 (m + 1) = v2 ((m + 1) / 2) + 1 := v2_even (m + 1) (by omega) (by omega)
  have hev' := (ev2_iff_v2 (m + 1) (by omega)).mp hev
  have hh1 : 1 ≤ (m + 1) / 2 := by omega
  have hhm : (m + 1) / 2 ≤ m := by omega
  intro j
  induction j with
  | zero =>
    have hrow : ∀ p, IsP m (0 * (m + 1)) p := by intro p; rw [Nat.zero_mul]; exact isP_zero m p
    exact ⟨hrow, blk_step m _ _ hmo rfl hrow (Or.inl (Nat.zero_mul _))⟩
  | succ j ih =>
    obtain ⟨hrow, hblk⟩ := ih
    -- h は v2 h = s が奇数なので (r + h, h) は N
    have hhN : ¬ IsP m (j * (m + 1) + (m + 1) / 2) ((m + 1) / 2) := by
      intro hP
      have := (hblk ((m + 1) / 2) hh1 hhm (Nat.le_refl _)).mp hP
      omega
    have hrow2 : ∀ p, IsP m ((j + 1) * (m + 1)) p := by
      rw [Nat.succ_mul]; exact row_next m _ hrow hhN
    exact ⟨hrow2, blk_step m _ _ hmo rfl hrow2 (Or.inr ⟨j * (m + 1), Nat.succ_mul j (m + 1), hrow, hblk⟩)⟩

/-- 定理 K4（m が奇数で v2(m+1) が偶数の場合の ⇐）：IsP m n 0 ↔ (m+1) | n。-/
theorem K4_odd (m : Nat) (hmo : m % 2 = 1) (hev : ev2 (m + 1) = true) (n : Nat) :
    IsP m n 0 ↔ n % (m + 1) = 0 := by
  have hdiv : n = (n / (m + 1)) * (m + 1) + n % (m + 1) := by
    have := Nat.div_add_mod n (m + 1)
    rw [Nat.mul_comm] at this; omega
  have hrow := (row_all_odd m hmo hev (n / (m + 1))).1
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    have hlt : n % (m + 1) < m + 1 := Nat.mod_lt n (by omega)
    rw [hdiv] at hP
    exact not_isP_of_row m _ (n % (m + 1)) 0 hrow (by omega) (by omega) (by omega) hP
  · intro h0
    rw [hdiv, h0, Nat.add_zero]
    exact hrow 0

/-- 定理 K4：m ≥ 1 のとき、「すべての n で (n, 0) が P ⇔ (m+1) | n」⇔ v2(m+1) が偶数。-/
theorem K4 (m : Nat) (hm : 1 ≤ m) :
    (∀ n, IsP m n 0 ↔ n % (m + 1) = 0) ↔ ev2 (m + 1) = true := by
  constructor
  · intro hall
    rw [← K4_first m hm, hall (m + 1)]
    exact Nat.mod_self (m + 1)
  · intro hev n
    by_cases hmo : m % 2 = 1
    · exact K4_odd m hmo hev n
    · exact K4_even m (by omega) n

end Rubidium
