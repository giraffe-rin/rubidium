/-
  Rubidium.K9 — 定理 K9 の十分性の形式化

  定理 K9（⇐）：v2(m+1) = 1（m % 4 = 1）、m ≥ 5、v2(3h+1) が奇数（h = (m+1)/2）なら、
    すべての n で (n, 0) が P 局面 ⇔ n mod (2m+3) ∈ {0, m+2}。
  もとの証明（木 T の事実の集合）の代わりに、K4 の形式化（Rubidium.K4Full）と同じ形の不変量を使う。
  e* = (3h+1)/2、s = v2(e*)（偶数）。a = i(2m+3)、b = a + (m+2) とする。
  - Blk m s a（偶数番目のブロック）：1 ≤ d ≤ m、v2 d ≤ s なら、(a + d, d) が P ⇔ v2 d が偶数。
  - BlkO m s b（奇数番目のブロック）：v2 x が奇数で v2 x < s、h + x ≤ m なら、(b + h + x, h + x) は N。
    手 e* + x/2 で (a + e* + x/2, e* + x/2) に移れて、v2(e* + x/2) = v2(x/2) は偶数なので、Blk m s a よりそこは P。
  Blk m s a' の 1 段（`blkE_step`）は K4 の `blk_step` と同じ形で、1 つ前のブロックの事実として Blk の代わりに BlkO を使う。
-/
import Rubidium.K6

namespace Rubidium

/-- 奇数番目のブロック b の性質：v2 x が奇数で v2 x < s、h + x ≤ m なら、(b + h + x, h + x) は N。-/
def BlkO (m s b : Nat) : Prop :=
  ∀ x, 1 ≤ x → v2 x % 2 = 1 → v2 x < s → (m + 1) / 2 + x ≤ m → ¬ IsP m (b + ((m + 1) / 2 + x)) ((m + 1) / 2 + x)

/-- Blk の 1 段（1 つ前のブロックの間隔が m+1）。m が奇数、行 r がすべての p で P で、
    r = 0 か、r = r' + (m+1) で行 r' がすべての p で P かつ BlkO r' なら、Blk r。-/
theorem blkE_step (m s r : Nat) (hmo : m % 2 = 1) (hrow : ∀ p, IsP m r p)
    (hprev : r = 0 ∨ ∃ r', r = r' + (m + 1) ∧ (∀ p, IsP m r' p) ∧ BlkO m s r') :
    Blk m s r := by
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
      rw [show r + d - d / 2 = r + d / 2 by omega]
      exact (ih (d / 2) (by omega) (by omega) (by omega) (by omega)).mpr (by omega)
    · intro hev
      rw [isP_iff]
      intro k hk1 hkm hkr hkd hPk
      by_cases hlt : k < d
      · rw [show r + d - k = r + (d - k) by omega] at hPk
        by_cases hk : k = d - k
        · have hde : d % 2 = 0 := by omega
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
          · -- d は偶数で k = h + d/2、v2(d/2) = v2 d − 1 は奇数
            have hde : d % 2 = 0 := by omega
            have hv : v2 d = v2 (d / 2) + 1 := v2_even d (by omega) hde
            have hkh : k = (m + 1) / 2 + d / 2 := by omega
            rw [← hk, hkh] at hPk
            exact hblk' (d / 2) (by omega) (by omega) (by omega) (by omega) hPk
          · exact not_isP_of_row m r' (m + 1 + d - k) k hrow' (by omega) (by omega) hk hPk

/-- BlkO：Blk m s a と v2 e* = s（e* = (3h+1)/2、h 奇数）から、BlkO m s (a + (m+2))。-/
theorem blkO_of_blk (m s a : Nat) (hm4 : m % 4 = 1)
    (he : v2 ((3 * ((m + 1) / 2) + 1) / 2) = s) (hblk : Blk m s a) : BlkO m s (a + (m + 2)) := by
  intro x hx1 hxo hxs hxm hP
  have hxe : x % 2 = 0 := even_of_v2_pos x (by omega)
  have hvx : v2 x = v2 (x / 2) + 1 := v2_even x (by omega) hxe
  -- 手 k = e* + x/2
  have hvk : v2 (x / 2 + (3 * ((m + 1) / 2) + 1) / 2) = v2 (x / 2) :=
    v2_add (x / 2) _ (by omega) (by omega) (by omega)
  -- k ≠ m + 1（v2(m+1) = 1 は奇数、v2 k は偶数）
  have hvm : v2 (m + 1) = 1 := by
    rw [v2_even (m + 1) (by omega) (by omega), v2_odd ((m + 1) / 2) (by omega)]
  have hkm : x / 2 + (3 * ((m + 1) / 2) + 1) / 2 ≤ m := by
    have hle : x / 2 + (3 * ((m + 1) / 2) + 1) / 2 ≤ m + 1 := by omega
    rcases Nat.lt_or_eq_of_le hle with h | h
    · omega
    · rw [h, hvm] at hvk; omega
  rw [isP_iff] at hP
  apply hP (x / 2 + (3 * ((m + 1) / 2) + 1) / 2) (by omega) hkm (by omega) (by omega)
  rw [show a + (m + 2) + ((m + 1) / 2 + x) - (x / 2 + (3 * ((m + 1) / 2) + 1) / 2)
      = a + (x / 2 + (3 * ((m + 1) / 2) + 1) / 2) by omega]
  exact (hblk _ (by omega) hkm (by omega)).mpr (by omega)

/-- K9 の不変量：すべての i で、行 i(2m+3) と行 i(2m+3) + (m+2) はすべての p で P、かつ Blk m s (i(2m+3))。-/
theorem k9_rows (m s : Nat) (hm4 : m % 4 = 1) (hm5 : 5 ≤ m)
    (he : v2 ((3 * ((m + 1) / 2) + 1) / 2) = s) (hse : s % 2 = 0) :
    ∀ i, (∀ p, IsP m (i * (2 * m + 3)) p) ∧ (∀ p, IsP m (i * (2 * m + 3) + (m + 2)) p) ∧
      Blk m s (i * (2 * m + 3)) := by
  have hmo : m % 2 = 1 := by omega
  have hh2 : 2 ≤ (m + 1) / 2 := by omega
  have hvh : v2 ((m + 1) / 2) = 0 := v2_odd _ (by omega)
  have he1 : (3 * ((m + 1) / 2) + 1) / 2 ≤ m := by omega
  have step : ∀ a, (∀ p, IsP m a p) → Blk m s a →
      (∀ p, IsP m (a + (m + 2)) p) ∧ (∀ p, IsP m (a + (2 * m + 3)) p) ∧ Blk m s (a + (2 * m + 3)) := by
    intro a hrow hblk
    have hah : IsP m (a + (m + 1) / 2) ((m + 1) / 2) := (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
    have hb := row_long m a hmo hh2 hrow hah
    have hO := blkO_of_blk m s a hm4 he hblk
    -- (b + h, h) は N：手 e* で (a + e*, e*) に移れる（v2 e* = s は偶数）
    have hbh : ¬ IsP m (a + (m + 2) + (m + 1) / 2) ((m + 1) / 2) := by
      intro hP
      rw [isP_iff] at hP
      apply hP ((3 * ((m + 1) / 2) + 1) / 2) (by omega) he1 (by omega) (by omega)
      rw [show a + (m + 2) + (m + 1) / 2 - (3 * ((m + 1) / 2) + 1) / 2 = a + (3 * ((m + 1) / 2) + 1) / 2 by omega]
      exact (hblk _ (by omega) he1 (by omega)).mpr (by omega)
    have hnext := row_next m (a + (m + 2)) hb hbh
    have hnext' : ∀ p, IsP m (a + (2 * m + 3)) p := by
      intro p; rw [show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega]; exact hnext p
    exact ⟨hb, hnext', blkE_step m s _ hmo hnext' (Or.inr ⟨a + (m + 2), by omega, hb, hO⟩)⟩
  intro i
  induction i with
  | zero =>
    have hrow : ∀ p, IsP m (0 * (2 * m + 3)) p := by intro p; rw [Nat.zero_mul]; exact isP_zero m p
    have hblk := blkE_step m s _ hmo hrow (Or.inl (Nat.zero_mul _))
    exact ⟨hrow, (step _ hrow hblk).1, hblk⟩
  | succ i ih =>
    obtain ⟨hrow, _, hblk⟩ := ih
    obtain ⟨_, hnext, hblk'⟩ := step _ hrow hblk
    rw [Nat.succ_mul]
    exact ⟨hnext, (step _ hnext hblk').1, hblk'⟩

/-- 定理 K9（⇐）：v2(m+1) = 1、m ≥ 5、v2(3h+1) が奇数なら、(n, 0) が P ⇔ n mod (2m+3) が 0 または m+2。-/
theorem K9_suff (m : Nat) (hm4 : m % 4 = 1) (hm5 : 5 ≤ m) (hodd : v2 (3 * ((m + 1) / 2) + 1) % 2 = 1) (n : Nat) :
    IsP m n 0 ↔ (n % (2 * m + 3) = 0 ∨ n % (2 * m + 3) = m + 2) := by
  have hv3 : v2 (3 * ((m + 1) / 2) + 1) = v2 ((3 * ((m + 1) / 2) + 1) / 2) + 1 :=
    v2_even _ (by omega) (by omega)
  obtain ⟨hrow, hrowb, hblk⟩ := k9_rows m _ hm4 hm5 rfl (by omega) (n / (2 * m + 3))
  have hdiv : n = (n / (2 * m + 3)) * (2 * m + 3) + n % (2 * m + 3) := by
    have := Nat.div_add_mod n (2 * m + 3)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (2 * m + 3) < 2 * m + 3 := Nat.mod_lt n (by omega)
  have hvh : v2 ((m + 1) / 2) = 0 := v2_odd _ (by omega)
  generalize hc : n % (2 * m + 3) = c at hdiv hlt
  generalize ha : n / (2 * m + 3) * (2 * m + 3) = a at hdiv hrow hrowb hblk
  subst hdiv
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases h1 : c ≤ m
    · exact not_isP_of_row m a c 0 hrow (by omega) h1 (by omega) hP
    · by_cases h2 : c = m + 1
      · subst h2
        rw [isP_iff] at hP
        apply hP ((m + 1) / 2) (by omega) (by omega) (by omega) (by omega)
        rw [show a + (m + 1) - (m + 1) / 2 = a + (m + 1) / 2 by omega]
        exact (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
      · rw [show a + c = a + (m + 2) + (c - (m + 2)) by omega] at hP
        exact not_isP_of_row m (a + (m + 2)) (c - (m + 2)) 0 hrowb (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h]; exact hrowb 0

end Rubidium

namespace Rubidium

/-- 定理 K9（⇒ の対偶）：v2(m+1) = 1、m ≥ 5、v2(3h+1) が偶数なら、(2m+3, 0) は N 局面。
    b = m+2 とおくと、行 b はすべての p で P（`row_long`、a = 0）。(b + h, h) は P：
    手 k < h の行き先 (b + (h−k), k) は h が奇数なので N。手 h+1 の行き先 (m+1, h+1) は手 h で (h, h)（K3 より P）に移れるので N。
    手 k ≥ h+2 の行き先 (m+2+h−k, k) は K3 の範囲で、P になるのは k = (3h+1)/2 かつ v2(k) が偶数のときだけだが、v2((3h+1)/2) は奇数。
    よって (2m+3, 0) から手 h で (b + h, h) に移れる。-/
theorem K9_nec (m : Nat) (hm4 : m % 4 = 1) (hm5 : 5 ≤ m) (heven : v2 (3 * ((m + 1) / 2) + 1) % 2 = 0) :
    ¬ IsP m (2 * m + 3) 0 := by
  have hmo : m % 2 = 1 := by omega
  have hh2 : 2 ≤ (m + 1) / 2 := by omega
  have hhh : IsP m ((m + 1) / 2) ((m + 1) / 2) :=
    (K3 m _ _ (by omega) (by omega)).mpr ⟨rfl, ev2_odd _ (by omega)⟩
  have hrow0 : ∀ p, IsP m 0 p := isP_zero m
  have hb : ∀ p, IsP m (0 + (m + 2)) p := row_long m 0 hmo hh2 hrow0 (by rw [Nat.zero_add]; exact hhh)
  have hv3 : v2 (3 * ((m + 1) / 2) + 1) = v2 ((3 * ((m + 1) / 2) + 1) / 2) + 1 :=
    v2_even _ (by omega) (by omega)
  -- (b + h, h) は P
  have hbh : IsP m (m + 2 + (m + 1) / 2) ((m + 1) / 2) := by
    rw [isP_iff]
    intro k hk1 hkm hkr hkp hPk
    by_cases hlt : k < (m + 1) / 2
    · rw [show m + 2 + (m + 1) / 2 - k = 0 + (m + 2) + ((m + 1) / 2 - k) by omega] at hPk
      exact not_isP_of_row m (0 + (m + 2)) ((m + 1) / 2 - k) k hb (by omega) (by omega) (by omega) hPk
    · by_cases hk1' : k = (m + 1) / 2 + 1
      · -- 行き先 (m+1, h+1)：手 h で (h, h) に移れる
        rw [hk1', show m + 2 + (m + 1) / 2 - ((m + 1) / 2 + 1) = m + 1 by omega, isP_iff] at hPk
        apply hPk ((m + 1) / 2) (by omega) (by omega) (by omega) (by omega)
        rw [show m + 1 - (m + 1) / 2 = (m + 1) / 2 by omega]
        exact hhh
      · rw [K3 m _ k (by omega) (by omega)] at hPk
        obtain ⟨hkeq, hev⟩ := hPk
        have hke : (3 * ((m + 1) / 2) + 1) / 2 = m + 2 + (m + 1) / 2 - k := by omega
        rw [← hke, ev2_iff_v2 _ (by omega)] at hev
        omega
  intro hP
  rw [isP_iff] at hP
  apply hP ((m + 1) / 2) (by omega) (by omega) (by omega) (by omega)
  rw [show 2 * m + 3 - (m + 1) / 2 = m + 2 + (m + 1) / 2 by omega]
  exact hbh

/-- 定理 K9：v2(m+1) = 1（m % 4 = 1）、m ≥ 5 のとき、
    「すべての n で (n, 0) が P ⇔ n mod (2m+3) ∈ {0, m+2}」⇔ v2(3h+1) が奇数。-/
theorem K9 (m : Nat) (hm4 : m % 4 = 1) (hm5 : 5 ≤ m) :
    (∀ n, IsP m n 0 ↔ (n % (2 * m + 3) = 0 ∨ n % (2 * m + 3) = m + 2)) ↔
      v2 (3 * ((m + 1) / 2) + 1) % 2 = 1 := by
  constructor
  · intro hall
    apply Decidable.byContradiction
    intro hne
    apply K9_nec m hm4 hm5 (by omega)
    exact (hall (2 * m + 3)).mpr (Or.inl (Nat.mod_self _))
  · intro hodd n
    exact K9_suff m hm4 hm5 hodd n

end Rubidium
