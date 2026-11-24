/-
  Rubidium.K10c — 定理 K10c と系 K10 (b) の形式化

  「m が交互型」：すべての n で (n, 0) が P ⇔ n mod (2m+3) ∈ {0, m+2}（`Alt`）。
  定理 K10c：m + 1 = 8u（u は奇数、u ≥ 3）で交互型なら、v2(9u+1) は奇数、v2(11u+1) は偶数。
  系 K10 (b)：u ≡ 3 または 7 (mod 8) なら交互型でない。
  h = 4u、b = m+2、c = 2m+3、X₁ = (9u+1)/2、X₃ = (11u+1)/2 とする。ブロックの理論 H(j) を使わず、局面の言葉で示す。
  - 行 b はすべての p で P（`row_long`、(h, h) は K3 より P）。
  - `blk1_even`：偶数 d（d + 1 ≠ h）で、(b + d, d) が P ⇔ (b + d/2, d/2) が N。
  - `blk1_odd`：奇数 d（d + 1 ≠ h、X = (m+2+d)/2 ≤ m）で、(b + d, d) が P ⇔ ev2 X = false（K3）。
  - ev2 X₁ = false なら (b + u, u) は P、(b + 2u, 2u) は N、(b + h, h) は P、よって (2m+3, 0) は N（手 h）。交互型に反する。
  - ev2 X₃ = true なら (b + 3u, 3u) は N、(b + 6u, 6u) は P、(c + h, h) は N（手 6u）、行 c + (m+1) = 3m+4 は P。
    (3m+4, 0) は P だが 3m+4 ≡ m+1 (mod 2m+3) なので交互型に反する。
-/
import Rubidium.K12

namespace Rubidium

/-- m が交互型：すべての n で (n, 0) が P ⇔ n mod (2m+3) ∈ {0, m+2}。-/
def Alt (m : Nat) : Prop := ∀ n, IsP m n 0 ↔ (n % (2 * m + 3) = 0 ∨ n % (2 * m + 3) = m + 2)

section K10c

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2 = 1) (hu3 : 3 ≤ u)
include hmu hu hu3

theorem k10c_hh : IsP m (4 * u) (4 * u) := by
  rw [K3 m _ _ (by omega) (by omega)]
  refine ⟨rfl, ?_⟩
  rw [ev2_even (4 * u) (by omega) (by omega), show 4 * u / 2 = 2 * u by omega,
    ev2_even (2 * u) (by omega) (by omega), show 2 * u / 2 = u by omega, ev2_odd u hu]
  rfl

theorem k10c_rowb : ∀ p, IsP m (m + 2) p := by
  have h := row_long m 0 (by omega) (by omega) (isP_zero m)
    (by rw [show (m + 1) / 2 = 4 * u by omega, Nat.zero_add]; exact k10c_hh m u hmu hu hu3)
  intro p; have := h p; rwa [Nat.zero_add] at this

/-- (m + 1, p) は p ≠ h なら N（手 h で (h, h) に移れる）。-/
theorem k10c_near (p : Nat) (hp : p ≠ 4 * u) : ¬ IsP m (m + 1) p := by
  have := not_isP_near m 0 (4 * u) p (by omega) (by omega) (by omega)
    (by rw [Nat.zero_add]; exact k10c_hh m u hmu hu hu3) hp
  rwa [Nat.zero_add] at this

/-- 行 b の偶数 d（d + 1 ≠ h）：(b + d, d) が P ⇔ (b + d/2, d/2) が N。-/
theorem blk1_even (d : Nat) (hd2 : 2 ≤ d) (hdm : d ≤ m) (hde : d % 2 = 0) (hdh : d + 1 ≠ 4 * u) :
    IsP m (m + 2 + d) d ↔ ¬ IsP m (m + 2 + d / 2) (d / 2) := by
  constructor
  · intro hP hP2
    exact not_isP_move m _ d (d / 2) (by omega) (by omega) (by omega) (by omega)
      (by rw [show m + 2 + d - d / 2 = m + 2 + d / 2 by omega]; exact hP2) hP
  · intro hN
    rw [isP_iff]
    intro k hk1 hkm hkr hkd hPk
    by_cases hlt : k < d
    · rw [show m + 2 + d - k = m + 2 + (d - k) by omega] at hPk
      by_cases hk : k = d - k
      · rw [← hk, show k = d / 2 by omega] at hPk; exact hN hPk
      · exact not_isP_of_row m (m + 2) (d - k) k (k10c_rowb m u hmu hu hu3) (by omega) (by omega) hk hPk
    · by_cases hk1' : k = d + 1
      · rw [hk1', show m + 2 + d - (d + 1) = m + 1 by omega] at hPk
        exact k10c_near m u hmu hu hu3 _ hdh hPk
      · rw [K3 m _ k (by omega) (by omega)] at hPk
        obtain ⟨hkeq, _⟩ := hPk
        omega

/-- 行 b の奇数 d（d + 1 ≠ h、(m+2+d)/2 ≤ m）：(b + d, d) が P ⇔ ev2((m+2+d)/2) = false。-/
theorem blk1_odd (d : Nat) (hd1 : 1 ≤ d) (hdo : d % 2 = 1) (hdh : d + 1 ≠ 4 * u) (hX : (m + 2 + d) / 2 ≤ m) :
    IsP m (m + 2 + d) d ↔ ev2 ((m + 2 + d) / 2) = false := by
  constructor
  · intro hP
    cases hb : ev2 ((m + 2 + d) / 2) with
    | false => rfl
    | true =>
      exfalso
      apply not_isP_move m _ d ((m + 2 + d) / 2) (by omega) hX (by omega) (by omega) _ hP
      rw [show m + 2 + d - (m + 2 + d) / 2 = (m + 2 + d) / 2 by omega,
        K3 m _ _ (by omega) hX]
      exact ⟨rfl, hb⟩
  · intro hev
    rw [isP_iff]
    intro k hk1 hkm hkr hkd hPk
    by_cases hlt : k < d
    · rw [show m + 2 + d - k = m + 2 + (d - k) by omega] at hPk
      exact not_isP_of_row m (m + 2) (d - k) k (k10c_rowb m u hmu hu hu3) (by omega) (by omega) (by omega) hPk
    · by_cases hk1' : k = d + 1
      · rw [hk1', show m + 2 + d - (d + 1) = m + 1 by omega] at hPk
        exact k10c_near m u hmu hu hu3 _ hdh hPk
      · rw [K3 m _ k (by omega) (by omega)] at hPk
        obtain ⟨hkeq, hev'⟩ := hPk
        rw [show m + 2 + d - k = (m + 2 + d) / 2 by omega] at hev'
        rw [hev] at hev'
        exact Bool.false_ne_true hev'

/-- ev2 X₁ = false なら交互型でない。-/
theorem k10c_X1 (hX1 : ev2 ((9 * u + 1) / 2) = false) : ¬ Alt m := by
  intro halt
  have hbu : IsP m (m + 2 + u) u :=
    (blk1_odd m u hmu hu hu3 u (by omega) hu (by omega) (by omega)).mpr
      (by rw [show (m + 2 + u) / 2 = (9 * u + 1) / 2 by omega]; exact hX1)
  have hb2u : ¬ IsP m (m + 2 + 2 * u) (2 * u) := by
    rw [blk1_even m u hmu hu hu3 (2 * u) (by omega) (by omega) (by omega) (by omega), show 2 * u / 2 = u by omega]
    exact fun h => h hbu
  have hbh : IsP m (m + 2 + 4 * u) (4 * u) := by
    rw [blk1_even m u hmu hu hu3 (4 * u) (by omega) (by omega) (by omega) (by omega), show 4 * u / 2 = 2 * u by omega]
    exact hb2u
  have hP := (halt (2 * m + 3)).mpr (Or.inl (Nat.mod_self _))
  exact not_isP_move m _ 0 (4 * u) (by omega) (by omega) (by omega) (by omega)
    (by rw [show 2 * m + 3 - 4 * u = m + 2 + 4 * u by omega]; exact hbh) hP

/-- ev2 X₁ = true かつ ev2 X₃ = true なら交互型でない。-/
theorem k10c_X3 (hX1 : ev2 ((9 * u + 1) / 2) = true) (hX3 : ev2 ((11 * u + 1) / 2) = true) : ¬ Alt m := by
  intro halt
  have hrowb := k10c_rowb m u hmu hu hu3
  -- (b + h, h) は N
  have hbu : ¬ IsP m (m + 2 + u) u := by
    rw [blk1_odd m u hmu hu hu3 u (by omega) hu (by omega) (by omega), show (m + 2 + u) / 2 = (9 * u + 1) / 2 by omega, hX1]
    decide
  have hb2u : IsP m (m + 2 + 2 * u) (2 * u) := by
    rw [blk1_even m u hmu hu hu3 (2 * u) (by omega) (by omega) (by omega) (by omega), show 2 * u / 2 = u by omega]
    exact hbu
  have hbh : ¬ IsP m (m + 2 + (m + 1) / 2) ((m + 1) / 2) := by
    rw [show (m + 1) / 2 = 4 * u by omega,
      blk1_even m u hmu hu hu3 (4 * u) (by omega) (by omega) (by omega) (by omega), show 4 * u / 2 = 2 * u by omega]
    exact fun h => h hb2u
  -- 行 c = 2m+3
  have hc0 := row_next m (m + 2) hrowb hbh
  have hc : ∀ p, IsP m (2 * m + 3) p := by
    intro p; rw [show 2 * m + 3 = m + 2 + (m + 1) by omega]; exact hc0 p
  -- (b + 3u, 3u) は N、(b + 6u, 6u) は P
  have hb3u : ¬ IsP m (m + 2 + 3 * u) (3 * u) := by
    rw [blk1_odd m u hmu hu hu3 (3 * u) (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + 3 * u) / 2 = (11 * u + 1) / 2 by omega, hX3]
    decide
  have hb6u : IsP m (m + 2 + 6 * u) (6 * u) := by
    rw [blk1_even m u hmu hu hu3 (6 * u) (by omega) (by omega) (by omega) (by omega), show 6 * u / 2 = 3 * u by omega]
    exact hb3u
  -- (c + h, h) は N：手 6u で (b + 6u, 6u) に移れる
  have hch : ¬ IsP m (2 * m + 3 + (m + 1) / 2) ((m + 1) / 2) :=
    not_isP_move m _ _ (6 * u) (by omega) (by omega) (by omega) (by omega)
      (by rw [show 2 * m + 3 + (m + 1) / 2 - 6 * u = m + 2 + 6 * u by omega]; exact hb6u)
  have hd0 := row_next m (2 * m + 3) hc hch
  have hP : IsP m (3 * m + 4) 0 := by rw [show 3 * m + 4 = 2 * m + 3 + (m + 1) by omega]; exact hd0 0
  have := (halt (3 * m + 4)).mp hP
  have hmod : (3 * m + 4) % (2 * m + 3) = m + 1 := by
    rw [show 3 * m + 4 = (m + 1) + (2 * m + 3) by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  omega

end K10c

/-- v2 x = 1 ⇔ x % 4 = 2（x ≥ 1）の ⇐ 側。-/
theorem v2_of_mod4 (x : Nat) (h : x % 4 = 2) : v2 x = 1 := by
  rw [v2_even x (by omega) (by omega), v2_odd (x / 2) (by omega)]

/-- 定理 K10c：m + 1 = 8u（u 奇数、u ≥ 3）で交互型なら、v2(9u+1) は奇数、v2(11u+1) は偶数。-/
theorem K10c (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2 = 1) (hu3 : 3 ≤ u) (halt : Alt m) :
    v2 (9 * u + 1) % 2 = 1 ∧ v2 (11 * u + 1) % 2 = 0 := by
  have h9 : v2 (9 * u + 1) = v2 ((9 * u + 1) / 2) + 1 := v2_even _ (by omega) (by omega)
  have h11 : v2 (11 * u + 1) = v2 ((11 * u + 1) / 2) + 1 := v2_even _ (by omega) (by omega)
  have e1 := ev2_iff_v2 ((9 * u + 1) / 2) (by omega)
  have e3 := ev2_iff_v2 ((11 * u + 1) / 2) (by omega)
  cases hb1 : ev2 ((9 * u + 1) / 2) with
  | false => exact absurd halt (k10c_X1 m u hmu hu hu3 hb1)
  | true =>
    cases hb3 : ev2 ((11 * u + 1) / 2) with
    | true => exact absurd halt (k10c_X3 m u hmu hu hu3 hb1 hb3)
    | false =>
      rw [hb1] at e1; rw [hb3] at e3
      have := e1.mp rfl
      simp at e3
      omega

/-- 系 K10 (b)：m + 1 = 8u、u ≡ 3 または 7 (mod 8) なら交互型でない。-/
theorem K10b (m u : Nat) (hmu : m + 1 = 8 * u) (hu8 : u % 8 = 3 ∨ u % 8 = 7) : ¬ Alt m := by
  intro halt
  have hK := K10c m u hmu (by omega) (by omega) halt
  rcases hu8 with h | h
  · -- 9u + 1 ≡ 4 (mod 8)：v2 = 2 は偶数
    have : v2 (9 * u + 1) = 2 := by
      rw [v2_even _ (by omega) (by omega), v2_of_mod4 ((9 * u + 1) / 2) (by omega)]
    omega
  · -- 11u + 1 ≡ 6 (mod 8)：v2 = 1 は奇数
    have : v2 (11 * u + 1) = 1 := v2_of_mod4 _ (by omega)
    omega

end Rubidium
