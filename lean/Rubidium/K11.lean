/-
  Rubidium.K11 — 定理 K11 の形式化

  定理 K11：m + 1 = 2^v·u（v ≥ 5 は奇数、u は奇数）なら、m は交互型でない（¬ Alt m）。
  h = (m+1)/2 は偶数で v2(h) = v − 1 は偶数。b = m+2、c = 2m+3 とする。ブロックの理論 H(j) を使わず、局面の言葉で示す。
  - 行 b の補題（PR #406 の blk1_even・blk1_odd を、h が偶数で ev2 h = true の一般の場合に広げたもの）：
    `g_even`：偶数 d で (b + d, d) が P ⇔ (b + d/2, d/2) が N。`g_odd`：奇数 d で (b + d, d) が P ⇔ ev2((m+2+d)/2) = false。
  - `g_iter`：(b + 2^i·x, 2^i·x) が P ⇔ ((b + x, x) が P ⇔ i が偶数)。
  - `g_blk2_even`：行 c の偶数 d で、(c + d/2, d/2) と (b + h + d/2, h + d/2) が N なら、(c + d, d) は P。
  v = 2s + 5、T = 4^s、w = T·u とおくと h = 16w、m + 1 = 32w。X₁ = (m+2+u)/2。
  - ev2 X₁ = false：(b + u, u) は P、よって (b + h, h) は P（`g_iter`、i = 2s+4）。(2m+3, 0) は N。
  - ev2 X₁ = true、u ≡ 3 (mod 4)：X₃ は奇数なので (b + 3u, 3u) は N、(b + 24w, 24w) は P（i = 2s+3）。
    (c + h, h) は手 24w で (b + 24w, 24w) に移れるので N。行 3m+4 は P。
  - ev2 X₁ = true、u ≡ 1 (mod 4)：X₅、X₉ は奇数なので (b + 5u)・(b + 9u) は N、(b + 20w) は N（i = 2s+2）、(b + 18w) は P（i = 2s+1）。
    (c + 4w) は N（手 18w）、(c + 8w) は P（`g_blk2_even`）、(c + h) は N（手 8w）。行 3m+4 は P。
-/
import Rubidium.K10c

namespace Rubidium

set_option linter.unusedSectionVars false

section General

variable (m h : Nat) (hmh : m + 1 = 2 * h) (hhe : h % 2 = 0) (hh2 : 2 ≤ h) (hev : ev2 h = true)
include hmh hhe hh2 hev

theorem g_hh : IsP m h h := (K3 m _ _ (by omega) (by omega)).mpr ⟨rfl, hev⟩

theorem g_rowb : ∀ p, IsP m (m + 2) p := by
  have hh : (m + 1) / 2 = h := by omega
  have r := row_long m 0 (by omega) (by omega) (isP_zero m)
    (by rw [hh, Nat.zero_add]; exact g_hh m h hmh hhe hh2 hev)
  intro p; have := r p; rwa [Nat.zero_add] at this

theorem g_near (p : Nat) (hp : p ≠ h) : ¬ IsP m (m + 1) p := by
  have := not_isP_near m 0 h p hmh (by omega) (by omega)
    (by rw [Nat.zero_add]; exact g_hh m h hmh hhe hh2 hev) hp
  rwa [Nat.zero_add] at this

theorem g_even (d : Nat) (hd2 : 2 ≤ d) (hdm : d ≤ m) (hde : d % 2 = 0) :
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
      · exact not_isP_of_row m (m + 2) (d - k) k (g_rowb m h hmh hhe hh2 hev) (by omega) (by omega) hk hPk
    · by_cases hk1' : k = d + 1
      · rw [hk1', show m + 2 + d - (d + 1) = m + 1 by omega] at hPk
        exact g_near m h hmh hhe hh2 hev _ (by omega) hPk
      · rw [K3 m _ k (by omega) (by omega)] at hPk
        obtain ⟨hkeq, _⟩ := hPk
        omega

theorem g_odd (d : Nat) (hd1 : 1 ≤ d) (hdo : d % 2 = 1) (hdh : d + 1 ≠ h) (hX : (m + 2 + d) / 2 ≤ m) :
    IsP m (m + 2 + d) d ↔ ev2 ((m + 2 + d) / 2) = false := by
  constructor
  · intro hP
    cases hb : ev2 ((m + 2 + d) / 2) with
    | false => rfl
    | true =>
      exfalso
      apply not_isP_move m _ d ((m + 2 + d) / 2) (by omega) hX (by omega) (by omega) _ hP
      rw [show m + 2 + d - (m + 2 + d) / 2 = (m + 2 + d) / 2 by omega, K3 m _ _ (by omega) hX]
      exact ⟨rfl, hb⟩
  · intro hev'
    rw [isP_iff]
    intro k hk1 hkm hkr hkd hPk
    by_cases hlt : k < d
    · rw [show m + 2 + d - k = m + 2 + (d - k) by omega] at hPk
      exact not_isP_of_row m (m + 2) (d - k) k (g_rowb m h hmh hhe hh2 hev) (by omega) (by omega) (by omega) hPk
    · by_cases hk1' : k = d + 1
      · rw [hk1', show m + 2 + d - (d + 1) = m + 1 by omega] at hPk
        exact g_near m h hmh hhe hh2 hev _ hdh hPk
      · rw [K3 m _ k (by omega) (by omega)] at hPk
        obtain ⟨hkeq, hev2⟩ := hPk
        rw [show m + 2 + d - k = (m + 2 + d) / 2 by omega, hev'] at hev2
        exact Bool.false_ne_true hev2

/-- 偶数の規則のくり返し：(b + 2^i·x, 2^i·x) が P ⇔ ((b + x, x) が P ⇔ i が偶数)。-/
theorem g_iter (x : Nat) (hx : 1 ≤ x) : ∀ i, 2 ^ i * x ≤ m →
    (IsP m (m + 2 + 2 ^ i * x) (2 ^ i * x) ↔ (IsP m (m + 2 + x) x ↔ i % 2 = 0)) := by
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
    have ih' := ih (by omega)
    rw [g_even m h hmh hhe hh2 hev (2 * (2 ^ i * x)) (by omega) hle (by omega),
      show 2 * (2 ^ i * x) / 2 = 2 ^ i * x by omega, ih']
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

/-- 行 c = 2m+3（すべての p で P、奇数 d は P）の偶数 d：(c + d/2, d/2) と (b + h + d/2, h + d/2) が N なら (c + d, d) は P。-/
theorem g_blk2_even (hrowc : ∀ p, IsP m (2 * m + 3) p) (d : Nat) (hd2 : 2 ≤ d) (hdm : d ≤ m) (hde : d % 2 = 0)
    (hN1 : ¬ IsP m (2 * m + 3 + d / 2) (d / 2)) (hN2 : ¬ IsP m (m + 2 + (h + d / 2)) (h + d / 2)) :
    IsP m (2 * m + 3 + d) d := by
  rw [isP_iff]
  intro k hk1 hkm hkr hkd hPk
  by_cases hlt : k < d
  · rw [show 2 * m + 3 + d - k = 2 * m + 3 + (d - k) by omega] at hPk
    by_cases hk : k = d - k
    · rw [← hk, show k = d / 2 by omega] at hPk; exact hN1 hPk
    · exact not_isP_of_row m _ (d - k) k hrowc (by omega) (by omega) hk hPk
  · rw [show 2 * m + 3 + d - k = m + 2 + (m + 1 + d - k) by omega] at hPk
    by_cases hk : k = m + 1 + d - k
    · rw [← hk, show k = h + d / 2 by omega] at hPk; exact hN2 hPk
    · exact not_isP_of_row m (m + 2) (m + 1 + d - k) k (g_rowb m h hmh hhe hh2 hev) (by omega) (by omega) hk hPk

/-- (b + h, h) が P なら交互型でない。-/
theorem g_notalt_b (hbh : IsP m (m + 2 + h) h) : ¬ Alt m := by
  intro halt
  have hP := (halt (2 * m + 3)).mpr (Or.inl (Nat.mod_self _))
  exact not_isP_move m _ 0 h (by omega) (by omega) (by omega) (by omega)
    (by rw [show 2 * m + 3 - h = m + 2 + h by omega]; exact hbh) hP

/-- 行 c = 2m+3 がすべての p で P で (c + h, h) が N なら交互型でない（行 3m+4 が P になる）。-/
theorem g_notalt_c (hrowc : ∀ p, IsP m (2 * m + 3) p) (hch : ¬ IsP m (2 * m + 3 + h) h) : ¬ Alt m := by
  intro halt
  have hh : (m + 1) / 2 = h := by omega
  have hd0 := row_next m (2 * m + 3) hrowc (by rw [hh]; exact hch)
  have hP : IsP m (3 * m + 4) 0 := by rw [show 3 * m + 4 = 2 * m + 3 + (m + 1) by omega]; exact hd0 0
  have := (halt (3 * m + 4)).mp hP
  have hmod : (3 * m + 4) % (2 * m + 3) = m + 1 := by
    rw [show 3 * m + 4 = (m + 1) + (2 * m + 3) by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  omega

end General

theorem ev2_four (x : Nat) (hx : 1 ≤ x) : ev2 (4 * x) = ev2 x := by
  rw [ev2_even (4 * x) (by omega) (by omega), show 4 * x / 2 = 2 * x by omega,
    ev2_even (2 * x) (by omega) (by omega), show 2 * x / 2 = x by omega, Bool.not_not]

theorem ev2_pow4 (u : Nat) (hu : 1 ≤ u) : ∀ s, ev2 (4 ^ s * u) = ev2 u := by
  intro s
  induction s with
  | zero => rw [Nat.pow_zero, Nat.one_mul]
  | succ s ih =>
    have hpos : 1 ≤ 4 ^ s * u := Nat.mul_pos (Nat.pow_pos (by omega)) hu
    rw [Nat.pow_succ, Nat.mul_comm (4 ^ s) 4, Nat.mul_assoc, ev2_four _ hpos, ih]

/-- 定理 K11：m + 1 = 2^v·u（v ≥ 5 奇数、u 奇数）なら交互型でない。-/
theorem K11 (m v u : Nat) (hmv : m + 1 = 2 ^ v * u) (hvo : v % 2 = 1) (hv5 : 5 ≤ v) (hu : u % 2 = 1) :
    ¬ Alt m := by
  -- v = 2s + 5、T = 4^s、w = T·u
  obtain ⟨s, hs⟩ : ∃ s, v = 2 * s + 5 := ⟨(v - 5) / 2, by omega⟩
  have hpw : ∀ j, 2 ^ (2 * s + j) = 4 ^ s * 2 ^ j := by
    intro j; rw [Nat.pow_add, Nat.pow_mul]
  have hT : 1 ≤ 4 ^ s := Nat.pow_pos (by omega)
  obtain ⟨w, hw⟩ : ∃ w, 4 ^ s * u = w := ⟨_, rfl⟩
  have hwu : u ≤ w := by rw [← hw]; exact Nat.le_mul_of_pos_left u hT
  have hu1 : 1 ≤ u := by omega
  -- 2^(2s+j)·(c·u) = (2^j·c)·w
  have hd : ∀ j c, 2 ^ (2 * s + j) * (c * u) = (2 ^ j * c) * w := by
    intro j c
    rw [hpw j, Nat.mul_assoc, ← Nat.mul_assoc (2 ^ j) c u, Nat.mul_left_comm (4 ^ s) (2 ^ j * c) u, hw]
  have hd1 : 2 ^ (2 * s + 4) * u = 16 * w := by
    rw [hpw 4, Nat.mul_assoc, Nat.mul_left_comm (4 ^ s) (2 ^ 4) u, hw]
  have hm : m + 1 = 32 * w := by
    rw [hmv, hs, hpw 5, Nat.mul_assoc, Nat.mul_left_comm (4 ^ s) (2 ^ 5) u, hw]
  -- h = 16w
  have hev : ev2 (16 * w) = true := by
    rw [show 16 * w = 4 * (4 * w) by omega, ev2_four _ (by omega), ev2_four _ (by omega), ← hw,
      ev2_pow4 u hu1 s, ev2_odd u hu]
  have hmh : m + 1 = 2 * (16 * w) := by omega
  have G := g_iter m (16 * w) hmh (by omega) (by omega) hev
  have Gu := G u hu1 (2 * s + 4) (by rw [hd1]; omega)
  rw [hd1] at Gu
  have hpar4 : (2 * s + 4) % 2 = 0 := by omega
  have hrowb := g_rowb m (16 * w) hmh (by omega) (by omega) hev
  cases hX1 : ev2 ((m + 2 + u) / 2) with
  | false =>
    -- (b + u, u) は P、(b + h, h) は P
    have hbu := (g_odd m (16 * w) hmh (by omega) (by omega) hev u hu1 hu (by omega) (by omega)).mpr hX1
    exact g_notalt_b m (16 * w) hmh (by omega) (by omega) hev (Gu.mpr ⟨fun _ => hpar4, fun _ => hbu⟩)
  | true =>
    have hbu : ¬ IsP m (m + 2 + u) u := by
      rw [g_odd m (16 * w) hmh (by omega) (by omega) hev u hu1 hu (by omega) (by omega), hX1]; decide
    -- (b + h, h) は N なので行 c は P
    have hbh : ¬ IsP m (m + 2 + 16 * w) (16 * w) := fun hP => hbu ((Gu.mp hP).mpr hpar4)
    have hc0 := row_next m (m + 2) hrowb (by rw [show (m + 1) / 2 = 16 * w by omega]; exact hbh)
    have hrowc : ∀ p, IsP m (2 * m + 3) p := by
      intro p; rw [show 2 * m + 3 = m + 2 + (m + 1) by omega]; exact hc0 p
    by_cases hu4 : u % 4 = 3
    · -- X₃ は奇数なので (b + 3u, 3u) は N、(b + 24w, 24w) は P
      have hb3u : ¬ IsP m (m + 2 + 3 * u) (3 * u) := by
        rw [g_odd m (16 * w) hmh (by omega) (by omega) hev (3 * u) (by omega) (by omega) (by omega) (by omega),
          ev2_odd _ (by omega)]; decide
      have G3 := G (3 * u) (by omega) (2 * s + 3) (by rw [hd 3 3]; show 24 * w ≤ m; omega)
      rw [hd 3 3, show 2 ^ 3 * 3 = 24 from rfl] at G3
      have h24 := G3.mpr ⟨fun hp => absurd hp hb3u, fun hp => by omega⟩
      apply g_notalt_c m (16 * w) hmh (by omega) (by omega) hev hrowc
      exact not_isP_move m _ _ (24 * w) (by omega) (by omega) (by omega) (by omega)
        (by rw [show 2 * m + 3 + 16 * w - 24 * w = m + 2 + 24 * w by omega]; exact h24)
    · -- u ≡ 1 (mod 4)：X₅・X₉ は奇数
      have hb5u : ¬ IsP m (m + 2 + 5 * u) (5 * u) := by
        rw [g_odd m (16 * w) hmh (by omega) (by omega) hev (5 * u) (by omega) (by omega) (by omega) (by omega),
          ev2_odd _ (by omega)]; decide
      have hb9u : ¬ IsP m (m + 2 + 9 * u) (9 * u) := by
        rw [g_odd m (16 * w) hmh (by omega) (by omega) hev (9 * u) (by omega) (by omega) (by omega) (by omega),
          ev2_odd _ (by omega)]; decide
      -- (b + 20w, 20w) は N（i = 2s+2 は偶数）、(b + 18w, 18w) は P（i = 2s+1 は奇数）
      have G5 := G (5 * u) (by omega) (2 * s + 2) (by rw [hd 2 5]; show 20 * w ≤ m; omega)
      rw [hd 2 5, show 2 ^ 2 * 5 = 20 from rfl] at G5
      have h20 : ¬ IsP m (m + 2 + 20 * w) (20 * w) := fun hP => hb5u ((G5.mp hP).mpr (by omega))
      have G9 := G (9 * u) (by omega) (2 * s + 1) (by rw [hd 1 9]; show 18 * w ≤ m; omega)
      rw [hd 1 9, show 2 ^ 1 * 9 = 18 from rfl] at G9
      have h18 := G9.mpr ⟨fun hp => absurd hp hb9u, fun hp => by omega⟩
      -- (c + 4w, 4w) は N（手 18w で (b + 18w, 18w) に移れる）
      have hc4 : ¬ IsP m (2 * m + 3 + 4 * w) (4 * w) :=
        not_isP_move m _ _ (18 * w) (by omega) (by omega) (by omega) (by omega)
          (by rw [show 2 * m + 3 + 4 * w - 18 * w = m + 2 + 18 * w by omega]; exact h18)
      -- (c + 8w, 8w) は P
      have hc8 : IsP m (2 * m + 3 + 8 * w) (8 * w) :=
        g_blk2_even m (16 * w) hmh (by omega) (by omega) hev hrowc (8 * w) (by omega) (by omega) (by omega)
          (by rw [show 8 * w / 2 = 4 * w by omega]; exact hc4)
          (by rw [show 16 * w + 8 * w / 2 = 20 * w by omega]; exact h20)
      apply g_notalt_c m (16 * w) hmh (by omega) (by omega) hev hrowc
      exact not_isP_move m _ _ (8 * w) (by omega) (by omega) (by omega) (by omega)
        (by rw [show 2 * m + 3 + 16 * w - 8 * w = 2 * m + 3 + 8 * w by omega]; exact hc8)

end Rubidium

namespace Rubidium

/-- K10c の u = 1：m = 7 は交互型でない。b = 9、h = 4。
    (10, 1) は N（K3、ev2 5 = true）、(11, 2) は P、(13, 4) は N なので行 17 は P。
    (8, 4) は P（手 k ≠ 4 の行き先 (8−k, k) は K3 より N）、よって (12, 3) は N（手 4）、(15, 6) は P、(21, 4) は N（手 6）。
    よって行 25 は P で、(25, 0) は P。25 ≡ 8 (mod 17) なので交互型に反する。-/
theorem not_alt_seven : ¬ Alt 7 := by
  have hev : ev2 4 = true := by rw [show 4 = 4 * 1 from rfl, ev2_four 1 (by omega)]; exact ev2_odd 1 rfl
  have hrowb := g_rowb 7 4 rfl rfl (by omega) hev
  -- (10, 1) は N
  have h10 : ¬ IsP 7 (7 + 2 + 1) 1 := by
    rw [g_odd 7 4 rfl rfl (by omega) hev 1 (by omega) rfl (by omega) (by omega), show (7 + 2 + 1) / 2 = 5 from rfl, ev2_odd 5 rfl]
    decide
  have h11 : IsP 7 (7 + 2 + 2) 2 := (g_even 7 4 rfl rfl (by omega) hev 2 (by omega) (by omega) rfl).mpr h10
  have h13 : ¬ IsP 7 (7 + 2 + 4) 4 := by
    rw [g_even 7 4 rfl rfl (by omega) hev 4 (by omega) (by omega) rfl]; exact fun h => h h11
  have hc0 := row_next 7 (7 + 2) hrowb h13
  -- (8, 4) は P
  have h8 : IsP 7 8 4 := by
    rw [isP_iff]
    intro k hk1 hkm hkr hkp hPk
    rw [K3 7 (8 - k) k (by omega) (by omega)] at hPk
    obtain ⟨hkeq, _⟩ := hPk
    omega
  have h12 : ¬ IsP 7 (7 + 2 + 3) 3 :=
    not_isP_move 7 _ 3 4 (by omega) (by omega) (by omega) (by omega) h8
  have h15 : IsP 7 (7 + 2 + 6) 6 := (g_even 7 4 rfl rfl (by omega) hev 6 (by omega) (by omega) rfl).mpr h12
  have h21 : ¬ IsP 7 (7 + 2 + (7 + 1) + 4) 4 :=
    not_isP_move 7 _ 4 6 (by omega) (by omega) (by omega) (by omega) h15
  have hd0 := row_next 7 (7 + 2 + (7 + 1)) hc0 h21
  intro halt
  have := (halt 25).mp (hd0 0)
  revert this; decide

/-- 定理 K10c（完全な形）：m + 1 = 8u（u は奇数）で交互型なら、u ≥ 3、v2(9u+1) は奇数、v2(11u+1) は偶数。-/
theorem K10c_full (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 2 = 1) (halt : Alt m) :
    3 ≤ u ∧ v2 (9 * u + 1) % 2 = 1 ∧ v2 (11 * u + 1) % 2 = 0 := by
  have hu3 : 3 ≤ u := by
    apply Decidable.byContradiction
    intro h
    have hu1 : u = 1 := by omega
    subst hu1
    have hm : m = 7 := by omega
    subst hm
    exact not_alt_seven halt
  exact ⟨hu3, K10c m u hmu hu hu3 halt⟩

end Rubidium
