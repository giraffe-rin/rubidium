/-
  Rubidium.K12 — 定理 K12 (a) の形式化

  定理 K12 (a)：m ≥ 5、v2(m+1) = 1（h = (m+1)/2 は奇数）、v2(3h+1) = 2、Q = (11h+5)/8 が奇数なら「110 型」：
    (n, 0) が P ⇔ n mod (3m+5) ∈ {0, m+2, 2m+4}。
  w = (3h+1)/4（奇数）、e* = (3h+1)/2 = 2w、m + 2 + w = 2Q。L = 3m+5、a = iL、b = a + (m+2)、c = b + (m+2) とする。
  ブロックの理論 H(j) を使わず、局面の言葉で示す。
  - 行 a：奇数 d の (a + d, d) は P（`odd_of_rows`）。
  - 行 b（`row_long`）：(b + w, w) は N（手 Q で (a + Q, Q) に移れる）、(b + e*, e*) は P（`p_two`）、
    (b + h, h) は P（手 e* の行き先 (a + e*, e*) は手 w で P に移れるので N）。
  - 行 c（`row_long` をもう一度）：(c + h, h) は N（手 e* で (b + e*, e*) に移れる）。行 c + (m+1) は `row_next`。
  omega の負担を減らすため、h、w、Q を変数にして、m + 1 = 2h、3h + 1 = 4w、11h + 5 = 8Q の 1 次の関係で扱う。
-/
import Rubidium.K13

namespace Rubidium

set_option maxHeartbeats 2000000

section K12

variable (m h w Q : Nat) (hmh : m + 1 = 2 * h) (hh3 : 3 ≤ h) (hw : 3 * h + 1 = 4 * w) (hwo : w % 2 = 1)
  (hq : 11 * h + 5 = 8 * Q) (hqo : Q % 2 = 1)
include hmh hh3 hw hwo hq hqo

/-- K12 の 1 周期分。行 a がすべての p で P、奇数 d の (a + d, d) が P なら、行 b・行 c・行 a + (3m+5) はすべての p で P、
    (a + h, h)・(b + h, h) は P、行 a + (3m+5) の奇数 d は P。-/
theorem k12_step (a : Nat) (hrow : ∀ p, IsP m a p) (hodd : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d) :
    (∀ p, IsP m (a + (m + 2)) p) ∧ (∀ p, IsP m (a + (2 * m + 4)) p) ∧ (∀ p, IsP m (a + (3 * m + 5)) p) ∧
    IsP m (a + h) h ∧ IsP m (a + (m + 2) + h) h ∧
    (∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + (3 * m + 5) + d) d) := by
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = h := by omega
  have hho : h % 2 = 1 := by omega
  have hah : IsP m (a + h) h := hodd h (by omega) (by omega) hho
  have hb := row_long m a hmo (by omega) hrow (by rw [hh]; exact hah)
  -- (a + 2w, 2w) は N：手 w で (a + w, w)（w は奇数）に移れる
  have hae : ¬ IsP m (a + 2 * w) (2 * w) :=
    not_isP_move m _ _ w (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + 2 * w - w = a + w by omega]; exact hodd w (by omega) (by omega) hwo)
  -- (b + w, w) は N：手 Q で (a + Q, Q)（Q は奇数）に移れる
  have hbw : ¬ IsP m (a + (m + 2) + w) w :=
    not_isP_move m _ _ Q (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (m + 2) + w - Q = a + Q by omega]; exact hodd Q (by omega) (by omega) hqo)
  -- (b + 2w, 2w) は P
  have hbe := p_two m a w hmo (by omega) (by omega) (by omega) (by omega) hrow hb (by rw [hh]; exact hah) hbw
  -- (b + h, h) は P
  have hbh : IsP m (a + (m + 2) + h) h := by
    rw [isP_iff]
    intro k hk1 hkm hkr hkp hPk
    by_cases hlt : k < h
    · rw [show a + (m + 2) + h - k = a + (m + 2) + (h - k) by omega] at hPk
      exact not_isP_of_row m _ (h - k) k hb (by omega) (by omega) (by omega) hPk
    · by_cases hk1' : k = h + 1
      · rw [hk1', show a + (m + 2) + h - (h + 1) = a + (m + 1) by omega] at hPk
        exact not_isP_near m a h _ (by omega) (by omega) (by omega) hah (by omega) hPk
      · rw [show a + (m + 2) + h - k = a + (m + 2 + h - k) by omega] at hPk
        by_cases hk : k = m + 2 + h - k
        · -- k = e* = 2w
          rw [← hk, show k = 2 * w by omega] at hPk
          exact hae hPk
        · exact not_isP_of_row m a (m + 2 + h - k) k hrow (by omega) (by omega) hk hPk
  -- 行 c = b + (m+2)
  have hc0 := row_long m (a + (m + 2)) hmo (by omega) hb (by rw [hh]; exact hbh)
  have hc : ∀ p, IsP m (a + (2 * m + 4)) p := by
    intro p; rw [show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hc0 p
  -- (c + h, h) は N：手 2w で (b + 2w, 2w) に移れる
  have hch : ¬ IsP m (a + (2 * m + 4) + h) h :=
    not_isP_move m _ _ (2 * w) (by omega) (by omega) (by omega) (by omega)
      (by rw [show a + (2 * m + 4) + h - 2 * w = a + (m + 2) + 2 * w by omega]; exact hbe)
  -- 行 a' = c + (m+1)
  have ha0 := row_next m (a + (2 * m + 4)) hc (by rw [hh]; exact hch)
  have ha' : ∀ p, IsP m (a + (3 * m + 5)) p := by
    intro p; rw [show a + (3 * m + 5) = a + (2 * m + 4) + (m + 1) by omega]; exact ha0 p
  have haodd := odd_of_rows m (a + (3 * m + 5)) hmo ha' (Or.inr ⟨a + (2 * m + 4), by omega, hc⟩)
  exact ⟨hb, hc, ha', hah, hbh, haodd⟩

/-- K12 の不変量：すべての i で、行 iL・iL + (m+2)・iL + (2m+4) はすべての p で P、(iL + h, h)・(iL + (m+2) + h, h) は P。-/
theorem k12_rows :
    ∀ i, (∀ p, IsP m (i * (3 * m + 5)) p) ∧ (∀ p, IsP m (i * (3 * m + 5) + (m + 2)) p) ∧
      (∀ p, IsP m (i * (3 * m + 5) + (2 * m + 4)) p) ∧
      IsP m (i * (3 * m + 5) + h) h ∧ IsP m (i * (3 * m + 5) + (m + 2) + h) h ∧
      (∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (i * (3 * m + 5) + d) d) := by
  have hmo : m % 2 = 1 := by omega
  intro i
  induction i with
  | zero =>
    have hrow : ∀ p, IsP m (0 * (3 * m + 5)) p := by intro p; rw [Nat.zero_mul]; exact isP_zero m p
    have hodd := odd_of_rows m (0 * (3 * m + 5)) hmo hrow (Or.inl (Nat.zero_mul _))
    obtain ⟨hb, hc, _, hah, hbh, _⟩ := k12_step m h w Q hmh hh3 hw hwo hq hqo _ hrow hodd
    exact ⟨hrow, hb, hc, hah, hbh, hodd⟩
  | succ i ih =>
    obtain ⟨hrow, _, _, _, _, hodd⟩ := ih
    obtain ⟨_, _, ha', _, _, haodd⟩ := k12_step m h w Q hmh hh3 hw hwo hq hqo _ hrow hodd
    obtain ⟨hb', hc', _, hah', hbh', _⟩ := k12_step m h w Q hmh hh3 hw hwo hq hqo _ ha' haodd
    rw [Nat.succ_mul]
    exact ⟨ha', hb', hc', hah', hbh', haodd⟩

end K12

/-- v2 x = 2 なら x % 8 = 4。-/
theorem mod8_of_v2_two (x : Nat) (hx : 1 ≤ x) (h : v2 x = 2) : x % 8 = 4 := by
  have he : x % 2 = 0 := even_of_v2_pos x (by omega)
  have h2 := v2_even x (by omega) he
  have := mod4_of_v2_one (x / 2) (by omega) (by omega)
  omega

/-- 定理 K12 (a)：m % 4 = 1、m ≥ 5、v2(3h+1) = 2、Q = (11h+5)/8 が奇数なら、(n, 0) が P ⇔ n mod (3m+5) ∈ {0, m+2, 2m+4}。-/
theorem K12a (m : Nat) (hm4 : m % 4 = 1) (hm5 : 5 ≤ m) (hv : v2 (3 * ((m + 1) / 2) + 1) = 2)
    (hQ : (11 * ((m + 1) / 2) + 5) / 8 % 2 = 1) (n : Nat) :
    IsP m n 0 ↔ (n % (3 * m + 5) = 0 ∨ n % (3 * m + 5) = m + 2 ∨ n % (3 * m + 5) = 2 * m + 4) := by
  have h8 := mod8_of_v2_two _ (by omega) hv
  obtain ⟨h, hh⟩ : ∃ h, (m + 1) / 2 = h := ⟨_, rfl⟩
  rw [hh] at h8 hQ
  have hmh : m + 1 = 2 * h := by omega
  obtain ⟨hrow, hrowb, hrowc, hah, hbh, _⟩ :=
    k12_rows m h ((3 * h + 1) / 4) ((11 * h + 5) / 8) hmh (by omega) (by omega) (by omega) (by omega) hQ
      (n / (3 * m + 5))
  have hdiv : n = (n / (3 * m + 5)) * (3 * m + 5) + n % (3 * m + 5) := by
    have := Nat.div_add_mod n (3 * m + 5)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (3 * m + 5) < 3 * m + 5 := Nat.mod_lt n (by omega)
  generalize hcc : n % (3 * m + 5) = c at hdiv hlt
  generalize ha : n / (3 * m + 5) * (3 * m + 5) = a at hdiv hrow hrowb hrowc hah hbh
  subst hdiv
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases h1 : c ≤ m
    · exact not_isP_of_row m a c 0 hrow (by omega) h1 (by omega) hP
    · by_cases h2 : c = m + 1
      · subst h2
        exact not_isP_near m a h 0 hmh (by omega) (by omega) hah (by omega) hP
      · by_cases h3 : c ≤ 2 * m + 2
        · rw [show a + c = a + (m + 2) + (c - (m + 2)) by omega] at hP
          exact not_isP_of_row m (a + (m + 2)) (c - (m + 2)) 0 hrowb (by omega) (by omega) (by omega) hP
        · by_cases h4 : c = 2 * m + 3
          · rw [h4, show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega] at hP
            exact not_isP_near m (a + (m + 2)) h 0 hmh (by omega) (by omega) hbh (by omega) hP
          · rw [show a + c = a + (2 * m + 4) + (c - (2 * m + 4)) by omega] at hP
            exact not_isP_of_row m (a + (2 * m + 4)) (c - (2 * m + 4)) 0 hrowc (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h]; exact hrowb 0
    · rw [h]; exact hrowc 0

end Rubidium
