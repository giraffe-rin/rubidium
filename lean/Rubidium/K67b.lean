/-
  Rubidium.K67b — 予想 K67 の u ≡ 19 (mod 64)（11100 型）の証明

  定理：m + 1 = 8u、u ≡ 19 (mod 64) なら、(n, 0) が P ⇔ n mod (5m+8) ∈ {0, m+2, 2m+4, 3m+6, 4m+7}（11100 型）。
  h = 4u。行 a（始まり、Blk m 3）、b₁ = a + (m+2)、b₂ = b₁ + (m+2)、b₃ = b₂ + (m+2)（O）、
  c = b₃ + (m+1)（E）、a' = c + (m+1)（E、次の始まり）。
  - (b + 4u) が P ⇔ (b + u) が P ⇔ 1 つ前の行の X₁ = (9u+1)/2 が N。
    X₁ = 2·o（o = (9u+1)/4 奇数）、o の相手 Y = (41u+5)/8 = 2·y（y 奇数）、y の相手 (169u+21)/32 は奇数。
    よって (b₁ + 4u)・(b₂ + 4u) は P、(b₃ + 4u) は N。
  - (c + 4u) は N：(b₃ + 6u) が P（3u の相手 X₃ = (11u+1)/2 → (27u+3)/4 → (59u+7)/8、どれも奇数）。
  - a' で Blk m 3：K4 の blk_step と同じ形。手 4u + d/2（v2(d) = 2）の行き先 (c + 4u + d/2) は v2 が 1 なので N。
-/
import Rubidium.K67c

namespace Rubidium

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

section K67b

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % 64 = 19)
include hmu hu

/-- a' = c + (m+1)（行 c で Blk m 1）で Blk m 3。-/
theorem k67b_blk (c : Nat) (hc : ∀ p, IsP m c p) (hblkc : Blk m 1 c) (ha' : ∀ p, IsP m (c + (m + 1)) p) :
    Blk m 3 (c + (m + 1)) := by
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
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
      rw [show c + (m + 1) + d - d / 2 = c + (m + 1) + d / 2 by omega]
      exact (ih (d / 2) (by omega) (by omega) (by omega) (by omega)).mpr (by omega)
    · intro hev
      rw [isP_iff]
      intro k hk1 hkm hkr hkd hPk
      by_cases hlt : k < d
      · rw [show c + (m + 1) + d - k = c + (m + 1) + (d - k) by omega] at hPk
        by_cases hk : k = d - k
        · have hde : d % 2 = 0 := by omega
          have hd2 : d / 2 = k := by omega
          have hv : v2 d = v2 k + 1 := by rw [v2_even d (by omega) hde, hd2]
          rw [← hk] at hPk
          have := (ih k hlt hk1 (by omega) (by omega)).mp hPk
          omega
        · exact not_isP_of_row m _ (d - k) k ha' (by omega) (by omega) hk hPk
      · rw [show c + (m + 1) + d - k = c + (m + 1 + d - k) by omega] at hPk
        by_cases hk : k = m + 1 + d - k
        · have hde : d % 2 = 0 := by omega
          have hv1 : v2 d = v2 (d / 2) + 1 := v2_even d (by omega) hde
          have hkx : k = d / 2 + 4 * u := by omega
          have hvk : v2 k = 1 := by rw [hkx, v2_add (d / 2) (4 * u) (by omega) (by omega) (by omega)]; omega
          rw [← hk] at hPk
          rw [hblkc k hk1 hkm (by omega), hvk] at hPk; omega
        · exact not_isP_of_row m c (m + 1 + d - k) k hc (by omega) (by omega) hk hPk

theorem k67b_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    (∀ p, IsP m (a + (m + 2)) p) ∧ (∀ p, IsP m (a + (2 * m + 4)) p) ∧ (∀ p, IsP m (a + (3 * m + 6)) p) ∧
    (∀ p, IsP m (a + (4 * m + 7)) p) ∧ (∀ p, IsP m (a + (5 * m + 8)) p) ∧ Blk m 3 (a + (5 * m + 8)) ∧
    IsP m (a + 4 * u) (4 * u) ∧ IsP m (a + (m + 2) + 4 * u) (4 * u) ∧ IsP m (a + (2 * m + 4) + 4 * u) (4 * u) := by
  have hmh : m + 1 = 2 * (4 * u) := by omega
  have hmo : m % 2 = 1 := by omega
  have hh : (m + 1) / 2 = 4 * u := by omega
  have hv4u : v2 (4 * u) = 2 := by
    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]
  have hoddA : ∀ d, 1 ≤ d → d ≤ m → d % 2 = 1 → IsP m (a + d) d :=
    fun d hd1 hdm hdo => (hblk d hd1 hdm (by rw [v2_odd d hdo]; omega)).mpr (by rw [v2_odd d hdo])
  have hN1 : ∀ d, 1 ≤ d → d ≤ m → d % 4 = 2 → ¬ IsP m (a + d) d := fun d hd1 hdm h2 => by
    have hv : v2 d = 1 := v2_of_mod4 d h2
    rw [hblk d hd1 hdm (by omega), hv]; omega
  have hah : IsP m (a + 4 * u) (4 * u) := (hblk _ (by omega) (by omega) (by omega)).mpr (by omega)
  -- 行 b₁、b₂、b₃
  have hb1 := row_long m a hmo (by omega) hrow (by rw [hh]; exact hah)
  -- O 型の行 b = p + (m+2) で (b + 4u) が P ⇔ (p + X₁) が N
  have h4u : ∀ p, (∀ q, IsP m p q) → (∀ q, IsP m (p + (m + 2)) q) → IsP m (p + 4 * u) (4 * u) →
      (IsP m (p + (m + 2) + 4 * u) (4 * u) ↔ ¬ IsP m (p + (9 * u + 1) / 2) ((9 * u + 1) / 2)) := by
    intro p hp hpb hph
    rw [show 4 * u = 2 * (2 * u) by omega, o_half' m (4 * u) p (2 * u) hmh hp hpb hph (by omega) (by omega) (by omega),
      o_half' m (4 * u) p u hmh hp hpb hph (by omega) (by omega) (by omega),
      o_odd_iff m (4 * u) p u hmh hp hpb hph (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + u) / 2 = (9 * u + 1) / 2 by omega]
    constructor
    · intro h1 h2; exact h1 (fun h3 => h3 h2)
    · intro h1 h2; exact h2 h1
  -- O 型の行 b = p + (m+2) で (b + X₁) が P ⇔ (p + Y) が P（X₁ = 2o、o の相手 Y）
  have hX1 : ∀ p, (∀ q, IsP m p q) → (∀ q, IsP m (p + (m + 2)) q) → IsP m (p + 4 * u) (4 * u) →
      (IsP m (p + (m + 2) + (9 * u + 1) / 2) ((9 * u + 1) / 2) ↔ IsP m (p + (41 * u + 5) / 8) ((41 * u + 5) / 8)) := by
    intro p hp hpb hph
    rw [show (9 * u + 1) / 2 = 2 * ((9 * u + 1) / 4) by omega,
      o_half' m (4 * u) p _ hmh hp hpb hph (by omega) (by omega) (by omega),
      o_odd_iff m (4 * u) p _ hmh hp hpb hph (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + (9 * u + 1) / 4) / 2 = (41 * u + 5) / 8 by omega]
    exact ⟨fun h => Classical.byContradiction h, fun h1 h2 => h2 h1⟩
  -- 同じく (b + Y) が P ⇔ (p + (169u+21)/32) が P
  have hY : ∀ p, (∀ q, IsP m p q) → (∀ q, IsP m (p + (m + 2)) q) → IsP m (p + 4 * u) (4 * u) →
      (IsP m (p + (m + 2) + (41 * u + 5) / 8) ((41 * u + 5) / 8) ↔ IsP m (p + (169 * u + 21) / 32) ((169 * u + 21) / 32)) := by
    intro p hp hpb hph
    rw [show (41 * u + 5) / 8 = 2 * ((41 * u + 5) / 16) by omega,
      o_half' m (4 * u) p _ hmh hp hpb hph (by omega) (by omega) (by omega),
      o_odd_iff m (4 * u) p _ hmh hp hpb hph (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + (41 * u + 5) / 16) / 2 = (169 * u + 21) / 32 by omega]
    exact ⟨fun h => Classical.byContradiction h, fun h1 h2 => h2 h1⟩
  have hb1h : IsP m (a + (m + 2) + 4 * u) (4 * u) :=
    (h4u a hrow hb1 hah).mpr (hN1 _ (by omega) (by omega) (by omega))
  have hb2 := row_long m (a + (m + 2)) hmo (by omega) hb1 (by rw [hh]; exact hb1h)
  -- (b₁ + X₁) は N（(a + Y) は v2 = 1 で N）
  have hb1X : ¬ IsP m (a + (m + 2) + (9 * u + 1) / 2) ((9 * u + 1) / 2) := by
    rw [hX1 a hrow hb1 hah]; exact hN1 _ (by omega) (by omega) (by omega)
  have hb2h : IsP m (a + (m + 2) + (m + 2) + 4 * u) (4 * u) := (h4u _ hb1 hb2 hb1h).mpr hb1X
  have hb3 := row_long m (a + (m + 2) + (m + 2)) hmo (by omega) hb2 (by rw [hh]; exact hb2h)
  -- (b₁ + Y) は P（(a + (169u+21)/32) は奇数で P）、(b₂ + X₁) は P、(b₃ + 4u) は N
  have hb1Y : IsP m (a + (m + 2) + (41 * u + 5) / 8) ((41 * u + 5) / 8) :=
    (hY a hrow hb1 hah).mpr (hoddA _ (by omega) (by omega) (by omega))
  have hb2X : IsP m (a + (m + 2) + (m + 2) + (9 * u + 1) / 2) ((9 * u + 1) / 2) :=
    (hX1 _ hb1 hb2 hb1h).mpr hb1Y
  have hb3h : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 4 * u) (4 * u) := fun h => ((h4u _ hb2 hb3 hb2h).mp h) hb2X
  -- 行 c = b₃ + (m+1)
  have hc := row_next m (a + (m + 2) + (m + 2) + (m + 2)) hb3 (by rw [hh]; exact hb3h)
  have hoddc := odd_of_rows m _ hmo hc (Or.inr ⟨_, rfl, hb3⟩)
  have hblkc := blk1_direct m _ hc hoddc
  -- (b₃ + 6u) は P：(b₃ + 3u) の相手 X₃（奇数）→ (b₂ + X₃) は P（相手 (27u+3)/4 の (b₁ + ·) が N、その相手 (59u+7)/8 は奇数）
  have hb1Z : ¬ IsP m (a + (m + 2) + (27 * u + 3) / 4) ((27 * u + 3) / 4) := by
    rw [o_odd_iff m (4 * u) a _ hmh hrow hb1 hah (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + (27 * u + 3) / 4) / 2 = (59 * u + 7) / 8 by omega]
    exact fun h => h (hoddA _ (by omega) (by omega) (by omega))
  have hb2X3 : IsP m (a + (m + 2) + (m + 2) + (11 * u + 1) / 2) ((11 * u + 1) / 2) := by
    rw [o_odd_iff m (4 * u) (a + (m + 2)) _ hmh hb1 hb2 hb1h (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + (11 * u + 1) / 2) / 2 = (27 * u + 3) / 4 by omega]
    exact hb1Z
  have hb33 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + 3 * u) (3 * u) := by
    rw [o_odd_iff m (4 * u) (a + (m + 2) + (m + 2)) (3 * u) hmh hb2 hb3 hb2h (by omega) (by omega) (by omega) (by omega),
      show (m + 2 + 3 * u) / 2 = (11 * u + 1) / 2 by omega]
    exact fun h => h hb2X3
  have hb36 : IsP m (a + (m + 2) + (m + 2) + (m + 2) + 6 * u) (6 * u) := by
    rw [show 6 * u = 2 * (3 * u) by omega,
      o_half' m (4 * u) (a + (m + 2) + (m + 2)) (3 * u) hmh hb2 hb3 hb2h (by omega) (by omega) (by omega)]
    exact hb33
  have hc4 : ¬ IsP m (a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + 4 * u) (4 * u) := by
    rw [e_iff m (4 * u) _ (4 * u) hmh hb3 hc (by omega) (by omega) (by omega),
      show 4 * u / 2 = 2 * u by omega, show 4 * u + 2 * u = 6 * u by omega]
    exact fun ⟨_, h⟩ => h hb36
  have ha' := row_next m _ hc (by rw [hh]; exact hc4)
  have hblk' := k67b_blk m u hmu hu _ hc hblkc ha'
  have e5 : a + (5 * m + 8) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) + (m + 1) := by omega
  refine ⟨hb1, ?_, ?_, ?_, ?_, ?_, hah, hb1h, ?_⟩
  · intro p; rw [show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hb2 p
  · intro p; rw [show a + (3 * m + 6) = a + (m + 2) + (m + 2) + (m + 2) by omega]; exact hb3 p
  · intro p; rw [show a + (4 * m + 7) = a + (m + 2) + (m + 2) + (m + 2) + (m + 1) by omega]; exact hc p
  · intro p; rw [e5]; exact ha' p
  · rw [e5]; exact hblk'
  · rw [show a + (2 * m + 4) = a + (m + 2) + (m + 2) by omega]; exact hb2h

theorem k67b_rows : ∀ i, (∀ p, IsP m (i * (5 * m + 8)) p) ∧ Blk m 3 (i * (5 * m + 8)) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨_, _, _, _, ha', hb', _⟩ := k67b_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha', hb'⟩

end K67b

/-- 予想 K67 の u ≡ 19 (mod 64)：(n, 0) が P ⇔ n mod (5m+8) ∈ {0, m+2, 2m+4, 3m+6, 4m+7}。-/
theorem K67_19 (m : Nat) (hm : (m + 1) % 512 = 152) (n : Nat) :
    IsP m n 0 ↔ (n % (5 * m + 8) = 0 ∨ n % (5 * m + 8) = m + 2 ∨ n % (5 * m + 8) = 2 * m + 4 ∨
      n % (5 * m + 8) = 3 * m + 6 ∨ n % (5 * m + 8) = 4 * m + 7) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := k67b_rows m _ hmu (by omega) (n / (5 * m + 8))
  obtain ⟨hr1, hr2, hr3, hr4, _, _, hah, hb1h, hb2h⟩ := k67b_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (5 * m + 8)) * (5 * m + 8) + n % (5 * m + 8) := by
    have := Nat.div_add_mod n (5 * m + 8)
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (5 * m + 8) < 5 * m + 8 := Nat.mod_lt n (by omega)
  generalize hcc : n % (5 * m + 8) = c at hdiv hlt
  generalize ha : n / (5 * m + 8) * (5 * m + 8) = a at hdiv hrow hr1 hr2 hr3 hr4 hah hb1h hb2h
  subst hdiv
  have hmh : m + 1 = 2 * (4 * ((m + 1) / 8)) := by omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
    by_cases h1 : c ≤ m
    · exact not_isP_of_row m a c 0 hrow (by omega) h1 (by omega) hP
    · by_cases h2 : c = m + 1
      · subst h2; exact not_isP_near m a _ 0 hmh (by omega) (by omega) hah (by omega) hP
      · by_cases h3 : c ≤ 2 * m + 2
        · rw [show a + c = a + (m + 2) + (c - (m + 2)) by omega] at hP
          exact not_isP_of_row m _ (c - (m + 2)) 0 hr1 (by omega) (by omega) (by omega) hP
        · by_cases h4 : c = 2 * m + 3
          · rw [h4, show a + (2 * m + 3) = a + (m + 2) + (m + 1) by omega] at hP
            exact not_isP_near m _ _ 0 hmh (by omega) (by omega) hb1h (by omega) hP
          · by_cases h5 : c ≤ 3 * m + 4
            · rw [show a + c = a + (2 * m + 4) + (c - (2 * m + 4)) by omega] at hP
              exact not_isP_of_row m _ (c - (2 * m + 4)) 0 hr2 (by omega) (by omega) (by omega) hP
            · by_cases h6 : c = 3 * m + 5
              · rw [h6, show a + (3 * m + 5) = a + (2 * m + 4) + (m + 1) by omega] at hP
                exact not_isP_near m _ _ 0 hmh (by omega) (by omega) hb2h (by omega) hP
              · by_cases h7 : c ≤ 4 * m + 6
                · rw [show a + c = a + (3 * m + 6) + (c - (3 * m + 6)) by omega] at hP
                  exact not_isP_of_row m _ (c - (3 * m + 6)) 0 hr3 (by omega) (by omega) (by omega) hP
                · rw [show a + c = a + (4 * m + 7) + (c - (4 * m + 7)) by omega] at hP
                  exact not_isP_of_row m _ (c - (4 * m + 7)) 0 hr4 (by omega) (by omega) (by omega) hP
  · intro h
    rcases h with h | h | h | h | h
    · rw [h, Nat.add_zero]; exact hrow 0
    · rw [h]; exact hr1 0
    · rw [h]; exact hr2 0
    · rw [h]; exact hr3 0
    · rw [h]; exact hr4 0

end Rubidium
