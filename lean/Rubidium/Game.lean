/-
  Rubidium.Game — 制限付き石取りゲーム（problems/restricted-stone-game/PROBLEM.md）の定義

  局面 (r, p)：r は山に残っている石の数、p は直前に相手が取った石の数（開始時は 0）。
  合法手 k：1 ≤ k ≤ min(m, r) かつ k ≠ p。手 k で局面は (r − k, k) に移る。
  合法手がなければ手番のプレイヤーの負け。

  IsP m r p：局面 (r, p) が後手必勝（P 局面）であること。
    「どの合法手で移った先も P 局面でない」と、r についての整礎な再帰で定める。
-/
namespace Rubidium

/-- 局面 (r, p) が後手必勝（P 局面）である。-/
def IsP (m : Nat) (r p : Nat) : Prop :=
  ∀ k, 1 ≤ k → k ≤ m → k ≤ r → k ≠ p → ¬ IsP m (r - k) k
termination_by r
decreasing_by omega

/-- IsP の展開。-/
theorem isP_iff (m r p : Nat) :
    IsP m r p ↔ ∀ k, 1 ≤ k → k ≤ m → k ≤ r → k ≠ p → ¬ IsP m (r - k) k := by
  rw [IsP]

/-- 石がなければ（r = 0）、合法手がないので P 局面。-/
theorem isP_zero (m p : Nat) : IsP m 0 p := by
  rw [isP_iff]
  intro k hk _ hkr _
  omega

/-- v2(r) が偶数であること（r ≥ 1 のとき）。r が奇数なら真、偶数なら r/2 についての値の否定。
    r = 0 では便宜上 true とする（使わない）。-/
def ev2 (r : Nat) : Bool :=
  if r = 0 then true
  else if r % 2 = 1 then true
  else !ev2 (r / 2)
termination_by r
decreasing_by omega

theorem ev2_odd (r : Nat) (h : r % 2 = 1) : ev2 r = true := by
  rw [ev2]
  simp [h]

theorem ev2_even (r : Nat) (h0 : r ≠ 0) (h : r % 2 = 0) : ev2 r = !ev2 (r / 2) := by
  rw [ev2]
  simp [h0, h]

end Rubidium
