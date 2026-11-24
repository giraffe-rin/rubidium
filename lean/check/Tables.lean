/-
  Tables.lean — 全局面 (r, p) の勝敗表を、Lean の Array による DP で計算して出す（JavaScript の solver_dp.js・solver_retro.js とは独立な実装）。
  局面 (r, p) が P ⇔ 1 ≤ k ≤ min(m, r)、k ≠ p のどの手 k でも (r − k, k) が P でない（PROBLEM.md の定義、Rubidium.IsP と同じ形）。
  出力：各行「m r 文字列」。文字列の p 文字目（p = 0..m）が (r, p) の勝敗（N：手番の勝ち、P：手番の負け）。
  実行方法（lean/ で）：lake env lean --run check/Tables.lean 30 2000 > ../data/lean_tables.txt
  照合：node code/lean_tables_compare.js data/lean_tables.txt <data/tables のあるディレクトリ>
-/
def table (m rmax : Nat) : Array (Array Bool) := Id.run do
  let mut t : Array (Array Bool) := #[]
  for r in [0:rmax + 1] do
    let mut row : Array Bool := #[]
    for p in [0:m + 1] do
      let mut isP := true
      for k in [1:(min m r) + 1] do
        if k != p && t[r - k]![k]! then
          isP := false
      row := row.push isP
    t := t.push row
  return t

def main (args : List String) : IO Unit := do
  let mmax := (args.getD 0 "30").toNat!
  let rmax := (args.getD 1 "2000").toNat!
  for m in [1:mmax + 1] do
    let t := table m rmax
    for r in [0:rmax + 1] do
      let s := String.ofList (t[r]!.toList.map fun b => if b then 'P' else 'N')
      IO.println s!"{m} {r} {s}"
