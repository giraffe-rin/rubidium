/-
  TableSummary.lean — 全局面 (r, p) の勝敗表を Array による DP で計算し（check/Tables.lean と同じ規則）、m ごとの要約を出す。
  要約：P 局面の数、チェックサム Σ (r(m+1) + p + 1)² mod (10^9 + 7)（P 局面 (r, p) についての和）、P の開始局面 (n, 0)（n ≥ 1）の最初の 20 個。
  出力：各行「m P の数 チェックサム [n, …]」。
  実行方法（lean/ で）：lake env lean --run check/TableSummary.lean 100 3000 > ../data/lean_table_summary.txt
  照合：node code/table_summary_compare.js data/lean_table_summary.txt 100 3000
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
  let mmax := (args.getD 0 "100").toNat!
  let rmax := (args.getD 1 "3000").toNat!
  let md := 1000000007
  for m in [1:mmax + 1] do
    let t := table m rmax
    let mut cnt := 0
    let mut sum := 0
    let mut starts : Array Nat := #[]
    for r in [0:rmax + 1] do
      for p in [0:m + 1] do
        if t[r]![p]! then
          cnt := cnt + 1
          let x := r * (m + 1) + p + 1
          sum := (sum + x * x) % md
      if r ≥ 1 && t[r]![0]! && starts.size < 20 then
        starts := starts.push r
    IO.println s!"{m} {cnt} {sum} {starts.toList}"
