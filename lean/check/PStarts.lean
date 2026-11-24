/-
  PStarts.lean — 計算できる版 isPb（Rubidium/Decide.lean、`isPb_iff` で IsP と同値と証明済み）を実行し、
  m = 1..10 について、開始局面 (n, 0) が後手必勝になる n（1 ≤ n ≤ 24）を出す。
  実行方法（lean/ で）：lake env lean --run check/PStarts.lean（数秒）
  照合：node code/lean_crosscheck.js（リポジトリのルートで、data/lean_pstarts.txt を読む）
-/
import Rubidium.Decide
open Rubidium
-- 開始局面 (n, 0) が後手必勝になる n（1 ≤ n ≤ 上限）を、m ごとに出す
def pStarts (m nmax : Nat) : List Nat := (List.range (nmax + 1)).filter fun n => n ≥ 1 && isPb m n 0
def main : IO Unit := do
  for m in (List.range 10).map (· + 1) do
    IO.println s!"m = {m}: {pStarts m 24}"
