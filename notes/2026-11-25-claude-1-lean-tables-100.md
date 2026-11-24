---
agent: claude-1
date: 2026-11-25
problem: restricted-stone-game
task: Lean と JavaScript の DP の照合を m ≤ 100、r ≤ 3000 に広げる（Issue #380）
branch: claude-1/lean-tables-100
---

# Lean と JavaScript の DP の照合を m ≤ 100、r ≤ 3000 に広げる

## 取りかかった理由

WIP 上限（未査読の証明 PR が 5 件）が続いているので、証明ではない検証の作業として、PR #379 の照合の範囲を広げた。

## やったこと

- 表全体（m ≤ 100、r ≤ 3000）は 10 MB を超えるので、m ごとの要約を比べる形にした。要約は次の 3 つ。
  - P 局面の数
  - チェックサム Σ (r(m+1) + p + 1)² mod (10^9 + 7)（P 局面 (r, p) についての和）
  - P の開始局面 (n, 0)（n ≥ 1）の最初の 20 個
- `lean/check/TableSummary.lean`：Lean の Array による DP（check/Tables.lean と同じ規則）で要約を出した（インタプリタで約 8 分）。出力は `data/lean_table_summary.txt`。
- `code/table_summary_compare.js`：このファイルの中で独立に書いた JavaScript の DP（Uint8Array で r の小さい順に埋める）で同じ要約を作り、Lean の出力と比べた。
- 結果（`data/table_summary_compare.txt`）：**100 個の m すべてで要約が一致**（局面の数の合計 15455150）。

## 意味

- 勝敗表の土台の照合を、m ≤ 30、r ≤ 2000（PR #379、全局面）から、m ≤ 100、r ≤ 3000（要約）に広げた。
- 最初の P の開始局面は、定理 K4・K5 と合う。たとえば m = 99 は v2(100) = 2 が偶数なので 100 の倍数、m = 100 は 101 の倍数。

## 状態

計算による照合（ラベルの変化なし）。
