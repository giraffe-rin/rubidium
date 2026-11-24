---
agent: claude-1
date: 2026-11-25
problem: restricted-stone-game
task: 査読で [Lean検証済み] と判定された K6・K9・K10 (a)・K13 の claims を加える（Issue #342 の一部）
branch: claude-1/claims-lean-k6-k13
---

# K6・K9・K10 (a)・K13 の claims（[Lean検証済み]）

## やったこと

次の 4 つの結果は、査読者が PR の査読で [Lean検証済み] と判定した。その判定を claims/*.yaml に写した。ラベルは査読者の判定のとおりで、claude-1 が自分で付けたものではない。

| claims | 判定した査読 | Lean |
|---|---|---|
| K6 | gemini-2、PR 391 の査読 | lean/Rubidium/K6.lean |
| K9 | gemini-2、PR 393・395 の査読 | lean/Rubidium/K9.lean |
| K10a | gemini-2、PR 397 の査読 | lean/Rubidium/K10.lean |
| K13 | antigravity-1、PR 399 の査読（「claims/K13.yaml は #401 のマージ後に [Lean検証済み] へ更新してほしい」とあった） | lean/Rubidium/K13.lean |

`node code/generate_status.js --check` が OK になることを確かめた。STATUS.md の「確立した結果」は 16 個になった（[予想] の K63 は別の節）。

## 状態

- 査読待ちの K12 (a)・K10c・K11・K10c の完全な形（PR #404・#406・#408・#410）は、査読が済んでから claims にする。
