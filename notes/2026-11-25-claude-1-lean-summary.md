---
agent: claude-1
date: 2026-11-25
problem: restricted-stone-game
task: Lean 4 による形式化のまとめ（どの定理が示され、m の分類のどこが埋まったか）
branch: claude-1/lean-summary
---

# Lean 4 による形式化のまとめ（2026-11-25 時点）

すべて `lean/`（Lean 4.36、Mathlib なし）にある。sorry はなく、公理は `propext`・`Quot.sound`（一部は `Classical.choice` も）。
どれもブロックの理論 H(j)（K8）を使わず、ゲームの定義 `IsP` から局面の言葉で直接示している。

## 示した定理と査読の状況

| 定理 | 内容 | Lean | PR | 査読 |
|---|---|---|---|---|
| K3 | 1 ≤ r ≤ m の (r, p) の P/N | K3.lean | #364 | Lean検証済み |
| K4 | (n,0) が P ⇔ (m+1)\|n ⇔ v2(m+1) 偶数 | K4Even・K4Full | #375・#377 | Lean検証済み |
| K5 | v2(m+1) 奇数なら最初の P は m+2 | K5.lean | #367 | Lean検証済み |
| isPb_iff | 計算できる判定と IsP の同値 | Decide.lean | #373 | Lean検証済み |
| K6 | m ≡ 5 (mod 8) は交互型 | K6.lean | #391 | Lean検証済み |
| K7′ | すべての m で勝敗表は周期的 | K7.lean | #418 | Lean検証済み |
| K9 | v2(m+1)=1：交互型 ⇔ v2(3h+1) 奇数 | K9.lean | #393・#395 | Lean検証済み |
| K10 (a) | m+1=8u、u≡1 (8)、u≥9 は交互型 | K10.lean | #397 | Lean検証済み |
| K10c・K10 (b) | v2(m+1)=3 で交互型の必要条件 | K10c・K11 | #406・#410 | Lean検証済み |
| K11 | v2(m+1) ≥ 5 奇数は交互型でない | K11.lean | #408 | Lean検証済み |
| K12 (a) | 110 型（k = 1） | K12.lean | #404 | Lean検証済み |
| K13 | 100 型（v2(m+1)=3） | K13.lean | #399 | Lean検証済み |
| K15 | 1(10)^k 型（一般の k ≥ 2） | K15gen.lean | #443 | 査読待ち |
| K29 | v ≥ 5 奇数、u ≡ 1 (4) は 1 0^{(v−1)/2} | K29・K29gen | #420・#434・#437 | Lean検証済み |
| K38 | v ≥ 5 奇数、u ≡ 3 (4)、w の条件で 1 0^{(v+1)/2} | K38・K38v7・K38gen・K38w | #424・#426・#429・#431 | #431 以外は Lean検証済み |

照合（証明ではない）：Lean の DP と JavaScript・Python の DP が、m ≤ 100、r ≤ 3000 の全局面で一致（#379・#381）。

## m の分類のうち Lean で型が決まった部分（m ≤ 10^6、`data/lean_coverage.txt`）

| v2(m+1) | 割合 | 使う定理 |
|---|---|---|
| 偶数 | 100% | K4 |
| 1 | 83.33% | K9、K12 (a)、K15 |
| 3 | 50.00% | K10 (a)、K13 |
| 5 以上の奇数 | 約 66% | K29、K38 |
| 合計 | **92.00%** | |

## 使い回せる道具（`lean/Rubidium/`）

- 行の補題：
  - `not_isP_of_row`：P の行から d 先は p = d でしか P にならない。
  - `row_long`・`row_next`：次の P の行。
  - `not_isP_near`、`not_isP_move`。
- ブロックの中の所属：
  - `odd_of_rows`、`p_two`、`p_four`、`p_oddb`、`e_even`・`e_iff`。
  - `o_half`・`o_iter`（h が奇数なら `o_half'`・`o_iter3`）、`o_odd_iff`。
- 付値の不変量：
  - `Blk`、`blk_step`（K4）、`blk_step2`、`blk_EO`、`blk1_direct`。
  - Inh の 1 段：`k38_istep`、`k29_istep`、`k15_istep`。
- 付値：`v2`、`v2_add`、`v2_pow_mul`、`v2_decomp`、`ev2_iff_v2`。

## まだ Lean で型が決まらない部分（約 8%）

- v2(m+1) = 1：v2(3h+1) が偶数で Q が偶数の場合。
  - K14 によると、v2(Q) が奇数なら 1(10)^k 型ではない。v2(Q) が 2 以上の偶数なら混在する。
- v2(m+1) = 3：K10 (a)・K13 以外。
  - 予想 K63 の (1)：(a + 4Y) の所属がブロックによって変わり、一定の事実の集合では閉じない（PR #414 の追記）。
  - 100 型以外のさまざまな型。
- v2(m+1) ≥ 5 の奇数：
  - w = v2(u+1) が偶数で v − 1 以下（K47、型が無限に多い）。
  - w = v（K47b）。
  - u ≡ 3 (mod 4) で w = 1 は起きない（u ≡ 3 なら w ≥ 2）。

## 次の候補

- K47・K47b の族（鎖の記号的な評価で示したもの）の Lean 化。鎖の長さが N に比例するので、K38gen のような帰納法の組み立てが要る。
- v2(m+1) = 1 で Q が偶数の場合の、型の分類（予想の段階から）。
