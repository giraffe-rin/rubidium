/*
 * check_k38.js — 定理 K38（v ≥ 5 奇数、w = v2(u+1) が奇数で 3 ≤ w ≤ v−2、または w ≥ v+1 なら、型は 1 0^{(v+1)/2}）の
 *                証明の各段階をブロック漸化式で確かめる
 *
 * 何を計算するか:
 *   奇数 v = 5, 7, 9 と、u ≡ 3 (mod 4) の奇数 u < UMAX（m = 2^v u − 1）で、定理の条件を満たすものについて、
 *   block_rule.js の nextBlock で 3 周期分（3(v+3)/2 ブロック）計算し、L = (v+3)/2 として、周期の始まりのブロック B（B ≡ 0 mod L）ごとに次を調べる。
 *     (1) 間隔の列が (1 0^{(v+1)/2}) のくり返しであること
 *     (2) ブロック B+1 で、u（c = 1）、3u、7u は入らない
 *     (3) 補題 Inh′：2 ≤ n ≤ (v−1)/2、q ∈ {3, 7}、2n−2 ≤ b ≤ v−3 で、[2^b q u ∈ S_{B+n}] = [b が奇数]
 *     (4) 1 ≤ n ≤ (v−1)/2 で 3·2^{v−2} u ∈ S_{B+n}
 *   あわせて、条件を満たさない u（w が偶数で w ≤ v−1）で、ブロック 1 に h が入る（g_1 = m+2）ことを数える。
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k38.js 2048 > data/k38_check.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const UMAX = +(process.argv[2] || 2048);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = ['# 定理 K38 の証明の各段階の確認（ブロック漸化式）', `# 生成: node code/check_k38.js ${UMAX}`, 'v | 条件を満たす u の個数 | (1) の違反 | (2) の違反 | (3) の違反 | (4) の違反 | w 偶数 ≤ v−1 の u の個数 | そのうち g_1 = m+2 の個数'];
for (const v of [5, 7, 9]) {
  const L = (v + 3) / 2; let cnt = 0, e1 = 0, e2 = 0, e3 = 0, e4 = 0, ce = 0, ceg = 0;
  for (let u = 3; u < UMAX; u += 4) {
    const m = 2 ** v * u - 1; if (m > 3e6) break; const w = v2(u + 1);
    const cond = (w % 2 === 1 && w >= 3 && w <= v - 2) || w >= v + 1;
    if (!cond) {
      if (w % 2 === 0 && w <= v - 1) { ce++; let pv = nextBlock(m, null); pv = nextBlock(m, pv); if (pv.g === m + 2) ceg++; }
      continue;
    }
    cnt++; let pv = null; const S = [], g = [];
    for (let j = 0; j < 3 * L; j++) { pv = nextBlock(m, pv); S.push(pv.S); g.push(pv.g === m + 2 ? 1 : 0); }
    if (g.join('') !== ('1' + '0'.repeat((v + 1) / 2)).repeat(3)) e1++;
    for (let B = 0; B + L <= 3 * L; B += L) {
      for (const c of [1, 3, 7]) if (S[B + 1][c * u] === 1) e2++;
      for (let n = 2; n <= (v - 1) / 2; n++) for (const q of [3, 7]) for (let b = 2 * n - 2; b <= v - 3; b++) if ((S[B + n][2 ** b * q * u] === 1) !== (b % 2 === 1)) e3++;
      for (let n = 1; n <= (v - 1) / 2; n++) if (S[B + n][3 * 2 ** (v - 2) * u] !== 1) e4++;
    }
  }
  out.push(`${v} | ${cnt} | ${e1} | ${e2} | ${e3} | ${e4} | ${ce} | ${ceg}`);
}
console.log(out.join(String.fromCharCode(10)));
