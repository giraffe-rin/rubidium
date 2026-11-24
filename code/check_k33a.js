/*
 * check_k33a.js — 定理 K33a（e 偶数で m = 9·2^e + 1 の型は周期 1^{e/2} 0）の証明の各段階をブロック漸化式で確かめる
 *
 * 何を計算するか:
 *   偶数 e = 2, 4, …, EMAX について m = 9·2^e + 1、o* = 3·2^e + 1、K = (e−2)/2、P = e/2 + 1 とし、
 *   block_rule.js の nextBlock で 3P ブロック計算して、次を調べる。
 *     (1) 間隔の列が (1^{e/2} 0) のくり返しであること
 *     (2) 0 ≤ i ≤ K で o_i = o* + 3·2^{e−1−2i}、1 ≤ i ≤ K+1 で x_i = 2o* + 3·2^{e−2i} とし、
 *         周期の始まりのブロック（j ≡ 0 mod P）で x_i ∈ S ⇔ i = K + 1 であること
 *     (3) O 型ブロック j（j mod P ≠ 0）で、[o_i ∈ S_j] = ¬[x_{i+1} ∈ S_{j−1}]（0 ≤ i ≤ K）、
 *         周期の始まりでない O 型ブロック j − 1 では [x_{i+1} ∈ S_{j−1}] = ¬[o_{i+1} ∈ S_{j−1}]（0 ≤ i ≤ K − 1）であること
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k33a.js 20 > data/k33a_check.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const EMAX = +(process.argv[2] || 16);
const out = ['# 定理 K33a の証明の各段階の確認（ブロック漸化式）', `# 生成: node code/check_k33a.js ${EMAX}`, 'e | m | (1) 間隔の列 | (2) の違反 | (3) の違反 | 調べた事実の数'];
for (let e = 2; e <= EMAX; e += 2) {
  const m = 9 * 2 ** e + 1, os = 3 * 2 ** e + 1, K = (e - 2) / 2, P = e / 2 + 1;
  const o = i => os + 3 * 2 ** (e - 1 - 2 * i), x = i => 2 * os + 3 * 2 ** (e - 2 * i);
  let pv = null; const S = [], g = [];
  for (let j = 0; j < 3 * P; j++) { pv = nextBlock(m, pv); S.push(pv.S); g.push(pv.g === m + 2 ? 1 : 0); }
  const okGaps = g.join('') === ('1'.repeat(e / 2) + '0').repeat(3);
  let v2 = 0, v3 = 0, n = 0;
  for (let j = 0; j < 3 * P; j++) {
    if (j % P === 0) { for (let i = 1; i <= K + 1; i++) { n++; if ((S[j][x(i)] === 1) !== (i === K + 1)) v2++; } continue; }
    for (let i = 0; i <= K; i++) { n++; if ((S[j][o(i)] === 1) !== !(S[j - 1][x(i + 1)] === 1)) v3++; }
    if ((j - 1) % P !== 0) for (let i = 0; i <= K - 1; i++) { n++; if ((S[j - 1][x(i + 1)] === 1) !== !(S[j - 1][o(i + 1)] === 1)) v3++; }
  }
  out.push(`${e} | ${m} | ${okGaps ? '(1^{e/2} 0)^3 と一致' : '不一致：' + g.join('')} | ${v2} | ${v3} | ${n}`);
}
console.log(out.join(String.fromCharCode(10)));
