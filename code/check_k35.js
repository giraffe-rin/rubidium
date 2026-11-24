/*
 * check_k35.js — 定理 K35（k ≥ 2 で m = (3·16^k − 13)/5 の型は周期 1^{2k−1} 0 0）の証明の各段階をブロック漸化式で確かめる
 *
 * 何を計算するか:
 *   k = 2, …, KMAX について m = (3·16^k − 13)/5、a = (16^k − 1)/5、M = m + 2 = 3a、P = 2k + 1 とし、
 *   block_rule.js の nextBlock で 3P ブロック計算して、次を調べる。
 *     (1) 間隔の列が (1^{2k−1} 0 0) のくり返しであること、v2(m+1) = 3 であること
 *     (2) 周期の始まりのブロック B（B ≡ 0 mod P）で、d3 = (27a − 1)/16 ∉ S、y_i = 2a − 4^i ∉ S（1 ≤ i ≤ 2k−3）、
 *         y_0 = 2a − 1 ∈ S、c_t = M − 3·2^t ∈ S（t = 2k − 2）であること
 *     (3) O 型ブロック j で、(O1)(O2) による次の関係が成り立つこと
 *         [h ∈ S_j] = ¬[d3 ∈ S_{j−1}]、[y_i ∈ S_j] = [y_{i−1} ∈ S_{j−1}]（1 ≤ i ≤ 2k−3、j − 1 も O 型）、
 *         [c_t ∈ S_j] = ¬[c_{t−1} ∈ S_{j−1}]（2k−1 ≤ t ≤ 4k−4）
 *     (4) 1 番目の E 型ブロック j で [h ∈ S_j] = ¬[3h/2 ∈ S_{j−1}] かつ 3h/2 ∈ S_{j−1}
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k35.js 6 > data/k35_check.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const KMAX = +(process.argv[2] || 6);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = ['# 定理 K35 の証明の各段階の確認（ブロック漸化式）', `# 生成: node code/check_k35.js ${KMAX}`, 'k | m | v2(m+1) | (1) 間隔の列 | (2) の違反 | (3) の違反 | (4) の違反 | 調べた事実の数'];
for (let k = 2; k <= KMAX; k++) {
  const m = (3 * 16 ** k - 13) / 5, a = (16 ** k - 1) / 5, M = m + 2, h = (m + 1) / 2, P = 2 * k + 1;
  const d3 = (27 * a - 1) / 16, y = i => 2 * a - 4 ** i, c = t => M - 3 * 2 ** t;
  let pv = null; const S = [], g = [];
  for (let j = 0; j < 3 * P; j++) { pv = nextBlock(m, pv); S.push(pv.S); g.push(pv.g === m + 2 ? 1 : 0); }
  const in_ = (j, d) => S[j][d] === 1;
  const okGaps = g.join('') === ('1'.repeat(2 * k - 1) + '00').repeat(3);
  let e2 = 0, e3 = 0, e4 = 0, n = 0;
  for (let j = 0; j < 3 * P; j++) {
    const r = j % P;
    if (r === 0) {
      n++; if (in_(j, d3)) e2++;
      for (let i = 1; i <= 2 * k - 3; i++) { n++; if (in_(j, y(i))) e2++; }
      n++; if (!in_(j, y(0))) e2++; n++; if (!in_(j, c(2 * k - 2))) e2++;
      continue;
    }
    const isO = r <= 2 * k - 1, prevO = r - 1 >= 1 && r - 1 <= 2 * k - 1;
    if (isO) {
      n++; if (in_(j, h) !== !in_(j - 1, d3)) e3++;
      if (prevO) for (let i = 1; i <= 2 * k - 3; i++) { n++; if (in_(j, y(i)) !== in_(j - 1, y(i - 1))) e3++; }
      for (let t = 2 * k - 1; t <= 4 * k - 4; t++) { n++; if (in_(j, c(t)) !== !in_(j - 1, c(t - 1))) e3++; }
    }
    if (r === 2 * k) { n++; if (in_(j, h) !== !in_(j - 1, 3 * h / 2) || !in_(j - 1, 3 * h / 2)) e4++; }
  }
  out.push(`${k} | ${m} | ${v2(m + 1)} | ${okGaps ? '(1^{2k−1} 0 0)^3 と一致' : '不一致：' + g.join('')} | ${e2} | ${e3} | ${e4} | ${n}`);
}
console.log(out.join(String.fromCharCode(10)));
