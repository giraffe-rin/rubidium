/*
 * k63_check_dp.js — 予想 K63 の対象（v2(m+1) = 3、v2(9u+1) = 1、v2(11u+1) ≥ 4 の偶数）の m が交互型かどうかを、
 *                   漸化式 R を使わない直接の DP（(r, p) が P ⇔ A_r ⊆ {p}）で、n ≤ 6(2m+3) まで確かめる
 *
 * 何を計算するか: 各 u ≤ UMAX について、1 ≤ n ≤ 6(2m+3) のすべてで「(n, 0) が P ⇔ n mod (2m+3) ∈ {0, m+2}」が成り立つか。
 *   成り立たなければ、最初に外れる n を出す。code/k63_alt3.js（R による）の結果と比べるためのもの。
 * 実行方法（リポジトリのルートで）:
 *   node code/k63_check_dp.js 1200 > data/k63_check_dp.txt
 */
'use strict';
const UMAX = +process.argv[2];
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = ['# 予想 K63 の対象の m の交互型の判定（直接の DP、n ≤ 6(2m+3)、u ≤ ' + UMAX + '）', '# 生成: node code/k63_check_dp.js ' + UMAX, 'u | m | v2(11u+1) | Y mod 4 | 交互型（n ≤ 6(2m+3) で） | 最初に外れる n'];
for (let u = 1; u <= UMAX; u += 2) {
  const e9 = v2(9 * u + 1), e11 = v2(11 * u + 1);
  if (e9 !== 1 || e11 < 4 || e11 % 2 !== 0) continue;
  const m = 8 * u - 1, L = 2 * m + 3, N = 6 * L, Y = (11 * u + 1) / 2 ** e11;
  const typ = new Int32Array(N + 1); typ[0] = -1; const isP = (r, p) => typ[r] === -1 || typ[r] === p;
  for (let r = 1; r <= N; r++) { let c = 0, kk = 0; for (let k = 1; k <= Math.min(m, r) && c < 2; k++) if (isP(r - k, k)) { c++; kk = k; } typ[r] = c === 0 ? -1 : c === 1 ? kk : -2; }
  let fail = -1; for (let n = 1; n <= N; n++) { const r = n % L; if (isP(n, 0) !== (r === 0 || r === m + 2)) { fail = n; break; } }
  out.push(`${u} | ${m} | ${e11} | ${Y % 4} | ${fail < 0 ? 'はい' : 'いいえ'} | ${fail < 0 ? '-' : fail}`);
}
console.log(out.join('\n'));
