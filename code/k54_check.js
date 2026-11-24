/*
 * k54_check.js — 定理 K54 の証明の帰納法（補題 K54.1：E_i(c, k) = Ψ(c, k) = [t(c) + k が奇数]）を、補題 K52 の再帰で数値的に確かめる
 *
 * 何を計算するか:
 *   v 奇数、偶数 ρ ≤ v − 1、M = 2^ρ − 1、z = ρ/2 について、R ≡ 1 (mod 2L) での補題 K52 の再帰を、補題 K53 の閉じた式
 *   F(c, k) = [t(c) + k が奇数]（3 ≤ c < M、t(c) = v2(c − 1)）、F(1, k) = [k が偶数]、c ≥ M は不明、で計算する（3 値、第 2 項を先に評価）。
 *   (1) j = 1..z−1 で E_j(1, 1) が「入らない」か。
 *   (2) 補題 K54.1 の範囲（c ≥ 3 奇数、c < 2^k、k ≤ ρ − 1 − 2i、1 の個数 + i ≤ z）のすべての (i, c, k) で E_i(c, k) = Ψ(c, k) か（範囲の全数）。
 *   (3) E_j(1, 1)（j ≤ z − 1）の評価で実際に現れた状態の数。
 * 実行方法（リポジトリのルートで）:
 *   node code/k54_check.js 5:4 7:6 9:8 11:10 13:12 15:14 17:16 19:18 21:20 23:22 13:6 17:8 21:10 25:12 > data/k54_check.txt
 */
'use strict';
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const pop = x => { let c = 0; while (x > 0n) { c += Number(x & 1n); x >>= 1n; } return c; };
const out = ['# 定理 K54 の帰納法（補題 K54.1）の数値での確認', '# 生成: node code/k54_check.js ' + process.argv.slice(2).join(' '), 'v | ρ | (1) E_j(1,1)（j = 1..z−1） | (2) 範囲内の状態の数 / 式と一致 | (3) 現れた状態の数'];
let allOk = true;
for (const a of process.argv.slice(2)) {
  const [v, rho] = a.split(':').map(Number), M = 2n ** BigInt(rho) - 1n, z = rho / 2;
  const F = (c, k) => { if (c === 1n) return k % 2 === 0; if (c >= M) return null; return (v2(c - 1n) + k) % 2 === 1; };
  const memo = new Map();
  const E = (j, c, k) => { const key = j + ':' + c + ':' + k; if (memo.has(key)) return memo.get(key); let res;
    if (k === v) res = true; else { const c2 = 2n ** BigInt(k) + c; const B = j === 1 ? F(c2, k + 1) : E(j - 1, c2, k + 1);
      if (B === true) res = false; else { const A = E(j, c, k + 1); res = A === true ? false : (A === null || B === null) ? null : true; } }
    memo.set(key, res); return res; };
  const top = []; for (let j = 1; j <= z - 1; j++) top.push(E(j, 1n, 1));
  const ok1 = top.every(x => x === false); const reached = memo.size;
  let n2 = 0, ok2 = 0;
  for (let i = 1; i <= z - 1; i++) for (let k = 2; k <= rho - 1 - 2 * i; k++) for (let c = 3n; c < 2n ** BigInt(k); c += 2n) {
    if (pop(c) + i > z) continue; n2++; if (E(i, c, k) === ((v2(c - 1n) + k) % 2 === 1)) ok2++; }
  if (!ok1 || ok2 !== n2) allOk = false;
  out.push(`${v} | ${rho} | ${top.map(x => x === null ? '?' : x ? 1 : 0).join('') || '-'}（${ok1 ? 'すべて入らない' : '違う'}） | ${n2} / ${ok2} | ${reached}`);
}
out.push('', allOk ? 'すべての組で (1) と (2) が成り立つ' : '成り立たないものがある');
console.log(out.join('\n'));
