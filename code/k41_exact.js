/*
 * k41_exact.js — 定理 K41c（m 偶数のときの R の状態の周期 λ の正確な式）を、Brent の方法で求めた λ と照合する
 *
 * 何を計算するか:
 *   偶数 m（n = m+1）について、ψ の各巡回 C = (x_1, …, x_ℓ)（x_{i+1} = ψ(x_i)）で、k_i := x_i から 2 を掛けて初めて n を超えるまでの回数
 *   （ψ(x_i) から x_i に戻る段数）の巡回列 (k_1, …, k_ℓ) を作る。
 *   その偶奇の列 (k_i mod 2) の最小周期 π（π | ℓ）と、π 個分の和 σ から、λ_C := π（σ が偶数）または 2π（σ が奇数）とし、λ_formula := lcm_C λ_C。
 *   data/state_period_even.txt の λ（状態そのものの周期）と比べる。
 * 実行方法（リポジトリのルートで）:
 *   node code/k41_exact.js data/state_period_even.txt > data/k41_exact.txt
 */
'use strict';
const fs = require('fs');
const file = process.argv[2];
const gcd = (a, b) => (b ? gcd(b, a % b) : a), lcm = (a, b) => (a / gcd(a, b)) * b;
const rows = fs.readFileSync(file, 'utf8').split(/\r?\n/).slice(3).filter(Boolean).map(l => l.split(' | '));
let tot = 0, ok = 0; const bad = [];
for (const [ms, , , lam] of rows) {
  const m = +ms; if (m % 2 === 1 || lam.includes('打ち')) continue; tot++; const n = m + 1;
  // ψ(d) と、ψ(d) から d に戻る段数 k（d = 2^k ψ(d) − n）
  const psi = new Map(), kk = new Map();
  for (let d = 1; d <= m - 1; d += 2) { let e = (n + d) / 2, t = 0; while (e % 2 === 0) { e /= 2; t++; } psi.set(d, e); kk.set(d, t + 1); }
  const seen = new Set(); let L = 1;
  for (let d = 1; d <= m - 1; d += 2) {
    if (seen.has(d)) continue; const ks = []; let x = d; do { seen.add(x); ks.push(kk.get(x) % 2); x = psi.get(x); } while (x !== d);
    const l = ks.length; let pi = l; for (let p = 1; p <= l; p++) if (l % p === 0 && ks.every((k, i) => k === ks[(i + p) % l])) { pi = p; break; }
    const sigma = ks.slice(0, pi).reduce((a, b) => a + b, 0); L = lcm(L, sigma % 2 === 0 ? pi : 2 * pi);
  }
  if (L === +lam) ok++; else bad.push(`${m}: ${L}/${lam}`);
}
console.log(['# 定理 K41c：状態の周期の正確な式と、Brent の方法で求めた λ の比較', `# 生成: node code/k41_exact.js ${file}`, `偶数 m ${tot} 個のうち一致 ${ok} 個`, bad.length ? '不一致: ' + bad.join('、') : '不一致なし'].join(String.fromCharCode(10)));
