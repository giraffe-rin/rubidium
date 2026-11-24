/*
 * state_period_psi.js — m が偶数のとき、漸化式 R の状態の周期 λ（state_period_even.js の出力）を、写像 ψ の巡回から求めた値 P と比べる
 *
 * 何を計算するか:
 *   m が偶数なら m+1 は奇数で、K4 により間隔はいつも m+1。このとき R は、奇数の d について
 *   [d ∈ S_j] = ¬[(m+1+d)/2 ∈ S_{j−1}]（(m+1+d)/2 ≤ m のとき）、偶数の d について [d ∈ S_j] = ¬[d/2 ∈ S_j] になる。
 *   よって奇数の d の値は、ψ(d) := (m+1+d)/2 の奇数部分の値から、符号 (−1)^{1 + v2((m+1+d)/2)} を掛けて決まる。
 *   ψ が奇数 1..m の上の置換なら、各巡回（長さ ℓ、符号の和 σ）の値の周期は ℓ（σ が偶数）か 2ℓ（σ が奇数）の約数で、
 *   P := それらの最小公倍数 は λ の倍数になるはず。各偶数 m で、ψ が置換か、P と λ（data/state_period_even.txt）を比べる。
 * 実行方法（リポジトリのルートで）:
 *   node code/state_period_psi.js data/state_period_even.txt > data/state_period_psi.txt
 */
'use strict';
const fs = require('fs');
const file = process.argv[2];
const gcd = (a, b) => (b ? gcd(b, a % b) : a), lcm = (a, b) => (a / gcd(a, b)) * b;
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const rows = fs.readFileSync(file, 'utf8').split(/\r?\n/).slice(3).filter(Boolean).map(l => l.split(' | '));
const out = ['# m 偶数：状態の周期 λ と、ψ の巡回から求めた P の比較', `# 生成: node code/state_period_psi.js ${file}`, 'm | ψ は置換か | P | λ | P = λ か | λ は P の約数か'];
let eqc = 0, divc = 0, tot = 0;
for (const [ms, , , lam] of rows) {
  const m = +ms; if (m % 2 === 1 || lam.includes('打ち')) continue; tot++;
  const psi = new Map(), sg = new Map(); let perm = true;
  for (let d = 1; d <= m; d += 2) { const e = (m + 1 + d) / 2; if (e > m) { perm = false; break; } const t = v2(e); psi.set(d, e / 2 ** t); sg.set(d, (1 + t) % 2); }
  let P = 1; const seen = new Set();
  if (perm) for (let d = 1; d <= m; d += 2) { if (seen.has(d)) continue; let x = d, len = 0, s = 0; do { seen.add(x); s += sg.get(x); x = psi.get(x); len++; } while (x !== d && !seen.has(x)); if (x !== d) { perm = false; break; } P = lcm(P, s % 2 ? 2 * len : len); }
  const L = +lam, isEq = perm && P === L, isDiv = perm && P % L === 0; if (isEq) eqc++; if (isDiv) divc++;
  out.push(`${m} | ${perm ? 'はい' : 'いいえ'} | ${perm ? P : '−'} | ${L} | ${isEq ? 'はい' : 'いいえ'} | ${isDiv ? 'はい' : 'いいえ'}`);
}
out.push('', `偶数 m ${tot} 個：P = λ が ${eqc} 個、λ が P の約数が ${divc} 個`);
console.log(out.join(String.fromCharCode(10)));
