/*
 * k41_orbit.js — 定理 K41 の P を、「n = m+1 を法として 2 を掛ける」写像の軌道から求め、ψ の巡回から求めた P と比べる
 *
 * 何を計算するか:
 *   偶数 m（n = m+1 は奇数）について、1..n−1 を「r ↦ 2r mod n」の軌道に分け、各軌道 O について
 *     o = |O|（軌道の長さ）、ℓ = O の中の奇数の個数
 *   とし、P_orb := lcm_O（o が偶数なら ℓ、奇数なら 2ℓ）を求める。
 *   data/state_period_psi.txt の P（ψ の巡回から求めた値）と比べる。
 * 実行方法（リポジトリのルートで）:
 *   node code/k41_orbit.js data/state_period_psi.txt > data/k41_orbit.txt
 */
'use strict';
const fs = require('fs');
const file = process.argv[2];
const gcd = (a, b) => (b ? gcd(b, a % b) : a), lcm = (a, b) => (a / gcd(a, b)) * b;
const rows = fs.readFileSync(file, 'utf8').split(/\r?\n/).slice(3).filter(l => /^\d+ \|/.test(l)).map(l => l.split(' | '));
let n0 = 0, ok = 0; const bad = [];
for (const [ms, , Ps] of rows) {
  const m = +ms, n = m + 1; if (Ps === '−') continue; n0++;
  const seen = new Uint8Array(n); let P = 1;
  for (let r = 1; r < n; r++) { if (seen[r]) continue; let x = r, o = 0, l = 0; do { seen[x] = 1; o++; if (x % 2 === 1) l++; x = (2 * x) % n; } while (x !== r); P = lcm(P, o % 2 === 0 ? l : 2 * l); }
  if (P === +Ps) ok++; else bad.push(`${m}: ${P}/${Ps}`);
}
console.log(['# 定理 K41 の P：軌道から求めた値と ψ の巡回から求めた値の比較', `# 生成: node code/k41_orbit.js ${file}`, `偶数 m ${n0} 個のうち一致 ${ok} 個`, bad.length ? '不一致: ' + bad.join('、') : '不一致なし'].join(String.fromCharCode(10)));
