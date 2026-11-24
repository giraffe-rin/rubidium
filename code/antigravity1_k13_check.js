// antigravity1_k13_check.js — 定理 K13 の主張を PROBLEM.md の定義だけから全探索で確かめる（PR #399 の査読用）。
// 実行方法（リポジトリのルートで）: node code/antigravity1_k13_check.js 700 6   （引数: m の上限、周期 3m+4 の何倍まで n を調べるか）
// Independent brute-force check of Theorem K13 (antigravity-1). Written from PROBLEM.md only.
// For each m ≡ 7 (mod 8) satisfying {v2(9u+1), v2(11u+1)} = {1,3} with u=(m+1)/8,
// check: (n,0) is P  <=>  n mod (3m+4) in {0, m+2, 2m+3}, for 0 <= n <= nmax.
// Also counts m ≡ 7 mod 8 NOT satisfying the hypothesis where the pattern still holds (info only).
'use strict';
const v2 = x => { let c = 0; while (x > 0 && x % 2 === 0) { x /= 2; c++; } return c; };
const MMAX = +(process.argv[2] || 400), PER = +(process.argv[3] || 6);
let tested = 0, fails = 0;
for (let m = 7; m <= MMAX; m += 8) {
  const u = (m + 1) / 8, a = v2(9 * u + 1), b = v2(11 * u + 1);
  const hyp = (a === 1 && b === 3) || (a === 3 && b === 1);
  if (!hyp) continue;
  const L = 3 * m + 4, nmax = PER * L + m;
  // P[r][p] for p in 0..m ; win table via rows
  const P = [];
  for (let r = 0; r <= nmax; r++) {
    const row = new Uint8Array(m + 1);
    for (let p = 0; p <= m; p++) {
      let isP = 1;
      const kmax = Math.min(m, r);
      for (let k = 1; k <= kmax; k++) { if (k === p) continue; if (P[r - k][k]) { isP = 0; break; } }
      row[p] = isP;
    }
    P.push(row);
  }
  let ok = true;
  for (let n = 0; n <= nmax; n++) {
    const c = n % L, pred = c === 0 || c === m + 2 || c === 2 * m + 3;
    if (!!P[n][0] !== pred) { ok = false; console.log(`FAIL m=${m} n=${n}`); break; }
  }
  tested++; if (!ok) fails++;
  console.log(`m=${m} u=${u} v2(9u+1)=${a} v2(11u+1)=${b} n<=${nmax} ${ok ? 'OK' : 'FAIL'}`);
}
console.log(`tested=${tested} fails=${fails}`);
