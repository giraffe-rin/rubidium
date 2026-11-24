/*
 * k48_runs.js — 補題 K48（直前に m+1 が z ≥ ρ/2 個続く位置から始まる m+2 の連の長さはちょうど R = ⌈(N−v)/ρ⌉）を数値で確かめる
 *
 * 何を計算するか:
 *   奇数 v = 5..VMAX、偶数 ρ = 2..v−1、q = 2^v − 2^ρ + 1、r = (2^ρ − 1)/3、偶数 N = v+ρ+1..NMAX で、
 *   q·a + r = s·2^N（s は最小の正の奇数で、a が奇数になるもの）、m = 3a − 2 とする（定理 K47 の族）。
 *   gapsBig（lazy_bigint.js）で J = max(400, 8N) ブロックの間隔を求め、ブロック 1..J−R−1 のすべての位置 B で、
 *   g_{B−z} = … = g_{B−1} = m+1（z = ρ/2。左端はブロック 0 まで）かつ g_B = m+2 なら、
 *   g_B, …, g_{B+R−1} = m+2、g_{B+R} = m+1 となっているかを調べる。
 *   あわせて、ブロック J/2 以降（周期の部分とみなす）に、そのような位置が現れるかを数える。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k48_runs.js 11 120 > data/k48_runs.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const VMAX = +(process.argv[2] || 11), NMAX = +(process.argv[3] || 120);
const out = ['# 補題 K48：0^z 1（z = ρ/2）の後の m+2 の連の長さ', '# 生成: node --stack-size=65500 code/k48_runs.js ' + VMAX + ' ' + NMAX,
  'v | ρ | N の個数 | 調べた位置 | 主張と違う位置 | 後半（ブロック J/2 以降）に位置がある N の個数'];
let totalPos = 0, totalBad = 0;
for (let v = 5; v <= VMAX; v += 2) for (let rho = 2; rho < v; rho += 2) {
  const q = 2n ** BigInt(v) - 2n ** BigInt(rho) + 1n, r = (2n ** BigInt(rho) - 1n) / 3n, z = rho / 2;
  let nN = 0, pos = 0, bad = 0, late = 0; const badEx = [];
  for (let N = v + rho + 1; N <= NMAX; N += 1) {
    if (N % 2) continue;
    let s = 1n; while ((s * 2n ** BigInt(N) - r) % q !== 0n) s += 2n;
    const a = (s * 2n ** BigInt(N) - r) / q, m = 3n * a - 2n, R = Math.ceil((N - v) / rho);
    const J = Math.max(400, 8 * N), g = gapsBig(m, J, 5e7).gaps; nN++; let seenLate = false;
    for (let B = z; B + R < J; B++) {
      if (g[B] !== '1') continue; let ok = true; for (let j = 1; j <= z; j++) if (g[B - j] !== '0') { ok = false; break; } if (!ok) continue;
      pos++; if (B >= J / 2) seenLate = true;
      const run = g.slice(B, B + R) === '1'.repeat(R) && g[B + R] === '0';
      if (!run) { bad++; if (badEx.length < 3) badEx.push(`N = ${N}, B = ${B}`); }
    }
    if (seenLate) late++;
  }
  totalPos += pos; totalBad += bad;
  out.push(`${v} | ${rho} | ${nN} | ${pos} | ${bad}${badEx.length ? '（' + badEx.join('; ') + '）' : ''} | ${late}`);
}
out.push('', `合計：調べた位置 ${totalPos}、主張と違う位置 ${totalBad}`);
console.log(out.join('\n'));
