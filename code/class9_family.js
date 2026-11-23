/*
 * class9_family.js — m ≡ 9 (mod 32)（v2(m+1) = 1）の類で、型の周期が伸び続ける族 m = 3a − 2、a = (15·2^N + 5)/13 を調べる
 *
 * 何を計算するか:
 *   (1) k = 8..KMAX について、2^{k−1} < m ≤ 2^k、m ≡ 9 (mod 32) での、ブロック 20〜299 の m+2 の連の最大と、それを実現する最小の m
 *       （type_vs_t.js の gapsLazy）
 *   (2) N ≡ 2 (mod 12)、14 ≤ N ≤ NMAX で a = (15·2^N + 5)/13、m = 3a − 2 とし、lazy_bigint.js の gapsBig（400 ブロック）から
 *       前周期 p、周期 L と、間隔の列の連の長さの並びを出す
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/class9_family.js 23 146 > data/class9_family.txt
 */
'use strict';
const { gapsLazy } = require('./type_vs_t');
const { gapsBig } = require('./lazy_bigint');
const [KMAX, NMAX] = process.argv.slice(2).map(Number);
const per = g => { for (let L = 1; L <= g.length / 3; L++) for (let p = 0; p <= 80; p++) { if (g.length - p < 3 * L) break; let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; } if (ok) return [p, L]; } return null; };
const rl = s => s.match(/1+|0+/g).map(r => r[0] + '^' + r.length).join(' ');
const out = ['# m ≡ 9 (mod 32) の類の m+2 の連と、周期が伸び続ける族', `# 生成: node --stack-size=65500 code/class9_family.js ${KMAX} ${NMAX}`, '', '## (1) k | 2^{k−1} < m ≤ 2^k の m ≡ 9 (mod 32) での m+2 の連の最大 | 実現する最小の m'];
for (let k = 8; k <= KMAX; k++) { let best = -1, bm = 0; for (let m = 2 ** (k - 1) + ((9 - 2 ** (k - 1) % 32) % 32 + 32) % 32; m <= 2 ** k; m += 32) { const g = gapsLazy(m, 300); let run = 0, R = 0; for (let j = 20; j < 300; j++) { if (g[j] === 1) { run++; if (run > R) R = run; } else run = 0; } if (R > best) { best = R; bm = m; } } out.push(`${k} | ${best} | ${bm}`); }
out.push('', '## (2) N | m mod 32 | 前周期 p | 周期 L | 連の並び（前周期 | 周期）');
for (let N = 14; N <= NMAX; N += 12) {
  const a = (15n * 2n ** BigInt(N) + 5n) / 13n, m = 3n * a - 2n; const g = gapsBig(m, 400, 8000000).gaps; const pl = per(g);
  out.push(`${N} | ${m % 32n} | ${pl ? pl[0] : '?'} | ${pl ? pl[1] : '?'} | ${pl ? (pl[0] ? rl(g.slice(0, pl[0])) + ' | ' : '') + rl(g.slice(pl[0], pl[0] + pl[1])) : '400 ブロックでは推測できない'}`);
}
console.log(out.join(String.fromCharCode(10)));
