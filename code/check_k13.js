/*
 * check_k13.js — 定理 K13（「100」型の条件）を実装 C で確かめる
 *
 * 何を計算するか:
 *   v2(m+1) = 3 の各 m（m+1 = 8u、m ≤ M）で、a = v2(9u+1)、b = v2(11u+1) がどちらも奇数のもの
 *   （K10c より、このとき g₁ = g₂ = m+1）について、
 *   A 行の間隔が「m+2, m+1, m+1」の繰り返し（100 型）になるかを、n ≤ min(NMAX, F·(m+2)) で調べる。
 *   K13：{a, b} = {1, 3} なら 100 型。これとの食い違いを数え、max(a, b) ごとの集計を出す。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k13.js 8000 100 2000000 > data/k13_check.txt
 */
'use strict';
const C = require('./solver_rowtype');
const M = +(process.argv[2] || 8000), F = +(process.argv[3] || 100), NMAX = +(process.argv[4] || 2000000);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const tab = {}; const fails = []; let n = 0;
for (let m = 7; m <= M; m += 8) {
  if (v2(m + 1) !== 3) continue;
  const u = (m + 1) / 8, a = v2(9 * u + 1), b = v2(11 * u + 1);
  if (a % 2 === 0 || b % 2 === 0) continue;
  const N = Math.min(NMAX, F * (m + 2));
  const ty = C.types(m, N);
  const A = []; for (let k = 1; k <= N; k++) if (ty[k] === 0) A.push(k);
  const g = A.map((x, i) => x - (i ? A[i - 1] : 0) - (m + 1));
  let is100 = true; for (let i = 0; i < g.length; i++) if (g[i] !== (i % 3 === 0 ? 1 : 0)) { is100 = false; break; }
  if (Math.min(a, b) === 1 && Math.max(a, b) === 3 && !is100) fails.push(`m=${m}`);
  const key = `max(v2(9u+1), v2(11u+1))=${Math.max(a, b)} 100 型=${is100 ? 'はい' : 'いいえ'}`;
  tab[key] = (tab[key] || 0) + 1; n++;
}
const out = ['# 定理 K13 の検証（v2(m+1) = 3、v2(9u+1) と v2(11u+1) がどちらも奇数の m、実装 C による）', `# 生成: node code/check_k13.js ${M} ${F} ${NMAX}`,
  `調べた m: ${n} 個。K13 との食い違い: ${fails.length === 0 ? 'なし' : fails.join(', ')}`, '集計:'];
for (const k of Object.keys(tab).sort()) out.push(`  ${k}: ${tab[k]}`);
process.stdout.write(out.join('\n') + '\n');
