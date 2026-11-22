/*
 * check_k12.js — 定理 K12（「110」型の条件）を実装 C で確かめる
 *
 * 何を計算するか:
 *   v2(m+1) = 1、v2(3h+1) = 2 の各 m（h = (m+1)/2、m ≤ M）について Q = (11h+5)/8 を計算する。
 *   A 行の間隔が「m+2, m+2, m+1」の繰り返し（110 型）になるかを、n ≤ min(NMAX, F·(m+2)) で調べる。
 *   さらに、ブロック 2 の間隔 g₂ を調べる。
 *   K12 (a)：Q が奇数 ⇒ 110 型。
 *   K12 (b)：g₂ = m+2 ⇔ v2(Q) が奇数。
 *   これらとの食い違いを数え、v2(Q) ごとの集計を出す。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k12.js 6000 200 3000000 > data/k12_check.txt
 */
'use strict';

const C = require('./solver_rowtype');
const M = +(process.argv[2] || 6000);
const F = +(process.argv[3] || 200);
const NMAX = +(process.argv[4] || 3000000);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };

const tab = {}; const fails = []; let n = 0;
for (let m = 5; m <= M; m += 4) {
  if (v2(m + 1) !== 1) continue;
  const h = (m + 1) / 2;
  if (v2(3 * h + 1) !== 2) continue;
  const N = Math.min(NMAX, F * (m + 2));
  const ty = C.types(m, N);
  const A = []; for (let k = 1; k <= N; k++) if (ty[k] === 0) A.push(k);
  const g = A.map((x, i) => x - (i ? A[i - 1] : 0) - (m + 1));
  let is110 = true; for (let i = 0; i < g.length; i++) if (g[i] !== (i % 3 === 2 ? 0 : 1)) { is110 = false; break; }
  const Q = (11 * h + 5) / 8;
  if (!Number.isInteger(Q)) fails.push(`Q が整数でない m=${m}`);
  const q = v2(Q);
  if (q === 0 && !is110) fails.push(`K12(a) m=${m}`);
  if ((g[2] === 1) !== (q % 2 === 1)) fails.push(`K12(b) m=${m}`);
  const key = `v2(Q)=${q >= 4 ? '4 以上' : q} 110 型=${is110 ? 'はい' : 'いいえ'}`;
  tab[key] = (tab[key] || 0) + 1; n++;
}
const out = ['# 定理 K12 の検証（v2(m+1) = 1、v2(3h+1) = 2 の m、実装 C による）', `# 生成: node code/check_k12.js ${M} ${F} ${NMAX}`,
  `調べた m: ${n} 個。K12 (a)(b) との食い違い: ${fails.length === 0 ? 'なし' : fails.join(', ')}`, '集計（v2(Q) と 110 型かどうか）:'];
for (const k of Object.keys(tab).sort()) out.push(`  ${k}: ${tab[k]}`);
process.stdout.write(out.join('\n') + '\n');
