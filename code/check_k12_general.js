/*
 * check_k12_general.js — 予想 K12′（「1(10)^k」型）と定理 K12″ を実装 C で確かめる
 *
 * 何を計算するか:
 *   v2(m+1) = 1、v2(3h+1) = 2k（k ≥ 2）の各 m（h = (m+1)/2、m ≤ M）について、
 *   w = (3h+1)/2^{2k}、Q_k = (m+2+w)/2 を計算する。
 *   A 行の間隔 g_j − (m+1) の列が、周期 2k+1 の「1 (10)^k」の繰り返しになるかを n ≤ min(NMAX, F·(m+2)) で調べる。
 *   さらに g₂ を調べる。
 *   K12″ (a)（k = 2）：Q₂ が奇数 ⇒ 11010 型。
 *   K12″ (b)（k ≥ 2、m ≠ 9）：g₂ = m+2 ⇔ v2(Q_k) が奇数。
 *   これらとの食い違いを数え、(k, v2(Q_k), 型かどうか) ごとの集計を出す。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k12_general.js 8000 12 1500000 > data/k12_general_check.txt
 *   （第 2 引数 F は「周期の長さ (m+2) + k(2m+3) の何倍まで調べるか」）
 */
'use strict';

const C = require('./solver_rowtype');
const M = +(process.argv[2] || 8000);
const F = +(process.argv[3] || 12);
const NMAX = +(process.argv[4] || 1500000);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };

const tab = {}; const fails = []; let n = 0;
for (let m = 5; m <= M; m += 4) {
  if (v2(m + 1) !== 1) continue;
  const h = (m + 1) / 2;
  const a = v2(3 * h + 1);
  if (a % 2 === 1 || a < 4) continue;
  const k = a / 2, L = 2 * k + 1;
  const N = Math.min(NMAX, F * ((m + 2) + k * (2 * m + 3)));
  const ty = C.types(m, N);
  const A = []; for (let x = 1; x <= N; x++) if (ty[x] === 0) A.push(x);
  const g = A.map((x, i) => x - (i ? A[i - 1] : 0) - (m + 1));
  let ok = true;
  for (let i = 0; i < g.length; i++) { const r = i % L; if (g[i] !== (r === 0 || r % 2 === 1 ? 1 : 0)) { ok = false; break; } }
  const w = (3 * h + 1) / 2 ** a;
  const Q = (m + 2 + w) / 2;
  if (!Number.isInteger(Q)) fails.push(`Q が整数でない m=${m}`);
  const q = v2(Q);
  if (k === 2 && q === 0 && !ok) fails.push(`K12″(a) m=${m}`);
  if (m !== 9 && (g[2] === 1) !== (q % 2 === 1)) fails.push(`K12″(b) m=${m}`);
  const key = `k=${k} v2(Q_k)=${q >= 3 ? '3 以上' : q} 型=${ok ? 'はい' : 'いいえ'}`;
  tab[key] = (tab[key] || 0) + 1; n++;
}
const out = ['# 予想 K12′・定理 K12″ の検証（v2(m+1) = 1、v2(3h+1) = 2k ≥ 4 の m、実装 C による）',
  `# 生成: node code/check_k12_general.js ${M} ${F} ${NMAX}`,
  `調べた m: ${n} 個。K12″ (a)(b) との食い違い: ${fails.length === 0 ? 'なし' : fails.join(', ')}`,
  '集計（k、v2(Q_k)、「1(10)^k」型かどうか）:'];
for (const key of Object.keys(tab).sort()) out.push(`  ${key}: ${tab[key]}`);
process.stdout.write(out.join('\n') + '\n');
