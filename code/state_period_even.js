/*
 * state_period_even.js — v2(m+1) が偶数の m で、漸化式 R の状態 (S_j, g_j) の前周期と周期（ブロック数）を求める
 *
 * 何を計算するか:
 *   v2(m+1) が偶数の 2 ≤ m ≤ MMAX について、ブロック 1 の状態から始め、block_rule.js の nextBlock を写像 f として、
 *   Brent の周期検出法で状態の前周期 μ と周期 λ を求める（状態そのものを比べるので、ハッシュの衝突はない。メモリは状態 3 つ分）。
 *   f を合計 CAP 回より多く使うときは打ち切る。
 *   あわせて、調べたブロックの間隔がすべて m+1 か（定理 K4 の型）を調べる。
 *   出力：m ごとの状態の前周期（ブロック 1 から数えたブロック数）と周期、間隔がすべて m+1 だったか。
 * 実行方法（リポジトリのルートで）:
 *   node code/state_period_even.js 300 4000000 > data/state_period_even.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const [MMAX, CAP] = process.argv.slice(2).map(Number);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const eq = (a, b) => a.g === b.g && a.S.every((x, i) => x === b.S[i]);
const out = ['# v2(m+1) が偶数の m の、漸化式 R の状態の前周期と周期（ブロック 1 から数える）', `# 生成: node code/state_period_even.js ${MMAX} ${CAP}`, 'm | v2(m+1) | 状態の前周期 μ | 状態の周期 λ | 間隔がすべて m+1'];
for (let m = 2; m <= MMAX; m++) {
  if (v2(m + 1) % 2 === 1) continue;
  let calls = 0, allK4 = true;
  const f = x => { calls++; const y = nextBlock(m, x); if (y.g !== m + 1) allK4 = false; return y; };
  const x0 = f(nextBlock(m, null));   // ブロック 1
  let power = 1, lam = 1, t = x0, h = f(x0), over = false;
  while (!eq(t, h)) { if (calls > CAP) { over = true; break; } if (power === lam) { t = h; power *= 2; lam = 0; } h = f(h); lam++; }
  let mu = null;
  if (!over) { t = x0; h = x0; for (let i = 0; i < lam; i++) h = f(h); mu = 0; while (!eq(t, h)) { t = f(t); h = f(h); mu++; } }
  out.push(`${m} | ${v2(m + 1)} | ${over ? '−' : mu} | ${over ? '> ' + CAP + ' 回で打ち切り' : lam} | ${allK4 ? 'はい' : 'いいえ'}`);
}
console.log(out.join(String.fromCharCode(10)));
