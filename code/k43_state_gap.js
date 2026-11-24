/*
 * k43_state_gap.js — v2(m+1) が奇数の m で、漸化式 R の状態の周期 λ が、間隔の列（型）の周期 L と等しいかを調べる（観察 K43）
 *
 * 何を計算するか:
 *   v2(m+1) が奇数の 3 ≤ m ≤ MMAX について、ブロック 1 から Brent の周期検出法で状態の前周期 μ と周期 λ を求める（CAP 回で打ち切り）。
 *   ブロック 0 から μ + 2λ + 1 ブロックの間隔の列を求め、ブロック μ+1 以降の列の最小の周期 L を求める（λ の約数を調べる）。
 *   λ = L か、L が λ の真の約数かを数え、比 λ/L の分布を出す。
 * 実行方法（リポジトリのルートで）:
 *   node code/k43_state_gap.js 3000 2000000 > data/k43_state_gap.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const [MMAX, CAP] = process.argv.slice(2).map(Number);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const eq = (a, b) => a.g === b.g && a.S.every((x, i) => x === b.S[i]);
function brent(m) { let calls = 0; const f = x => { calls++; return nextBlock(m, x); }; const x0 = f(nextBlock(m, null)); let power = 1, lam = 1, t = x0, h = f(x0);
  while (!eq(t, h)) { if (calls > CAP) return null; if (power === lam) { t = h; power *= 2; lam = 0; } h = f(h); lam++; }
  t = x0; h = x0; for (let i = 0; i < lam; i++) h = f(h); let mu = 0; while (!eq(t, h)) { t = f(t); h = f(h); mu++; } return [mu, lam]; }
const st = {}; const ex = []; const ratio = {}; let maxLam = 0, maxMu = 0, cut = 0;
for (let m = 3; m <= MMAX; m += 2) {
  const v = v2(m + 1); if (v % 2 === 0) continue; const r = brent(m); if (!r) { cut++; continue; }
  const [mu, lam] = r; if (lam > maxLam) maxLam = lam; if (mu > maxMu) maxMu = mu;
  let pv = null; const g = []; for (let j = 0; j <= mu + 1 + 2 * lam; j++) { pv = nextBlock(m, pv); g.push(pv.g === m + 2 ? 1 : 0); }
  const tail = g.slice(mu + 1); let L = lam; for (let d = 1; d <= lam; d++) if (lam % d === 0 && tail.every((x, i) => i + d >= tail.length || x === tail[i + d])) { L = d; break; }
  const k = v >= 5 ? '≥5' : String(v); (st[k] = st[k] || [0, 0]); st[k][0]++; ratio[lam / L] = (ratio[lam / L] || 0) + 1; if (L !== lam) { st[k][1]++; if (ex.length < 10) ex.push(`m=${m}（λ=${lam}, L=${L}）`); }
}
console.log(['# v2(m+1) が奇数の m：状態の周期 λ と間隔の列の周期 L', `# 生成: node code/k43_state_gap.js ${MMAX} ${CAP}`,
  ...Object.entries(st).map(([k, [n, b]]) => `v2(m+1) = ${k}: ${n} 個、λ ≠ L: ${b}`), `打ち切り: ${cut}、λ の最大: ${maxLam}、μ の最大: ${maxMu}`, `λ/L の分布: ${Object.entries(ratio).sort((a, b) => a[0] - b[0]).map(([r, c]) => r + ': ' + c).join('、')}`, ex.length ? 'λ ≠ L の例: ' + ex.join('、') : 'λ ≠ L の例なし'].join(String.fromCharCode(10)));
