/*
 * k42_renorm.js — v2(m+1) = v が 2 以上の偶数の奇数 m で、漸化式 R の状態の周期 λ(m) が、偶数 m' = u − 1（u = (m+1)/2^v）の
 *                 状態の周期 λ(m') と等しいかを調べる（予想 K42）
 *
 * 何を計算するか:
 *   v ∈ {2, 4, 6}、奇数 u（3 ≤ u ≤ UMAX）について m = 2^v u − 1 とし、ブロック 1 から Brent の周期検出法で状態の前周期 μ と周期 λ を求める
 *   （state_period_even.js と同じ方法。f の呼び出しが CAP 回を超えたら打ち切る）。m' = u − 1 についても同じく求め、比べる。
 * 実行方法（リポジトリのルートで）:
 *   node code/k42_renorm.js 101 3000000 > data/k42_renorm.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const [UMAX, CAP] = process.argv.slice(2).map(Number);
const eq = (a, b) => a.g === b.g && a.S.every((x, i) => x === b.S[i]);
function brent(m) {
  let calls = 0; const f = x => { calls++; return nextBlock(m, x); };
  const x0 = f(nextBlock(m, null)); let power = 1, lam = 1, t = x0, h = f(x0);
  while (!eq(t, h)) { if (calls > CAP) return null; if (power === lam) { t = h; power *= 2; lam = 0; } h = f(h); lam++; }
  t = x0; h = x0; for (let i = 0; i < lam; i++) h = f(h); let mu = 0; while (!eq(t, h)) { t = f(t); h = f(h); mu++; }
  return [mu, lam];
}
const out = ['# 予想 K42：λ(2^v u − 1) = λ(u − 1) か', `# 生成: node code/k42_renorm.js ${UMAX} ${CAP}`, 'u | λ(u−1) | v=2: μ, λ | v=4: μ, λ | v=6: μ, λ | 一致'];
let ok = 0, ng = 0, skip = 0;
for (let u = 3; u <= UMAX; u += 2) {
  const base = brent(u - 1); const res = [2, 4, 6].map(v => brent(2 ** v * u - 1));
  if (!base || res.some(r => !r)) { skip++; out.push(`${u} | ${base ? base[1] : '打ち切り'} | ${res.map(r => r ? r.join(', ') : '打ち切り').join(' | ')} | −`); continue; }
  const good = res.every(r => r[1] === base[1] && r[0] === 0); good ? ok++ : ng++;
  out.push(`${u} | ${base[1]} | ${res.map(r => r.join(', ')).join(' | ')} | ${good ? 'はい' : 'いいえ'}`);
}
out.push('', `一致 ${ok}、不一致 ${ng}、打ち切り ${skip}`);
console.log(out.join(String.fromCharCode(10)));
