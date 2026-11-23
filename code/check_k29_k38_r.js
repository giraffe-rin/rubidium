/*
 * check_k29_k38_r.js — 定理 K29・K38 が予言する型を、漸化式 R の状態の繰り返しで直接求めた型と照合する
 *
 * 何を計算するか:
 *   v2(m+1) = v ≥ 5（奇数）の 5 ≤ m ≤ MMAX について、u = (m+1)/2^v、w = v2(u+1) とする。
 *     K29：u ≡ 1 (mod 4) なら、前周期なし、周期 1 0^{(v−1)/2}（周期 (v+1)/2 ブロック）
 *     K38：w が奇数で 3 ≤ w ≤ v−2、または w ≥ v+1 なら、前周期なし、周期 1 0^{(v+1)/2}（周期 (v+3)/2 ブロック）
 *   block_rule.js の periods で状態が繰り返すまで計算し、前周期のブロック数 preBlocks と周期のブロック数 periodBlocks を求める。
 *   nextBlock で、ブロック 0 から「前周期 + 状態の周期の 2 回分」の間隔の列を求め、予言の周期のくり返しと一致するか、
 *   状態の周期が予言の周期の倍数かを調べる。状態が繰り返したあとは間隔の列も繰り返すので、これで型が予言どおりと確定する。
 *   注意：状態の周期は、型（間隔の列）の周期の倍数になることがある。
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k29_k38_r.js 200000 > data/check_k29_k38_r.txt
 */
'use strict';
const { periods, nextBlock } = require('./block_rule');
const MMAX = +(process.argv[2] || 200000);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
let n29 = 0, b29 = 0, n38 = 0, b38 = 0; const bad = [];
for (let m = 31; m <= MMAX; m += 2) {
  const v = v2(m + 1); if (v < 5 || v % 2 === 0) continue;
  const u = (m + 1) / 2 ** v, w = v2(u + 1); let want = null, which = null;
  if (u % 4 === 1) { want = '1' + '0'.repeat((v - 1) / 2); which = 'K29'; }
  else if ((w % 2 === 1 && w >= 3 && w <= v - 2) || w >= v + 1) { want = '1' + '0'.repeat((v + 1) / 2); which = 'K38'; }
  if (!want) continue;
  const r = periods(m); let pv = null, seq = ''; const len = r.preBlocks + 2 * r.periodBlocks;
  for (let j = 0; j < len; j++) { pv = nextBlock(m, pv); seq += pv.g === m + 2 ? 1 : 0; }
  // 状態が繰り返すまでの範囲（前周期 + 状態の周期の 2 回分）で、間隔の列がブロック 0 から want のくり返しであること。
  // 状態の周期は型の周期の倍数になりうる（そのときも間隔の列は want のくり返し）。
  const good = r.periodBlocks % want.length === 0 && seq === want.repeat(Math.ceil(len / want.length)).slice(0, len);
  if (which === 'K29') { n29++; if (!good) b29++; } else { n38++; if (!good) b38++; }
  if (!good && bad.length < 10) bad.push(`m=${m}（${which}）`);
}
console.log(['# 定理 K29・K38 の型と、R の状態の繰り返しで求めた型の照合', `# 生成: node code/check_k29_k38_r.js ${MMAX}`,
  `K29 の対象: ${n29} 個、食い違い: ${b29}`, `K38 の対象: ${n38} 個、食い違い: ${b38}`, bad.length ? '食い違いの例: ' + bad.join('、') : '食い違いなし'].join(String.fromCharCode(10)));
