/*
 * check_k19_k20_k26_r.js — 定理 K19・K20・K26 が予言する型を、漸化式 R の状態の繰り返しで直接求めた型と照合する
 *
 * 何を計算するか:
 *   5 ≤ m ≤ MMAX について、次の予言（どれも前周期なし）を作る。
 *     K19：v2(m+1) = 1、r = v2(h−1)（h = (m+1)/2）が奇数で r = 2j+1 なら、周期 1^{j+1} 0
 *     K20：v2(m+1) = 3、ℓ = v2(5m+13) が 6 以上の偶数で ℓ = 2i なら、i が奇数のとき周期 1^{i−1} 0、偶数のとき 1^{i−1} 0 0
 *     K26：v2(m+1) = 3、u = (m+1)/8、v2(5u+1) = 1、p = v2((11u+1)/2) とし、p = 1 かつ m ≥ 71 なら周期 1 0、
 *          p が 30 以下の偶数なら周期 1 0 0（coverage.js と同じ範囲）
 *   block_rule.js の periods で状態が繰り返すまで計算し、ブロック 0 から「前周期 + 状態の周期の 2 回分」の間隔の列が
 *   予言の周期のくり返しと一致し、状態の周期が予言の周期の倍数かを調べる（check_k29_k38_r.js と同じ判定）。
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k19_k20_k26_r.js 20000 > data/check_k19_k20_k26_r.txt
 */
'use strict';
const { periods, nextBlock } = require('./block_rule');
const MMAX = +(process.argv[2] || 20000);
const v2 = x => { if (x === 0) return 99; let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const st = { K19: [0, 0], K20: [0, 0], K26: [0, 0] }; const bad = [];
for (let m = 5; m <= MMAX; m += 2) {
  const v = v2(m + 1); let want = null, which = null;
  if (v === 1) { const r = v2((m + 1) / 2 - 1); if (r % 2 === 1 && r < 99) { const j = (r - 1) / 2; want = '1'.repeat(j + 1) + '0'; which = 'K19'; } }
  else if (v === 3) {
    const l = v2(5 * m + 13);
    if (l >= 6 && l % 2 === 0) { const i = l / 2; want = '1'.repeat(i - 1) + (i % 2 === 1 ? '0' : '00'); which = 'K20'; }
    else { const u = (m + 1) / 8; if (v2(5 * u + 1) === 1) { const p = v2((11 * u + 1) / 2); if (p === 1 && m >= 71) { want = '10'; which = 'K26'; } else if (p % 2 === 0 && p <= 30) { want = '100'; which = 'K26'; } } }
  }
  if (!want) continue;
  const r = periods(m); let pv = null, seq = ''; const len = r.preBlocks + 2 * r.periodBlocks;
  for (let j = 0; j < len; j++) { pv = nextBlock(m, pv); seq += pv.g === m + 2 ? 1 : 0; }
  const good = r.periodBlocks % want.length === 0 && seq === want.repeat(Math.ceil(len / want.length)).slice(0, len);
  st[which][0]++; if (!good) { st[which][1]++; if (bad.length < 10) bad.push(`m=${m}（${which}）`); }
}
console.log(['# 定理 K19・K20・K26 の型と、R の状態の繰り返しで求めた型の照合', `# 生成: node code/check_k19_k20_k26_r.js ${MMAX}`,
  ...Object.entries(st).map(([k, [n, b]]) => `${k} の対象: ${n} 個、食い違い: ${b}`), bad.length ? '食い違いの例: ' + bad.join('、') : '食い違いなし'].join(String.fromCharCode(10)));
