/*
 * k7_check_dp.js — 予想 K7 の確認：block_rule.js periods（漸化式 R による）が出した開始局面列の前周期・周期を、R を使わない直接の DP で確かめる
 *
 * 何を計算するか:
 *   A_r = {k : 1 ≤ k ≤ min(m, r)、(r − k, k) が P}。PROBLEM.md の定義から、(r, p) が P ⇔ A_r ⊆ {p}。
 *   よって各行 r の P の集合は「すべての p」（A_r が空）、「p = k だけ」（A_r = {k}）、「なし」（|A_r| ≥ 2）のどれかで、O(m) で求まる。
 *   block_rule.js の出力の行（m=… | v2 | … | 開始局面列の前周期 t, 周期 L | …）を読み、n ≤ NMAX までの開始局面列 P(n) = 「(n, 0) が P」について
 *   t < n ≤ NMAX − L のすべての n で P(n) = P(n + L)、かつ（t > 0 なら）P(t) ≠ P(t + L) を確かめる。NMAX = t + 4L + 10。
 * 実行方法（リポジトリのルートで）:
 *   node code/k7_check_dp.js data/k7_periods_201-400.txt > data/k7_check_dp.txt
 */
'use strict';
const fs = require('fs');
const out = ['# 予想 K7：漸化式 R による開始局面列の前周期・周期を、直接の DP で確かめる', '# 生成: node code/k7_check_dp.js ' + process.argv.slice(2).join(' '), 'm | 前周期 t | 周期 L | 確かめた n の上限 | 結果'];
let ok = 0, tot = 0;
for (const l of fs.readFileSync(process.argv[2], 'utf8').split(/\r?\n/)) {
  const f = l.split('|'); if (!f[0].startsWith('m=')) continue;
  const m = +f[0].slice(2), [t, L] = f[4].split(',').map(x => +x.trim());
  const NMAX = t + 4 * L + 10;
  // typ[r]：-1 = すべての p で P、-2 = P なし、k ≥ 1 = p = k のときだけ P（r ≥ 1 では p = 0 は「すべて」のときだけ）
  const typ = new Int32Array(NMAX + 1); typ[0] = -1;
  const isP = (r, p) => typ[r] === -1 || typ[r] === p;
  for (let r = 1; r <= NMAX; r++) {
    let cnt = 0, kk = 0;
    for (let k = 1; k <= Math.min(m, r) && cnt < 2; k++) if (isP(r - k, k)) { cnt++; kk = k; }
    typ[r] = cnt === 0 ? -1 : cnt === 1 ? kk : -2;
  }
  const S = n => isP(n, 0);
  let good = true;
  for (let n = t + 1; n + L <= NMAX; n++) if (S(n) !== S(n + L)) { good = false; break; }
  if (good && t > 0 && S(t) === S(t + L)) good = false;
  tot++; if (good) ok++;
  out.push(`${m} | ${t} | ${L} | ${NMAX} | ${good ? '一致' : '不一致'}`);
}
out.push('', `${tot} 個の m のうち ${ok} 個で一致`);
console.log(out.join('\n'));
