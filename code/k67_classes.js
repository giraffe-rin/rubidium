/*
 * k67_classes.js — 予想 K67 の確認：m + 1 = 8u で、u ≡ 13, 19, 61 (mod 64) のとき型はそれぞれ 10、11100、100 か
 *
 * 何を計算するか: u ≤ UMAX の各類の u で、漸化式 R（code/block_rule.js periods）の型を求めて予想の型と比べる。
 *   u ≤ DPMAX では、R を使わない直接の DP（(r, p) が P ⇔ A_r ⊆ {p}）で n ≤ 3L まで確かめる。
 * 実行方法（リポジトリのルートで）: node code/k67_classes.js 40000 600 > data/k67_classes.txt
 */
'use strict';
const { execFileSync } = require('child_process'), path = require('path');
const [UMAX, DPMAX] = process.argv.slice(2).map(Number);
const CL = { 13: '10', 19: '11100', 61: '100' };
const out = ['# 予想 K67：m + 1 = 8u、u ≡ 13, 19, 61 (mod 64) の型（u ≤ ' + UMAX + '、直接の DP は u ≤ ' + DPMAX + '）', '# 生成: node code/k67_classes.js ' + process.argv.slice(2).join(' ')];
for (const [c, word] of Object.entries(CL)) {
  let tot = 0, ok = 0, dpT = 0, dpOk = 0; const bad = [];
  for (let u = +c; u <= UMAX; u += 64) {
    const m = 8 * u - 1;
    const line = execFileSync(process.execPath, [path.join(__dirname, 'block_rule.js'), 'periods', String(m), String(m)], { encoding: 'utf8' }).split(/\r?\n/).find(l => l.startsWith('m='));
    const f = line.split('|'), t = +f[4].split(',')[0], w = f[5].trim();
    tot++; if (t === 0 && w === word) ok++; else bad.push(u);
    if (u <= DPMAX) {
      const gaps = [...word].map(ch => ch === '1' ? m + 2 : m + 1), L = gaps.reduce((s, x) => s + x, 0), N = 3 * L;
      const Ps = new Set([0]); let x = 0; for (const g of gaps.slice(0, -1)) { x += g; Ps.add(x); }
      const typ = new Int32Array(N + 1); typ[0] = -1; const isP = (r, p) => typ[r] === -1 || typ[r] === p;
      for (let r = 1; r <= N; r++) { let cc = 0, kk = 0; for (let k = 1; k <= Math.min(m, r) && cc < 2; k++) if (isP(r - k, k)) { cc++; kk = k; } typ[r] = cc === 0 ? -1 : cc === 1 ? kk : -2; }
      let good = true; for (let n = 0; n <= N; n++) if (isP(n, 0) !== Ps.has(n % L)) { good = false; break; }
      dpT++; if (good) dpOk++;
    }
  }
  out.push(`u ≡ ${c} (mod 64)、予想の型 ${word}：${tot} 個中 ${ok} 個が R で一致、直接の DP で ${dpT} 個中 ${dpOk} 個が一致` + (bad.length ? `（外れ u = ${bad.slice(0, 10).join(', ')}）` : ''));
}
console.log(out.join('\n'));
