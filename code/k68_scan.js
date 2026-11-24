/*
 * k68_scan.js — v2(m+1) = 3 で Lean で型が決まっていない u の類（u mod 64）を u mod 512 に分け、型が一定の類を探す
 * 実行方法（リポジトリのルートで）: node code/k68_scan.js 12000
 */
'use strict';
const { execFileSync } = require('child_process'), path = require('path');
const UMAX = +process.argv[2];
const out = ['# v2(m+1) = 3、u mod 64 ∈ {3,7,23,29,35,39,45,51,55} を u mod 512 で分けた型（漸化式 R、u ≤ ' + UMAX + '）'];
for (const c of [3, 7, 23, 29, 35, 39, 45, 51, 55]) for (let s = 0; s < 8; s++) {
  const r = c + 64 * s; const types = new Map();
  for (let u = r; u <= UMAX; u += 512) {
    const m = 8 * u - 1;
    const line = execFileSync(process.execPath, [path.join(__dirname, 'block_rule.js'), 'periods', String(m), String(m)], { encoding: 'utf8' }).split(/\r?\n/).find(l => l.startsWith('m='));
    const f = line.split('|'), t = +f[4].split(',')[0], w = f[5].trim(); const key = (t === 0 ? '' : 'pre ') + w;
    types.set(key, (types.get(key) || 0) + 1);
  }
  const e = [...types.entries()];
  out.push(`u ≡ ${r} (mod 512): ` + (e.length === 1 ? '一定 ' : '') + e.map(([k, n]) => `${k}×${n}`).join(', '));
}
console.log(out.join('\n'));
