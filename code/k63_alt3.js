/*
 * k63_alt3.js — v2(m+1) = 3（m + 1 = 8u、u 奇数）、v2(9u+1) = 1、v2(11u+1) ≥ 4 の偶数の m が交互型かどうかを、
 *               漸化式 R（code/block_rule.js periods）で調べ、Y = (11u+1)/2^{v2(11u+1)} の剰余と比べる（予想 K63）
 *
 * 何を計算するか:
 *   u ≤ UMAX の各 u について block_rule.js periods m m を実行し、開始局面列の前周期 t と間隔の周期の語を読む。
 *   交互型 ⇔ t = 0 かつ周期の語が「10」（g₀ = m+2 なので、交互型ならこの形）。
 *   v2(11u+1) ごと・Y mod 4 ごとに、交互型の個数を数える。
 * 実行方法（リポジトリのルートで）:
 *   node code/k63_alt3.js 20000 > data/k63_alt3.txt
 */
'use strict';
const { execFileSync } = require('child_process'), path = require('path');
const UMAX = +process.argv[2];
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = ['# v2(m+1) = 3、v2(9u+1) = 1、v2(11u+1) ≥ 4 の偶数の m（u ≤ ' + UMAX + '）が交互型かどうか（漸化式 R による）', '# 生成: node code/k63_alt3.js ' + UMAX,
  'u | m | v2(11u+1) | Y mod 8（Y = (11u+1) の奇数部分） | 開始局面列の前周期 | 間隔の周期の語 | 交互型'];
const stat = {};
for (let u = 1; u <= UMAX; u += 2) {
  const e9 = v2(9 * u + 1), e11 = v2(11 * u + 1);
  if (e9 !== 1 || e11 < 4 || e11 % 2 !== 0) continue;
  const m = 8 * u - 1, Y = (11 * u + 1) / 2 ** e11;
  const s = execFileSync(process.execPath, ['--max-old-space-size=3000', path.join(__dirname, 'block_rule.js'), 'periods', String(m), String(m)], { encoding: 'utf8', maxBuffer: 1 << 26 });
  const line = s.split(/\r?\n/).find(x => x.startsWith('m='));
  const f = line.split('|'), t = +f[4].split(',')[0], word = f[5].trim();
  const alt = t === 0 && word === '10';
  const key = `v2(11u+1) = ${e11}、Y ≡ ${Y % 4} (mod 4)`;
  stat[key] = stat[key] || [0, 0]; stat[key][0]++; if (alt) stat[key][1]++;
  out.push(`${u} | ${m} | ${e11} | ${Y % 8} | ${t} | ${word.length > 40 ? word.slice(0, 40) + '…（長さ ' + word.length + '）' : word} | ${alt ? 'はい' : 'いいえ'}`);
}
out.push('', '## まとめ', '類 | 個数 | 交互型の個数');
for (const k of Object.keys(stat).sort()) out.push(`${k} | ${stat[k][0]} | ${stat[k][1]}`);
console.log(out.join('\n'));
