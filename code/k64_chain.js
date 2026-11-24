/*
 * k64_chain.js — 予想 K64 の確認：v2(m+1) = 1、v2(3h+1) = 2（3h+1 = 4w）のとき、X₀ = Q = (m+2+w)/2、X_{i+1} = (m+2+X_i/2)/2 とおく。
 *                v2(X₀) = … = v2(X_{j−1}) = 1 で X_j が奇数なら、型は 1^{j+2} 0（前周期なし）か
 *
 * 何を計算するか: m ≤ MMAX の対象の各 m で、上の j を求め、漸化式 R（code/block_rule.js periods）の型と比べる。
 *   m ≤ DPMAX では、R を使わない直接の DP（(r, p) が P ⇔ A_r ⊆ {p}）でも n ≤ 3L まで確かめる。
 * 実行方法（リポジトリのルートで）: node code/k64_chain.js 40000 4000 > data/k64_chain.txt
 */
'use strict';
const { execFileSync } = require('child_process'), path = require('path');
const [MMAX, DPMAX] = process.argv.slice(2).map(Number);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = ['# 予想 K64：v2(m+1) = 1、v2(3h+1) = 2、Q 偶数のときの型（m ≤ ' + MMAX + '、直接の DP は m ≤ ' + DPMAX + '）', '# 生成: node code/k64_chain.js ' + process.argv.slice(2).join(' '),
  'm | j | 予想の型 | R による型（前周期） | 一致 | 直接の DP'];
const st = {};
for (let m = 5; m <= MMAX; m += 4) {
  const h = (m + 1) / 2; if (v2(3 * h + 1) !== 2) continue;
  const w = (3 * h + 1) / 4; let X = (m + 2 + w) / 2, j = 0;
  while (v2(X) === 1) { X = (m + 2 + X / 2) / 2; j++; }
  if (v2(X) !== 0 || j === 0) continue;
  const exp = '1'.repeat(j + 2) + '0';
  const line = execFileSync(process.execPath, [path.join(__dirname, 'block_rule.js'), 'periods', String(m), String(m)], { encoding: 'utf8' }).split(/\r?\n/).find(l => l.startsWith('m='));
  const f = line.split('|'), t = +f[4].split(',')[0], word = f[5].trim(), ok = t === 0 && word === exp;
  let dp = '-';
  if (m <= DPMAX) {
    const L = (j + 2) * (m + 2) + (m + 1), N = 3 * L; const typ = new Int32Array(N + 1); typ[0] = -1; const isP = (r, p) => typ[r] === -1 || typ[r] === p;
    for (let r = 1; r <= N; r++) { let c = 0, kk = 0; for (let x = 1; x <= Math.min(m, r) && c < 2; x++) if (isP(r - x, x)) { c++; kk = x; } typ[r] = c === 0 ? -1 : c === 1 ? kk : -2; }
    const Ps = new Set(); for (let i = 0; i <= j + 2; i++) Ps.add(i * (m + 2)); let good = true; for (let n = 0; n <= N; n++) if (isP(n, 0) !== Ps.has(n % L)) { good = false; break; }
    dp = good ? '一致' : '不一致';
  }
  st[j] = st[j] || [0, 0, 0]; st[j][0]++; if (ok) st[j][1]++; if (dp === '一致') st[j][2]++;
  out.push(`${m} | ${j} | ${exp} | ${word}（${t}） | ${ok ? 'はい' : 'いいえ'} | ${dp}`);
}
out.push('', '## まとめ（j：対象の数、R で一致、直接の DP で一致）', ...Object.entries(st).map(([j, [n, a, b]]) => `j=${j}：${n} 個、R で一致 ${a}、直接の DP で一致 ${b}`));
console.log(out.join('\n'));
