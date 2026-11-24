/*
 * check_k10.js — v2(m+1) = 3 の m の交互型を、実装 C（solver_rowtype.js）で調べる
 *
 * 何を計算するか:
 *   v2(m+1) = 3 の各 m（m+1 = 8u、u は奇数、m ≤ M）について、次を調べる。
 *   - A 行の間隔の列が「m+2, m+1, m+2, m+1, …」の交互型かどうか。
 *     A 行は開始局面 (n,0) が P になる n。n ≤ min(NMAX, PER·(2m+3)) の範囲で見る。
 *   - 最初の 8 個の間隔（ギャップ − (m+1) を 0/1 で）。
 *   - g₁ の予測（g₁ = m+2 ⇔ v2(9u+1) が偶数）が合うか。
 *   - 予想 K10（u ≡ 1 (mod 8) かつ u ≥ 9 なら交互型、u ≡ 3, 7 (mod 8) なら交互型でない）が合うか。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k10.js 1000 60 200000 > data/k10_v2eq3.txt
 *   引数: m の上限 M、周期 2m+3 を何周期分見るか PER、n の上限 NMAX
 */
'use strict';

const C = require('./solver_rowtype');
const M = +(process.argv[2] || 1000);
const PER = +(process.argv[3] || 60);
const NMAX = +(process.argv[4] || 200000);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };

const out = ['# v2(m+1) = 3 の m の交互型（実装 C による）', `# 生成: node code/check_k10.js ${M} ${PER} ${NMAX}`,
  '# 列: m | u | u mod 8 | v2(9u+1) | 調べた n の上限 | 交互型か | 最初の 8 個の間隔（ギャップ − (m+1)）'];
const fails = [];
let count = 0;
for (let m = 7; m <= M; m += 8) {
  if (v2(m + 1) !== 3) continue;
  const u = (m + 1) / 8;
  const N = Math.min(NMAX, PER * (2 * m + 3));
  const ty = C.types(m, N);
  const As = []; for (let n = 1; n <= N; n++) if (ty[n] === 0) As.push(n);
  const g = As.map((x, i) => x - (i ? As[i - 1] : 0) - (m + 1));
  let alt = true; for (let i = 0; i < g.length; i++) if (g[i] !== (i % 2 === 0 ? 1 : 0)) { alt = false; break; }
  const a = v2(9 * u + 1);
  if ((g[1] === 1) !== (a % 2 === 0)) fails.push(`g₁ の式 m=${m}`);
  if (u % 8 === 1 && u >= 9 && !alt) fails.push(`K10(u≡1) m=${m}`);
  if ((u % 8 === 3 || u % 8 === 7) && alt) fails.push(`K10(u≡3,7) m=${m}`);
  out.push(`m=${m} | ${u} | ${u % 8} | ${a} | ${N} | ${alt ? '交互型' : '—'} | ${g.slice(0, 8).join('')}`);
  count++;
}
out.push('');
out.push(`調べた m: ${count} 個。g₁ の式と予想 K10: ${fails.length === 0 ? '反例なし' : '反例 ' + fails.join(', ')}`);
process.stdout.write(out.join('\n') + '\n');
