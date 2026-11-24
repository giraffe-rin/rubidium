/*
 * check_k9.js — 予想 K9（v2(m+1) = 1 のときの交互型の条件）を調べる
 *
 * 何を計算するか:
 *   v2(m+1) が奇数の各 m（3 ≤ m ≤ M）について、間隔 g_j が「m+2, m+1, m+2, m+1, …」の交互になるかを調べる。
 *   ここで g_j は A 行（すべての p で P になる行）の間隔。
 *   交互型 ⇔ 開始局面 (n,0) が P ⇔ n ≡ 0, m+2 (mod 2m+3)。
 *   2 通りの方法で調べる。
 *     (1) 漸化式 R（code/block_rule.js）の状態が繰り返すまで回す方法。すべての n を扱えるが、R の正しさ（[非形式証明] K8）が前提。
 *     (2) 全探索ソルバー（solver_dp.js と solver_retro.js の一致を確認）で、m ≤ MS, n ≤ NS の範囲を直接調べる方法。
 *   どちらも、予想 K9「v2(m+1) = 1 のとき、交互型 ⇔ v2(3h+1) が奇数（h = (m+1)/2）」と比べる。
 *   v2(m+1) ≥ 3 の m については、交互型かどうかの一覧だけを出す。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k9.js 400 100 10000 > data/k9_alternation.txt
 *   引数: R 経由で調べる m の上限 M、全探索で調べる m の上限 MS、全探索の n の上限 NS
 */
'use strict';

const R = require('./block_rule');
const A = require('./solver_dp');
const B = require('./solver_retro');

const M = +(process.argv[2] || 400);
const MS = +(process.argv[3] || 100);
const NS = +(process.argv[4] || 10000);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };

const out = [];
out.push('# 予想 K9 の検証（v2(m+1) が奇数の m について、A 行の間隔が m+2, m+1 の交互になるか）');
out.push(`# 生成: node code/check_k9.js ${M} ${MS} ${NS}`);

const altR = new Map();
for (let m = 3; m <= M; m += 2) {
  if (v2(m + 1) % 2 === 0) continue;
  const p = R.periods(m);
  let prev = null, alt = true;
  for (let j = 0; j < p.preBlocks + 2 * p.periodBlocks; j++) {
    prev = R.nextBlock(m, prev);
    if (prev.g !== (j % 2 === 0 ? m + 2 : m + 1)) { alt = false; break; }
  }
  altR.set(m, alt);
}

const fails = [];
for (const [m, alt] of altR) {
  if (v2(m + 1) !== 1) continue;
  const h = (m + 1) / 2;
  if (alt !== (v2(3 * h + 1) % 2 === 1)) fails.push(`R 経由 m=${m}`);
}

let checkedS = 0;
for (let m = 3; m <= MS; m += 2) {
  if (v2(m + 1) % 2 === 0) continue;
  const t = A.solve(m, NS), tb = B.solve(m, NS);
  for (let r = 0; r <= NS; r++) if (t[r] !== tb[r]) { console.error(`ソルバー不一致 m=${m} r=${r}`); process.exit(1); }
  let alt = true;
  for (let n = 1; n <= NS; n++) {
    const q = n % (2 * m + 3);
    if ((t[n][0] === 'P') !== (q === 0 || q === m + 2)) { alt = false; break; }
  }
  if (alt !== altR.get(m)) fails.push(`全探索と R が不一致 m=${m}`);
  if (v2(m + 1) === 1) {
    const h = (m + 1) / 2;
    if (alt !== (v2(3 * h + 1) % 2 === 1)) fails.push(`全探索 m=${m}`);
  }
  checkedS++;
}

out.push(`K9: ${fails.length === 0 ? '反例なし' : '反例 ' + fails.join(', ')}`);
out.push(`  範囲: v2(m+1) = 1 の 5 ≤ m ≤ ${M}（R 経由、すべての n）。全探索でも v2(m+1) 奇数の m ≤ ${MS}（${checkedS} 個）, n ≤ ${NS} を確認`);
const list = v => [...altR].filter(([m, a]) => a && v(m)).map(([m]) => m).join(', ');
out.push(`交互型の m（v2(m+1) = 1）: ${list(m => v2(m + 1) === 1)}`);
out.push(`交互型の m（v2(m+1) ≥ 3）: ${list(m => v2(m + 1) >= 3)}`);
out.push(`交互型でない m（v2(m+1) ≥ 3）: ${[...altR].filter(([m, a]) => !a && v2(m + 1) >= 3).map(([m]) => m).join(', ')}`);
process.stdout.write(out.join('\n') + '\n');
