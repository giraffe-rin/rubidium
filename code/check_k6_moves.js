/*
 * check_k6_moves.js — 定理 K6 の補足「先手の必勝手」（訂正版）を全探索で確かめる
 *
 * 何を計算するか:
 *   m ≡ 5 (mod 8)、m ≤ MMAX について、局面 (r, p) の勝敗を全探索で求め（r ≤ NMAX）、
 *   開始局面 (n, 0)、c = n mod (2m+3) ∉ {0, m+2} で、次の手 k が合法かつ相手を P 局面に移すかを調べる。
 *     旧版：0 < c < m+2 なら k = c、m+2 < c なら k = c − (m+2)
 *     訂正版：0 < c ≤ m なら k = c、c = m+1 なら k = (m+1)/2、m+2 < c なら k = c − (m+2)
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k6_moves.js 101 3000 > data/k6_moves_check.txt
 */
'use strict';
const MMAX = +(process.argv[2] || 101), NMAX = +(process.argv[3] || 3000);
const out = ['# 定理 K6 の補足「先手の必勝手」の確認（全探索）', `# 生成: node code/check_k6_moves.js ${MMAX} ${NMAX}`, 'm | 調べた n | 旧版の誤り（非合法または P に移らない）| 訂正版の誤り'];
let tot = [0, 0, 0];
for (let m = 5; m <= MMAX; m += 8) {
  // P[r][p]：局面 (r, p) が P か
  const P = []; for (let r = 0; r <= NMAX; r++) { P.push(new Uint8Array(m + 1));
    for (let p = 0; p <= m; p++) { let win = false; for (let k = 1; k <= Math.min(m, r) && !win; k++) if (k !== p && P[r - k][k]) win = true; P[r][p] = win ? 0 : 1; } }
  const ok = (n, k) => k >= 1 && k <= Math.min(m, n) && P[n - k][k] === 1;
  let cnt = 0, bad0 = 0, bad1 = 0;
  for (let n = 1; n <= NMAX; n++) { const c = n % (2 * m + 3); if (c === 0 || c === m + 2) continue; cnt++;
    const k0 = c < m + 2 ? c : c - (m + 2); const k1 = c <= m ? c : c === m + 1 ? (m + 1) / 2 : c - (m + 2);
    if (!ok(n, k0)) bad0++; if (!ok(n, k1)) bad1++; }
  out.push(`${m} | ${cnt} | ${bad0} | ${bad1}`); tot[0] += cnt; tot[1] += bad0; tot[2] += bad1;
}
out.push(`合計 | ${tot[0]} | ${tot[1]} | ${tot[2]}`);
console.log(out.join('\n'));
