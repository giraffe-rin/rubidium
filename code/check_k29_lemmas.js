/*
 * check_k29_lemmas.js — 定理 K29（すべての奇数 v ≥ 5）の手での証明の補題を、3 値の計算で確かめる
 *
 * 何を計算するか:
 *   k29_symbolic.js と同じ 3 値の計算（距離 c·u、1 ≤ c < 2^v、u ≡ 1 または 5 (mod 8)）で、ブロック 1〜L の S_n を求め、
 *   証明（notes/2026-11-23-claude-1-k29-proof.md）の補題を確かめる。
 *     補題 P_n（2 ≤ n ≤ L）：偶数 c で b = v2(c) ≤ 2n−3 なら、S_n[c] = 入る ⇔ b が偶数（不明にならない）。
 *     補題 Inh_n（2 ≤ n ≤ L）：偶数 c で 2n−2 ≤ b ≤ v−3 なら、S_n[c] = S_1[c]（3 値として等しい）。
 *     補題 E：2 ≤ n ≤ L−1 で S_n[2^{v−2}] = 入る。S_{L−1}[3·2^{v−2}] = 入らない。
 *     結論：S_n[2^{v−1}] は n ≤ L−1 で入らない、n = L で入る。
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k29_lemmas.js 21 > data/k29_lemmas.txt
 */
'use strict';
const T = 1, F = 0, U = 2;
const not = x => (x === U ? U : 1 - x);
const and = (x, y) => (x === F || y === F ? F : x === T && y === T ? T : U);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const VMAX = +(process.argv[2] || 21);
const out = ['# 定理 K29 の証明の補題の確認（3 値の計算）', `# 生成: node code/check_k29_lemmas.js ${VMAX}`, 'v | u mod 8 | P の違反 | Inh の違反 | 補題 E | 結論'];
for (let v = 5; v <= VMAX; v += 2) for (const u0 of [1, 5]) {
  const N = 2 ** v, H = N / 2, L = (v + 1) / 2; const S = [null];
  for (let n = 1; n <= L; n++) {
    const s = new Uint8Array(N);
    for (let c = 1; c < N; c++) {
      if (n === 1) s[c] = c % 2 === 1 ? (c % 4 === 1 ? F : (c === H - 1 && u0 === 1) ? U : ((c * u0 + 1) % 8 === 4 ? T : U)) : not(s[c / 2]);
      else s[c] = c % 2 === 1 ? T : and(not(s[c / 2]), not(S[n - 1][H + c / 2]));
    }
    S.push(s);
  }
  let p = 0, inh = 0;
  for (let n = 2; n <= L; n++) for (let c = 2; c < N; c += 2) {
    const b = v2(c);
    if (b <= 2 * n - 3) { if (S[n][c] !== (b % 2 === 0 ? T : F)) p++; }
    else if (b <= v - 3) { if (S[n][c] !== S[1][c]) inh++; }
  }
  let e = true; for (let n = 2; n <= L - 1; n++) if (S[n][H / 2] !== T) e = false; if (S[L - 1][3 * H / 2] !== F) e = false;
  let concl = true; for (let n = 1; n <= L; n++) if (S[n][H] !== (n === L ? T : F)) concl = false;
  out.push(`v=${v} | ${u0} | ${p} | ${inh} | ${e ? '成り立つ' : '成り立たない'} | ${concl ? '成り立つ' : '成り立たない'}`);
}
console.log(out.join('\n'));
