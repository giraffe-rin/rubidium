/*
 * k29_symbolic.js — 予想 K29 の、u によらない 3 値の証明書（v ごと）
 *
 * 何を計算するか:
 *   v2(m+1) = v（≥ 5 の奇数）、u = (m+1)/2^v ≡ 1 (mod 4)、m = 2^v u − 1、h = 2^{v−1}u とする。
 *   距離 c·u（1 ≤ c ≤ 2^v − 1）だけを考え、ブロック漸化式 R を「入る／入らない／不明」の 3 値で計算する
 *   （証明は notes/2026-11-23-claude-1-k29-general.md）。
 *     O 型のブロック（1 つ前の間隔 m+2）：
 *       奇数の c：(ii) の e = ((2^v + c)u + 1)/2。c ≡ 1 (mod 4) なら e は奇数で、1 つ前のブロック（K3 か E 型）に必ず入るので「入らない」。
 *                 c ≡ 3 (mod 4) なら e は偶数で、u の深い桁によるので「不明」（(iii) の h − 1 = (2^{v−1} − 1)u（u = 1）もここに入る）。
 *       偶数の c：(i) だけ。c·u ∈ ⇔ (c/2)·u ∉。
 *     E 型のブロック（1 つ前の間隔 m+1 = 2^v u）：
 *       奇数の c：入る。偶数の c：(c/2)u ∉ かつ (2^{v−1} + c/2)u ∉（1 つ前のブロック）のとき入る。
 *   O 型のブロックの計算は、1 つ前のブロックの奇数の距離 e が入ることだけを使うので、ブロック 1 とブロック qL+1（q ≥ 1）で同じになる。
 *   よって、ブロック 1〜L（L = (v+1)/2）を 3 値で計算し、h = 2^{v−1}u が「ブロック 1〜L−1 で入らない、ブロック L で入る」と
 *   決まれば、すべての u ≡ 1 (mod 4) で型が 1 0^{L−1} になる。
 * 実行方法（リポジトリのルートで）:
 *   node --max-old-space-size=4096 code/k29_symbolic.js 27 > data/k29_symbolic.txt
 */
'use strict';
const VMAX = +(process.argv[2] || 21);
const T = 1, F = 0, U = 2;   // 入る / 入らない / 不明
const not = x => (x === U ? U : 1 - x);
const and = (x, y) => (x === F || y === F ? F : x === T && y === T ? T : U);
const out = ['# 予想 K29 の、u によらない 3 値の証明書（u ≡ 1, 5 (mod 8) の 2 通り）', `# 生成: node code/k29_symbolic.js ${VMAX}`, 'v | u mod 8 | L | h の所属（ブロック 1〜L）| 結果 | 不明の距離の個数（ブロック 1〜L）'];
for (let v = 5; v <= VMAX; v += 2) for (const u0 of [1, 5]) {
  const N = 2 ** v, L = (v + 1) / 2, H = N / 2;
  let prev = null; const hs = [], unk = [];
  for (let n = 1; n <= L; n++) {
    const S = new Uint8Array(N);
    const O = n === 1;   // ブロック 1 だけが O 型（ブロック 2〜L は E 型）
    for (let c = 1; c < N; c++) {
      if (O) {
        if (c % 2 === 1) S[c] = c % 4 === 1 ? F : (c === H - 1 && u0 === 1) ? U : ((c * u0 + 1) % 8 === 4 ? T : U);
        else S[c] = not(S[c / 2]);
      } else {
        if (c % 2 === 1) S[c] = T;
        else S[c] = and(not(S[c / 2]), not(prev[H + c / 2]));
      }
    }
    hs.push(S[H]); let k = 0; for (let c = 1; c < N; c++) if (S[c] === U) k++; unk.push(k);
    prev = S;
  }
  const ok = hs.every((x, i) => x === (i === L - 1 ? T : F));
  out.push(`v=${v} | ${u0} | ${L} | ${hs.map(x => (x === T ? '入' : x === F ? '外' : '?')).join('')} | ${ok ? '成功' : '失敗'} | ${unk.join(',')}`);
}
console.log(out.join('\n'));
