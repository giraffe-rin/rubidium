/*
 * k29_cone.js — 定理 K29.3 の 3 値の計算で、ブロック L の h の所属を決めるのに使う (ブロック, c) の集まり（依存の範囲）を求める
 *
 * 何を計算するか:
 *   k29_symbolic.js と同じ 3 値の規則を、h = 2^{v−1}u（ブロック L）から必要な分だけ遅延評価し、参照した (ブロック n, c) を集める。
 *   v = 5, 7, …, VMAX と u ≡ 1, 5 (mod 8) について、参照した距離の個数と、ブロック 1 で参照した c の一覧を出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k29_cone.js 17 > data/k29_cone.txt
 */
'use strict';
const T = 1, F = 0, U = 2;
const not = x => (x === U ? U : 1 - x);
const VMAX = +(process.argv[2] || 17);
const out = ['# 定理 K29.3 の 3 値の計算の依存の範囲', `# 生成: node --stack-size=65500 code/k29_cone.js ${VMAX}`,
  'v | u mod 8 | h（ブロック L）| 参照した (ブロック, c) の個数 | 2^{L+1} − 3 | ブロック 1 で参照した c'];
for (let v = 5; v <= VMAX; v += 2) for (const u0 of [1, 5]) {
  const N = 2 ** v, H = N / 2, L = (v + 1) / 2; const memo = new Map();
  function val(n, c) {
    const k = n * N + c; if (memo.has(k)) return memo.get(k); let r;
    if (n === 1) {
      if (c % 2 === 1) r = c % 4 === 1 ? F : (c === H - 1 && u0 === 1) ? U : ((c * u0 + 1) % 8 === 4 ? T : U);
      else r = not(val(1, c / 2));
    } else if (c % 2 === 1) r = T;
    else {
      const a = val(n, c / 2);   // (i)
      if (a === T) r = F;
      else { const b = val(n - 1, H + c / 2); r = (a === F && b === F) ? T : (b === T ? F : U); }   // (ii)
    }
    memo.set(k, r); return r;
  }
  const r = val(L, H);
  const b1 = [...memo.keys()].filter(k => Math.floor(k / N) === 1).map(k => k % N).sort((a, b) => a - b);
  out.push(`v=${v} | ${u0} | ${r === T ? '入る' : r === F ? '入らない' : '不明'} | ${memo.size} | ${2 ** (L + 1) - 3} | ${b1.length <= 12 ? b1.join(',') : b1.slice(0, 12).join(',') + ',…（' + b1.length + ' 個）'}`);
}
console.log(out.join('\n'));
