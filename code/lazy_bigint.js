/*
 * lazy_bigint.js — ブロック漸化式 R の遅延評価の BigInt 版と、予想 K33・K34 の族の照合
 *
 * 何を計算するか:
 *   gapsBig(m, J)：m（BigInt）について、ブロック 0〜J−1 の間隔（1 = m+2、0 = m+1）を、h から必要な (j, d) だけ遅延評価で求める。
 *     規則は block_rule.js の nextBlock と同じ（ブロック 0 は K3：d ∈ S_0 ⇔ v2(d) が偶数）。
 *     再帰を使わず、明示的なスタックで評価する（深い鎖でもスタックがあふれない）。
 *   CLI：
 *     selftest：m = 2..300 の 40 ブロックで nextBlock と一致するか
 *     k33 EMAX：e = 7..EMAX で m = 9·2^e + 1 の間隔の列が、予想 K33 の周期の 3 回分と一致するか
 *     k34 KMAX：k = 4..KMAX で m = 8(36·16^k − 1)/5 − 1 の間隔の列が、予想 K34 の周期の 3 回分と一致するか
 *     k35 KMAX：k = 2..KMAX で m = (3·16^k − 13)/5 の間隔の列が、定理 K35 の周期 1^{2k−1} 0 0 の 3 回分と一致するか
 * 実行方法（リポジトリのルートで）:
 *   node code/lazy_bigint.js selftest
 *   node code/lazy_bigint.js k33 200 > data/k33_bigint.txt
 *   node code/lazy_bigint.js k34 50 > data/k34_bigint.txt
 *   node code/lazy_bigint.js k35 60 > data/k35_bigint.txt
 */
'use strict';
function gapsBig(m, J, cap = Infinity) {   // cap：評価する事実の数の上限（超えたら例外）
  const h = (m + 1n) / 2n, odd = m % 2n === 1n;
  const memo = new Map(), gm = [];
  const key = (j, d) => j + ':' + d;
  const v2even = d => { let c = 0; while (d % 2n === 0n) { d /= 2n; c++; } return c % 2 === 0; };
  // S(j, d) を明示的なスタックで評価する。各フレームは段階 st を持つ。
  function S(j0, d0) {
    const k0 = key(j0, d0); if (memo.has(k0)) return memo.get(k0);
    const stack = [{ j: j0, d: d0, st: 0 }];
    let ret;
    while (stack.length) {
      if (memo.size > cap) throw new Error('事実が多すぎる');
      const f = stack[stack.length - 1]; const k = key(f.j, f.d);
      if (memo.has(k)) { ret = memo.get(k); stack.pop(); continue; }
      if (f.j === 0) { const r = v2even(f.d); memo.set(k, r); stack.pop(); ret = r; continue; }
      if (f.st === 0) {   // (i)
        f.st = 1;
        if (f.d % 2n === 0n) { const k2 = key(f.j, f.d / 2n); if (!memo.has(k2)) { stack.push({ j: f.j, d: f.d / 2n, st: 0 }); continue; } }
      }
      if (f.st === 1) {
        if (f.d % 2n === 0n && memo.get(key(f.j, f.d / 2n))) { memo.set(k, false); stack.pop(); ret = false; continue; }
        f.st = 2;
        // 1 つ前の間隔（ブロック j−1 で h が入るか）
        if (gm[f.j - 1] === undefined) { const kh = key(f.j - 1, h); if (!memo.has(kh)) { stack.push({ j: f.j - 1, d: h, st: 0 }); continue; } }
      }
      if (f.st === 2) {
        if (gm[f.j - 1] === undefined) gm[f.j - 1] = (odd && memo.get(key(f.j - 1, h))) ? m + 2n : m + 1n;
        const g = gm[f.j - 1], s = g + f.d; f.st = 3;
        if (s % 2n === 0n && s / 2n <= m) { const k2 = key(f.j - 1, s / 2n); if (!memo.has(k2)) { stack.push({ j: f.j - 1, d: s / 2n, st: 0 }); continue; } }
      }
      if (f.st === 3) {
        const g = gm[f.j - 1], s = g + f.d; let r = true;
        if (s % 2n === 0n && s / 2n <= m && memo.get(key(f.j - 1, s / 2n))) r = false;
        if (r && g === m + 2n && f.d === h - 1n) r = false;
        memo.set(k, r); stack.pop(); ret = r;
      }
    }
    return memo.get(k0);
  }
  const out = [];
  for (let j = 0; j < J; j++) { if (gm[j] === undefined) gm[j] = (odd && S(j, h)) ? m + 2n : m + 1n; out.push(gm[j] === m + 2n ? 1 : 0); }
  return { gaps: out.join(''), facts: memo.size };
}
module.exports = { gapsBig };
if (require.main === module) {
  const [mode, lim] = process.argv.slice(2);
  if (mode === 'selftest') {
    const { nextBlock } = require('./block_rule'); let bad = 0;
    for (let m = 2; m <= 300; m++) { let pv = null, s = ''; for (let j = 0; j < 40; j++) { pv = nextBlock(m, pv); s += pv.g === m + 2 ? 1 : 0; } if (gapsBig(BigInt(m), 40).gaps !== s) bad++; }
    console.log('m = 2..300、40 ブロックで nextBlock と食い違う m の個数: ' + bad);
  } else if (mode === 'k33' || mode === 'k34' || mode === 'k35') {
    const N = +lim; const out = [`# 予想 ${mode.toUpperCase()} の BigInt 版の遅延評価による照合（周期の 3 回分）`, `# 生成: node code/lazy_bigint.js ${mode} ${N}`, (mode === 'k33' ? 'e' : 'k') + ' | m の桁数（10 進）| 周期の長さ | 一致 | 評価した事実の数'];
    let ok = 0, ng = 0;
    for (let n = mode === 'k33' ? 7 : mode === 'k35' ? 2 : 4; n <= N; n++) {
      let m, per;
      if (mode === 'k33') { m = 9n * 2n ** BigInt(n) + 1n; per = n % 2 === 0 ? '1'.repeat(n / 2) + '0' : '1'.repeat(n - 1) + '0' + '1'.repeat((n - 1) / 2) + '0'; }
      else if (mode === 'k35') { m = (3n * 16n ** BigInt(n) - 13n) / 5n; per = '1'.repeat(2 * n - 1) + '00'; }
      else { m = 8n * (36n * 16n ** BigInt(n) - 1n) / 5n - 1n; per = '1'.repeat(4 * n + 2) + '0' + ('1'.repeat(2 * n + 1) + '00').repeat(2); }
      const r = gapsBig(m, 3 * per.length); const good = r.gaps === per.repeat(3); good ? ok++ : ng++;
      out.push(`${n} | ${m.toString().length} | ${per.length} | ${good ? '一致' : '不一致'} | ${r.facts}`);
    }
    out.push('', `一致 ${ok}、不一致 ${ng}`);
    console.log(out.join(String.fromCharCode(10)));
  }
}
