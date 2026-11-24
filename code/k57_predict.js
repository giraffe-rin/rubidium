/*
 * k57_predict.js — 一般の族 q·a + r = s·2^N、m = 3a − 2 で、ブロック 0（K3）からの h の一本道の鎖を b の軌道で記号的に追い、間隔の列の先頭を予測する（命題 K57）
 *
 * 何を計算するか:
 *   定理 K47 の鎖の記述を一般の (q, r) にしたものを使う：鎖の距離 d = (αa − c)/2^K、β = rα + qc とすると r(αa − c) = βa − c·s·2^N。
 *   h は c = 1、α = 3、K = 1、β = 3r + q。奇数の点での b = β/2^K は T(b) = (b + 3r)/2^{t(b)}、t(b) = v2(b + 3r) で動く。
 *   ブロック i（g_0..g_{i−1} = m+2 と仮定）の h の鎖はブロック 0 まで i 回の奇数の段をたどり、終点の v2 は t(b_i) − 1、
 *   段数は s_i = (v2(β_0) − 1) + i + Σ_{j<i}(t(b_j) − 1)。v2(β) が N 未満のあいだ（終点の v2(β) = K_i + t(b_i) < N）、
 *   g_i = m+2 ⇔ [終点の v2 が偶数（K3 で入る）] XOR [s_i が奇数] が「入らない」の反対、つまり h ∈ S_i ⇔ (終点で入る) ≠ (s_i が奇数)。
 *   予測は、最初に g_i = m+1 となる i か、v2(β) が N に達して予測できなくなる i まで行う（その間の (M+d)/2 ≤ m と d ≠ h − 1 は確かめない：数値と比べる）。
 *   引数の各族 q:r:s:N について、予測した先頭の間隔の列と、gapsBig（lazy_bigint.js）で求めた実際の列を比べる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k57_predict.js 29:4641:1:56 29:4641:1:112 29:4641:1:224 29:4641:1:336 17:5:3:30 17:5:3:62 23:1:1:22 23:1:1:88 125:1:1:100 125:1:1:200 random:300:12345 > data/k57_predict.txt
 *   引数 random:個数:種 で無作為な族を加える。
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const v2 = x => { x = x < 0n ? -x : x; let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 命題 K57：ブロック 0 からの h の鎖の b の軌道による間隔の列の先頭の予測', '# 生成: node --stack-size=65500 code/k57_predict.js ' + process.argv.slice(2).join(' '),
  'q | r | s | N | v | 予測した先頭（最初の m+1 まで、または予測が尽きるまで） | 実際の先頭 | 一致'];
let tot = 0, ok = 0;
// 引数 random:個数:種 は、無作為な族（q は 3..255 の奇数、|r| は 5000 以下の奇数、N は 40..119、s は a が正の奇数になる最小の正の奇数）に展開する
const args = []; for (const x of process.argv.slice(2)) { if (!x.startsWith('random:')) { args.push(x); continue; }
  const [, cnt, sd] = x.split(':').map(Number); let seed = sd; const rnd = n => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % n; }; let k = 0;
  while (k < cnt) { const q = BigInt(2 * rnd(127) + 3), r = BigInt(2 * rnd(2500) + 1) * (rnd(2) ? 1n : -1n), N = 40 + rnd(80), X = 2n ** BigInt(N);
    for (let s = 1n; s < 2n * q; s += 2n) if ((s * X - r) % q === 0n) { const a = (s * X - r) / q; if (a > 0n && a % 2n === 1n) { args.push(q + ':' + r + ':' + s + ':' + N); k++; } break; } } }
for (const arg of args) {
  const [q, r, s] = arg.split(':').slice(0, 3).map(BigInt), N = +arg.split(':')[3];
  const X = 2n ** BigInt(N); if ((s * X - r) % q !== 0n) { out.push(`${arg}：割り切れない`); continue; }
  const a = (s * X - r) / q, m = 3n * a - 2n; if (a % 2n === 0n) { out.push(`${arg}：a が偶数`); continue; }
  const beta0 = 3n * r + q, v = v2(beta0);
  const R3 = 3n * r, T = b => { let x = b + R3, t = 0; while (x % 2n === 0n) { x /= 2n; t++; } return [x, t]; };
  // ブロック 0：h ∈ S_0 ⇔ v2(h) = v − 1 が偶数
  let pred = (v - 1) % 2 === 0 ? '1' : '0';
  if (pred === '1') {
    let b = beta0 / 2n ** BigInt(v), K = v, sPar = (v - 1), stopped = false;   // 奇数の点の b と K、段数（ここまでの半分にする段）
    const bs = [], Ks = [];
    for (let i = 1; i < 400; i++) {
      // ブロック i の鎖：奇数の点は b_1..b_i（ブロック i, i−1, …, 1）。b_j は i によらない（同じ h から）
      bs.push(b); Ks.push(K);
      const [nb, t] = T(b);
      const endV2beta = K + t; if (endV2beta >= N) { stopped = true; break; }
      // 段数の偶奇：(v − 1) + i + Σ_{j<i}(t_j − 1)
      let sp = (v - 1) + i; for (let j = 0; j < i - 1; j++) sp += T(bs[j])[1] - 1;
      const inB = (t - 1) % 2 === 0; const hin = inB !== (sp % 2 === 1);
      pred += hin ? '1' : '0';
      if (!hin) break;
      K += t; b = nb;
    }
    if (stopped) pred += '…';
  }
  const J = pred.replace('…', '').length + 2, g = gapsBig(m, J, 5e7).gaps;
  const p = pred.replace('…', ''), same = g.slice(0, p.length) === p;
  tot++; if (same) ok++;
  out.push(`${q} | ${r} | ${s} | ${N} | ${v} | ${pred.replace(/1+/g, x => x.length > 2 ? '1^' + x.length : x)} | ${g.slice(0, p.length + 1).replace(/1+/g, x => x.length > 2 ? '1^' + x.length : x)} | ${same ? 'はい' : 'いいえ'}`);
}
out.push('', `${tot} 個中 ${ok} 個で予測した部分が一致`);
console.log(out.join('\n'));
