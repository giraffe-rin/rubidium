/*
 * k58_shapes.js — 予想 K58（5a + 1 = 7·2^N、N ≡ 3 (mod 4)、周期 1^{R+2} 0 1^R 0、R = (N − 3)/2）の帰納法の 1 段の、自明でない評価木と
 *                 その中の O 型ブロックの鎖の形を書き出し、N によらないかを比べる
 *
 * 何を計算するか:
 *   周期の始まり B（ブロック 0）の事実は、一般の仮定（奇数は入る、v2 = 1 は入らない：補題 K33d）と仮定 2(a − 7) ∉ S_B。
 *   E 型ブロック（R+3 と L = 2R+4）では、奇数の距離は入り、v2 = 1 の距離は入らない（自明）。それ以外（v2 ≥ 2）は E 型の規則で評価する。
 *   O 型ブロックに入った距離は、一本道で 1 つ前の E 型ブロック（B か R+3）まで進め（例外 (M+d)/2 > m、d = h − 1 はそこで値を決める）、
 *   そこでの値から決める。評価するのは、h の各ブロックでの値（g_1..g_L）と、仮定 2(a − 7) のブロック L での値。
 *   出力（N ごと）：
 *     - 評価が周期 w と仮定に一致するか。
 *     - 自明でない E 型の事実（何番目の E 型ブロックか、距離の a の 1 次式、値）。
 *     - E 型ブロックの評価から入った O 型の鎖のそれぞれについて、入口の形、鎖の長さ（ブロック数）、
 *       各奇数の段の後の「半分にする段の数」の列の連長表示、終点の v2 と値。
 *   引数に複数の N を与え、最後に「自明でない事実の集合が同じか」「鎖の形（連長表示の値の列）が同じで、連の長さの差が R の差の整数倍か」を比べる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k58_shapes.js $(seq 43 4 199) > data/k58_shapes.txt
 */
'use strict';
const v2 = x => { x = x < 0n ? -x : x; if (x === 0n) return 999; let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 予想 K58 の帰納法の 1 段の自明でない評価木と鎖の形', '# 生成: node --stack-size=65500 code/k58_shapes.js ' + process.argv.slice(2).join(' ')];
const results = [];
for (const N of process.argv.slice(2).map(Number)) {
  if (N % 4 !== 3) { out.push(`N = ${N}：N ≡ 3 (mod 4) でない`); continue; }
  const X = 2n ** BigInt(N), a = (7n * X - 1n) / 5n, m = 3n * a - 2n, M = m + 2n, h = (m + 1n) / 2n, R = (N - 3) / 2, L = 2 * R + 4;
  const w = '1'.repeat(R + 2) + '0' + '1'.repeat(R) + '0';
  const gap = i => w[((i % L) + L) % L];
  const form = d => { for (let k = 0n; k <= 10n; k++) { const t = d * 2n ** k; const P = (t + a / 2n) / a; const Q = t - P * a; if (Q > -(2n ** 24n) && Q < 2n ** 24n) return `(${P}a${Q < 0n ? '−' + (-Q) : '+' + Q})/2^${k}`; } return '大'; };
  const A = 2n * (a - 7n);
  const eIndex = i => (i === 0 || i === L ? 'B' : i === R + 3 ? 'E1' : '?');
  const memo = new Map(), nontriv = new Set(), chains = [];
  // E 型ブロック i での値（i は 0 か R+3 か L）
  const E = (i, d) => {
    const key = 'E' + i + ':' + d; if (memo.has(key)) return memo.get(key); let r;
    const t = v2(d);
    if (t === 0) r = true; else if (t === 1) r = false;
    else if (i === 0) { if (d === A) r = false; else throw new Error('B での不明な距離 ' + form(d)); }
    else { r = !E(i, d / 2n) && !(h + d / 2n <= m && O(i - 1, h + d / 2n, i)); nontriv.add(`${eIndex(i)}：${form(d)}（v2 ${t}）${r ? '入' : '不'}`); }
    memo.set(key, r); return r;
  };
  // O 型ブロック i での値：一本道で 1 つ前の E 型ブロックまで
  const O = (i, d, fromE) => {
    const key = 'O' + i + ':' + d; if (memo.has(key)) return memo.get(key);
    let j = i, dd = d, st = 0, r, cur = 0; const ts = [];
    while (gap(j - 1) === '1') {
      if (dd % 2n === 0n) { dd /= 2n; cur++; }
      else { if (dd === h - 1n) { r = st % 2 === 0 ? false : true; break; } if ((M + dd) / 2n > m) { r = st % 2 === 0; break; }
        if (ts.length || cur) ts.push(cur); cur = 0; dd = (M + dd) / 2n; j--; }
      st++;
    }
    if (r === undefined) { const b = E(j, dd); r = st % 2 === 0 ? b : !b; ts.push(cur); }
    const rle = []; for (const x of ts) { if (rle.length && rle[rle.length - 1][0] === x) rle[rle.length - 1][1]++; else rle.push([x, 1]); }
    if (fromE !== undefined) chains.push({ from: eIndex(fromE), entry: form(d), len: i - j, rle, endV2: v2(dd), val: r });
    memo.set(key, r); return r;
  };
  // h の各ブロック
  let ok = true;
  for (let i = 1; i <= L; i++) { const x = gap(i - 1) === '1' ? O(i, h) : E(i, h); if ((x ? '1' : '0') !== w[i % L]) ok = false; }
  if (E(L, A) !== false) ok = false;
  results.push({ N, R, nontriv: [...nontriv].sort(), chains });
  out.push('', `## N = ${N}（R = ${R}、L = ${L}）：1 段が閉じる ${ok ? 'はい' : 'いいえ'}`, '自明でない E 型の事実：', ...[...nontriv].sort().map(x => '  ' + x), 'E 型の評価から入った鎖：',
    ...chains.map(c => `  ${c.from} の評価から：入口 ${c.entry}、長さ ${c.len}、半分にする段の連長 ${c.rle.map(([x, k]) => x + '×' + k).join(' ')}、終点の v2 ${c.endV2}、値 ${c.val ? '入' : '不'}`));
}
// 比較
if (results.length >= 2) {
  const r0 = results[0]; let sameNT = true, sameShape = true;
  for (const r of results.slice(1)) {
    if (r.nontriv.join('|') !== r0.nontriv.join('|')) sameNT = false;
    if (r.chains.length !== r0.chains.length) { sameShape = false; continue; }
    r.chains.forEach((c, k) => { const c0 = r0.chains[k]; const dR = r.R - r0.R;
      if (c.entry !== c0.entry || c.endV2 !== c0.endV2 || c.val !== c0.val || c.rle.length !== c0.rle.length) { sameShape = false; return; }
      c.rle.forEach(([x, n], q) => { const [x0, n0] = c0.rle[q]; const dn = n - n0; if (x !== x0 || !(dn === 0 || (dR !== 0 && dn % dR === 0))) sameShape = false; }); });
  }
  out.push('', '## 比較', `自明でない E 型の事実の集合がすべての N で同じ：${sameNT ? 'はい' : 'いいえ'}`, `鎖の入口・終点・値と、連長表示の値の列がすべての N で同じで、連の長さの差が R の差の整数倍：${sameShape ? 'はい' : 'いいえ'}`);
}
console.log(out.join('\n'));
