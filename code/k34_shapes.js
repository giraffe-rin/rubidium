/*
 * k34_shapes.js — 定理 K47 の族の v = 3、ρ = 2、N 奇数（5a + 1 = s·2^N）の帰納法の 1 段の、自明でない評価木と O 型ブロックの鎖の形を書き出し、
 *                 N によらないかを比べる（k58_shapes.js の一般化：E 型ブロックが続く場合も扱う）
 *
 * 何を計算するか:
 *   s = 3（N ≡ 1 (mod 4)、予想 K34、周期 1^{2R} 0 (1^R 0 0)^2）または s = 7（N ≡ 3 (mod 4)、定理 K58、周期 1^{R+2} 0 1^R 0）、R = (N − 3)/2。
 *   周期の始まり B の事実は、一般の仮定（奇数は入る、v2 = 1 は入らない：補題 K33d）と仮定の集合 A（s = 3：2(a − 3)、3(a − 3) は入らない／入る ― 値は prove3 で
 *   得たもの、s = 7：2(a − 7) は入らない）。E 型ブロックでは、奇数は入り v2 = 1 は入らない（自明）、それ以外は E 型の規則で評価する。
 *   E 型の規則の第 2 項 h + d/2 は、1 つ前のブロックが E 型ならそこで、O 型なら一本道で 1 つ前の E 型ブロックまで進めて評価する。
 *   評価するのは、h の各ブロックでの値と、A の各距離の次の周期の始まり（ブロック L）での値。
 *   出力（N ごと）：1 段が閉じるか、自明でない E 型の事実（何番目の E 型ブロックか、距離、値）、E 型の評価から入った O 型の鎖の形
 *   （入口、長さ、各奇数の段の後に半分にする段の数の列の連長表示、終点の v2、値）。最後に、すべての N で集合と形が同じかを比べる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k34_shapes.js $(seq 41 2 201) > data/k34_shapes.txt
 */
'use strict';
const { prove3 } = require('./period_induction');
const v2 = x => { x = x < 0n ? -x : x; if (x === 0n) return 999; let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# v = 3、ρ = 2、N 奇数の族の帰納法の 1 段の自明でない評価木と鎖の形', '# 生成: node --stack-size=65500 code/k34_shapes.js ' + process.argv.slice(2).join(' ')];
const results = { 3: [], 7: [] };
for (const N of process.argv.slice(2).map(Number)) {
  const s = N % 4 === 1 ? 3n : N % 4 === 3 ? 7n : null; if (!s) continue;
  const X = 2n ** BigInt(N), a = (s * X - 1n) / 5n, m = 3n * a - 2n, M = m + 2n, h = (m + 1n) / 2n, R = (N - 3) / 2;
  const w = s === 3n ? '1'.repeat(2 * R) + '0' + ('1'.repeat(R) + '00').repeat(2) : '1'.repeat(R + 2) + '0' + '1'.repeat(R) + '0', L = w.length;
  const pr = prove3(m, '', w, 20000, 20000000); const Aval = new Map(pr.Aset.map(([d, val]) => [BigInt(d), val]));
  const gap = i => w[((i % L) + L) % L];
  const eBlocks = []; for (let i = 1; i <= L; i++) if (gap(i - 1) === '0') eBlocks.push(i);
  const eName = i => (i === 0 || i === L ? 'B' : eBlocks.includes(i) ? 'E' + (eBlocks.indexOf(i) + 1) : 'O 型ブロック（例外で止まった）');
  const form = d => { for (let k = 0n; k <= 10n; k++) { const t = d * 2n ** k; const P = (t + a / 2n) / a; const Q = t - P * a; if (Q > -(2n ** 24n) && Q < 2n ** 24n) return `(${P}a${Q < 0n ? '−' + (-Q) : '+' + Q})/2^${k}`; } return '大'; };
  const memo = new Map(), nontriv = new Set(), chains = [];
  const isE = i => i === 0 || gap(i - 1) === '0';
  const E = (i, d) => {
    if (i === L) i = L; const key = 'E' + i + ':' + d; if (memo.has(key)) return memo.get(key); let r;
    const t = v2(d);
    if (t === 0) r = true; else if (t === 1) r = false;
    else if (i === 0) { if (Aval.has(d)) r = Aval.get(d); else throw new Error('B での不明な距離 ' + form(d)); }
    else { const e = h + d / 2n; r = !E(i, d / 2n) && !(e <= m && (isE(i - 1) ? E(i - 1, e) : O(i - 1, e, i))); nontriv.add(`${eName(i)}：${form(d)}（v2 ${t}）${r ? '入' : '不'}`); }
    memo.set(key, r); return r;
  };
  const O = (i, d, fromE) => {
    const key = 'O' + i + ':' + d; if (memo.has(key)) return memo.get(key);
    let j = i, dd = d, st = 0, r, cur = 0; const ts = [];
    while (!isE(j)) {
      if (dd % 2n === 0n) { dd /= 2n; cur++; }
      else { if (dd === h - 1n) { r = st % 2 === 0 ? false : true; break; } if ((M + dd) / 2n > m) { r = st % 2 === 0; break; }
        ts.push(cur); cur = 0; dd = (M + dd) / 2n; j--; }
      st++;
    }
    if (r === undefined) { const b = E(j, dd); r = st % 2 === 0 ? b : !b; ts.push(cur); }
    const rle = []; for (const x of ts) { if (rle.length && rle[rle.length - 1][0] === x) rle[rle.length - 1][1]++; else rle.push([x, 1]); }
    if (fromE !== undefined) chains.push({ from: eName(fromE), entry: form(d), to: eName(j), len: i - j, rle, endV2: v2(dd), val: r });
    memo.set(key, r); return r;
  };
  let ok = pr.ok;
  for (let i = 1; i <= L; i++) { const x = isE(i) ? E(i, h) : O(i, h); if ((x ? '1' : '0') !== w[i % L]) ok = false; }
  for (const [d, val] of Aval) if (E(L, d) !== val) ok = false;
  const ntList = [...nontriv].sort();
  results[s].push({ N, R, ok, nontriv: ntList, chains });
  out.push('', `## N = ${N}（s = ${s}、R = ${R}、L = ${L}、E 型ブロック ${eBlocks.length}）：1 段が閉じる ${ok ? 'はい' : 'いいえ'}、仮定 ${[...Aval].map(([d, val]) => form(d) + (val ? '入' : '不')).join(' ')}`,
    `自明でない E 型の事実（${ntList.length}）：`, ...ntList.map(x => '  ' + x), `E 型の評価から入った鎖（${chains.length}）：`,
    ...chains.map(c => `  ${c.from} の評価から ${c.to} まで：入口 ${c.entry}、長さ ${c.len}、半分にする段の連長 ${c.rle.map(([x, k]) => x + '×' + k).join(' ')}、終点の v2 ${c.endV2}、値 ${c.val ? '入' : '不'}`));
}
out.push('', '## 比較');
for (const s of [3, 7]) {
  const rs = results[s]; if (rs.length < 2) continue; const r0 = rs[0]; let allOk = rs.every(r => r.ok), sameNT = true, sameShape = true;
  for (const r of rs.slice(1)) {
    if (r.nontriv.join('|') !== r0.nontriv.join('|')) sameNT = false;
    if (r.chains.length !== r0.chains.length) { sameShape = false; continue; }
    r.chains.forEach((c, k) => { const c0 = r0.chains[k]; const dR = r.R - r0.R;
      if (c.entry !== c0.entry || c.from !== c0.from || c.to !== c0.to || c.endV2 !== c0.endV2 || c.val !== c0.val || c.rle.length !== c0.rle.length) { sameShape = false; return; }
      c.rle.forEach(([x, n], q) => { const [x0, n0] = c0.rle[q]; const dn = n - n0; if (x !== x0 || !(dn === 0 || (dR !== 0 && dn % dR === 0))) sameShape = false; }); });
  }
  out.push(`s = ${s}（${rs.length} 個の N）：1 段がすべて閉じる ${allOk ? 'はい' : 'いいえ'}、自明でない E 型の事実の集合が同じ ${sameNT ? 'はい' : 'いいえ'}、鎖の形が同じで連の長さの差が R の差の整数倍 ${sameShape ? 'はい' : 'いいえ'}`);
}
console.log(out.join('\n'));
