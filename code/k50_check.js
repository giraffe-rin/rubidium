/*
 * k50_check.js — 定理 K50 の結論（R が data/k50_general.txt の剰余類に入れば、すべての m+2 の極大な連の長さが R、m+1 の連は z..⌈v/2⌉）を数値で確かめる
 *
 * 何を計算するか:
 *   data/k50_general.txt の各行（v、ρ、P、R0、剰余類）について、剰余類のそれぞれの値 g と t = 0, 1 で、R = g + P·t（R ≥ R0 の最小のものから 2 つ。P > 50 の組は 1 つ）をとり、
 *   ⌈(N − v)/ρ⌉ = R となる偶数 N の最小値をとる。定理 K47 の族（s は最小の正の奇数で a が奇数）、m = 3a − 2 について、
 *   gapsBig（lazy_bigint.js）で J = 4(R + v) + 40 ブロックの間隔を求め、中で完結する m+2 の連がすべて長さ R、m+1 の連がすべて z..⌈v/2⌉ かを調べる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k50_check.js data/k50_general.txt > data/k50_check.txt
 */
'use strict';
const fs = require('fs');
const { gapsBig } = require('./lazy_bigint');
const file = process.argv[2];
const out = ['# 定理 K50 の数値での照合', '# 生成: node --stack-size=65500 code/k50_check.js ' + file, 'v | ρ | R | N | m+2 の連（個数、すべて R か） | m+1 の連の長さの範囲 | 一致'];
let tot = 0, ok = 0;
for (const l of fs.readFileSync(file, 'utf8').split(/\r?\n/)) {
  const mm = l.match(/^v = (\d+)、ρ = (\d+).*P = (\d+)、.*R mod \d+（R ≥ (\d+)）: \{([\d, ]+)\}/); if (!mm) continue;
  const [v, rho, P, R0] = mm.slice(1, 5).map(Number), gs = mm[5].split(',').map(x => +x.trim()), z = rho / 2;
  const q = 2n ** BigInt(v) - 2n ** BigInt(rho) + 1n, r = (2n ** BigInt(rho) - 1n) / 3n;
  for (const g0 of gs) {
    let R = g0; while (R < R0) R += P;
    for (let t = 0; t < (P > 50 ? 1 : 2); t++, R += P) {   // P が大きい組は 1 個だけ
      let N = v + rho * (R - 1) + 1; if (N % 2) N++;
      if (Math.ceil((N - v) / rho) !== R) { out.push(`${v} | ${rho} | ${R} | - | 偶数 N がない | - | -`); continue; }
      let s = 1n; while ((s * 2n ** BigInt(N) - r) % q !== 0n) s += 2n;
      const a = (s * 2n ** BigInt(N) - r) / q, m = 3n * a - 2n;
      const J = 4 * (R + v) + 40, gg = gapsBig(m, J, 1e8).gaps;
      const ones = [], zeros = []; let i = 0;
      while (i < J) { let j = i; while (j < J && gg[j] === gg[i]) j++; if (j < J) (gg[i] === '1' ? ones : zeros).push(j - i); i = j; }
      const a1 = ones.length >= 2 && ones.every(x => x === R), a0 = zeros.every(x => x >= z && x <= Math.ceil(v / 2));
      tot++; if (a1 && a0) ok++;
      console.error(`${v} ${rho} ${R} ${N}`);
      out.push(`${v} | ${rho} | ${R} | ${N} | ${ones.length}、${a1 ? 'はい' : 'いいえ'} | ${Math.min(...zeros)}..${Math.max(...zeros)} | ${a1 && a0 ? 'はい' : 'いいえ'}`);
    }
  }
}
out.push('', `${tot} 個中 ${ok} 個で一致`);
console.log(out.join('\n'));
