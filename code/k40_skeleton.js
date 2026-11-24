/*
 * k40_skeleton.js — 予想 K40（a = (2^N − 1)/23、m = 3a − 2、N 偶数）の証明の骨格で使う鎖の、段数と終わりの距離を求める
 *
 * 何を計算するか:
 *   N = 22, 44, …, NMAX（22 の倍数）について、O 型ブロックの一本道の規則（偶数なら同じブロックで半分、奇数なら 1 つ前のブロックで (M + d)/2）で、
 *   最後の O 型ブロック P − 1（P = N/2）から周期の始まり B（相対位置 0）までたどり、段数と、B での距離の種類を出す。
 *     g = (21a − 5)/8、f = (33a − 9)/16、および X（g の鎖の終わり）について h + X/8、h + X/4、h + X/2
 *   途中で d = h − 1 になる、または (M + d)/2 > m になる段があれば「例外」と出す。
 *   段数 s と終わりの値 v₀（奇数なら入る、v2 = 1 なら入らない、X）から、P − 1 での値は「s が偶数なら v₀、奇数なら ¬v₀」。
 * 実行方法（リポジトリのルートで）:
 *   node code/k40_skeleton.js 440 > data/k40_skeleton.txt
 */
'use strict';
const NMAX = +(process.argv[2] || 440);
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 予想 K40 の証明の骨格で使う鎖', `# 生成: node code/k40_skeleton.js ${NMAX}`, 'N | N/2 mod 2 | 鎖：段数、終わり（例外の有無）…'];
for (let N = 22; N <= NMAX; N += 22) {
  const a = (2n ** BigInt(N) - 1n) / 23n, m = 3n * a - 2n, M = m + 2n, h = (m + 1n) / 2n, P = N / 2;
  const walk = d0 => { let d = d0, j = P - 1, s = 0, bad = false; while (j > 0) { if (d === h - 1n) { bad = true; break; } if (d % 2n === 0n) d /= 2n; else { const e = (M + d) / 2n; if (e > m) { bad = true; break; } d = e; j--; } s++; } return { d, s, bad }; };
  const g = walk((21n * a - 5n) / 8n), X = g.d;
  const kind = d => d === X ? 'X' : v2(d) === 0 ? '奇数' : v2(d) === 1 ? 'v2=1' : 'v2=' + v2(d);
  const parts = [['g', g]]; parts.push(['f', walk((33n * a - 9n) / 16n)]);
  for (const [nm, d0] of [['h+X/8', h + X / 8n], ['h+X/4', h + X / 4n], ['h+X/2', h + X / 2n]]) parts.push([nm, walk(d0)]);
  out.push(`${N} | ${P % 2} | ` + parts.map(([nm, r]) => `${nm}: ${r.s}、${kind(r.d)}${r.bad ? '（例外）' : ''}`).join(' ／ ') + ` ／ v2(X) = ${v2(X)}`);
}
console.log(out.join(String.fromCharCode(10)));
