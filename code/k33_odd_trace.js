/*
 * k33_odd_trace.js — 予想 K33（e 奇数、m = 9·2^e + 1）の周期についての帰納法の 1 段を、O 型ブロックの一本道の鎖と E 型ブロックの評価に分けて追う
 *
 * 何を計算するか:
 *   prove（period_induction.js）で得た仮定の集合 A を周期の始まりの事実として、1 周期（L = e + (e+1)/2 ブロック）の h と A の各距離を評価し直す。
 *   O 型ブロック（直前の間隔が m+2）は一本道の規則で E 型ブロックかブロック 0 まで進め、E 型ブロックは E 型の規則で評価する。
 *   引数の各 e について、評価が w と A に一致するか、E 型の事実の数、O 型の鎖の数、鎖の終点のブロックの分布を出す。
 *   環境変数 DUMP=e を与えると、E 型ブロック（ブロック e と L）の事実を (αX + β)/2^k（X = 2^e）の形で、v2 と値とともに出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k33_odd_trace.js 15 21 27 33 > data/k33_odd_trace.txt
 *   DUMP=21 node --stack-size=65500 code/k33_odd_trace.js > data/k33_odd_trace_21.txt
 */
'use strict';
const {prove}=require('./period_induction');
const v2=x=>{let c=0;while(x%2n===0n){x/=2n;c++}return c};
for(const e of process.argv.slice(2).map(Number)){
 const X=2n**BigInt(e),m=9n*X+1n,M=m+2n,h=(m+1n)/2n,w='1'.repeat(e-1)+'0'+'1'.repeat((e-1)/2)+'0',L=w.length;
 const A=new Map(prove(m,w).Aset.map(([d,v])=>[BigInt(d),v]));
 const gap=i=>w[((i%L)+L)%L]; // ブロック i（0 = 周期の始まり B）の直前の間隔は w[i−1]
 let nE=0,nO=0;const chains=[];const memo=new Map();
 const S=(i,d)=>{const key=i+':'+d;if(memo.has(key))return memo.get(key);let r;
  if(i===0){if(d%2n===1n)r=true;else if(A.has(d))r=A.get(d);else throw new Error('不明 '+d)}
  else if(gap(i-1)==='1'){ // O 型：一本道を B まで、または E 型ブロックに着くまで進む
   nO++;let j=i,dd=d,s=0;
   while(j>0&&gap(j-1)==='1'){if(dd%2n===0n)dd/=2n;else{if(dd===h-1n){r=false;break}if((M+dd)/2n>m){r=true;break}dd=(M+dd)/2n;j--}s++}
   if(r===undefined){const b=S(j,dd);r=s%2===0?b:!b}
   chains.push([i,j]);
  } else { nE++; // E 型
   if(d%2n===1n)r=true;else if(S(i,d/2n))r=false;else{const ee=h+d/2n;r=!(ee<=m&&S(i-1,ee))}}
  memo.set(key,r);return r};
 let ok=true;for(let i=1;i<=L;i++)if((S(i,h)?'1':'0')!==w[i%L])ok=false;
 for(const [d,val] of A)if(S(L,d)!==val)ok=false;
 const ends={};for(const [a,b] of chains){const k=(a===b?'self':'→'+b);ends[k]=(ends[k]||0)+1}
 console.log('e',e,'ok',ok,'E型の事実',nE,'O型の鎖',nO,'鎖の終点のブロック',JSON.stringify(ends))}
// 形の分類：E 型ブロックの事実を (αX + β)/2^k で表す
if (process.env.DUMP) { const e = +process.env.DUMP; const X = 2n ** BigInt(e), m = 9n * X + 1n, M = m + 2n, h = (m + 1n) / 2n, w = '1'.repeat(e - 1) + '0' + '1'.repeat((e - 1) / 2) + '0', L = w.length;
  const A = new Map(prove(m, w).Aset.map(([d, v]) => [BigInt(d), v])); const gap = i => w[((i % L) + L) % L]; const memo = new Map(); const rows = [];
  const form = d => { for (let k = 0n; k <= 6n; k++) { const t = d * 2n ** k; const al = (t + X / 2n) / X; const be = t - al * X; if (be > -(X / 4n) && be < X / 4n) { const bs = be === 0n ? '' : (be < 0n ? '−' : '+') + (be < 0n ? -be : be); return `(${al}X${bs})/2^${k}`; } } return '?'; };
  const S = (i, d) => { const key = i + ':' + d; if (memo.has(key)) return memo.get(key); let r;
    if (i === 0) { r = d % 2n === 1n ? true : A.get(d); }
    else if (gap(i - 1) === '1') { let j = i, dd = d, s = 0; while (j > 0 && gap(j - 1) === '1') { if (dd % 2n === 0n) dd /= 2n; else { if (dd === h - 1n) { r = false; break; } if ((M + dd) / 2n > m) { r = true; break; } dd = (M + dd) / 2n; j--; } s++; } if (r === undefined) { const b = S(j, dd); r = s % 2 === 0 ? b : !b; } }
    else { if (d % 2n === 1n) r = true; else if (S(i, d / 2n)) r = false; else { const ee = h + d / 2n; r = !(ee <= m && S(i - 1, ee)); } rows.push(`ブロック ${i === e ? 'e' : i === L ? 'L' : i}：${form(d)}（v2 = ${v2(d)}）${r ? '入' : '不'}`); }
    memo.set(key, r); return r; };
  for (let i = 1; i <= L; i++) S(i, h); for (const [d] of A) S(L, d);
  console.log(rows.sort().join('\n')); }
