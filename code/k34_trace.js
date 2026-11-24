/*
 * k34_trace.js — 予想 K34・K58（v = 3、ρ = 2、N 奇数、5a + 1 = s·2^N）の周期についての帰納法の 1 段を、O 型ブロックの鎖と E 型ブロックの評価に分けて追う
 *
 * 何を計算するか:
 *   引数の各奇数 N について、s（N ≡ 1 (mod 4) で 3、≡ 3 で 7）、a = (s·2^N − 1)/5、m = 3a − 2、R = (N − 3)/2、
 *   周期 w（K34：1^{2R} 0 (1^R 0 0)^2、K58：1^{R+2} 0 1^R 0）について、prove3（period_induction.js）で得た仮定の集合 A を周期の始まりの事実とし、
 *   1 周期の h と A の各距離を評価し直す。O 型ブロックは一本道（例外 (M+d)/2 > m と d = h − 1 はそこで値を決め、それまでの段数で反転する）、E 型ブロックは E 型の規則。
 *   出力：評価が w と A に一致するか、仮定の距離（a の 1 次式）、E 型の事実の数、O 型の鎖の数。環境変数 DUMP を与えると E 型の事実を出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k34_trace.js 41 45 49 53 43 47 51 > data/k34_trace.txt
 */
'use strict';
const {prove3}=require('./period_induction');
const v2=x=>{x=x<0n?-x:x;if(x===0n)return 99;let c=0;while(x%2n===0n){x/=2n;c++}return c};
for(const N of process.argv.slice(2).map(Number)){
 let s=1n;while((s*2n**BigInt(N)-1n)%5n!==0n)s+=2n;const a=(s*2n**BigInt(N)-1n)/5n,m=3n*a-2n,M=m+2n,h=(m+1n)/2n,R=(N-3)/2;
 const w=N%4===1?'1'.repeat(2*R)+'0'+('1'.repeat(R)+'00').repeat(2):'1'.repeat(R+2)+'0'+'1'.repeat(R)+'0',L=w.length;
 const pr=prove3(m,'',w);const A=new Map(pr.Aset.map(([d,v])=>[BigInt(d),v]));const bound=Math.min(2*(w.length-w.replace(/0+$/,'').length)-1,2);
 const gap=i=>w[((i%L)+L)%L];const memo=new Map();let nE=0;const entries=[];const efacts=[];
 const form=d=>{for(let k=0n;k<=8n;k++){const t=d*2n**k*5n;// 5·2^k d = P(5a) + Q' → P a 表示：d = (P a + Q)/2^k
   const P=(t+(5n*a)/2n)/(5n*a);const Q=(d*2n**k)-P*a;if(Q>-(2n**30n)&&Q<2n**30n)return `(${P}a${Q<0n?'−'+(-Q):'+'+Q})/2^${k}`}return '?'};
 const S=(i,d)=>{const key=i+':'+d;if(memo.has(key))return memo.get(key);let r;
  if(i===0){const t=v2(d);if(t===0)r=true;else if(t<=bound)r=t%2===0;else if(A.has(d))r=A.get(d);else throw new Error('不明')}
  else if(gap(i-1)==='1'){let j=i,dd=d,st=0;while(j>0&&gap(j-1)==='1'){if(dd%2n===0n)dd/=2n;else{if(dd===h-1n){r=st%2===0?false:true;break}if((M+dd)/2n>m){r=st%2===0?true:false;break}dd=(M+dd)/2n;j--}st++}
   if(r===undefined){entries.push(`ブロック ${i}→${j}：入口 ${form(d)}`);const b=S(j,dd);r=st%2===0?b:!b}}
  else{nE++;if(d%2n===1n)r=true;else if(S(i,d/2n))r=false;else{const ee=h+d/2n;r=!(ee<=m&&S(i-1,ee))}efacts.push(`ブロック ${i}：${form(d)}（v2 ${v2(d)}）${r?'入':'不'}`)}
  memo.set(key,r);return r};
 let ok=true;for(let i=1;i<=L;i++)if((S(i,h)?'1':'0')!==w[i%L])ok=false;for(const [d,val] of A)if(S(L,d)!==val)ok=false;
 console.log('N',N,'s',s,'R',R,'L',L,'ok',ok,'仮定',[...A.keys()].map(form).join(' '),'E の事実',nE,'鎖',entries.length);
 if(process.env.DUMP)console.log(efacts.join('\n'))}
