/*
 * family_search.js — v2(m+1) = V で、型の周期が一定の幅で伸び続ける族 m = 3a − 2、a = (c·2^N + b)/q を探す
 *
 * 何を計算するか:
 *   q（奇数の一覧）、1 ≤ c ≤ 15（奇数）、|b| ≤ 150 について、a = (c·2^N + b)/q が整数になる N を、N ≥ 16 から
 *   2 の q を法とする位数ずつ 4 つ取る。m = 3a − 2 が 4 つとも v2(m+1) = V のとき、lazy_bigint.js の gapsBig
 *   （300 ブロック、事実の数の上限 200000）から周期の長さ L を推測し、L が一定の幅で増える (q, c, b) を出す。
 *   （m + 2 = 3a の形は、定理 K33a・K35 の族と同じ。）
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/family_search.js 3 > data/family_search_v3.txt
 *   node --stack-size=65500 code/family_search.js 5 > data/family_search_v5.txt
 */
const {gapsBig}=require('./lazy_bigint');
const v2=x=>{let c=0;while(x%2n===0n){x/=2n;c++;}return c;};
function per(g){for(let L=1;L<=g.length/3;L++)for(let p=0;p<=80;p++){if(g.length-p<3*L)break;let ok=true;for(let i=p;i+L<g.length;i++)if(g[i]!==g[i+L]){ok=false;break;}if(ok)return [p,L];}return null;}
const V=+process.argv[2];
const ord=q=>{let x=2%q,o=1;while(x!==1){x=x*2%q;o++;}return o;};
const found=[];
for (const q of [3,5,7,9,11,13,15,17,21,31,33,43,51,63,65,85,127]) { const o=ord(q);
 for (let c=1;c<=15;c+=2) for (let b=-150;b<=150;b++) {
  // a = (c·2^N + b)/q が整数になる N（N ≡ N0 mod o）
  let N0=-1; for(let n=0;n<o;n++) if(((c*Number(2n**BigInt(n)%BigInt(q)))+b)%q===0||((c*Number(2n**BigInt(n)%BigInt(q))+b)%q+q)%q===0){N0=n;break;}
  if(N0<0) continue;
  const Ns=[]; for(let N=N0;Ns.length<4;N+=o) if(N>=16) Ns.push(N);
  const as=Ns.map(N=>(BigInt(c)*2n**BigInt(N)+BigInt(b))/BigInt(q));
  if(!as.every(a=>v2(3n*a-1n)===V)) continue;
  const Ls=[]; let ok=true;
  for(const a of as){const m=3n*a-2n; let pl=null; try{pl=per(gapsBig(m,300,200000).gaps);}catch(e){} if(!pl){ok=false;break;} Ls.push(pl[1]);}
  if(ok&&Ls[1]>Ls[0]&&Ls[2]-Ls[1]===Ls[1]-Ls[0]&&Ls[3]-Ls[2]===Ls[1]-Ls[0]) found.push([q,c,b,Ns[0],o,Ls.join(",")]);
 }}
console.log("v="+V,found.length); for(const f of found.slice(0,12)) console.log("  q="+f[0]+" c="+f[1]+" b="+f[2]+" N0="+f[3]+" step="+f[4]+" L="+f[5]);
