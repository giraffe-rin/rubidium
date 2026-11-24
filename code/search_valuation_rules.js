/*
 * search_valuation_rules.js — 「ある 1 次式の 2 進付値で型が決まる」規則（K19、K20 の形）を探す
 *
 * 何を計算するか:
 *   v2(m+1) = V の m を u = (m+1)/2^V（奇数）で表す。奇数 c（1 ≤ c ≤ CMAX）と s = ±1 について、
 *   F = c·u + s の付値 ℓ = v2(F)（LMIN ≤ ℓ ≤ LMAX）ごとに、類 {m : v2(F) = ℓ}（m の 1 つの合同類）に
 *   affine_certificate.js の certify を当てる（(p, L) は類の中で 3000 以上の最小の m で推測し、周期の 1, 2 倍を試す）。
 *   出力は 1 行に 1 つの (c, s) で、各 ℓ について 型（前周期|周期）、または S（偶奇が t による）、F（その他の失敗）、
 *   ?（周期を推測できない）、偶（その ℓ では u が偶数になり、類が空）。
 *   ℓ とともに型が規則的に伸びる (c, s) が、K19（V = 1、c = 1、s = −1）や K20（V = 3、c = 5、s = +1）の形の規則の候補になる。
 *   証明できた行は、その類について K16 と同じ主張（類のすべての m ≥ M_min でその型）になるが、M_min は出力しない。
 *
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/search_valuation_rules.js 3 15 4 12 > data/valuation_search_v3.txt
 *   node --stack-size=65500 code/search_valuation_rules.js 5 63 4 11 > data/valuation_search_v5.txt
 *   （引数: V CMAX LMIN LMAX）
 */
'use strict';
const { certify, guess, Split, Fail } = require('./affine_certificate');
const V=+process.argv[2], CMAX=+process.argv[3], LMIN=+process.argv[4], LMAX=+process.argv[5];
console.log(`# 付値の規則の探索（v2(m+1) = ${V}、F = c·u ± 1、c ≤ ${CMAX}、${LMIN} ≤ ℓ ≤ ${LMAX}）
# 生成: node --stack-size=65500 code/search_valuation_rules.js ${V} ${CMAX} ${LMIN} ${LMAX}
# 各 ℓ: 型（前周期|周期）/ S = 偶奇が t による / F = その他の失敗 / ? = 周期を推測できない / 偶 = 類が空`);
const inv=(c,M)=>{for(let x=1n;;x+=2n)if((BigInt(c)*x)%M===1n)return x};
for(let c=1;c<=CMAX;c+=2)for(const s of [1,-1]){
  const line=[];
  for(let l=LMIN;l<=LMAX;l++){
    const M=2n**BigInt(l+1);const u0=(((2n**BigInt(l)-BigInt(s))%M+M)%M*inv(c,M))%M; // c u + s ≡ 2^l mod 2^{l+1}
    if(u0%2n===0n){line.push(l+':偶');continue}
    const A=2**(V+l+1),B=Number(u0)*2**V-1;const t=Math.max(0,Math.ceil((3000-B)/A));const m=A*t+B;
    const pl=guess(m,300);let r='?';
    if(pl)for(const mult of [1,2]){try{const res=certify(A,B,pl[0],mult*pl[1],3e5);const g=res.gaps.join('');r=(g.slice(0,pl[0])||'-')+'|'+g.slice(pl[0]);break}catch(e){r=e.constructor.name==='Split'?'S':'F'}}
    line.push(l+':'+r);
  }
  console.log(`c=${c} s=${s>0?'+':'-'}1`,line.join(' '));
}
