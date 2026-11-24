// 使い方: node code/k68_gen11100.js facts.json 195 243 247 で鎖の事実を作り、node code/k68_asm11100.js lean/Rubidium/K67b.lean facts.json lean/Rubidium/K68c.lean で Lean ファイルを組み立てる
// gen11100.js out r1 r2 ... : u ≡ r (mod 256)、11100 型、始まりの行 Blk m 3 の鎖の事実 F0..F3 を生成
const fs=require('fs');
const v2=x=>{let c=0;while(x%2==0){x/=2;c++}return c};
const [out,...rr]=process.argv.slice(2); const rs=rr.map(Number);
const pr=e=>e.D===1?(e.B===0?`${e.A} * u`:`${e.A} * u + ${e.B}`):`(${e.A} * u + ${e.B}) / ${e.D}`;
const ev=(e,u)=>(e.A*u+e.B)/e.D;
const B=k=>'a'+' + (m + 2)'.repeat(k);
function chain(k,e,u){const st=[];let neg=0;
  while(k>0){const x=ev(e,u);
    if(x%2===0){const z={A:e.A,B:e.B,D:e.D*2}; st.push({t:'h',k,e,z}); e=z;}
    else {const y={A:e.A+8*e.D,B:e.B+e.D,D:e.D*2}; st.push({t:'o',k,e,y}); e=y; k--;}
    neg++;}
  return {st,fin:e,neg};}
const X1={A:9,B:1,D:2}, starts=[[0,X1],[1,X1],[2,X1],[3,{A:6,B:0,D:1}]];
const trip=[['a','hrow','hb1','hah'],['(a + (m + 2))','hb1','hb2','hb1h'],['(a + (m + 2) + (m + 2))','hb2','hb3','hb2h']];
const want=[false,false,true,true];
const res={};
for(const r of rs){
  const shape=u=>starts.map(([k,e])=>{const c=chain(k,e,u);const n=v2(ev(c.fin,u));return c.st.map(s=>s.t).join('')+':'+n;}).join(' ');
  const s0=shape(r); for(let t=1;t<8;t++) if(shape(r+256*t)!==s0) throw new Error('shape varies r='+r+' '+s0+' / '+shape(r+256*t));
  let facts='';
  starts.forEach(([k,e],i)=>{
    const c=chain(k,e,r), y=c.fin, n=v2(ev(y,r));
    if(n>3) throw new Error('v2>3 r='+r+' F'+i);
    const valA=n%2===0, val=(c.neg%2===0)?valA:!valA;
    if(val!==want[i]) throw new Error(`sign mismatch r=${r} F${i}`);
    let pf='';
    for(const s of c.st){const [p,h1,h2,h3]=trip[s.k-1];
      if(s.t==='h') pf+=`    rw [show ${pr(s.e)} = 2 * (${pr(s.z)}) by omega,\n      o_half' m (4 * u) ${p} (${pr(s.z)}) hmh ${h1} ${h2} ${h3} (by omega) (by omega) (by omega)]\n`;
      else pf+=`    rw [o_odd_iff m (4 * u) ${p} (${pr(s.e)}) hmh ${h1} ${h2} ${h3} (by omega) (by omega) (by omega) (by omega),\n      show (m + 2 + ${pr(s.e)}) / 2 = ${pr(s.y)} by omega]\n`;}
    const Y=pr(y);
    const v2steps=Array.from({length:n},(_,j)=>`v2_even (${Y}${' / 2'.repeat(j)}) (by omega) (by omega)`).concat([`v2_odd (${Y}${' / 2'.repeat(n)}) (by omega)`]).join(',\n        ');
    facts+=`  have F${i} : ${want[i]?'':'¬ '}IsP m (${B(k)} + ${pr(e)}) (${pr(e)}) := by\n${pf}    have hv : v2 (${Y}) = ${n} := by\n      have : (${Y}) % ${2**(n+1)} = ${2**n} := by omega\n      rw [${v2steps}]\n    rw [hblk _ (by omega) (by omega) (by rw [hv]; omega), hv]\n    decide\n`;
  });
  res[r]=facts;
}
fs.writeFileSync(out,JSON.stringify(res));
console.log('ok', Object.keys(res));
