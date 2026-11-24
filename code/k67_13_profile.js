const u=+process.argv[2], K=+process.argv[3]; const m=8*u-1, L=2*m+3, R=L*K+m+1;
const P=[]; for(let r=0;r<=R;r++){const row=new Uint8Array(m+1);const w=[];for(let k=1;k<=Math.min(m,r);k++) if(P[r-k][k]) w.push(k);
 for(let p=0;p<=m;p++) row[p]=w.every(k=>k===p)?1:0; P.push(row);}
const v2=x=>{let c=0;while(x%2==0){x/=2;c++}return c};
let last='',stab=-1,bad;
for(let i=1;i<=K;i++){const a=i*L; bad=[];for(let d=1;d<=m;d++){const e=v2(d)%2==0?1:0; if(P[a+d][d]!==e) bad.push(d);}
 const key=bad.join(','); if(key!==last){stab=i;last=key;}}
console.log('u='+u,'stable from period',stab,'(of',K+')','size',bad.length);
console.log(bad.map(d=>d+'['+v2(d)+']').join(' '));
console.log('in units of u/ 4:', bad.map(d=>(d/u).toFixed(3)).join(' '));
