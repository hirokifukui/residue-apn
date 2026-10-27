/* brute_sparse.c (adapted from rep_family/brute.c): function-level verification of the SPARSE family
   p_c = reduced polynomial of B_c(x)^3, B_c(x) = x^(2^(m-2)) + x^(2^(m-1)) + x + x^2 + c x^4.
   Theorem predicts: (H), mu=0, Z empty  iff  B_c injective and c not in F_2; then eps=1, B_c(rho)=1, rho!=1.
   Independent of sym.py: evaluates the function at all points, interpolates the reduced polynomial at
   exponents 0, 2^i, 2^i+2^j, re-evaluates at ALL points (fail-closed: any other exponent would show up as a mismatch),
   then computes p', rho, eps, mu (second Hasse coefficient), Lambda and Z by full enumeration.
   usage: ./brute m poly mode [arg] [apn]
     mode=all     : every d in F_q^*
     mode=sample N: N pseudo-random d (xorshift, fixed seed) with Tr(d)=Tr(1/d)=0, plus N with the condition failing
   apn=1 additionally checks APN by full DDT (q^2 work per d).
   Output: one JSON object per d on stdout, summary on stderr-free last line "SUMMARY {...}". */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int m; static uint32_t q, POLY;
static uint32_t mul(uint32_t a, uint32_t b){ uint32_t r=0; while(b){ if(b&1) r^=a; b>>=1; a<<=1; if(a&q) a^=POLY; } return r; }
static uint32_t pw(uint32_t a, uint64_t e){ uint32_t r=1; while(e){ if(e&1) r=mul(r,a); a=mul(a,a); e>>=1; } return r; }
static uint32_t inv(uint32_t a){ return pw(a, q-2); }
static uint32_t frob(uint32_t a,int k){ k%=m; while(k--) a=mul(a,a); return a; }
static int tr(uint32_t a){ uint32_t t=0,x=a; for(int i=0;i<m;i++){ t^=x; x=mul(x,x);} if(t>1){fprintf(stderr,"trace?\n");exit(3);} return (int)t; }
static uint64_t S=0x243F6A8885A308D3ULL; static uint64_t rnd(void){ S^=S<<13; S^=S>>7; S^=S<<17; return S; }
static uint32_t *f, *dv, *Fr, *Ir; static unsigned char *seen;
static int ne; static int E[400]; static uint32_t cf[400];
static long n_ok=0, n_fail_pred=0, n_total=0;
static int run(uint32_t d, int apn){
  /* B_c(x) = x^(2^(m-2)) + x^(2^(m-1)) + x + x^2 + c x^4 */
  for(uint32_t x=0;x<q;x++){ uint32_t a=Fr[(size_t)x*m+(m-2)]^Fr[(size_t)x*m+(m-1)]^x^Fr[(size_t)x*m+1]^mul(d,Fr[(size_t)x*m+2]); f[x]=mul(a,mul(a,a)); }
  int Td=tr(d), Tid=d?tr(inv(d)):-1;
  memset(seen,0,q); int perm=1; for(uint32_t x=0;x<q;x++){ if(seen[f[x]]) perm=0; seen[f[x]]=1; }
  int pred = (perm && d>1);
  printf("{\"m\":%d,\"c\":%u,\"Tr_d\":%d,\"Tr_inv_d\":%d,\"perm\":%d",m,d,Td,Tid,perm);
  if(!perm){ printf(",\"H\":0,\"why\":\"not a permutation\",\"pred_hit\":%d}\n",pred); return pred?0:1; }
  int apn_ok=-1;
  if(apn){ apn_ok=1; unsigned short *cnt=calloc(q,sizeof(unsigned short));
    for(uint32_t a=1;a<q && apn_ok;a++){ memset(cnt,0,q*sizeof(unsigned short)); for(uint32_t x=0;x<q;x++){ if(++cnt[f[x^a]^f[x]]>2){apn_ok=0;break;} } }
    free(cnt); }
  /* interpolation */
  for(int k=0;k<ne;k++){ int e=E[k]; uint32_t s;
    if(e==0) s=f[0];
    else { s=0; int i=-1,j=-1; for(int b=0;b<m;b++) if(e>>b&1){ if(i<0) i=b; else j=b; }
      for(uint32_t a=1;a<q;a++) if(f[a]){ uint32_t t = Ir[(size_t)a*m+i]; if(j>=0) t=mul(t,Ir[(size_t)a*m+j]); s^=mul(f[a],t); } }
    cf[k]=s; }
  int okev=1;
  for(uint32_t a=0;a<q && okev;a++){ uint32_t s=cf[0]; for(int k=1;k<ne;k++) if(cf[k]){ int e=E[k]; int i=-1,j=-1; for(int b=0;b<m;b++) if(e>>b&1){ if(i<0) i=b; else j=b; }
      uint32_t t=Fr[(size_t)a*m+i]; if(j>=0) t=mul(t,Fr[(size_t)a*m+j]); s^=mul(cf[k],t);} if(s!=f[a]) okev=0; }
  if(!okev){ printf(",\"H\":0,\"why\":\"reeval mismatch\",\"pred_hit\":%d}\n",pred); return 0; }
  /* p' = c_1 + sum_{j>=1} c_{1+2^j} X^{2^j} */
  uint32_t c1=0, cK[32]={0}, c2=0; for(int k=0;k<ne;k++){ if(E[k]==1) c1=cf[k]; if(E[k]==2) c2=cf[k]; for(int j=1;j<m;j++) if(E[k]==1+(1<<j)) cK[j]=cf[k]; }
  for(uint32_t a=0;a<q;a++){ uint32_t s=c1; for(int j=1;j<m;j++) if(cK[j]) s^=mul(cK[j],Fr[(size_t)a*m+j]); dv[a]=s; }
  int haszero=0; memset(seen,0,q); int twotoone=1;
  for(uint32_t a=0;a<q;a++){ if(!dv[a]) haszero=1; if(seen[dv[a]]>=2) twotoone=0; else seen[dv[a]]++; }
  for(uint32_t a=0;a<q;a++) if(seen[dv[a]]!=2) twotoone=0;
  uint32_t rho=0; for(uint32_t a=1;a<q;a++) if(dv[a]==dv[0]){ rho=a; break; }
  int H = (!haszero && twotoone && rho!=0 && (apn_ok!=0));
  /* mu: sum over e>2 with C(e,2) odd of c_e rho^(e-2) */
  uint32_t mu=0; for(int k=0;k<ne;k++){ int e=E[k]; if(e>2 && (((long)e*(e-1)/2)&1) && cf[k]) mu^=mul(cf[k],pw(rho,e-2)); }
  long z=0; for(uint32_t a=0;a<q;a++) if((f[a^rho]^f[a]^mul(rho,dv[a]))==0) z++;
  uint32_t Brho = Fr[(size_t)rho*m+(m-2)]^Fr[(size_t)rho*m+(m-1)]^rho^Fr[(size_t)rho*m+1]^mul(d,Fr[(size_t)rho*m+2]);
  uint32_t rho_pred = (Brho==1 && rho!=1) ? rho : 0xFFFFFFFF; uint32_t eps_pred = 1;
  int nterms=0; for(int k=0;k<ne;k++) if(cf[k]) nterms++;
  int deg=0; for(int k=0;k<ne;k++) if(cf[k] && E[k]>deg) deg=E[k];
  printf(",\"apn\":%d,\"reeval_ok\":1,\"eps_notin_ImK\":%d,\"pprime_2to1\":%d,\"H\":%d,\"rho\":%u,\"B(rho)=1,rho!=1\":%d,\"eps\":%u,\"eps_eq_1\":%d,\"mu\":%u,\"z\":%ld,\"deg\":%d,\"nterms\":%d,\"c2\":%u,\"pred_hit\":%d}\n",
    apn_ok,!haszero,twotoone,H,rho,rho==rho_pred,c1,c1==eps_pred,mu,z,deg,nterms,c2,pred);
  int hit = H && mu==0 && z==0;
  if(hit) n_ok++;
  return (hit==pred) && (!pred || (rho==rho_pred && c1==eps_pred));
}
int main(int argc,char**argv){
  if(argc<4){ fprintf(stderr,"usage\n"); return 2; }
  m=atoi(argv[1]); POLY=(uint32_t)strtoul(argv[2],0,10); q=1u<<m;
  int apn = 0; long N=0; int mode_all = !strcmp(argv[3],"all");
  if(!mode_all){ N=atol(argv[4]); if(argc>5) apn=atoi(argv[5]); } else if(argc>4) apn=atoi(argv[4]);
  f=malloc(q*4); dv=malloc(q*4); seen=malloc(q); Fr=malloc((size_t)q*m*4); Ir=malloc((size_t)q*m*4);
  for(uint32_t x=0;x<q;x++){ uint32_t y=x, z=x?inv(x):0; for(int i=0;i<m;i++){ Fr[(size_t)x*m+i]=y; Ir[(size_t)x*m+i]=z; y=mul(y,y); z=mul(z,z);} }
  if(Fr[(size_t)2*m+m-1]==0 || mul(Fr[(size_t)2*m+m-1],Fr[(size_t)2*m+m-1])!=2){ fprintf(stderr,"poly not irreducible?\n"); return 2; }
  ne=0; E[ne++]=0; for(int i=0;i<m;i++) E[ne++]=1<<i; for(int i=0;i<m;i++) for(int j=i+1;j<m;j++) E[ne++]=(1<<i)+(1<<j);
  long agree=0, tot=0;
  if(mode_all){ for(uint32_t d=0; d<q; d++){ agree+=run(d,apn); tot++; } }
  else { long got1=0, got0=0; S^=(uint64_t)m*0x9E3779B97F4A7C15ULL;
    (void)got1; (void)got0; for(long i=0;i<N;i++){ uint32_t d=(uint32_t)(rnd()%q); agree+=run(d,apn); tot++; } }
  printf("SUMMARY {\"m\":%d,\"poly\":%u,\"tested\":%ld,\"agree_with_theorem\":%ld,\"hits\":%ld}\n",m,POLY,tot,agree,n_ok);
  return agree==tot?0:1;
}
