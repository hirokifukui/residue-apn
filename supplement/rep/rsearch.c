/* rsearch.c (R03-11): random search over p = L(A(x)^3), A,L invertible linear maps of GF(2^m),
   for reduced quadratic optimal APN permutations with mu=0 and Z empty.
   Independent of inv.py/repsel.py. Coefficients computed at Dembowski-Ostrom + linear + constant exponents,
   then the polynomial is re-evaluated at ALL x and compared with the function (fail-closed).
   usage: ./rsearch m seed tries [ctrans]   (ctrans=1 also uses p=L((A x + c)^3)) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int m,q; static unsigned POLY; static int lg[1<<13], ex[1<<14];
static unsigned mul(unsigned a,unsigned b){ if(!a||!b) return 0; return ex[lg[a]+lg[b]]; }
static unsigned pw(unsigned a,long e){ if(!a) return e==0; return ex[(int)(((long)lg[a]*e)%(q-1))]; }
static uint64_t S=88172645463325252ULL; static uint64_t rnd(){ S^=S<<13; S^=S>>7; S^=S<<17; return S; }
static unsigned lin(unsigned *M,unsigned x){ unsigned r=0; for(int i=0;i<m;i++) if(x>>i&1) r^=M[i]; return r; }
static int invertible(unsigned *M){ /* rank via gaussian elimination */
  unsigned b[16]; for(int i=0;i<m;i++) b[i]=M[i]; int r=0;
  for(int bit=0;bit<m;bit++){ int piv=-1; for(int i=r;i<m;i++) if(b[i]>>bit&1){piv=i;break;}
    if(piv<0) continue; unsigned t=b[piv]; b[piv]=b[r]; b[r]=t;
    for(int i=0;i<m;i++) if(i!=r && (b[i]>>bit&1)) b[i]^=b[r]; r++; }
  return r==m; }
int main(int argc,char**argv){
  if(argc<4){fprintf(stderr,"usage\n");return 2;}
  m=atoi(argv[1]); long seed=atol(argv[2]); long tries=atol(argv[3]); int ct=argc>4?atoi(argv[4]):0;
  if(m==5)POLY=37; else if(m==7)POLY=131; else if(m==9)POLY=529; else if(m==11)POLY=(1u<<11)|5; else {fprintf(stderr,"m?\n");return 2;}
  q=1<<m; S^=(uint64_t)seed*0x9E3779B97F4A7C15ULL; for(int i=0;i<20;i++) rnd();
  unsigned x=1; for(int i=0;i<q-1;i++){ ex[i]=x; ex[i+q-1]=x; lg[x]=i; x<<=1; if(x&q) x^=POLY; }
  if(x!=1){fprintf(stderr,"poly not primitive\n");return 2;}
  /* exponent set: 0, 2^i, 2^i+2^j (i<j) */
  int ne=0, E[200]; E[ne++]=0; for(int i=0;i<m;i++) E[ne++]=1<<i;
  for(int i=0;i<m;i++) for(int j=i+1;j<m;j++) E[ne++]=(1<<i)+(1<<j);
  unsigned *f=malloc(q*sizeof(unsigned)), *c=calloc(q,sizeof(unsigned)), *dv=malloc(q*sizeof(unsigned));
  long st_ok=0, st_mu0=0, st_mu0z0=0, st_mu1z0=0, st_mu1z=0, st_mu0z=0, st_bad=0, st_noninv=0;
  printf("RSEARCH m=%d poly=%u seed=%ld tries=%ld ctrans=%d\n",m,POLY,seed,tries,ct);
  for(long t=0;t<tries;t++){
    unsigned A[16],L[16]; for(int i=0;i<m;i++){A[i]=rnd()%q; L[i]=rnd()%q;}
    unsigned cc = ct ? (unsigned)(rnd()%q) : 0;
    if(!invertible(A)||!invertible(L)){st_noninv++;continue;}
    for(unsigned a=0;a<(unsigned)q;a++){ unsigned y=lin(A,a)^cc; f[a]=lin(L,mul(y,mul(y,y))); }
    for(int k=0;k<ne;k++){ int e=E[k]; unsigned s;
      if(e==0) s=f[0];
      else { s=0; for(unsigned a=1;a<(unsigned)q;a++) if(f[a]) s^=mul(f[a],pw(a,(long)(q-1-e))); }
      c[e]=s; }
    /* fail-closed: re-evaluate */
    int okev=1; for(unsigned a=0;a<(unsigned)q && okev;a++){ unsigned s=0; for(int k=0;k<ne;k++) if(c[E[k]]) s^=mul(c[E[k]],pw(a,E[k])); if(s!=f[a]) okev=0; }
    if(!okev){ st_bad++; continue; }
    /* p' = c1 + sum_j c_{1+2^j} X^{2^j} */
    for(unsigned a=0;a<(unsigned)q;a++){ unsigned s=c[1]; for(int j=1;j<m;j++) if(c[1+(1<<j)]) s^=mul(c[1+(1<<j)],pw(a,1<<j)); dv[a]=s; }
    int zero=0; for(unsigned a=0;a<(unsigned)q;a++) if(!dv[a]) zero=1;
    if(zero) continue;
    unsigned rho=0; int nrho=0; for(unsigned a=1;a<(unsigned)q;a++) if(dv[a]==dv[0]){rho=a;nrho++;}
    if(nrho!=1) continue;
    /* permutation check */
    { static unsigned char seen[1<<13]; int perm=1; for(int a=0;a<q;a++) seen[a]=0; for(int a=0;a<q;a++){ if(seen[f[a]]) perm=0; seen[f[a]]=1;} if(!perm){st_bad++;continue;} }
    st_ok++;
    /* mu = [X^2](p(X+rho)+p(X)) = sum over e with C(e,2) odd of c_e rho^{e-2}, e>2 (e=2 term cancels) */
    unsigned mu=0; for(int k=0;k<ne;k++){ int e=E[k]; if(e>2 && ((e*(e-1)/2)&1) && c[e]) mu^=mul(c[e],pw(rho,e-2)); }
    int z=0; for(unsigned a=0;a<(unsigned)q;a++) if((f[a^rho]^f[a]^mul(rho,dv[a]))==0) z++;
    if(mu==0){ st_mu0++; if(z==0) st_mu0z0++; else st_mu0z++; }
    else { if(z==0) st_mu1z0++; else st_mu1z++; }
    if(mu==0){
      printf("HIT t=%ld rho=%u mu=0 z=%d cconst=%u A=",t,rho,z,cc); for(int i=0;i<m;i++) printf("%u%s",A[i],i<m-1?",":""); printf(" L=");
      for(int i=0;i<m;i++) printf("%u%s",L[i],i<m-1?",":""); printf(" coeffs="); int first=1;
      for(int k=0;k<ne;k++) if(c[E[k]]){ printf("%s%d:%u",first?"":",",E[k],c[E[k]]); first=0; } printf("\n"); fflush(stdout);
    }
  }
  printf("STATS optimal=%ld mu0=%ld mu0_z0=%ld mu0_zpos=%ld mu1_z0=%ld mu1_zpos=%ld noninv=%ld evalfail_or_nonperm=%ld\n",st_ok,st_mu0,st_mu0z0,st_mu0z,st_mu1z0,st_mu1z,st_noninv,st_bad);
  return st_bad?1:0;
}
