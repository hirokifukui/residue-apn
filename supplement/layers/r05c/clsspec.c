// Exhaustive class/pair spectrum for a row alpha in layer v_j of GR(2^K,m).
// For each listed residue class (given by the Taylor coefficients f_s = F^[s](x), s<K, at a centre x),
// enumerate y = x + 2z, z mod 2^{n-1} (n=K-j), compute T(y) = (F(y+alpha)-F(y))/alpha mod 2^n
// via F(x+h) = sum_{s<K} f_s h^s (exact for h in 2R), and histogram T(y) over the union of the listed classes.
// All values must be congruent to `base` mod 2^sh (sh=2: one class or a merged pair; sh=1: any pair).
// Output: lines "count multiplicity" where count = #{y mod 2^n in the union : T(y)=gamma}.
// usage: clsspec infile
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int m,K,n,j; static unsigned MOD,MODN; static int fpi[16],nfp;
typedef struct {unsigned d[8];} el;
static inline el mulr(el a, el b){unsigned c[16]={0};
 for(int i=0;i<m;i++)if(a.d[i]){unsigned ai=a.d[i];for(int k=0;k<m;k++)c[i+k]+=ai*b.d[k];}
 for(int d=2*m-2;d>=m;d--){unsigned t=c[d];if(t)for(int k=0;k<nfp;k++)c[d-m+fpi[k]]-=t;}
 el r;for(int i=0;i<m;i++)r.d[i]=c[i]&(MOD-1);return r;}
static inline el addr(el a, el b){el r;for(int i=0;i<m;i++)r.d[i]=(a.d[i]+b.d[i])&(MOD-1);return r;}
static inline el subr(el a, el b){el r;for(int i=0;i<m;i++)r.d[i]=(a.d[i]-b.d[i])&(MOD-1);return r;}
static el rd(FILE*f){el r;memset(&r,0,sizeof r);for(int i=0;i<m;i++){long v;if(fscanf(f,"%ld",&v)!=1){fprintf(stderr,"read\n");exit(2);}r.d[i]=((v%MOD)+MOD)%MOD;}return r;}
int main(int argc,char**argv){
 FILE*f=fopen(argv[1],"r"); long fb;
 int sh; if(fscanf(f,"%d %d %ld %d %d",&m,&K,&fb,&j,&sh)!=5)return 2;
 MOD=1u<<K; n=K-j; MODN=1u<<n; nfp=0; for(int i=0;i<m;i++)if((fb>>i)&1)fpi[nfp++]=i;
 el alpha=rd(f), uinv=rd(f), base=rd(f); int nc; if(fscanf(f,"%d",&nc)!=1)return 2;
 el *fs=malloc(sizeof(el)*K*nc); for(int c=0;c<nc;c++)for(int s=0;s<K;s++)fs[c*K+s]=rd(f);
 int nb=n-sh; if(nb<0)nb=0; uint64_t NB=1ull<<(nb*m); uint32_t*cnt=calloc(NB,4);
 uint64_t NZ=1ull<<((n-1)*m);
 for(int c=0;c<nc;c++){el*F=fs+c*K;
  for(uint64_t z=0;z<NZ;z++){el h;for(int i=0;i<m;i++)h.d[i]=((unsigned)((z>>((n-1)*i))&((1u<<(n-1))-1))<<1)&(MOD-1);
   el h2=addr(h,alpha); el p1=F[K-1],p2=F[K-1];
   for(int s=K-2;s>=0;s--){p1=addr(mulr(p1,h2),F[s]);p2=addr(mulr(p2,h),F[s]);}
   el D=subr(p1,p2); el Dj;
   for(int i=0;i<m;i++){if(D.d[i]&((1u<<j)-1)){fprintf(stderr,"valuation violated\n");return 5;} Dj.d[i]=(D.d[i]>>j)&(MODN-1);}
   // T = Dj*uinv mod 2^n (compute in R_K then reduce)
   el T=mulr(Dj,uinv); uint64_t idx=0;
   for(int i=0;i<m;i++){unsigned t=(T.d[i]-base.d[i])&(MODN-1); if(t&((1u<<sh)-1)){fprintf(stderr,"not in base coset mod 2^sh (class %d)\n",c);return 6;} idx|=(uint64_t)(t>>sh)<<(nb*i);}
   cnt[idx]++;}}
 // histogram of counts
 uint64_t maxc=0; for(uint64_t i=0;i<NB;i++)if(cnt[i]>maxc)maxc=cnt[i];
 uint64_t*h=calloc(maxc+1,8); for(uint64_t i=0;i<NB;i++)h[cnt[i]]++;
 for(uint64_t v=1;v<=maxc;v++)if(h[v])printf("%llu %llu\n",(unsigned long long)v,(unsigned long long)h[v]);
 return 0;}
