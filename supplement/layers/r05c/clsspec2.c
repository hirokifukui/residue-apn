// Exhaustive class/pair spectrum, faster variant: each class is given by the Taylor coefficients t_r = T^[r](x), r<n,
// of T = (F(X+alpha)-F(X))/alpha at its centre x (exact polynomial identity), so T(x+2z) = sum_r t_r (2z)^r mod 2^n.
// Enumerates z mod 2^{n-1}; histogram of T values (relative to base, must be = base mod 2^sh).
// Input file: m n fpolybits sh / base / nclasses / per class n lines of t_r.   Output: "count multiplicity".
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int m,n,fast; static unsigned MODN; static int fpi[16],nfp;
typedef struct {unsigned d[8];} el;
static inline el mulr5(el a, el b){ // m=5, f = t^5 + t^2 + 1  (fpoly 37)
 unsigned c0=a.d[0]*b.d[0], c1=a.d[0]*b.d[1]+a.d[1]*b.d[0], c2=a.d[0]*b.d[2]+a.d[1]*b.d[1]+a.d[2]*b.d[0],
  c3=a.d[0]*b.d[3]+a.d[1]*b.d[2]+a.d[2]*b.d[1]+a.d[3]*b.d[0], c4=a.d[0]*b.d[4]+a.d[1]*b.d[3]+a.d[2]*b.d[2]+a.d[3]*b.d[1]+a.d[4]*b.d[0],
  c5=a.d[1]*b.d[4]+a.d[2]*b.d[3]+a.d[3]*b.d[2]+a.d[4]*b.d[1], c6=a.d[2]*b.d[4]+a.d[3]*b.d[3]+a.d[4]*b.d[2],
  c7=a.d[3]*b.d[4]+a.d[4]*b.d[3], c8=a.d[4]*b.d[4];
 // t^5 = -(t^2+1) in the 0/1 lift f~ = t^5+t^2+1 : c_d t^d -> -c_d t^(d-3) - c_d t^(d-5)
 c5-=c8; c3-=c8; c4-=c7; c2-=c7; c3-=c6; c1-=c6; c2-=c5; c0-=c5;
 el r; r.d[0]=c0&(MODN-1); r.d[1]=c1&(MODN-1); r.d[2]=c2&(MODN-1); r.d[3]=c3&(MODN-1); r.d[4]=c4&(MODN-1); return r;}
static inline el mulr(el a, el b){unsigned c[16]={0};
 for(int i=0;i<m;i++)if(a.d[i]){unsigned ai=a.d[i];for(int k=0;k<m;k++)c[i+k]+=ai*b.d[k];}
 for(int d=2*m-2;d>=m;d--){unsigned t=c[d];if(t)for(int k=0;k<nfp;k++)c[d-m+fpi[k]]-=t;}
 el r;for(int i=0;i<m;i++)r.d[i]=c[i]&(MODN-1);return r;}
static inline el addr(el a, el b){el r;for(int i=0;i<m;i++)r.d[i]=(a.d[i]+b.d[i])&(MODN-1);return r;}
static el rd(FILE*f){el r;memset(&r,0,sizeof r);for(int i=0;i<m;i++){long v;if(fscanf(f,"%ld",&v)!=1){fprintf(stderr,"read\n");exit(2);}r.d[i]=((v%MODN)+MODN)%MODN;}return r;}
int main(int argc,char**argv){
 FILE*f=fopen(argv[1],"r"); long fb; int sh;
 if(fscanf(f,"%d %d %ld %d",&m,&n,&fb,&sh)!=4)return 2;
 MODN=1u<<n; nfp=0; fast=(m==5&&fb==37); for(int i=0;i<m;i++)if((fb>>i)&1)fpi[nfp++]=i;
 el base=rd(f); int nc; if(fscanf(f,"%d",&nc)!=1)return 2;
 el *ts=malloc(sizeof(el)*n*nc); for(int c=0;c<nc;c++)for(int s=0;s<n;s++)ts[c*n+s]=rd(f);
 int nb=n-sh; if(nb<0)nb=0; uint64_t NB=1ull<<(nb*m); uint32_t*cnt=calloc(NB,4);
 uint64_t NZ=1ull<<((n-1)*m); unsigned zm=(1u<<(n-1))-1;
 for(int c=0;c<nc;c++){el*Tt=ts+c*n;
  for(uint64_t z=0;z<NZ;z++){el h;for(int i=0;i<m;i++)h.d[i]=(((unsigned)(z>>((n-1)*i))&zm)<<1)&(MODN-1);
   el p=Tt[n-1]; for(int s=n-2;s>=0;s--)p=addr(fast?mulr5(p,h):mulr(p,h),Tt[s]);
   uint64_t idx=0;
   for(int i=0;i<m;i++){unsigned t=(p.d[i]-base.d[i])&(MODN-1); if(t&((1u<<sh)-1)){fprintf(stderr,"not in base coset mod 2^sh (class %d)\n",c);return 6;} idx|=(uint64_t)(t>>sh)<<(nb*i);}
   cnt[idx]++;}}
 uint64_t maxc=0; for(uint64_t i=0;i<NB;i++)if(cnt[i]>maxc)maxc=cnt[i];
 uint64_t*hh=calloc(maxc+1,8); for(uint64_t i=0;i<NB;i++)hh[cnt[i]]++;
 for(uint64_t v=1;v<=maxc;v++)if(hh[v])printf("%llu %llu\n",(unsigned long long)v,(unsigned long long)hh[v]);
 return 0;}
