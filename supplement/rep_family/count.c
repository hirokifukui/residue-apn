/* count.c: N(m) = #{d in F_q^*: Tr(d)=Tr(1/d)=0} and Kloosterman-type sum K'=sum_{d!=0}(-1)^{Tr(d+1/d)}; check N=(q-3+K')/4 and |K'|<=2 sqrt(q) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
static int m; static uint32_t q,POLY;
static uint32_t mul(uint32_t a,uint32_t b){uint32_t r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&q)a^=POLY;}return r;}
static uint32_t pw(uint32_t a,uint64_t e){uint32_t r=1;while(e){if(e&1)r=mul(r,a);a=mul(a,a);e>>=1;}return r;}
int main(int c,char**v){ m=atoi(v[1]); POLY=strtoul(v[2],0,10); q=1u<<m;
  /* trace as linear functional: Tr(x) = parity(x & tmask) */
  uint32_t tmask=0; for(int i=0;i<m;i++){ uint32_t x=1u<<i,t=0; for(int k=0;k<m;k++){t^=x;x=mul(x,x);} if(t>1) return 3; if(t) tmask|=1u<<i; }
  long N=0,K=0; for(uint32_t d=1; d<q; d++){ uint32_t id=pw(d,q-2); int a=__builtin_parity(d&tmask), b=__builtin_parity(id&tmask); if(!a&&!b) N++; K += (a^b)?-1:1; }
  printf("{\"m\":%d,\"q\":%u,\"N\":%ld,\"Kprime\":%ld,\"formula_ok\":%d,\"weil_ok\":%d,\"weil_lower_bound\":%.1f}\n",m,q,N,K,4*N==(long)q-3+K,fabs((double)K)<=2*sqrt((double)q),((double)q-3-2*sqrt((double)q))/4);
  return 0; }
