// enumerate (v,theta,X) with A = S_u theta S_v, X = u theta^{1/2}, mu=0 and A(1)=r
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int m; static uint32_t q,P; static uint32_t *LOG,*EXP;
static uint32_t mulr(uint32_t a,uint32_t b){uint32_t r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&q)a^=P;}return r;}
static inline uint32_t mul(uint32_t a,uint32_t b){ if(!a||!b) return 0; return EXP[(LOG[a]+LOG[b])%(q-1)]; }
static uint32_t sqrtf_(uint32_t a){ if(!a) return 0; uint32_t l=LOG[a]; if(l&1) l+=q-1; return EXP[(l/2)%(q-1)]; }
int main(int argc,char**argv){ m=atoi(argv[1]); P=atoi(argv[2]); q=1u<<m; LOG=calloc(q,4); EXP=calloc(2*q,4);
 // find generator
 for(uint32_t g=2;g<q;g++){ uint32_t x=1; int ok=1; for(uint32_t i=0;i<q-1;i++){ EXP[i]=x; LOG[x]=i; x=mulr(x,g); if(x==1 && i<q-2){ok=0;break;} } if(ok) break; }
 long cnt=0;
 for(uint32_t v=1;v<q;v++){ uint32_t sv=sqrtf_(v), v2=mul(v,v);
  for(uint32_t th=2;th<q;th++){ uint32_t th2=mul(th,th); uint32_t a1=th^th2; uint32_t thv=mul(th,v); uint32_t D=th^mul(th2,v2);
   for(uint32_t X=0;X<q;X++){ uint32_t am1=X^thv, a0=X^D; if(!am1||!a0) continue;
     uint32_t lhs=mul(a1,mul(am1,am1)), rhs=mul(a0,mul(a0,a0)); if(lhs!=rhs) continue;
     uint32_t A1=mul(X,sv)^thv^mul(th2,v2); if(mul(A1,a0)!=mul(am1,am1)) continue;
     // u = X / theta^{1/2}
     uint32_t u=mul(X,EXP[(q-1-LOG[sqrtf_(th)])%(q-1)]);
     printf("%u %u %u\n",u,th,v); cnt++; }}}
 fprintf(stderr,"m=%d solutions %ld\n",m,cnt); return 0; }
