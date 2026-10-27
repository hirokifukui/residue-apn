// A = S_u th1 S_u th2 S_u (positions -3..3). Conditions (i) a1 am1^2=a0^3 (mu=0), (ii) am2^2 a0 = am1^3 (eps=a0 r^2).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int m; static uint32_t q,P; static uint32_t *LOG,*EXP;
static uint32_t mulr(uint32_t a,uint32_t b){uint32_t r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&q)a^=P;}return r;}
static inline uint32_t mul(uint32_t a,uint32_t b){ if(!a||!b) return 0; return EXP[(LOG[a]+LOG[b])%(q-1)]; }
static inline uint32_t fr(uint32_t a,int k){ if(!a) return 0; k%=m; if(k<0)k+=m; uint64_t l=LOG[a]; for(int i=0;i<k;i++) l=(l*2)%(q-1); return EXP[l]; }
static int noroot(uint32_t g){ for(uint32_t y=0;y<q;y++) if((mul(y,mul(y,y))^y^g)==0) return 0; return 1; }
typedef struct { uint32_t c[16]; } Op;
static Op comp(Op B, Op C){ Op R={{0}}; for(int i=0;i<16;i++) if(B.c[i]) for(int j=0;j<16;j++) if(C.c[j]){ int pi=i-7,pj=j-7; int k=pi+pj+7; R.c[k]^=mul(B.c[i],fr(C.c[j],pi)); } return R; }
static Op S(uint32_t u){ Op R={{0}}; R.c[6]=u; R.c[7]=1; R.c[8]=1; return R; }
static Op sc(uint32_t t){ Op R={{0}}; R.c[7]=t; return R; }
int main(int argc,char**argv){ m=atoi(argv[1]); P=atoi(argv[2]); q=1u<<m; LOG=calloc(q,4); EXP=calloc(2*q,4);
 for(uint32_t g=2;g<q;g++){ uint32_t x=1; int ok=1; for(uint32_t i=0;i<q-1;i++){ EXP[i]=x; LOG[x]=i; x=mulr(x,g); if(x==1 && i<q-2){ok=0;break;} } if(ok) break; }
 long n=0;
 for(uint32_t u=1;u<q;u++){ if(!noroot(u)) continue; Op Su=S(u);
  for(uint32_t t1=1;t1<q;t1++){ Op L1=comp(Su,sc(t1));
   for(uint32_t t2=1;t2<q;t2++){ Op A=comp(L1,comp(S(u),comp(sc(t2),Su)));
    uint32_t am2=A.c[5],am1=A.c[6],a0=A.c[7],a1=A.c[8];
    if(!am1||!a0) continue;
    if(mul(a1,mul(am1,am1))!=mul(a0,mul(a0,a0))) continue;
    if(mul(mul(am2,am2),a0)!=mul(am1,mul(am1,am1))) continue;
    n++; printf("%u %u %u\n",u,t1,t2);
 }}}
 fprintf(stderr,"m=%d points (u in G) %ld\n",m,n); return 0; }
