// A = S_u o th1 o S_v o th2 o S_w, S_u = u s^{-1} + 1 + s. For given (u,v,w) count (th1,th2) with mu=0 and A(1)=r.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int m; static uint32_t q,P; static uint32_t *LOG,*EXP;
static uint32_t mulr(uint32_t a,uint32_t b){uint32_t r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&q)a^=P;}return r;}
static inline uint32_t mul(uint32_t a,uint32_t b){ if(!a||!b) return 0; return EXP[(LOG[a]+LOG[b])%(q-1)]; }
static inline uint32_t fr(uint32_t a,int k){ if(!a) return 0; k%=m; if(k<0)k+=m; uint64_t l=LOG[a]; for(int i=0;i<k;i++) l=(l*2)%(q-1); return EXP[l]; }
typedef struct { uint32_t c[16]; } Op; // positions -7..8 -> index +7
static Op comp(Op B, Op C){ Op R={{0}}; for(int i=0;i<16;i++) if(B.c[i]) for(int j=0;j<16;j++) if(C.c[j]){ int pi=i-7,pj=j-7; int k=pi+pj+7; if(k<0||k>15) {fprintf(stderr,"range\n");exit(1);} R.c[k]^=mul(B.c[i],fr(C.c[j],pi)); } return R; }
static Op S(uint32_t u){ Op R={{0}}; R.c[6]=u; R.c[7]=1; R.c[8]=1; return R; }
static Op sc(uint32_t t){ Op R={{0}}; R.c[7]=t; return R; }
static int has_root_cubic(uint32_t g){ for(uint32_t y=0;y<q;y++) if((mul(y,mul(y,y))^y^g)==0) return 1; return 0; }
int main(int argc,char**argv){ m=atoi(argv[1]); P=atoi(argv[2]); int trials=atoi(argv[3]); q=1u<<m; LOG=calloc(q,4); EXP=calloc(2*q,4);
 for(uint32_t g=2;g<q;g++){ uint32_t x=1; int ok=1; for(uint32_t i=0;i<q-1;i++){ EXP[i]=x; LOG[x]=i; x=mulr(x,g); if(x==1 && i<q-2){ok=0;break;} } if(ok) break; }
 // G = {g: x^3+x+g no root}; S_u injective iff u^2 in G iff u in G
 uint32_t *G=malloc(q*4); int ng=0; for(uint32_t g=1;g<q;g++) if(!has_root_cubic(g)) G[ng++]=g;
 fprintf(stderr,"|G|=%d (q+1)/3=%u\n",ng,(q+1)/3);
 uint64_t S0=88172645463325252ULL;
 for(int t=0;t<trials;t++){
  S0^=S0<<13;S0^=S0>>7;S0^=S0<<17; uint32_t u=G[S0%ng]; S0^=S0<<13;S0^=S0>>7;S0^=S0<<17; uint32_t v=G[S0%ng]; S0^=S0<<13;S0^=S0>>7;S0^=S0<<17; uint32_t w=G[S0%ng];
  int cnt=0;
  for(uint32_t t1=1;t1<q;t1++) for(uint32_t t2=1;t2<q;t2++){
    Op A=comp(S(u),comp(sc(t1),comp(S(v),comp(sc(t2),S(w)))));
    uint32_t am2=A.c[5],am1=A.c[6],a0=A.c[7],a1=A.c[8];
    if(!am1||!a0) continue;
    if(mul(a1,mul(am1,am1))!=mul(a0,mul(a0,a0))) continue;
    uint32_t s=0; for(int i=0;i<16;i++) s^=A.c[i];
    if(mul(s,a0)!=mul(am1,am1)) continue;
    cnt++; printf("%u %u %u %u %u\n",u,v,w,t1,t2);
  }
  fprintf(stderr,"u=%u v=%u w=%u : %d solutions\n",u,v,w,cnt);
 }
 return 0; }
