// A = S_u th S_v; conditions (i) a1 am1^2 = a0^3, (ii) am2^2 a0 = am1^3. print u th v and G-membership
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int m; static uint32_t q,P; static uint32_t *LOG,*EXP;
static uint32_t mulr(uint32_t a,uint32_t b){uint32_t r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&q)a^=P;}return r;}
static inline uint32_t mul(uint32_t a,uint32_t b){ if(!a||!b) return 0; return EXP[(LOG[a]+LOG[b])%(q-1)]; }
static uint32_t sqr(uint32_t a){ if(!a) return 0; uint32_t l=LOG[a]; if(l&1) l+=q-1; return EXP[(l/2)%(q-1)]; }
static int noroot(uint32_t g){ for(uint32_t y=0;y<q;y++) if((mul(y,mul(y,y))^y^g)==0) return 0; return 1; }
int main(int argc,char**argv){ m=atoi(argv[1]); P=atoi(argv[2]); q=1u<<m; LOG=calloc(q,4); EXP=calloc(2*q,4);
 for(uint32_t g=2;g<q;g++){ uint32_t x=1; int ok=1; for(uint32_t i=0;i<q-1;i++){ EXP[i]=x; LOG[x]=i; x=mulr(x,g); if(x==1 && i<q-2){ok=0;break;} } if(ok) break; }
 char *G=calloc(q,1); for(uint32_t g=1;g<q;g++) G[g]=noroot(g);
 long n=0,ng=0;
 for(uint32_t u=1;u<q;u++) for(uint32_t th=1;th<q;th++) for(uint32_t v=1;v<q;v++){
   uint32_t sth=sqr(th), X=mul(u,sth);
   uint32_t am2=mul(X,sqr(v)), am1=X^mul(th,v), a0=X^th^mul(mul(th,th),mul(v,v)), a1=th^mul(th,th);
   if(!am1||!a0) continue;
   if(mul(a1,mul(am1,am1))!=mul(a0,mul(a0,a0))) continue;
   if(mul(mul(am2,am2),a0)!=mul(am1,mul(am1,am1))) continue;
   n++; if(G[u]&&G[v]) ng++;
   printf("%u %u %u %d %d\n",u,th,v,G[u],G[v]);
 }
 fprintf(stderr,"m=%d curve points %ld, both in G %ld\n",m,n,ng); return 0; }
