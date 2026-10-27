#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
/* GF(2^m) with modulus given; count affine points of Q=(h(z)+h(w))/(z+w) via sum N(N-1)+1 */
static int m; static uint32_t mod;
static uint32_t mul(uint32_t a,uint32_t b){uint32_t r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a>>m&1)a^=mod;}return r;}
int main(int argc,char**argv){m=atoi(argv[1]);mod=strtoul(argv[2],0,0);uint32_t q=1u<<m;
 uint32_t *cnt=calloc(q,4);
 for(uint32_t z=0;z<q;z++){uint32_t z2=mul(z,z),z4=mul(z2,z2),z8=mul(z4,z4),z12=mul(z8,z4),z14=mul(z12,z2),z15=mul(z14,z);
  cnt[z15^z14^z12^z8]++;}
 unsigned long long s=1; for(uint32_t c=0;c<q;c++) s+=(unsigned long long)cnt[c]*(cnt[c]-1);
 printf("m=%d points=%llu\n",m,s); return 0;}
