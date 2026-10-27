#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int m; static uint32_t mod;
static uint32_t mul(uint32_t a,uint32_t b){uint32_t r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a>>m&1)a^=mod;}return r;}
static uint32_t sq(uint32_t a){return mul(a,a);}
int main(int argc,char**argv){m=atoi(argv[1]);mod=strtoul(argv[2],0,0);uint32_t q=1u<<m;
 /* c is injective iff no nonzero x in kernel; kernel elements x<->c=h(1/x^{1/4}); so injective iff c not in image of h on nonzero z */
 char *hit=calloc(q,1);
 for(uint32_t z=1;z<q;z++){uint32_t z2=sq(z),z4=sq(z2),z8=sq(z4),z12=mul(z8,z4),z14=mul(z12,z2),z15=mul(z14,z);hit[z15^z14^z12^z8]=1;}
 /* direct check for a few c by brute force too */
 int n=0; for(uint32_t c=2;c<q;c++) if(!hit[c]) n++;
 /* brute force verification on all c for small m */
 int nb=0; if(m<=11){ for(uint32_t c=2;c<q;c++){int ok=1; for(uint32_t x=1;x<q&&ok;x++){uint32_t y=x; uint32_t p[64]; p[0]=x; for(int i=1;i<m;i++)p[i]=sq(p[i-1]);
   uint32_t B=p[m-2]^p[m-1]^p[0]^p[1]^mul(c,p[2]); if(!B)ok=0;} nb+=ok;} }
 printf("m=%d |C_m|=%d brute=%d\n",m,n,nb);}
