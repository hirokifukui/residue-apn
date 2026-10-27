/* kercount.c: for B_c(x) = x^(2^(m-2)) + x^(2^(m-1)) + x + x^2 + c x^4 over F_{2^m}:
   kernel elements y=x^(1/4) != 0 satisfy c = h(z), z = 1/y, h(z) = z^15+z^14+z^12+z^8.
   Prints: #c with B_c injective (= q - |h(F_q^*)|), N_ge2 = #c with dim ker >= 2,
   fiber-size histogram, and the affine point count of Q(z,w) = (h(z)+h(w))/(z+w) = 0 over F_q
   (= sum_c N_c(N_c-1) + 1, N_c counted over all z in F_q; the +1 is the point (0,0)).
   Also checks c=1 injectivity (expected iff 5 does not divide m).  usage: kercount m poly */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint32_t q, P; static int m;
static uint32_t mul(uint32_t a, uint32_t b){ uint32_t r=0; while(b){ if(b&1) r^=a; b>>=1; a<<=1; if(a&q) a^=P; } return r; }
static uint32_t pw(uint32_t a, uint64_t e){ uint32_t r=1; while(e){ if(e&1) r=mul(r,a); a=mul(a,a); e>>=1; } return r; }
int main(int argc, char **argv){
  m = atoi(argv[1]); P = (uint32_t)atol(argv[2]); q = 1u<<m;
  uint32_t *cnt = calloc(q, 4);
  for(uint32_t z=0; z<q; z++){ uint32_t z2=mul(z,z), z4=mul(z2,z2), z8=mul(z4,z4); uint32_t z12=mul(z8,z4), z14=mul(z12,z2), z15=mul(z14,z);
    uint32_t h = z15^z14^z12^z8; cnt[h]++; }
  /* fibers over F_q^* : subtract z=0 contribution (h(0)=0) */
  uint64_t pts = 1; long hist[64]={0}; long img_star=0; long nge2=0;
  for(uint32_t c=0;c<q;c++){ uint64_t n=cnt[c]; pts += n*(n-1); uint32_t nstar = n - (c==0); if(nstar){ img_star++; if(nstar<64) hist[nstar]++; if(nstar>=3) nge2++; } }
  long ninj = (long)q - img_star;
  int c1inj = (cnt[1]==0);
  printf("{\"m\":%d,\"q\":%u,\"n_injective_c\":%ld,\"N_ge2\":%ld,\"c1_injective\":%d,\"curve_affine_points\":%llu,\"fiber_hist\":{",m,q,ninj,nge2,c1inj,(unsigned long long)pts);
  int first=1; for(int i=1;i<64;i++) if(hist[i]){ printf("%s\"%d\":%ld",first?"":",",i,hist[i]); first=0; }
  long s=1; for(int i=2;i<64;i++) s+=hist[i]*(i-1); printf("},\"identity_ninj_eq_1_plus_sum_(n-1)\":%d}\n", (int)(s==ninj));
  return 0; }
