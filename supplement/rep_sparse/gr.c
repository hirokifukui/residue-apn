/* gr.c : brute-force tools over the Galois ring R_k = (Z/2^k)[t]/(f~), f~ = 0/1 lift of f (as in the paper).
   Elements are packed as m digits of k bits (digit i = coefficient of t^i), so a packed element is also a table index.
   usage:
     gr aset  m poly k terms rho            : A_F(a) for all a (needs k>=2); prints zero count, A_F(0), and the table
     gr rows  m poly k terms rho [nrows seed [r0 r1]]  (nrows=-1: rows with index r0<=r<r1) : exceptional rows (alpha = rho~ + 2t); all rows if nrows=0
     gr ord   m poly k terms rho nrows seed   : sampled ordinary rows (residue of alpha not in {0,rho})
   terms file: first line n, then n lines "e d_0 ... d_{m-1}" (coefficient digits, read mod 2^k).
   Row output: one JSON line per row with the multiset {entry:count}; final SUMMARY line. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int m, k; static uint32_t q, POLY; static uint64_t M;   /* M = 2^k */
static int FH[32];
typedef struct { int d[16]; } E;   /* digits */
static int nt; static uint64_t ex[64]; static E co[64];
static E emul(const E *a, const E *b){ long c[32]={0}; for(int i=0;i<m;i++) if(a->d[i]) for(int j=0;j<m;j++) c[i+j]+= (long)a->d[i]*b->d[j];
  for(int d=2*m-2; d>=m; d--){ long t=c[d]%(long)M; if(t){ for(int i=0;i<m;i++) c[d-m+i]-=t*FH[i]; } c[d]=0; }
  E r; for(int i=0;i<m;i++){ long v=c[i]%(long)M; if(v<0) v+=M; r.d[i]=(int)v; } for(int i=m;i<16;i++) r.d[i]=0; return r; }
static E eadd(const E *a,const E *b){ E r; for(int i=0;i<16;i++) r.d[i]=(int)((a->d[i]+b->d[i])%M); return r; }
static E esub(const E *a,const E *b){ E r; for(int i=0;i<16;i++) r.d[i]=(int)((a->d[i]-b->d[i]+M)%M); return r; }
static uint64_t pack(const E *a){ uint64_t x=0; for(int i=0;i<m;i++) x|=((uint64_t)a->d[i])<<(k*i); return x; }
static E unpack(uint64_t x){ E r; memset(&r,0,sizeof r); for(int i=0;i<m;i++) r.d[i]=(int)((x>>(k*i))&(M-1)); return r; }
static E liftF(uint32_t a){ E r; memset(&r,0,sizeof r); for(int i=0;i<m;i++) r.d[i]=(a>>i)&1; return r; }
static uint32_t res(const E *a){ uint32_t r=0; for(int i=0;i<m;i++) r|=(uint32_t)(a->d[i]&1)<<i; return r; }
/* evaluate polynomial with exponent list ex/co at x (exponents < 2^(2m) allowed): uses x^(2^i) chain */
static E pw2[64];
static E evalT(const E *x, int n, const uint64_t *exs, const E *cos);
static E evalF(const E *x, int deriv){
  /* deriv=1: evaluate F'(x) = sum e*c*x^(e-1) */
  int nb = 0; for(int t=0;t<nt;t++){ uint64_t e=ex[t]; int b=0; while(e){ b++; e>>=1; } if(b>nb) nb=b; }
  pw2[0]=*x; for(int i=1;i<nb;i++) pw2[i]=emul(&pw2[i-1],&pw2[i-1]);
  E acc; memset(&acc,0,sizeof acc);
  for(int t=0;t<nt;t++){ uint64_t e=ex[t]; E c=co[t];
    if(deriv){ if(e==0) continue; for(int i=0;i<m;i++) c.d[i]=(int)((uint64_t)c.d[i]*(e%M)%M); e=e-1; }
    E p; memset(&p,0,sizeof p); p.d[0]=1; int first=1;
    for(int i=0;e;i++,e>>=1) if(e&1){ if(first){ p=pw2[i]; first=0; } else p=emul(&p,&pw2[i]); }
    if(first){ memset(&p,0,sizeof p); p.d[0]=1; }
    p=emul(&c,&p); acc=eadd(&acc,&p); }
  return acc; }
static E evalT(const E *x, int n, const uint64_t *exs, const E *cos){
  int nb=1; for(int t=0;t<n;t++){ uint64_t e=exs[t]; int b=0; while(e){ b++; e>>=1; } if(b>nb) nb=b; }
  E p2[64]; p2[0]=*x; for(int i=1;i<nb;i++) p2[i]=emul(&p2[i-1],&p2[i-1]);
  E acc; memset(&acc,0,sizeof acc);
  for(int t=0;t<n;t++){ uint64_t e=exs[t]; E p; memset(&p,0,sizeof p); p.d[0]=1; int first=1;
    for(int i=0;e;i++,e>>=1) if(e&1){ if(first){ p=p2[i]; first=0; } else p=emul(&p,&p2[i]); }
    E c=cos[t]; p=emul(&c,&p); acc=eadd(&acc,&p); }
  return acc; }
/* SWAR add/sub of packed elements, k-bit fields */
static uint64_t HMASK, LMASK, ONES;
static inline uint64_t padd(uint64_t a,uint64_t b){ return ((a&LMASK)+(b&LMASK)) ^ ((a^b)&HMASK); }
static inline uint64_t pneg(uint64_t b){ return padd(~b & (HMASK|LMASK), ONES); }
static inline uint64_t psub(uint64_t a,uint64_t b){ return padd(a,pneg(b)); }
static uint64_t S=0x9E3779B97F4A7C15ULL; static uint64_t rnd(void){ S^=S<<13; S^=S>>7; S^=S<<17; return S; }
static void read_terms(const char *fn){ FILE *f=fopen(fn,"r"); if(!f){perror(fn);exit(1);} if(fscanf(f,"%d",&nt)!=1) exit(2);
  for(int t=0;t<nt;t++){ unsigned long long e; if(fscanf(f,"%llu",&e)!=1) exit(2); ex[t]=e; memset(&co[t],0,sizeof(E)); for(int i=0;i<m;i++){ long v; if(fscanf(f,"%ld",&v)!=1) exit(2); v%= (long)M; if(v<0) v+=M; co[t].d[i]=(int)v; } } fclose(f); }
int main(int argc,char**argv){
  if(argc<7){ fprintf(stderr,"usage\n"); return 1; }
  const char *mode=argv[1]; m=atoi(argv[2]); POLY=(uint32_t)atol(argv[3]); k=atoi(argv[4]); q=1u<<m; M=1ull<<k;
  for(int i=0;i<=m;i++) FH[i]=(POLY>>i)&1;
  read_terms(argv[5]); uint32_t rho=(uint32_t)atol(argv[6]);
  HMASK=0; LMASK=0; ONES=0; for(int i=0;i<m;i++){ HMASK|=(1ull<<(k-1))<<(k*i); LMASK|=((1ull<<(k-1))-1)<<(k*i); ONES|=1ull<<(k*i); }
  if(!strcmp(mode,"aset")){
    E tau=liftF(rho); long zeros=0; uint32_t A0=0; printf("{\"A\":[");
    for(uint32_t a=0;a<q;a++){ E x=liftF(a); E y=eadd(&x,&tau); E d1=evalF(&y,1), d0=evalF(&x,1); E df=esub(&d1,&d0);
      for(int i=0;i<m;i++) if(df.d[i]&1){ fprintf(stderr,"A: numerator not even at a=%u\n",a); return 3; }
      E h; memset(&h,0,sizeof h); for(int i=0;i<m;i++) h.d[i]=df.d[i]/2; uint32_t Av=res(&h); if(a==0) A0=Av; if(!Av) zeros++;
      printf("%s%u",a?",":"",Av); }
    printf("],\"zeros\":%ld,\"A0\":%u}\n",zeros,A0); return 0; }
  /* build F table over R_k (direct evaluation, or Taylor expansion at Teichmueller points if mode ends with 'T') */
  uint64_t N = 1ull<<(k*m);
  uint32_t *T = malloc(N*sizeof(uint32_t)); if(!T){ fprintf(stderr,"oom\n"); return 4; }
  int taylor = mode[strlen(mode)-1]=='T';
  if(!taylor){ for(uint64_t x=0;x<N;x++){ E xe=unpack(x); E v=evalF(&xe,0); T[x]=(uint32_t)pack(&v); } }
  else {
    /* F(T(a)+2z) = sum_{i<k} F^[i](T(a)) (2z)^i  exactly in R_k (Hasse derivatives, binomial coefficients exact) */
    static uint64_t hx[4][64]; static E hc[4][64]; int hn[4];
    for(int i=0;i<k && i<4;i++){ hn[i]=0; for(int t=0;t<nt;t++){ if(ex[t]<(uint64_t)i) continue; uint64_t b=1; for(int j=0;j<i;j++) b=b*(ex[t]-j)/(j+1); b%=M; if(!b) continue;
        hx[i][hn[i]]=ex[t]-i; E c=co[t]; for(int d=0;d<m;d++) c.d[d]=(int)((uint64_t)c.d[d]*b%M); hc[i][hn[i]]=c; hn[i]++; } }
    uint64_t NZ = 1ull<<((k-1)*m);
    for(uint32_t a=0;a<q;a++){
      E ta=liftF(a); for(int j=0;j<m*(k-1);j++) ta=emul(&ta,&ta);   /* Teichmueller T(a) = a~^(q^(k-1)) */
      E cf[4]; for(int i=0;i<k;i++) cf[i]=evalT(&ta,hn[i],hx[i],hc[i]);
      for(uint64_t zz=0; zz<NZ; zz++){
        E z; memset(&z,0,sizeof z); for(int d=0;d<m;d++) z.d[d]=(int)((zz>>((k-1)*d)) & ((1ull<<(k-1))-1));
        E h=z; for(int d=0;d<m;d++) h.d[d]=(int)(2*h.d[d]%M);          /* h = 2z */
        E acc=cf[k-1]; for(int i=k-2;i>=0;i--){ acc=emul(&acc,&h); acc=eadd(&acc,&cf[i]); }
        E xx=eadd(&ta,&h); T[pack(&xx)]=(uint32_t)pack(&acc); } }
  }
  if(argc>11 && !strcmp(argv[11],"crosscheck")){ long bad=0; for(uint64_t x=0;x<N;x++){ E xe=unpack(x); E v=evalF(&xe,0); if(T[x]!=(uint32_t)pack(&v)) bad++; } fprintf(stderr,"taylor-vs-direct mismatches: %ld\n",bad); }
  /* permutation check (lift of a permutation is a permutation) */
  { unsigned char *seen=calloc(N,1); long dup=0; for(uint64_t x=0;x<N;x++){ if(seen[T[x]]) dup++; seen[T[x]]=1; } free(seen); fprintf(stderr,"table built N=%llu dup=%ld\n",(unsigned long long)N,dup); }
  uint32_t *cnt = calloc(N,sizeof(uint32_t)); uint32_t *touched = malloc(N*sizeof(uint32_t));
  long nrows = argc>7? atol(argv[7]) : 0; if(argc>8) S ^= (uint64_t)atoll(argv[8])*0x2545F4914F6CDD1DULL;
  int ord = !strncmp(mode,"ord",3);
  uint64_t qk1 = N / q;   /* q^(k-1) */
  long done=0, match=0, mismatch=0; uint32_t gmax=0;
  uint64_t r0=0; uint64_t total = ord? (uint64_t)nrows : (nrows>0? (uint64_t)nrows : qk1);
  if(!ord && nrows<0){ r0=(uint64_t)atoll(argv[9]); total=(uint64_t)atoll(argv[10]); nrows=0; }
  E rt = liftF(rho);
  for(uint64_t r=r0;r<total;r++){
    uint64_t alpha;
    if(ord){ uint32_t a0; do { a0 = (uint32_t)(rnd()%q); } while(a0==0||a0==rho); E e=liftF(a0); uint64_t t=rnd()%qk1; E tt=unpack(0); /* 2t */
      for(int i=0;i<m;i++){ tt.d[i] = (int)(((t>>((k-1)*i)) & ((1ull<<(k-1))-1))*2 % M); } E s=eadd(&e,&tt); alpha=pack(&s); }
    else { uint64_t t = nrows? rnd()%qk1 : r; E tt=unpack(0); for(int i=0;i<m;i++) tt.d[i]=(int)(((t>>((k-1)*i)) & ((1ull<<(k-1))-1))*2 % M); E s=eadd(&rt,&tt); alpha=pack(&s); }
    uint64_t nt2=0;
    for(uint64_t x=0;x<N;x++){ uint64_t y=padd(x,alpha); uint32_t d=(uint32_t)psub(T[y],T[x]); if(cnt[d]++==0) touched[nt2++]=d; }
    /* multiset */
    uint32_t mx=0; for(uint64_t i=0;i<nt2;i++) if(cnt[touched[i]]>mx) mx=cnt[touched[i]];
    long *mult = calloc(mx+1,sizeof(long)); for(uint64_t i=0;i<nt2;i++){ mult[cnt[touched[i]]]++; cnt[touched[i]]=0; }
    int ok;
    if(ord) ok = (mx<=2);
    else ok = (mx==q && mult[q]==(long)qk1 && nt2==qk1);
    if(ok) match++; else mismatch++;
    if(mx>gmax) gmax=mx;
    if(!ok || r<r0+3){ printf("{\"alpha\":%llu,\"max\":%u,\"multiset\":{",(unsigned long long)alpha,mx); int f=1; for(uint32_t v=1;v<=mx;v++) if(mult[v]){ printf("%s\"%u\":%ld",f?"":",",v,mult[v]); f=0; } printf("},\"ok\":%d}\n",ok); }
    free(mult); done++;
  }
  printf("SUMMARY {\"mode\":\"%s\",\"m\":%d,\"k\":%d,\"rows\":%ld,\"MATCH\":%ld,\"MISMATCH\":%ld,\"max_entry\":%u,\"prediction\":\"%s\"}\n",mode,m,k,done,match,mismatch,gmax, ord? "entries<=2":"q^(k-1) entries equal to q");
  return 0; }
