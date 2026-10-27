// Reduced exhaustive row spectra for alpha in layer v_j of GR(2^K,m):
// uses only Lemma R: delta_F(alpha,2^j*g) = q^j * #{y in R_K, y mod 2^n (n=K-j) representatives : (F(y+alpha)-F(y))/2^j == g mod 2^n}.
// usage: redspec m K fpolybits termsfile alphasfile ; alphas packed in K-bit digits; j computed from alpha.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t u64;
static int m,K,MOD; static int fpoly[16];
typedef struct {int d[16];} el;
static int nfp, fpi[16];
static el mulr(el a, el b){unsigned c[40]={0};
 for(int i=0;i<m;i++)if(a.d[i]){unsigned ai=a.d[i];for(int j=0;j<m;j++)c[i+j]+=ai*(unsigned)b.d[j];}
 for(int d=2*m-2;d>=m;d--){unsigned t=c[d];if(t)for(int k=0;k<nfp;k++)c[d-m+fpi[k]]-=t;}
 el r;for(int i=0;i<m;i++){r.d[i]=(int)(c[i]&(MOD-1));}return r;}
static el addr(el a, el b){el r;for(int i=0;i<m;i++)r.d[i]=(a.d[i]+b.d[i])&(MOD-1);return r;}
static el subr(el a, el b){el r;for(int i=0;i<m;i++)r.d[i]=(a.d[i]-b.d[i]+MOD)&(MOD-1);return r;}
static int nt,maxb; static long*E; static el*C;
static el evalF(el x){el pw[64];pw[0]=x;for(int b=1;b<maxb;b++)pw[b]=mulr(pw[b-1],pw[b-1]);
 el acc;for(int i=0;i<m;i++)acc.d[i]=0;
 for(int t=0;t<nt;t++){el v;int first=1;for(int b=0;b<maxb;b++)if((E[t]>>b)&1){v=first?pw[b]:mulr(v,pw[b]);first=0;}
  if(first){for(int i=0;i<m;i++)v.d[i]=0;v.d[0]=1;} acc=addr(acc,mulr(C[t],v));}
 return acc;}
int main(int argc,char**argv){
 m=atoi(argv[1]);K=atoi(argv[2]);MOD=1<<K;long fb=atol(argv[3]);
 for(int i=0;i<=m;i++)fpoly[i]=(fb>>i)&1;
 nfp=0;for(int i=0;i<m;i++)if(fpoly[i])fpi[nfp++]=i;
 FILE*tf=fopen(argv[4],"r");if(fscanf(tf,"%d",&nt)!=1)return 1;E=malloc(sizeof(long)*nt);C=malloc(sizeof(el)*nt);
 for(int t=0;t<nt;t++){if(fscanf(tf,"%ld",&E[t])!=1)return 1;for(int i=0;i<m;i++){int d;if(fscanf(tf,"%d",&d)!=1)return 1;C[t].d[i]=((d%MOD)+MOD)%MOD;}}
 maxb=1;for(int t=0;t<nt;t++){int b=0;while(E[t]>>b)b++;if(b>maxb)maxb=b;}
 FILE*af=fopen(argv[5],"r"); unsigned long long al;
 while(fscanf(af,"%llu",&al)==1){el a;for(int i=0;i<m;i++)a.d[i]=(al>>(K*i))&(MOD-1);
  int j=K;for(int i=0;i<m;i++){int x=a.d[i],v=0;if(!x)continue;while(!((x>>v)&1))v++;if(v<j)j=v;}
  int n=K-j; u64 NN=1ull<<(n*m); int*cnt=calloc(NN,sizeof(int));
  for(u64 y=0;y<NN;y++){el x;for(int i=0;i<m;i++)x.d[i]=(y>>(n*i))&((1<<n)-1);
   el D=subr(evalF(addr(x,a)),evalF(x)); u64 idx=0;
   for(int i=0;i<m;i++){if(D.d[i]&((1<<j)-1)){fprintf(stderr,"valuation violated\n");return 5;} idx|=(u64)((D.d[i]>>j)&((1<<n)-1))<<(n*i);}
   cnt[idx]++;}
  long*hist=calloc(NN+1,sizeof(long)); for(u64 y=0;y<NN;y++)hist[cnt[y]]++;
  long qj=1;for(int i=0;i<j*m;i++)qj*=2;
  printf("alpha %llu j %d |",al,j); for(u64 v=1;v<=NN;v++)if(hist[v])printf(" %ldx%ld",v*qj,hist[v]); printf("\n");fflush(stdout);
  free(cnt);free(hist);}
 return 0;}
