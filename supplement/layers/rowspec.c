// Exhaustive row spectra of a lift F over GR(2^K,m) for a given list of directions alpha.
// usage: rowspec m K fpolybits termsfile alphasfile   (alphas: packed integers, one per line)
// packing: element = sum_i digit_i << (K*i), digit_i in [0,2^K) is the coefficient of t^i.
// output per alpha: "alpha <packed> | v1xc1 v2xc2 ..." (value x number-of-beta), values sorted.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint32_t u32;
static int m,K,MOD; static u32 N,FM,HM,ONE; static int fpoly[16];
static inline int dig(u32 x,int i){return (x>>(K*i))&(MOD-1);}
static inline u32 add(u32 a,u32 b){return ((a&~HM)+(b&~HM))^((a^b)&HM);}
static inline u32 neg(u32 b){return add((~b)&FM,ONE);}
static inline u32 sub(u32 a,u32 b){return add(a,neg(b));}
static u32 mul(u32 a,u32 b){long c[40]={0};int ad[16],bd[16];
 for(int i=0;i<m;i++){ad[i]=dig(a,i);bd[i]=dig(b,i);}
 for(int i=0;i<m;i++)if(ad[i])for(int j=0;j<m;j++)c[i+j]+=(long)ad[i]*bd[j];
 for(int d=2*m-2;d>=m;d--){long t=c[d]%MOD;if(t)for(int i=0;i<m;i++)c[d-m+i]-=t*fpoly[i];c[d]=0;}
 u32 r=0;for(int i=0;i<m;i++){long t=((c[i]%MOD)+MOD)%MOD;r|=(u32)t<<(K*i);}return r;}
static int cmpi(const void*a,const void*b){long x=*(long*)a,y=*(long*)b;return x<y?-1:x>y;}
int main(int argc,char**argv){
 if(argc<6){fprintf(stderr,"usage\n");return 2;}
 m=atoi(argv[1]);K=atoi(argv[2]);MOD=1<<K;long fb=atol(argv[3]);
 if(K*m>30||m>15){fprintf(stderr,"too big\n");return 2;}
 for(int i=0;i<=m;i++)fpoly[i]=(fb>>i)&1;
 N=1u<<(K*m);FM=N-1;HM=0;ONE=0;for(int i=0;i<m;i++){HM|=(u32)(MOD>>1)<<(K*i);ONE|=1u<<(K*i);}
 FILE*tf=fopen(argv[4],"r");int nt;if(fscanf(tf,"%d",&nt)!=1)return 1;long*E=malloc(sizeof(long)*nt);u32*C=malloc(sizeof(u32)*nt);
 for(int t=0;t<nt;t++){if(fscanf(tf,"%ld",&E[t])!=1)return 1;u32 c=0;for(int i=0;i<m;i++){int d;if(fscanf(tf,"%d",&d)!=1)return 1;c|=(u32)(((d%MOD)+MOD)%MOD)<<(K*i);}C[t]=c;}
 fclose(tf);
 int maxb=1;for(int t=0;t<nt;t++){int b=0;while(E[t]>>b)b++;if(b>maxb)maxb=b;}
 u32*F=malloc(sizeof(u32)*N);u32 pw[64];
 for(u32 x=0;x<N;x++){pw[0]=x;for(int b=1;b<maxb;b++)pw[b]=mul(pw[b-1],pw[b-1]);u32 acc=0;
  for(int t=0;t<nt;t++){u32 v=0;int first=1;for(int b=0;b<maxb;b++)if((E[t]>>b)&1){v=first?pw[b]:mul(v,pw[b]);first=0;}
   if(first)v=1u; acc=add(acc,mul(C[t],v));}F[x]=acc;}
 int*cnt=calloc(N,sizeof(int)); long *hist=calloc(N+1,sizeof(long));
 FILE*af=fopen(argv[5],"r"); unsigned long al;
 while(fscanf(af,"%lu",&al)==1){u32 a=(u32)al;
  for(u32 x=0;x<N;x++){cnt[sub(F[add(x,a)],F[x])]++;}
  // histogram of values
  long nv=0; long *vals=malloc(sizeof(long)*64*2); 
  for(u32 y=0;y<N;y++){int v=cnt[y]; if(v){hist[v]++; cnt[y]=0;}}
  printf("alpha %u |",a);
  for(u32 v=1;v<=N;v++) if(hist[v]){printf(" %ux%ld",v,hist[v]);hist[v]=0;}
  printf("\n");fflush(stdout); free(vals);}
 return 0;}
