// GR(2^K,m), elements packed as m fields of K bits (packed index == element). Row stats by direction class.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint32_t u32;
static int m,K,MOD,RHO=1; static u32 N,FM,HM,ONE; static int fpoly[16];
static inline int dig(u32 x,int i){return (x>>(K*i))&(MOD-1);}
static inline u32 add(u32 a,u32 b){return ((a&~HM)+(b&~HM))^((a^b)&HM);}
static inline u32 neg(u32 b){return add((~b)&FM,ONE);}
static inline u32 sub(u32 a,u32 b){return add(a,neg(b));}
static u32 mul(u32 a,u32 b){int c[40]={0},ad[16],bd[16];
 for(int i=0;i<m;i++){ad[i]=dig(a,i);bd[i]=dig(b,i);}
 for(int i=0;i<m;i++)if(ad[i])for(int j=0;j<m;j++)c[i+j]+=ad[i]*bd[j];
 for(int d=2*m-2;d>=m;d--){int t=c[d]%MOD;if(t)for(int i=0;i<m;i++)c[d-m+i]-=t*fpoly[i];c[d]=0;}
 u32 r=0;for(int i=0;i<m;i++){int t=((c[i]%MOD)+MOD)%MOD;r|=(u32)t<<(K*i);}return r;}
static const char* cls(u32 a){ // ord, exc, v1, v2, ...
 int v=K; for(int i=0;i<m;i++){int d=dig(a,i);int vv=0; if(d==0)vv=K; else while(!((d>>vv)&1))vv++; if(vv<v)v=vv;}
 static char buf[8];
 if(v==0){int ok=1;for(int i=0;i<m;i++)if((dig(a,i)&1)!=((RHO>>i)&1))ok=0; return ok?"exc":"ord";}
 sprintf(buf,"v%d",v); return buf;}
int main(int argc,char**argv){
 if(argc<7){fprintf(stderr,"usage: m K fpolybits termsfile per seed [mode]\n");return 2;}
 if(getenv("RHO"))RHO=atoi(getenv("RHO"));
 m=atoi(argv[1]);K=atoi(argv[2]);
 /* R03 input range checks (fail-closed) */
 if(m<2||m>15){fprintf(stderr,"m out of range [2,15]\n");return 2;}
 if(K<1||K*m>30){fprintf(stderr,"need 1<=K and K*m<=30\n");return 2;}
 MOD=1<<K;long fb=atol(argv[3]);
 if(fb<=0||((fb>>m)&1)!=1||(fb>>(m+1))!=0||(fb&1)!=1){fprintf(stderr,"fpolybits must encode a degree-m polynomial with constant term 1\n");return 2;}
 for(int i=0;i<=m;i++)fpoly[i]=(fb>>i)&1;
 if(RHO<=0||RHO>=(1<<m)){fprintf(stderr,"RHO out of range\n");return 2;}
 N=1u<<(K*m);FM=N-1;HM=0;ONE=0;for(int i=0;i<m;i++){HM|=(u32)(MOD>>1)<<(K*i);ONE|=1u<<(K*i);}
 FILE*tf=fopen(argv[4],"r");if(!tf){fprintf(stderr,"missing %s\n",argv[4]);return 3;}int nt;if(fscanf(tf,"%d",&nt)!=1)return 1;if(nt<1||nt>1000000){fprintf(stderr,"term count out of range\n");return 2;}long*E=malloc(sizeof(long)*nt);u32*C=malloc(sizeof(u32)*nt);if(!E||!C){fprintf(stderr,"oom\n");return 4;}
 for(int t=0;t<nt;t++){if(fscanf(tf,"%ld",&E[t])!=1)return 1;if(E[t]<0||E[t]>=(1L<<62)){fprintf(stderr,"exponent out of range\n");return 2;}u32 c=0;for(int i=0;i<m;i++){int d;if(fscanf(tf,"%d",&d)!=1)return 1;c|=(u32)(((d%MOD)+MOD)%MOD)<<(K*i);}C[t]=c;}
 int maxb=1;for(int t=0;t<nt;t++){int b=0;while(E[t]>>b)b++;if(b>maxb)maxb=b;}
 u32*F=malloc(sizeof(u32)*N);if(!F){fprintf(stderr,"oom\n");return 4;}u32 pw[64];
 for(u32 x=0;x<N;x++){pw[0]=x;for(int b=1;b<maxb;b++)pw[b]=mul(pw[b-1],pw[b-1]);u32 acc=0;
  for(int t=0;t<nt;t++){u32 v=1u;int first=1;for(int b=0;b<maxb;b++)if((E[t]>>b)&1){v=first?pw[b]:mul(v,pw[b]);first=0;}acc=add(acc,mul(C[t],v));}F[x]=acc;}
 {char*s=calloc(N,1);if(!s){fprintf(stderr,"oom\n");return 4;}long d=0;for(u32 x=0;x<N;x++){if(s[F[x]])d++;s[F[x]]=1;}printf("perm_dups %ld\n",d);free(s);}
 int per=atoi(argv[5]);srand(atoi(argv[6]));
 int*cnt=calloc(N,sizeof(int));
 const char*names[]={"ord","exc","v1","v2","v3","v4","v5"};int got[7]={0};
 char*used=calloc(N,1); if(!cnt||!used){fprintf(stderr,"oom\n");return 4;} long guard=0; const char*mode=argc>7?argv[7]:"sample";
 int allmode=strcmp(mode,"sample")!=0; u32 iter=0;
 while(1){u32 a; if(allmode){iter++; if(iter>=N)break; a=iter; if(strcmp(cls(a),mode))continue;} else { if(guard++>=50000000)break; a=(((u32)rand()<<16)^rand())&FM; if(!a||used[a])continue;} const char*c=cls(a);int ci=-1;for(int k=0;k<7;k++)if(!strcmp(c,names[k]))ci=k; if(ci<0||(!allmode&&got[ci]>=per))continue; got[ci]++; used[a]=1;
  int mx=0;for(u32 x=0;x<N;x++){u32 df=sub(F[add(x,a)],F[x]);int v=++cnt[df];if(v>mx)mx=v;}
  int vals[64],nv[64],nvals=0;for(u32 x=0;x<N;x++){u32 df=sub(F[add(x,a)],F[x]);int v=cnt[df];if(v){int k;for(k=0;k<nvals;k++)if(vals[k]==v)break;if(k==nvals){if(nvals<64){vals[nvals]=v;nv[nvals]=0;nvals++;}else k=63;}nv[k]++;cnt[df]=0;}}
  printf("%s %u max %d |",c,a,mx);for(int k=0;k<nvals;k++)printf(" %dx%d",vals[k],nv[k]);printf("\n");fflush(stdout);
  if(!allmode){int done=1;for(int k=0;k<K+1&&k<7;k++)if(got[k]<per)done=0; if(done)break;}}
 return 0;}
