// Audit indépendant : énumération de TOUS les couples g,f, puis déduplication
// des matrices. Aucun critère de Claude n'est utilisé pour tester le complément.
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using U=__uint128_t;
using namespace std;
int main(int argc,char**argv){
 int maxn=argc>1?atoi(argv[1]):13;
 assert(1<=maxn && maxn<=13);
 cout<<"n,total_couples,matrices_distinctes,complement_riordan,formule,erreurs_critere,secondes\n"<<flush;
 for(int n=1;n<=maxn;++n){
  auto start=chrono::steady_clock::now();int m=n-1;
  if(m==0){cout<<"1,1,1,1,1,0,0\n"<<flush;continue;}
  unsigned Q=1u<<m, mask=Q-1;
  // Table de multiplication des polynômes dans F_2[t]/(t^m).
  vector<uint16_t> mt(size_t(Q)*Q);
  for(unsigned a=0;a<Q;++a)for(unsigned b=1;b<Q;++b){
   unsigned bit=b&-b;
   mt[size_t(a)*Q+b]=mt[size_t(a)*Q+(b^bit)] ^ ((a<<__builtin_ctz(bit))&mask);
  }
  vector<U> matrices;matrices.reserve(size_t(Q)*(Q/2));
  for(unsigned g=0;g<Q;++g)for(unsigned f=0;f<Q;f+=2){
   unsigned col=g;U R=0;int offset=0;
   for(int j=0;j<m;++j){
    assert((col&((1u<<j)-1))==0);
    R|=U(col>>j)<<offset;offset+=m-j;
    col=mt[size_t(col)*Q+f];
   }
   matrices.push_back(R);
  }
  sort(matrices.begin(),matrices.end());
  matrices.erase(unique(matrices.begin(),matrices.end()),matrices.end());
  U full=(U(1)<<(m*(m+1)/2))-1;
  vector<bool> good(matrices.size(),false);
  size_t lo=0,hi=matrices.size()-1;uint64_t count=0;
  while(lo<=hi){
   U sum=matrices[lo]+matrices[hi];
   if(sum<full)++lo;
   else if(sum>full){if(hi==0)break;--hi;}
   else {
    good[lo]=true;good[hi]=true;count+=(lo==hi?1:2);
    ++lo;if(hi==0)break;--hi;
   }
  }
  uint64_t errors=0, tested=0;vector<uint64_t> byval(m,0);
  for(size_t idx=0;idx<matrices.size();++idx){
   unsigned g=unsigned(matrices[idx]&mask);
   if(g && good[idx]) ++byval[__builtin_ctz(g)];
   if(!g || (g&1))continue;
   unsigned v=__builtin_ctz(g),r=m-v,u=g>>v;
   unsigned c1=(unsigned(matrices[idx]>>m)&((1u<<(m-1))-1))<<1;
   unsigned residual=c1>>v,f=0;
   // Division triangulaire indépendante par l'unité u, pour retrouver f.
   for(unsigned d=0;d<r;++d)if(residual&(1u<<d)){
    f|=1u<<d;residual^=u<<d;
   }
   assert(!(f&1));unsigned delta=f^2u;
   bool pred=(((unsigned(mt[size_t(delta)*Q+delta])<<v)&mask)==0);
   if(pred!=good[idx])++errors;
   ++tested;
  }
  uint64_t expected=1;
  for(int k=1;k<n;++k)expected+=uint64_t(1)<<(3*(k-1)/2);
  uint64_t totalexpected=((uint64_t(1)<<(2*m))+2)/3;
  assert(matrices.size()==totalexpected && count==expected && errors==0);
  for(int v=1;v<m;++v){int r=m-v;assert(byval[v]==(uint64_t(1)<<(r-1+r/2)));}
  double sec=chrono::duration<double>(chrono::steady_clock::now()-start).count();
  cout<<n<<","<<size_t(Q)*(Q/2)<<","<<matrices.size()<<","<<count<<","<<expected<<","<<errors<<","<<sec<<"\n"<<flush;
  cerr<<"n="<<n<<" : critère testé sur "<<tested<<" matrices non nulles de valuation >=1 ; profils v :";
  for(int v=0;v<m;++v)cerr<<" "<<byval[v];cerr<<"\n"<<flush;
 }
}
