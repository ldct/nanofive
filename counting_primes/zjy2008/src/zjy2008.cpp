// Library Checker "Counting Primes", submission 346093 by zjy2008 (15 ms):
// https://judge.yosupo.jp/submission/346093
// The RV32IM port of prime_benchmark/counting_primes_zjy2008.py, recompiled
// for RV64IM. pi below is that port's pi (port changes marked //*: fdiv() is an
// exact integer division, sqrtl -> integer sqrt), except that it is not
// `inline`, so that start.S can call it. The port's I/O (read_u64, print_u64,
// main) is replaced by start.S, which calls pi with N in a0 and prints the
// result with ecall 1, so the program meets the same specification as the
// other counting_primes programs.
// ---- runtime (from the port's rt.h) ----
#include <stdint.h>
#include <stddef.h>
namespace std {}

extern "C" void *memset(void *d, int c, size_t n) {  // gcc emits calls to it
  unsigned char *p = (unsigned char *)d; while (n--) *p++ = c; return d;
}

extern char _end[];                    // end of .bss, from the linker script
static char *heap = _end;
template <typename T> struct vector {  // just enough of std::vector: vector<T> v(n) is n zeros
  T *d;
  explicit vector(size_t n) : d((T *)((uintptr_t)(heap + 7) & ~(uintptr_t)7)) {
    heap = (char *)(d + n); memset(d, 0, n * sizeof(T));
  }
  T &operator[](size_t i) { return d[i]; }
};

static uint64_t isqrt64(uint64_t n) {  // floor(sqrt(n)), what sqrtl gives for n <= 1e11
  uint64_t x = n, y = (x + 1) / 2;
  while (y < x) { x = y; y = (x + n / x) / 2; }
  return x;
}
// ---- end of rt.h ----

#define LL long long
#define uint unsigned
#define uLL unsigned long long
using namespace std;
inline LL fdiv(const LL&x,const LL&y){
	return x/y;  //* static_cast<LL>(static_cast<double>(x)/static_cast<double>(y))
}
LL pi(LL n){  //* was inline
	if(n<7)return (2<=n)+(3<=n)+(5<=n);
	const int R=isqrt64(n),sqR=isqrt64(R);  //* sqrtl(n), sqrtl(R)
	int C=0,V=(R+1)/2;
	vector<int>small(V),rough(V);
	vector<bool>skip(R+1);
	vector<LL>large(V);
	for(int i=0;i<V;++i)small[i]=i,rough[i]=i*2+1,large[i]=(fdiv(n,i*2+1)-1)>>1;
	const auto calc=[&](int p){
		skip[p]=1;
		for(int i=p*p;i<=R;i+=p+p)skip[i]=1;
		int m=0;
		for(int i=0;i<V;++i)if(!skip[rough[i]]){
			LL d=1LL*rough[i]*p;
			large[m]=large[i]-(d<=R?large[small[d>>1]-C]:small[(fdiv(n,d)-1)>>1])+C;
			rough[m++]=rough[i];
		}
		V=m,m=(R-1)>>1;
		for(int i=(R/p-1)|1;i>=p;i-=2){
			int s=small[i>>1]-C;
			for(int j=(i*p)>>1;j<=m;--m)small[m]-=s;
		}
		++C;
	};
	if(9<=R){
		calc(3);
		if(25<=R){
			calc(5);
			static const int wheel[8]={4,2,4,2,4,6,2,6};
			for(int p=7,c=0;p<=sqR;p+=wheel[(c++)&7])if(!skip[p])calc(p);
		}
	}
	LL z=large[0]+1+(V+C+C-2)*(V-1LL)/2;
	for(int i=1;i<V;++i)z-=large[i];
	for(int i=1;i<V;++i){
		int q=rough[i];
		LL y=fdiv(n,q);
		int e=small[(fdiv(y,q)-1)>>1]-C;
		if(e<i+1)break;
		for(int j=i+1;j<=e;++j)z+=small[(fdiv(y,rough[j])-1)>>1];
		z-=(e-i)*(C+i-1LL);
	}
	return z;
}
