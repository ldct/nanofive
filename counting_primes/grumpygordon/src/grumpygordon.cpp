// Library Checker "Counting Primes", submission 50137 by grumpygordon (14 ms):
// https://judge.yosupo.jp/submission/50137
// The RV32IM port of prime_benchmark/counting_primes_grumpygordon.py, recompiled
// for RV64IM. prime_pi below is that port's prime_pi, unchanged (port changes
// marked //*: no avx2/O3 attribute, and divide() is an exact integer division).
// The port's I/O (read_u64, print_u64, main) is replaced by start.S, which
// calls prime_pi with N in a0 and prints the result with ecall 1, so the
// program meets the same specification as the other counting_primes programs.
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

using namespace std;

using i64 = long long;

int isqrt(i64 n) {
  return isqrt64(n);  //* sqrtl(n)
}

i64 prime_pi(const i64 N) {  //* __attribute__((target("avx2"), optimize("O3", "unroll-loops")))
  if (N <= 1) return 0;
  if (N == 2) return 1;
  const int v = isqrt(N);
  int s = (v + 1) / 2;
  vector<int> smalls(s); for (int i = 1; i < s; ++i) smalls[i] = i;
  vector<int> roughs(s); for (int i = 0; i < s; ++i) roughs[i] = 2 * i + 1;
  vector<i64> larges(s); for (int i = 0; i < s; ++i) larges[i] = (N / (2 * i + 1) - 1) / 2;
  vector<bool> skip(v + 1);
  const auto divide = [] (i64 n, i64 d) -> int { return n / d; };  //* double(n) / d
  const auto half = [] (int n) -> int { return (n - 1) >> 1; };
  int pc = 0;
  for (int p = 3; p <= v; p += 2) if (!skip[p]) {
    int q = p * p;
    if (i64(q) * q > N) break;
    skip[p] = true;
    for (int i = q; i <= v; i += 2 * p) skip[i] = true;
    int ns = 0;
    for (int k = 0; k < s; ++k) {
      int i = roughs[k];
      if (skip[i]) continue;
      i64 d = i64(i) * p;
      larges[ns] = larges[k] - (d <= v ? larges[smalls[d >> 1] - pc] : smalls[half(divide(N, d))]) + pc;
      roughs[ns++] = i;
    }
    s = ns;
    for (int i = half(v), j = ((v / p) - 1) | 1; j >= p; j -= 2) {
      int c = smalls[j >> 1] - pc;
      for (int e = (j * p) >> 1; i >= e; --i) smalls[i] -= c;
    }
    ++pc;
  }
  larges[0] += i64(s + 2 * (pc - 1)) * (s - 1) / 2;
  for (int k = 1; k < s; ++k) larges[0] -= larges[k];
  for (int l = 1; l < s; ++l) {
    int q = roughs[l];
    i64 M = N / q;
    int e = smalls[half(M / q)] - pc;
    if (e < l + 1) break;
    i64 t = 0;
    for (int k = l + 1; k <= e; ++k) t += smalls[half(divide(M, roughs[k]))];
    larges[0] += t - i64(e - l) * (pc + l - 1);
  }
  return larges[0] + 1;
}
