// Library Checker "Counting Primes", submission 195894 by lpha (13 ms):
// https://judge.yosupo.jp/submission/195894
// The RV32IM port of prime_benchmark/counting_primes_lpha.py, recompiled for
// RV64IM. prime_count below is that port's prime_count, unchanged (port changes
// marked //*: integer sqrt, plain 64-bit divisions for divide_p and invs[]).
// The port's I/O (read_u64, print_u64, main) is replaced by start.S, which
// calls prime_count with N in a0 and prints the result with ecall 1, so the
// program meets the same specification as the other counting_primes programs.
// ---- runtime (from the port's rt.h) ----
#include <stdint.h>
#include <stddef.h>
namespace std {}

extern "C" void *memset(void *d, int c, size_t n) {  // gcc emits calls to it
  unsigned char *p = (unsigned char *)d; while (n--) *p++ = c; return d;
}

static uint64_t isqrt64(uint64_t n) {  // floor(sqrt(n)), what sqrtl gives for n <= 1e11
  uint64_t x = n, y = (x + 1) / 2;
  while (y < x) { x = y; y = (x + n / x) / 2; }
  return x;
}
// ---- end of rt.h ----

uint32_t prime_count( uint64_t N ) {  //* __attribute__((optimize("O3")))
    if (N <= 1) return 0;

    const uint64_t v = isqrt64(N);  //* std::sqrt(N)
    size_t s = ( v + 1 ) / 2;

    constexpr size_t V = 316228;  //* std::sqrt(1e11) + 1
    uint32_t smalls[V/2];
    uint32_t larges[V/2];
    uint32_t roughs[V/2];
    uint64_t invs  [V/2];
    bool     smooth[V] = {};
    for( size_t i = 0; i < s; ++i ) {
        smalls[i] = i;
        roughs[i] = 2 * i + 1;
        invs  [i] = N / roughs[i];  //* (double)N / roughs[i]
        larges[i] = (invs[i] - 1) / 2;
    }
    const auto index = []( uint64_t n ) -> size_t { return ( n - 1 ) / 2 ; };

    uint32_t pc = 0;
    for( uint64_t p = 3; p * p <= v; p += 2 ) {
        if( smooth[p] ) { continue; }
        smooth[p] = true;
        for( uint64_t i = p * p; i <= v; i += 2 * p ) {
            smooth[i] = true;
        }

        const auto divide_p = [p]( uint64_t inv_j ) -> uint64_t { return inv_j / p; };  //* [invp = (__uint128_t(1) << 102) / p + 1] ... inv_j * invp >> 102

        size_t ns = 0;
        size_t k = 0;
        for( ; ; ++k ) {
            const uint64_t j = roughs[k];
            if( smooth[j] ) { continue; }
            if( j * p > v ) { break; }

            larges[ns] = larges[k] - larges[smalls[j * p / 2] - pc] + pc;
            invs  [ns] = invs  [k];
            roughs[ns] = roughs[k];
            ++ns;
        }
        for( ; k < s; ++k ) {
            const uint64_t j = roughs[k];
            if( smooth[j] ) { continue; }

            larges[ns] = larges[k] - smalls[index( divide_p( invs[k] ) )] + pc;
            invs  [ns] = invs  [k];
            roughs[ns] = roughs[k];
            ++ns;
        }
        s = ns;

        uint64_t i = ( v - 1 ) / 2;
        for( uint64_t j = ( ( v / p ) - 1 ) | 1; j >= p; j -= 2 ) {
            const uint32_t d = smalls[j / 2] - pc;
            for( ; i >= j * p / 2; --i ) {
                smalls[i] -= d;
            }
        }

        ++pc;
    }

    uint32_t ret = 1;

    ret += larges[0];

    for( size_t k = 1; k < s; ++k ) {
        ret -= larges[k];
    }
    ret += s * ( s - 1 ) / 2 + ( pc - 1 ) * ( s - 1 );

    for( size_t k1 = 1; k1 < s; ++k1 ) {
        const uint64_t p = roughs[k1];
        const auto divide_p = [p]( uint64_t inv_j ) -> uint64_t { return inv_j / p; };  //* 128-bit reciprocal

        const size_t k2_max = smalls[index( divide_p( invs[k1] ) )] - pc;
        if( k2_max <= k1 ) { break; }
        for( size_t k2 = k1 + 1; k2 <= k2_max; ++k2 ) {
            ret += smalls[index( divide_p( invs[k2] ) )];
        }
        ret -= ( k2_max - k1 ) * ( pc + k1 - 1 );
    }

    return ret;
}
