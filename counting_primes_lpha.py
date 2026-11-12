from machine import *

# Library Checker "Counting Primes" (https://judge.yosupo.jp/problem/counting_primes,
# N <= 1e11): fast accepted submission 195894 by lpha, ported to nanofive.
# Compiled to RV32IM machine code (no libc/libstdc++; I/O via ecalls, RARS
# convention, see machine.ECALL) with riscv64-unknown-elf-g++ 13.2:
#   g++ -march=rv32im -mabi=ilp32 -O2 -std=c++17 -ffreestanding -nostdlib
#       -fno-exceptions -fno-rtti -fno-tree-loop-distribute-patterns
#       -fno-threadsafe-statics -DMEM_SIZE=0x400000 ... -lgcc
# (libgcc supplies the 64-bit division routines __udivdi3 etc.)
# and laid out flat from address 0: code, then read-only data. Zeroed data
# (.bss) follows the image; the stack grows down from the top of memory.
# Startup code:
#   _start: li sp, MEM_SIZE; call main; li a7, 93; ecall   (exit(main()))
# Reads N from stdin, prints pi(N) = the number of primes <= N.
#   echo 100000000 | python3 counting_primes_lpha.py   ->  5761455
#
# C++ source:
#
#   // Library Checker "Counting Primes", submission 195894 by lpha (13 ms):
#   // https://judge.yosupo.jp/submission/195894
#   // Rough-number Lucy/min_25 prime counting; all tables on the stack, sized for N <= 1e11.
#   // Port changes (marked //*): runtime from rt.h instead of <stdio.h>/<cmath>,
#   // std::sqrt -> integer sqrt, and divide_p's 128-bit reciprocal multiply
#   // (rv32 gcc has no __uint128_t) and the double division for invs[] are plain
#   // 64-bit integer divisions with the same results.
#   // ---- rt.h (inlined) ----
#   // Freestanding runtime for nanofive (no libc / libstdc++): I/O through the
#   // RARS-style ecalls (a7=12 read char, a7=11 print char), a bump allocator
#   // for vector<T>, and the integer square root the submissions get from sqrtl.
#   #include <stdint.h>
#   #include <stddef.h>
#   namespace std {}
#
#   static inline int getchar_() { register int a0 asm("a0"); register int a7 asm("a7") = 12;
#     asm volatile("ecall" : "=r"(a0) : "r"(a7)); return a0; }
#   static inline void putchar_(int c) { register int a0 asm("a0") = c; register int a7 asm("a7") = 11;
#     asm volatile("ecall" :: "r"(a0), "r"(a7)); }
#
#   static uint64_t read_u64() {          // replaces scanf("%lld") / cin >>
#     int c = getchar_();
#     while (c < '0' || c > '9') c = getchar_();
#     uint64_t n = 0;
#     for (; c >= '0' && c <= '9'; c = getchar_()) n = n * 10 + (c - '0');
#     return n;
#   }
#   static void print_u64(uint64_t n) {   // replaces printf("%lld\n") / cout <<
#     char buf[20]; int i = 0;
#     do { buf[i++] = '0' + n % 10; n /= 10; } while (n);
#     while (i) putchar_(buf[--i]);
#     putchar_('\n');
#   }
#
#   extern "C" void *memset(void *d, int c, size_t n) {  // gcc emits calls to it
#     unsigned char *p = (unsigned char *)d; while (n--) *p++ = c; return d;
#   }
#
#   extern char _end[];                    // end of .bss, from the linker script
#   static char *heap = _end;
#   template <typename T> struct vector {  // just enough of std::vector: vector<T> v(n) is n zeros
#     T *d;
#     explicit vector(size_t n) : d((T *)((uintptr_t)(heap + 7) & ~(uintptr_t)7)) {
#       heap = (char *)(d + n); memset(d, 0, n * sizeof(T));
#     }
#     T &operator[](size_t i) { return d[i]; }
#   };
#
#   static uint64_t isqrt64(uint64_t n) {  // floor(sqrt(n)), what sqrtl gives for n <= 1e11
#     uint64_t x = n, y = (x + 1) / 2;
#     while (y < x) { x = y; y = (x + n / x) / 2; }
#     return x;
#   }
#   // ---- end of rt.h ----
#
#   uint32_t prime_count( uint64_t N ) {  //* __attribute__((optimize("O3")))
#       if (N <= 1) return 0;
#
#       const uint64_t v = isqrt64(N);  //* std::sqrt(N)
#       size_t s = ( v + 1 ) / 2;
#
#       constexpr size_t V = 316228;  //* std::sqrt(1e11) + 1
#       uint32_t smalls[V/2];
#       uint32_t larges[V/2];
#       uint32_t roughs[V/2];
#       uint64_t invs  [V/2];
#       bool     smooth[V] = {};
#       for( size_t i = 0; i < s; ++i ) {
#           smalls[i] = i;
#           roughs[i] = 2 * i + 1;
#           invs  [i] = N / roughs[i];  //* (double)N / roughs[i]
#           larges[i] = (invs[i] - 1) / 2;
#       }
#       const auto index = []( uint64_t n ) -> size_t { return ( n - 1 ) / 2 ; };
#
#       uint32_t pc = 0;
#       for( uint64_t p = 3; p * p <= v; p += 2 ) {
#           if( smooth[p] ) { continue; }
#           smooth[p] = true;
#           for( uint64_t i = p * p; i <= v; i += 2 * p ) {
#               smooth[i] = true;
#           }
#
#           const auto divide_p = [p]( uint64_t inv_j ) -> uint64_t { return inv_j / p; };  //* [invp = (__uint128_t(1) << 102) / p + 1] ... inv_j * invp >> 102
#
#           size_t ns = 0;
#           size_t k = 0;
#           for( ; ; ++k ) {
#               const uint64_t j = roughs[k];
#               if( smooth[j] ) { continue; }
#               if( j * p > v ) { break; }
#
#               larges[ns] = larges[k] - larges[smalls[j * p / 2] - pc] + pc;
#               invs  [ns] = invs  [k];
#               roughs[ns] = roughs[k];
#               ++ns;
#           }
#           for( ; k < s; ++k ) {
#               const uint64_t j = roughs[k];
#               if( smooth[j] ) { continue; }
#
#               larges[ns] = larges[k] - smalls[index( divide_p( invs[k] ) )] + pc;
#               invs  [ns] = invs  [k];
#               roughs[ns] = roughs[k];
#               ++ns;
#           }
#           s = ns;
#
#           uint64_t i = ( v - 1 ) / 2;
#           for( uint64_t j = ( ( v / p ) - 1 ) | 1; j >= p; j -= 2 ) {
#               const uint32_t d = smalls[j / 2] - pc;
#               for( ; i >= j * p / 2; --i ) {
#                   smalls[i] -= d;
#               }
#           }
#
#           ++pc;
#       }
#
#       uint32_t ret = 1;
#
#       ret += larges[0];
#
#       for( size_t k = 1; k < s; ++k ) {
#           ret -= larges[k];
#       }
#       ret += s * ( s - 1 ) / 2 + ( pc - 1 ) * ( s - 1 );
#
#       for( size_t k1 = 1; k1 < s; ++k1 ) {
#           const uint64_t p = roughs[k1];
#           const auto divide_p = [p]( uint64_t inv_j ) -> uint64_t { return inv_j / p; };  //* 128-bit reciprocal
#
#           const size_t k2_max = smalls[index( divide_p( invs[k1] ) )] - pc;
#           if( k2_max <= k1 ) { break; }
#           for( size_t k2 = k1 + 1; k2 <= k2_max; ++k2 ) {
#               ret += smalls[index( divide_p( invs[k2] ) )];
#           }
#           ret -= ( k2_max - k1 ) * ( pc + k1 - 1 );
#       }
#
#       return ret;
#   }
#
#   int main() {
#       uint64_t n = read_u64();       //* scanf("%" SCNu64, &n)
#       print_u64(prime_count(n));     //* printf("%" PRIu32 "\n", ...)
#   }

prog = [
  # _start:
  0x00400137,  #     0: lui   sp,0x400
  0x1a5000ef,  #     4: jal   2472 <main>
  0x05d00893,  #     8: li    a7,93
  0x00000073,  #    12: ecall
  # memset:
  0x0ff5f593,  #    16: zext.ba1,a1
  0x00c50733,  #    20: add   a4,a0,a2
  0x00050793,  #    24: mv    a5,a0
  0x00060863,  #    28: beqz  a2,44
  0x00178793,  #    32: addi  a5,a5,1
  0xfeb78fa3,  #    36: sb    a1,-1(a5)
  0xfef71ce3,  #    40: bne   a4,a5,32
  0x00008067,  #    44: ret
  # prime_count(unsigned long long):
  0xb7010113,  #    48: addi  sp,sp,-1168
  0x49212023,  #    52: sw    s2,1152(sp)
  0x47312e23,  #    56: sw    s3,1148(sp)
  0x48112623,  #    60: sw    ra,1164(sp)
  0x48812423,  #    64: sw    s0,1160(sp)
  0x48912223,  #    68: sw    s1,1156(sp)
  0x47412c23,  #    72: sw    s4,1144(sp)
  0x47512a23,  #    76: sw    s5,1140(sp)
  0x47612823,  #    80: sw    s6,1136(sp)
  0x47712623,  #    84: sw    s7,1132(sp)
  0x47812423,  #    88: sw    s8,1128(sp)
  0x47912223,  #    92: sw    s9,1124(sp)
  0x47a12023,  #    96: sw    s10,1120(sp)
  0x45b12e23,  #   100: sw    s11,1116(sp)
  0xffcaf2b7,  #   104: lui   t0,0xffcaf
  0x00510133,  #   108: add   sp,sp,t0
  0x00058913,  #   112: mv    s2,a1
  0x00050993,  #   116: mv    s3,a0
  0x0a0580e3,  #   120: beqz  a1,2328
  0x00198413,  #   124: addi  s0,s3,1
  0x01343a33,  #   128: sltu  s4,s0,s3
  0x012a0a33,  #   132: add   s4,s4,s2
  0x01fa1793,  #   136: slli  a5,s4,0x1f
  0x00145413,  #   140: srli  s0,s0,0x1
  0x001a5a13,  #   144: srli  s4,s4,0x1
  0x0087e433,  #   148: or    s0,a5,s0
  0x0b2a7ee3,  #   152: bgeu  s4,s2,2388
  0x00040613,  #   156: mv    a2,s0
  0x000a0693,  #   160: mv    a3,s4
  0x00098513,  #   164: mv    a0,s3
  0x00090593,  #   168: mv    a1,s2
  0x6d9000ef,  #   172: jal   3972 <__udivdi3>
  0x008507b3,  #   176: add   a5,a0,s0
  0x014585b3,  #   180: add   a1,a1,s4
  0x00a7b533,  #   184: sltu  a0,a5,a0
  0x00b50533,  #   188: add   a0,a0,a1
  0x00040b93,  #   192: mv    s7,s0
  0x000a0493,  #   196: mv    s1,s4
  0x01f51713,  #   200: slli  a4,a0,0x1f
  0x0017d413,  #   204: srli  s0,a5,0x1
  0x00155a13,  #   208: srli  s4,a0,0x1
  0x00876433,  #   212: or    s0,a4,s0
  0xfc9a62e3,  #   216: bltu  s4,s1,156
  0x01449463,  #   220: bne   s1,s4,228
  0xfb746ee3,  #   224: bltu  s0,s7,156
  0x001b8413,  #   228: addi  s0,s7,1
  0x017437b3,  #   232: sltu  a5,s0,s7
  0x009787b3,  #   236: add   a5,a5,s1
  0x01f79793,  #   240: slli  a5,a5,0x1f
  0x00145413,  #   244: srli  s0,s0,0x1
  0x0087e433,  #   248: or    s0,a5,s0
  0xffcaf537,  #   252: lui   a0,0xffcaf
  0x00351ab7,  #   256: lui   s5,0x351
  0xc1450513,  #   260: addi  a0,a0,-1004
  0x3f0a8793,  #   264: addi  a5,s5,1008
  0x0004d637,  #   268: lui   a2,0x4d
  0x00a787b3,  #   272: add   a5,a5,a0
  0x06010713,  #   276: addi  a4,sp,96
  0x34460613,  #   280: addi  a2,a2,836
  0x00000593,  #   284: li    a1,0
  0x00e78533,  #   288: add   a0,a5,a4
  0x00040a13,  #   292: mv    s4,s0
  0xee9ff0ef,  #   296: jal   16 <memset>
  0x02040ee3,  #   300: beqz  s0,2408
  0xffcfcdb7,  #   304: lui   s11,0xffcfc
  0xf58d8d93,  #   308: addi  s11,s11,-168
  0x3f0a8793,  #   312: addi  a5,s5,1008
  0x06010713,  #   316: addi  a4,sp,96
  0x01b787b3,  #   320: add   a5,a5,s11
  0xffe31d37,  #   324: lui   s10,0xffe31
  0xc68d0d13,  #   328: addi  s10,s10,-920
  0x00e78db3,  #   332: add   s11,a5,a4
  0x3f0a8793,  #   336: addi  a5,s5,1008
  0x01a787b3,  #   340: add   a5,a5,s10
  0xffecbb37,  #   344: lui   s6,0xffecb
  0x2f0b0b13,  #   348: addi  s6,s6,752
  0x00e78d33,  #   352: add   s10,a5,a4
  0x3f0a8793,  #   356: addi  a5,s5,1008
  0x016787b3,  #   360: add   a5,a5,s6
  0xffd96cb7,  #   364: lui   s9,0xffd96
  0x5e0c8c93,  #   368: addi  s9,s9,1504
  0x00e78b33,  #   372: add   s6,a5,a4
  0x3f0a8793,  #   376: addi  a5,s5,1008
  0x019787b3,  #   380: add   a5,a5,s9
  0x00000693,  #   384: li    a3,0
  0x00912423,  #   388: sw    s1,8(sp)
  0x00e78cb3,  #   392: add   s9,a5,a4
  0x00100a93,  #   396: li    s5,1
  0x00000c13,  #   400: li    s8,0
  0x00068493,  #   404: mv    s1,a3
  0x000a8613,  #   408: mv    a2,s5
  0x018da023,  #   412: sw    s8,0(s11)
  0x015d2023,  #   416: sw    s5,0(s10)
  0x00048693,  #   420: mv    a3,s1
  0x00098513,  #   424: mv    a0,s3
  0x00090593,  #   428: mv    a1,s2
  0x5d5000ef,  #   432: jal   3972 <__udivdi3>
  0x00153713,  #   436: seqz  a4,a0
  0xfff50793,  #   440: addi  a5,a0,-1
  0x40e58733,  #   444: sub   a4,a1,a4
  0x01f71713,  #   448: slli  a4,a4,0x1f
  0x0017d793,  #   452: srli  a5,a5,0x1
  0x002a8613,  #   456: addi  a2,s5,2
  0x00f767b3,  #   460: or    a5,a4,a5
  0x00ab2023,  #   464: sw    a0,0(s6)
  0x01563733,  #   468: sltu  a4,a2,s5
  0x00bb2223,  #   472: sw    a1,4(s6)
  0x00fca023,  #   476: sw    a5,0(s9)
  0x001c0c13,  #   480: addi  s8,s8,1
  0x004d8d93,  #   484: addi  s11,s11,4
  0x004d0d13,  #   488: addi  s10,s10,4
  0x00060a93,  #   492: mv    s5,a2
  0x009704b3,  #   496: add   s1,a4,s1
  0x008b0b13,  #   500: addi  s6,s6,8
  0x004c8c93,  #   504: addi  s9,s9,4
  0xf9841ee3,  #   508: bne   s0,s8,408
  0x00812483,  #   512: lw    s1,8(sp)
  0x72048c63,  #   516: beqz  s1,2364
  0x00351837,  #   520: lui   a6,0x351
  0xfffb8693,  #   524: addi  a3,s7,-1
  0xffcaf737,  #   528: lui   a4,0xffcaf
  0x0016d313,  #   532: srli  t1,a3,0x1
  0xc1470713,  #   536: addi  a4,a4,-1004
  0x3f080693,  #   540: addi  a3,a6,1008
  0x00e686b3,  #   544: add   a3,a3,a4
  0x001bb793,  #   548: seqz  a5,s7
  0x06010713,  #   552: addi  a4,sp,96
  0x00e68733,  #   556: add   a4,a3,a4
  0x40f487b3,  #   560: sub   a5,s1,a5
  0x01f79613,  #   564: slli  a2,a5,0x1f
  0x04e12223,  #   568: sw    a4,68(sp)
  0x0017d793,  #   572: srli  a5,a5,0x1
  0x04f12a23,  #   576: sw    a5,84(sp)
  0x04412783,  #   580: lw    a5,68(sp)
  0xffe31537,  #   584: lui   a0,0xffe31
  0xc6850513,  #   588: addi  a0,a0,-920
  0x00378b13,  #   592: addi  s6,a5,3
  0x3f080793,  #   596: addi  a5,a6,1008
  0x00a787b3,  #   600: add   a5,a5,a0
  0x06010513,  #   604: addi  a0,sp,96
  0x00a787b3,  #   608: add   a5,a5,a0
  0xffecb8b7,  #   612: lui   a7,0xffecb
  0x2f088e93,  #   616: addi  t4,a7,752
  0x02f12423,  #   620: sw    a5,40(sp)
  0xffcaf8b7,  #   624: lui   a7,0xffcaf
  0x3f080793,  #   628: addi  a5,a6,1008
  0x00080513,  #   632: mv    a0,a6
  0x011787b3,  #   636: add   a5,a5,a7
  0x06010813,  #   640: addi  a6,sp,96
  0x010788b3,  #   644: add   a7,a5,a6
  0xffd967b7,  #   648: lui   a5,0xffd96
  0x3f050813,  #   652: addi  a6,a0,1008
  0x00f80833,  #   656: add   a6,a6,a5
  0x06010793,  #   660: addi  a5,sp,96
  0x00666733,  #   664: or    a4,a2,t1
  0x00f807b3,  #   668: add   a5,a6,a5
  0x3f050313,  #   672: addi  t1,a0,1008
  0xffcfc837,  #   676: lui   a6,0xffcfc
  0x01030333,  #   680: add   t1,t1,a6
  0x06010813,  #   684: addi  a6,sp,96
  0x3f050f13,  #   688: addi  t5,a0,1008
  0x01030833,  #   692: add   a6,t1,a6
  0xffecb337,  #   696: lui   t1,0xffecb
  0x006f0f33,  #   700: add   t5,t5,t1
  0xffcfcdb7,  #   704: lui   s11,0xffcfc
  0x06010313,  #   708: addi  t1,sp,96
  0xf58d8d93,  #   712: addi  s11,s11,-168
  0x006f0333,  #   716: add   t1,t5,t1
  0x3f050f13,  #   720: addi  t5,a0,1008
  0x06010f93,  #   724: addi  t6,sp,96
  0xffd965b7,  #   728: lui   a1,0xffd96
  0x01bf0f33,  #   732: add   t5,t5,s11
  0x5e058e13,  #   736: addi  t3,a1,1504
  0x01ff0db3,  #   740: add   s11,t5,t6
  0x3f050f13,  #   744: addi  t5,a0,1008
  0x3f050513,  #   748: addi  a0,a0,1008
  0x01cf0f33,  #   752: add   t5,t5,t3
  0x01d50533,  #   756: add   a0,a0,t4
  0x05c12423,  #   760: sw    t3,72(sp)
  0x01f50533,  #   764: add   a0,a0,t6
  0x01ff0e33,  #   768: add   t3,t5,t6
  0x04e12823,  #   772: sw    a4,80(sp)
  0x000b0a93,  #   776: mv    s5,s6
  0x05d12623,  #   780: sw    t4,76(sp)
  0x00600c13,  #   784: li    s8,6
  0x00000d13,  #   788: li    s10,0
  0x00300613,  #   792: li    a2,3
  0x00000693,  #   796: li    a3,0
  0x00000993,  #   800: li    s3,0
  0x00900593,  #   804: li    a1,9
  0x00000713,  #   808: li    a4,0
  0x05c12c23,  #   812: sw    t3,88(sp)
  0x04a12e23,  #   816: sw    a0,92(sp)
  0x000b8c93,  #   820: mv    s9,s7
  0x00078b13,  #   824: mv    s6,a5
  0x000ac503,  #   828: lbu   a0,0(s5)
  0x1e050263,  #   832: beqz  a0,1316
  0x00260713,  #   836: addi  a4,a2,2
  0x00c73633,  #   840: sltu  a2,a4,a2
  0x00d606b3,  #   844: add   a3,a2,a3
  0x02e685b3,  #   848: mul   a1,a3,a4
  0x00070613,  #   852: mv    a2,a4
  0x004c0713,  #   856: addi  a4,s8,4
  0x01873533,  #   860: sltu  a0,a4,s8
  0x00070c13,  #   864: mv    s8,a4
  0x002a8a93,  #   868: addi  s5,s5,2
  0x01a50d33,  #   872: add   s10,a0,s10
  0x02c63733,  #   876: mulhu a4,a2,a2
  0x00159593,  #   880: slli  a1,a1,0x1
  0x00e58733,  #   884: add   a4,a1,a4
  0x02c605b3,  #   888: mul   a1,a2,a2
  0x00e4e663,  #   892: bltu  s1,a4,904
  0xfa971ee3,  #   896: bne   a4,s1,828
  0xfabcfce3,  #   900: bgeu  s9,a1,828
  0xfff98c93,  #   904: addi  s9,s3,-1
  0xfffa0793,  #   908: addi  a5,s4,-1
  0x00351637,  #   912: lui   a2,0x351
  0xffd96737,  #   916: lui   a4,0xffd96
  0x3f060693,  #   920: addi  a3,a2,1008
  0x00e686b3,  #   924: add   a3,a3,a4
  0x02fa0533,  #   928: mul   a0,s4,a5
  0x06010713,  #   932: addi  a4,sp,96
  0x00e68733,  #   936: add   a4,a3,a4
  0x5e072703,  #   940: lw    a4,1504(a4)
  0x00100693,  #   944: li    a3,1
  0x00170713,  #   948: addi  a4,a4,1
  0x02fc85b3,  #   952: mul   a1,s9,a5
  0x00155513,  #   956: srli  a0,a0,0x1
  0x5d46fe63,  #   960: bgeu  a3,s4,2460
  0xffd967b7,  #   964: lui   a5,0xffd96
  0x5e078793,  #   968: addi  a5,a5,1504
  0x3f060693,  #   972: addi  a3,a2,1008
  0x00f686b3,  #   976: add   a3,a3,a5
  0x06010793,  #   980: addi  a5,sp,96
  0x00f687b3,  #   984: add   a5,a3,a5
  0x00f12423,  #   988: sw    a5,8(sp)
  0x00812683,  #   992: lw    a3,8(sp)
  0x002a1613,  #   996: slli  a2,s4,0x2
  0x00478793,  #  1000: addi  a5,a5,4
  0x00d60633,  #  1004: add   a2,a2,a3
  0x0007a683,  #  1008: lw    a3,0(a5)
  0x00478793,  #  1012: addi  a5,a5,4
  0x40d70733,  #  1016: sub   a4,a4,a3
  0xfef61ae3,  #  1020: bne   a2,a5,1008
  0x003516b7,  #  1024: lui   a3,0x351
  0xffecb7b7,  #  1028: lui   a5,0xffecb
  0x2f078793,  #  1032: addi  a5,a5,752
  0x3f068613,  #  1036: addi  a2,a3,1008
  0x00f60633,  #  1040: add   a2,a2,a5
  0x06010793,  #  1044: addi  a5,sp,96
  0x00f607b3,  #  1048: add   a5,a2,a5
  0xffe31c37,  #  1052: lui   s8,0xffe31
  0x00f12a23,  #  1056: sw    a5,20(sp)
  0xc6cc0c13,  #  1060: addi  s8,s8,-916
  0x00b50533,  #  1064: add   a0,a0,a1
  0x3f068793,  #  1068: addi  a5,a3,1008
  0x00e50d33,  #  1072: add   s10,a0,a4
  0x018787b3,  #  1076: add   a5,a5,s8
  0x06010713,  #  1080: addi  a4,sp,96
  0x00e78c33,  #  1084: add   s8,a5,a4
  0x01412783,  #  1088: lw    a5,20(sp)
  0x3f068713,  #  1092: addi  a4,a3,1008
  0x00100493,  #  1096: li    s1,1
  0x01078b93,  #  1100: addi  s7,a5,16
  0xffcfc7b7,  #  1104: lui   a5,0xffcfc
  0x00f70733,  #  1108: add   a4,a4,a5
  0x06010793,  #  1112: addi  a5,sp,96
  0x00f707b3,  #  1116: add   a5,a4,a5
  0x00f12423,  #  1120: sw    a5,8(sp)
  0x01412783,  #  1124: lw    a5,20(sp)
  0xfffc8c93,  #  1128: addi  s9,s9,-1
  0x000d0d93,  #  1132: mv    s11,s10
  0x00878793,  #  1136: addi  a5,a5,8
  0x00f12a23,  #  1140: sw    a5,20(sp)
  0x000c2903,  #  1144: lw    s2,0(s8)
  0xff8ba503,  #  1148: lw    a0,-8(s7)
  0xffcba583,  #  1152: lw    a1,-4(s7)
  0x00000693,  #  1156: li    a3,0
  0x00090613,  #  1160: mv    a2,s2
  0x2f9000ef,  #  1164: jal   3972 <__udivdi3>
  0x00812703,  #  1168: lw    a4,8(sp)
  0xfff50793,  #  1172: addi  a5,a0,-1
  0x0017d793,  #  1176: srli  a5,a5,0x1
  0x00279793,  #  1180: slli  a5,a5,0x2
  0x00f707b3,  #  1184: add   a5,a4,a5
  0xf587aa83,  #  1188: lw    s5,-168(a5)
  0x413a8ab3,  #  1192: sub   s5,s5,s3
  0x4354f063,  #  1196: bgeu  s1,s5,2252
  0x00148b13,  #  1200: addi  s6,s1,1
  0x056ae663,  #  1204: bltu  s5,s6,1280
  0x01412783,  #  1208: lw    a5,20(sp)
  0x003a9413,  #  1212: slli  s0,s5,0x3
  0x000b8d13,  #  1216: mv    s10,s7
  0x00f40433,  #  1220: add   s0,s0,a5
  0x000d2503,  #  1224: lw    a0,0(s10)
  0x004d2583,  #  1228: lw    a1,4(s10)
  0x00090613,  #  1232: mv    a2,s2
  0x00000693,  #  1236: li    a3,0
  0x2ad000ef,  #  1240: jal   3972 <__udivdi3>
  0x00812703,  #  1244: lw    a4,8(sp)
  0xfff50793,  #  1248: addi  a5,a0,-1
  0x0017d793,  #  1252: srli  a5,a5,0x1
  0x00279793,  #  1256: slli  a5,a5,0x2
  0x00f707b3,  #  1260: add   a5,a4,a5
  0xf587a783,  #  1264: lw    a5,-168(a5)
  0x008d0d13,  #  1268: addi  s10,s10,8
  0x00fd8db3,  #  1272: add   s11,s11,a5
  0xfda416e3,  #  1276: bne   s0,s10,1224
  0x016c87b3,  #  1280: add   a5,s9,s6
  0x409a8ab3,  #  1284: sub   s5,s5,s1
  0x035787b3,  #  1288: mul   a5,a5,s5
  0x004c0c13,  #  1292: addi  s8,s8,4
  0x008b8b93,  #  1296: addi  s7,s7,8
  0x40fd8db3,  #  1300: sub   s11,s11,a5
  0x3b4b0a63,  #  1304: beq   s6,s4,2252
  0x000b0493,  #  1308: mv    s1,s6
  0xf59ff06f,  #  1312: j     1144
  0x00100513,  #  1316: li    a0,1
  0x00aa8023,  #  1320: sb    a0,0(s5)
  0x02e4ee63,  #  1324: bltu  s1,a4,1384
  0x3e970c63,  #  1328: beq   a4,s1,2344
  0x04412783,  #  1332: lw    a5,68(sp)
  0x00100e93,  #  1336: li    t4,1
  0x00b78533,  #  1340: add   a0,a5,a1
  0x018587b3,  #  1344: add   a5,a1,s8
  0x00b7b5b3,  #  1348: sltu  a1,a5,a1
  0x01a70733,  #  1352: add   a4,a4,s10
  0x01d50023,  #  1356: sb    t4,0(a0)
  0x00e58733,  #  1360: add   a4,a1,a4
  0x01850533,  #  1364: add   a0,a0,s8
  0x00078593,  #  1368: mv    a1,a5
  0x00e4e663,  #  1372: bltu  s1,a4,1384
  0xfe9710e3,  #  1376: bne   a4,s1,1344
  0xfcfcfee3,  #  1380: bgeu  s9,a5,1344
  0x04812583,  #  1384: lw    a1,72(sp)
  0x003517b7,  #  1388: lui   a5,0x351
  0x3f078713,  #  1392: addi  a4,a5,1008
  0x00b70733,  #  1396: add   a4,a4,a1
  0x06010593,  #  1400: addi  a1,sp,96
  0x00b70433,  #  1404: add   s0,a4,a1
  0x04c12583,  #  1408: lw    a1,76(sp)
  0x3f078713,  #  1412: addi  a4,a5,1008
  0xffe31bb7,  #  1416: lui   s7,0xffe31
  0x3f078793,  #  1420: addi  a5,a5,1008
  0x00b70733,  #  1424: add   a4,a4,a1
  0x017787b3,  #  1428: add   a5,a5,s7
  0x06010593,  #  1432: addi  a1,sp,96
  0x02812283,  #  1436: lw    t0,40(sp)
  0x00b703b3,  #  1440: add   t2,a4,a1
  0x00000913,  #  1444: li    s2,0
  0x00000f13,  #  1448: li    t5,0
  0x00b78bb3,  #  1452: add   s7,a5,a1
  0x0600006f,  #  1456: j     1552
  0x309e0063,  #  1460: beq   t3,s1,2228
  0x0003ae03,  #  1464: lw    t3,0(t2)
  0x0043ae83,  #  1468: lw    t4,4(t2)
  0x0015d593,  #  1472: srli  a1,a1,0x1
  0x00259593,  #  1476: slli  a1,a1,0x2
  0x00b805b3,  #  1480: add   a1,a6,a1
  0x2fc72823,  #  1484: sw    t3,752(a4)
  0x2fd72a23,  #  1488: sw    t4,756(a4)
  0xf585a703,  #  1492: lw    a4,-168(a1)
  0x00042f83,  #  1496: lw    t6,0(s0)
  0xc6a7a423,  #  1500: sw    a0,-920(a5)
  0x41370733,  #  1504: sub   a4,a4,s3
  0x00271713,  #  1508: slli  a4,a4,0x2
  0x00eb0733,  #  1512: add   a4,s6,a4
  0x5e072703,  #  1516: lw    a4,1504(a4)
  0x01f987b3,  #  1520: add   a5,s3,t6
  0x001f0f13,  #  1524: addi  t5,t5,1
  0x40e787b3,  #  1528: sub   a5,a5,a4
  0x5ef0a023,  #  1532: sw    a5,1504(ra)
  0x00190913,  #  1536: addi  s2,s2,1
  0x00428293,  #  1540: addi  t0,t0,4
  0x00440413,  #  1544: addi  s0,s0,4
  0x00838393,  #  1548: addi  t2,t2,8
  0x0002a503,  #  1552: lw    a0,0(t0)
  0x002f1793,  #  1556: slli  a5,t5,0x2
  0x003f1713,  #  1560: slli  a4,t5,0x3
  0x00a885b3,  #  1564: add   a1,a7,a0
  0xc145cf83,  #  1568: lbu   t6,-1004(a1)
  0x00fb00b3,  #  1572: add   ra,s6,a5
  0x00e30733,  #  1576: add   a4,t1,a4
  0x00fb87b3,  #  1580: add   a5,s7,a5
  0xfc0f98e3,  #  1584: bnez  t6,1536
  0x02a685b3,  #  1588: mul   a1,a3,a0
  0x02c53e33,  #  1592: mulhu t3,a0,a2
  0x01c58e33,  #  1596: add   t3,a1,t3
  0x02c505b3,  #  1600: mul   a1,a0,a2
  0xf7c4f8e3,  #  1604: bgeu  s1,t3,1460
  0x27497a63,  #  1608: bgeu  s2,s4,2236
  0x02812583,  #  1612: lw    a1,40(sp)
  0x05812503,  #  1616: lw    a0,88(sp)
  0x00291713,  #  1620: slli  a4,s2,0x2
  0x00391413,  #  1624: slli  s0,s2,0x3
  0x00e50bb3,  #  1628: add   s7,a0,a4
  0x00e58933,  #  1632: add   s2,a1,a4
  0x05c12703,  #  1636: lw    a4,92(sp)
  0x002a1793,  #  1640: slli  a5,s4,0x2
  0x00b785b3,  #  1644: add   a1,a5,a1
  0x00870433,  #  1648: add   s0,a4,s0
  0x00351737,  #  1652: lui   a4,0x351
  0xffe317b7,  #  1656: lui   a5,0xffe31
  0x3f070713,  #  1660: addi  a4,a4,1008
  0x00f70733,  #  1664: add   a4,a4,a5
  0x06010793,  #  1668: addi  a5,sp,96
  0x00f707b3,  #  1672: add   a5,a4,a5
  0x03512623,  #  1676: sw    s5,44(sp)
  0x03812c23,  #  1680: sw    s8,56(sp)
  0x03a12e23,  #  1684: sw    s10,60(sp)
  0x05b12023,  #  1688: sw    s11,64(sp)
  0x000b8d13,  #  1692: mv    s10,s7
  0x00090d93,  #  1696: mv    s11,s2
  0x000f0a13,  #  1700: mv    s4,t5
  0x02f12223,  #  1704: sw    a5,36(sp)
  0x01312e23,  #  1708: sw    s3,28(sp)
  0x00058a93,  #  1712: mv    s5,a1
  0x00c12a23,  #  1716: sw    a2,20(sp)
  0x00d12c23,  #  1720: sw    a3,24(sp)
  0x03912823,  #  1724: sw    s9,48(sp)
  0x02912a23,  #  1728: sw    s1,52(sp)
  0x00040c13,  #  1732: mv    s8,s0
  0x00080b93,  #  1736: mv    s7,a6
  0x02612023,  #  1740: sw    t1,32(sp)
  0x00088913,  #  1744: mv    s2,a7
  0x0100006f,  #  1748: j     1764
  0x000da783,  #  1752: lw    a5,0(s11)
  0x00f907b3,  #  1756: add   a5,s2,a5
  0xc147cf83,  #  1760: lbu   t6,-1004(a5)
  0x002a1493,  #  1764: slli  s1,s4,0x2
  0x01412603,  #  1768: lw    a2,20(sp)
  0x01812683,  #  1772: lw    a3,24(sp)
  0x009b0433,  #  1776: add   s0,s6,s1
  0x060f9c63,  #  1780: bnez  t6,1900
  0x000c2303,  #  1784: lw    t1,0(s8)
  0x004c2383,  #  1788: lw    t2,4(s8)
  0x000d2883,  #  1792: lw    a7,0(s10)
  0x01c12783,  #  1796: lw    a5,28(sp)
  0x00030513,  #  1800: mv    a0,t1
  0x00038593,  #  1804: mv    a1,t2
  0x011789b3,  #  1808: add   s3,a5,a7
  0x00612423,  #  1812: sw    t1,8(sp)
  0x00712623,  #  1816: sw    t2,12(sp)
  0x069000ef,  #  1820: jal   3972 <__udivdi3>
  0xfff50793,  #  1824: addi  a5,a0,-1
  0x0017d793,  #  1828: srli  a5,a5,0x1
  0x02012703,  #  1832: lw    a4,32(sp)
  0x00279793,  #  1836: slli  a5,a5,0x2
  0x00fb87b3,  #  1840: add   a5,s7,a5
  0xf587a683,  #  1844: lw    a3,-168(a5)
  0x003a1793,  #  1848: slli  a5,s4,0x3
  0x00f707b3,  #  1852: add   a5,a4,a5
  0x02412703,  #  1856: lw    a4,36(sp)
  0x000dac83,  #  1860: lw    s9,0(s11)
  0x00812303,  #  1864: lw    t1,8(sp)
  0x00c12383,  #  1868: lw    t2,12(sp)
  0x40d988b3,  #  1872: sub   a7,s3,a3
  0x00970833,  #  1876: add   a6,a4,s1
  0xc7982423,  #  1880: sw    s9,-920(a6)
  0x5f142023,  #  1884: sw    a7,1504(s0)
  0x2e67a823,  #  1888: sw    t1,752(a5)
  0x2e77aa23,  #  1892: sw    t2,756(a5)
  0x001a0a13,  #  1896: addi  s4,s4,1
  0x004d8d93,  #  1900: addi  s11,s11,4
  0x004d0d13,  #  1904: addi  s10,s10,4
  0x008c0c13,  #  1908: addi  s8,s8,8
  0xf7ba90e3,  #  1912: bne   s5,s11,1752
  0x02c12a83,  #  1916: lw    s5,44(sp)
  0x01c12983,  #  1920: lw    s3,28(sp)
  0x01412603,  #  1924: lw    a2,20(sp)
  0x01812683,  #  1928: lw    a3,24(sp)
  0x03012c83,  #  1932: lw    s9,48(sp)
  0x03412483,  #  1936: lw    s1,52(sp)
  0x03812c03,  #  1940: lw    s8,56(sp)
  0x03c12d03,  #  1944: lw    s10,60(sp)
  0x02012303,  #  1948: lw    t1,32(sp)
  0x04012d83,  #  1952: lw    s11,64(sp)
  0x00090893,  #  1956: mv    a7,s2
  0x000b8813,  #  1960: mv    a6,s7
  0x000c8513,  #  1964: mv    a0,s9
  0x00048593,  #  1968: mv    a1,s1
  0x02612023,  #  1972: sw    t1,32(sp)
  0x01012e23,  #  1976: sw    a6,28(sp)
  0x01112c23,  #  1980: sw    a7,24(sp)
  0x00c12a23,  #  1984: sw    a2,20(sp)
  0x00d12423,  #  1988: sw    a3,8(sp)
  0x7bc000ef,  #  1992: jal   3972 <__udivdi3>
  0x00812683,  #  1996: lw    a3,8(sp)
  0x00153713,  #  2000: seqz  a4,a0
  0x40e58733,  #  2004: sub   a4,a1,a4
  0xfff50513,  #  2008: addi  a0,a0,-1
  0x01412603,  #  2012: lw    a2,20(sp)
  0x01812883,  #  2016: lw    a7,24(sp)
  0x01c12803,  #  2020: lw    a6,28(sp)
  0x02012303,  #  2024: lw    t1,32(sp)
  0x00156f93,  #  2028: ori   t6,a0,1
  0x00070393,  #  2032: mv    t2,a4
  0x0ad76c63,  #  2036: bltu  a4,a3,2220
  0x12e68c63,  #  2040: beq   a3,a4,2352
  0x02c70733,  #  2044: mul   a4,a4,a2
  0x05012e03,  #  2048: lw    t3,80(sp)
  0x05412583,  #  2052: lw    a1,84(sp)
  0x03f68533,  #  2056: mul   a0,a3,t6
  0x02cfb2b3,  #  2060: mulhu t0,t6,a2
  0x00a70733,  #  2064: add   a4,a4,a0
  0x02cf8433,  #  2068: mul   s0,t6,a2
  0x005702b3,  #  2072: add   t0,a4,t0
  0x001fd793,  #  2076: srli  a5,t6,0x1
  0x00279793,  #  2080: slli  a5,a5,0x2
  0x00f807b3,  #  2084: add   a5,a6,a5
  0x01f29713,  #  2088: slli  a4,t0,0x1f
  0x00145f13,  #  2092: srli  t5,s0,0x1
  0x0012d513,  #  2096: srli  a0,t0,0x1
  0xf587ae83,  #  2100: lw    t4,-168(a5)
  0x01e76f33,  #  2104: or    t5,a4,t5
  0x02a5ee63,  #  2108: bltu  a1,a0,2168
  0x08b50263,  #  2112: beq   a0,a1,2244
  0x002e1793,  #  2116: slli  a5,t3,0x2
  0x41d98eb3,  #  2120: sub   t4,s3,t4
  0x00fd87b3,  #  2124: add   a5,s11,a5
  0x0007a703,  #  2128: lw    a4,0(a5)
  0x001e3913,  #  2132: seqz  s2,t3
  0x412585b3,  #  2136: sub   a1,a1,s2
  0x01d70733,  #  2140: add   a4,a4,t4
  0x00e7a023,  #  2144: sw    a4,0(a5)
  0xfffe0e13,  #  2148: addi  t3,t3,-1
  0xffc78793,  #  2152: addi  a5,a5,-4
  0x00a5e663,  #  2156: bltu  a1,a0,2168
  0xfeb510e3,  #  2160: bne   a0,a1,2128
  0xfdee7ee3,  #  2164: bgeu  t3,t5,2128
  0xffef8713,  #  2168: addi  a4,t6,-2
  0x01f73fb3,  #  2172: sltu  t6,a4,t6
  0x418407b3,  #  2176: sub   a5,s0,s8
  0xfff38393,  #  2180: addi  t2,t2,-1
  0x00f43533,  #  2184: sltu  a0,s0,a5
  0x41a282b3,  #  2188: sub   t0,t0,s10
  0x007f83b3,  #  2192: add   t2,t6,t2
  0x00078413,  #  2196: mv    s0,a5
  0x00070f93,  #  2200: mv    t6,a4
  0x40a282b3,  #  2204: sub   t0,t0,a0
  0x00d3e663,  #  2208: bltu  t2,a3,2220
  0xf6769ce3,  #  2212: bne   a3,t2,2076
  0xf6c77ae3,  #  2216: bgeu  a4,a2,2076
  0x00198993,  #  2220: addi  s3,s3,1
  0xa95ff06f,  #  2224: j     836
  0xd0bcf2e3,  #  2228: bgeu  s9,a1,1464
  0xd9496ae3,  #  2232: bltu  s2,s4,1612
  0x000f0a13,  #  2236: mv    s4,t5
  0xeedff06f,  #  2240: j     1964
  0xf9ee70e3,  #  2244: bgeu  t3,t5,2116
  0xfb1ff06f,  #  2248: j     2168
  0x000d8d13,  #  2252: mv    s10,s11
  0x003512b7,  #  2256: lui   t0,0x351
  0x00510133,  #  2260: add   sp,sp,t0
  0x48c12083,  #  2264: lw    ra,1164(sp)
  0x000d0513,  #  2268: mv    a0,s10
  0x48812403,  #  2272: lw    s0,1160(sp)
  0x48412483,  #  2276: lw    s1,1156(sp)
  0x48012903,  #  2280: lw    s2,1152(sp)
  0x47c12983,  #  2284: lw    s3,1148(sp)
  0x47812a03,  #  2288: lw    s4,1144(sp)
  0x47412a83,  #  2292: lw    s5,1140(sp)
  0x47012b03,  #  2296: lw    s6,1136(sp)
  0x46c12b83,  #  2300: lw    s7,1132(sp)
  0x46812c03,  #  2304: lw    s8,1128(sp)
  0x46412c83,  #  2308: lw    s9,1124(sp)
  0x46012d03,  #  2312: lw    s10,1120(sp)
  0x45c12d83,  #  2316: lw    s11,1116(sp)
  0x49010113,  #  2320: addi  sp,sp,1168
  0x00008067,  #  2324: ret
  0x00100793,  #  2328: li    a5,1
  0x00000d13,  #  2332: li    s10,0
  0xf4a7ee63,  #  2336: bltu  a5,a0,124
  0xfadff06f,  #  2340: j     2256
  0xc0bcf6e3,  #  2344: bgeu  s9,a1,1332
  0xc3dff06f,  #  2348: j     1384
  0xeccff6e3,  #  2352: bgeu  t6,a2,2044
  0x00198993,  #  2356: addi  s3,s3,1
  0xa0dff06f,  #  2360: j     836
  0x00800793,  #  2364: li    a5,8
  0x8d77e4e3,  #  2368: bltu  a5,s7,520
  0x00040a13,  #  2372: mv    s4,s0
  0xfff00c93,  #  2376: li    s9,-1
  0x00000993,  #  2380: li    s3,0
  0xa3dff06f,  #  2384: j     908
  0x01491463,  #  2388: bne   s2,s4,2396
  0xf5346263,  #  2392: bltu  s0,s3,156
  0x00098b93,  #  2396: mv    s7,s3
  0x00090493,  #  2400: mv    s1,s2
  0xf98ff06f,  #  2404: j     252
  0x8a0490e3,  #  2408: bnez  s1,520
  0x00800793,  #  2412: li    a5,8
  0x8977ece3,  #  2416: bltu  a5,s7,520
  0x00351737,  #  2420: lui   a4,0x351
  0xffd967b7,  #  2424: lui   a5,0xffd96
  0x3f070713,  #  2428: addi  a4,a4,1008
  0x00f70733,  #  2432: add   a4,a4,a5
  0x06010793,  #  2436: addi  a5,sp,96
  0x00f707b3,  #  2440: add   a5,a4,a5
  0x5e07a703,  #  2444: lw    a4,1504(a5)
  0x00000513,  #  2448: li    a0,0
  0x00100593,  #  2452: li    a1,1
  0x00170713,  #  2456: addi  a4,a4,1
  0x00b70733,  #  2460: add   a4,a4,a1
  0x00a70d33,  #  2464: add   s10,a4,a0
  0xf2dff06f,  #  2468: j     2256
  # main:
  0xfd010113,  #  2472: addi  sp,sp,-48
  0x02112623,  #  2476: sw    ra,44(sp)
  0x00c00893,  #  2480: li    a7,12
  0x00000073,  #  2484: ecall
  0x00900793,  #  2488: li    a5,9
  0xfd050513,  #  2492: addi  a0,a0,-48
  0x00a7fa63,  #  2496: bgeu  a5,a0,2516
  0x00c00893,  #  2500: li    a7,12
  0x00000073,  #  2504: ecall
  0xfd050513,  #  2508: addi  a0,a0,-48
  0xfea7eae3,  #  2512: bltu  a5,a0,2500
  0x00000793,  #  2516: li    a5,0
  0x00000593,  #  2520: li    a1,0
  0x00900813,  #  2524: li    a6,9
  0x01e7d613,  #  2528: srli  a2,a5,0x1e
  0x00279713,  #  2532: slli  a4,a5,0x2
  0x00259693,  #  2536: slli  a3,a1,0x2
  0x00f707b3,  #  2540: add   a5,a4,a5
  0x00d666b3,  #  2544: or    a3,a2,a3
  0x00b686b3,  #  2548: add   a3,a3,a1
  0x00e7b733,  #  2552: sltu  a4,a5,a4
  0x00d70733,  #  2556: add   a4,a4,a3
  0x00171713,  #  2560: slli  a4,a4,0x1
  0x01f7d693,  #  2564: srli  a3,a5,0x1f
  0x00179793,  #  2568: slli  a5,a5,0x1
  0x00f507b3,  #  2572: add   a5,a0,a5
  0x00e6e733,  #  2576: or    a4,a3,a4
  0x41f55593,  #  2580: srai  a1,a0,0x1f
  0x00e585b3,  #  2584: add   a1,a1,a4
  0x00a7b533,  #  2588: sltu  a0,a5,a0
  0x00b505b3,  #  2592: add   a1,a0,a1
  0x00c00893,  #  2596: li    a7,12
  0x00000073,  #  2600: ecall
  0xfd050513,  #  2604: addi  a0,a0,-48
  0xfaa878e3,  #  2608: bgeu  a6,a0,2528
  0x00078513,  #  2612: mv    a0,a5
  0xdf8ff0ef,  #  2616: jal   48 <prime_count(unsigned long long)>
  0xccccd5b7,  #  2620: lui   a1,0xccccd
  0xccccde37,  #  2624: lui   t3,0xccccd
  0x00050693,  #  2628: mv    a3,a0
  0x00000713,  #  2632: li    a4,0
  0x00000813,  #  2636: li    a6,0
  0x00c10313,  #  2640: addi  t1,sp,12
  0x00500e93,  #  2644: li    t4,5
  0xccd58593,  #  2648: addi  a1,a1,-819
  0xccce0e13,  #  2652: addi  t3,t3,-820
  0x00900f13,  #  2656: li    t5,9
  0x00e687b3,  #  2660: add   a5,a3,a4
  0x00d7b633,  #  2664: sltu  a2,a5,a3
  0x00c787b3,  #  2668: add   a5,a5,a2
  0x03d7f7b3,  #  2672: remu  a5,a5,t4
  0x00070893,  #  2676: mv    a7,a4
  0x00180813,  #  2680: addi  a6,a6,1
  0x01030633,  #  2684: add   a2,t1,a6
  0x00068293,  #  2688: mv    t0,a3
  0x40f687b3,  #  2692: sub   a5,a3,a5
  0x00f6b533,  #  2696: sltu  a0,a3,a5
  0x40a70733,  #  2700: sub   a4,a4,a0
  0x03c78fb3,  #  2704: mul   t6,a5,t3
  0x02b70733,  #  2708: mul   a4,a4,a1
  0x02b7b533,  #  2712: mulhu a0,a5,a1
  0x01f70733,  #  2716: add   a4,a4,t6
  0x02b787b3,  #  2720: mul   a5,a5,a1
  0x00a70733,  #  2724: add   a4,a4,a0
  0x01f71513,  #  2728: slli  a0,a4,0x1f
  0x00175713,  #  2732: srli  a4,a4,0x1
  0x0017d793,  #  2736: srli  a5,a5,0x1
  0x00f567b3,  #  2740: or    a5,a0,a5
  0x00279513,  #  2744: slli  a0,a5,0x2
  0x00f50533,  #  2748: add   a0,a0,a5
  0x00151513,  #  2752: slli  a0,a0,0x1
  0x40a68533,  #  2756: sub   a0,a3,a0
  0x03050513,  #  2760: addi  a0,a0,48
  0xfea60fa3,  #  2764: sb    a0,-1(a2)
  0x00078693,  #  2768: mv    a3,a5
  0xf80898e3,  #  2772: bnez  a7,2660
  0xf85f66e3,  #  2776: bltu  t5,t0,2660
  0x00060793,  #  2780: mv    a5,a2
  0xfff7c503,  #  2784: lbu   a0,-1(a5)
  0x00b00893,  #  2788: li    a7,11
  0x00000073,  #  2792: ecall
  0xfff78793,  #  2796: addi  a5,a5,-1
  0xfef318e3,  #  2800: bne   t1,a5,2784
  0x00a00513,  #  2804: li    a0,10
  0x00000073,  #  2808: ecall
  0x02c12083,  #  2812: lw    ra,44(sp)
  0x00000513,  #  2816: li    a0,0
  0x03010113,  #  2820: addi  sp,sp,48
  0x00008067,  #  2824: ret
  # __divdi3:
  0x00050313,  #  2828: mv    t1,a0
  0x00058e13,  #  2832: mv    t3,a1
  0x00000893,  #  2836: li    a7,0
  0x0005dc63,  #  2840: bgez  a1,2864
  0x00a037b3,  #  2844: snez  a5,a0
  0x40b00e33,  #  2848: neg   t3,a1
  0x40fe0e33,  #  2852: sub   t3,t3,a5
  0x40a00333,  #  2856: neg   t1,a0
  0xfff00893,  #  2860: li    a7,-1
  0x0006dc63,  #  2864: bgez  a3,2888
  0x00c037b3,  #  2868: snez  a5,a2
  0x40d006b3,  #  2872: neg   a3,a3
  0xfff8c893,  #  2876: not   a7,a7
  0x40f686b3,  #  2880: sub   a3,a3,a5
  0x40c00633,  #  2884: neg   a2,a2
  0x00060713,  #  2888: mv    a4,a2
  0x00030813,  #  2892: mv    a6,t1
  0x000e0793,  #  2896: mv    a5,t3
  0x28069c63,  #  2900: bnez  a3,3564
  0x00001597,  #  2904: auipc a1,0x1
  0x85c58593,  #  2908: addi  a1,a1,-1956
  0x0ece7663,  #  2912: bgeu  t3,a2,3148
  0x000106b7,  #  2916: lui   a3,0x10
  0x0cd67863,  #  2920: bgeu  a2,a3,3128
  0x10063693,  #  2924: sltiu a3,a2,256
  0x0016b693,  #  2928: seqz  a3,a3
  0x00369693,  #  2932: slli  a3,a3,0x3
  0x00d65533,  #  2936: srl   a0,a2,a3
  0x00a585b3,  #  2940: add   a1,a1,a0
  0x0005c583,  #  2944: lbu   a1,0(a1)
  0x02000513,  #  2948: li    a0,32
  0x00d586b3,  #  2952: add   a3,a1,a3
  0x40d505b3,  #  2956: sub   a1,a0,a3
  0x00d50c63,  #  2960: beq   a0,a3,2984
  0x00be17b3,  #  2964: sll   a5,t3,a1
  0x00d356b3,  #  2968: srl   a3,t1,a3
  0x00b61733,  #  2972: sll   a4,a2,a1
  0x00f6e7b3,  #  2976: or    a5,a3,a5
  0x00b31833,  #  2980: sll   a6,t1,a1
  0x01075593,  #  2984: srli  a1,a4,0x10
  0x02b7de33,  #  2988: divu  t3,a5,a1
  0x01071613,  #  2992: slli  a2,a4,0x10
  0x01065613,  #  2996: srli  a2,a2,0x10
  0x02b7f7b3,  #  3000: remu  a5,a5,a1
  0x000e0513,  #  3004: mv    a0,t3
  0x03c60333,  #  3008: mul   t1,a2,t3
  0x01079693,  #  3012: slli  a3,a5,0x10
  0x01085793,  #  3016: srli  a5,a6,0x10
  0x00d7e7b3,  #  3020: or    a5,a5,a3
  0x0067fe63,  #  3024: bgeu  a5,t1,3052
  0x00f707b3,  #  3028: add   a5,a4,a5
  0xfffe0513,  #  3032: addi  a0,t3,-1
  0x00e7e863,  #  3036: bltu  a5,a4,3052
  0x0067f663,  #  3040: bgeu  a5,t1,3052
  0xffee0513,  #  3044: addi  a0,t3,-2
  0x00e787b3,  #  3048: add   a5,a5,a4
  0x406787b3,  #  3052: sub   a5,a5,t1
  0x02b7d333,  #  3056: divu  t1,a5,a1
  0x01081813,  #  3060: slli  a6,a6,0x10
  0x01085813,  #  3064: srli  a6,a6,0x10
  0x02b7f7b3,  #  3068: remu  a5,a5,a1
  0x026606b3,  #  3072: mul   a3,a2,t1
  0x01079793,  #  3076: slli  a5,a5,0x10
  0x00f86833,  #  3080: or    a6,a6,a5
  0x00030793,  #  3084: mv    a5,t1
  0x00d87c63,  #  3088: bgeu  a6,a3,3112
  0x01070833,  #  3092: add   a6,a4,a6
  0xfff30793,  #  3096: addi  a5,t1,-1
  0x00e86663,  #  3100: bltu  a6,a4,3112
  0x00d87463,  #  3104: bgeu  a6,a3,3112
  0xffe30793,  #  3108: addi  a5,t1,-2
  0x01051513,  #  3112: slli  a0,a0,0x10
  0x00f56533,  #  3116: or    a0,a0,a5
  0x00000593,  #  3120: li    a1,0
  0x0e00006f,  #  3124: j     3348
  0x01000537,  #  3128: lui   a0,0x1000
  0x01800693,  #  3132: li    a3,24
  0xf2a67ce3,  #  3136: bgeu  a2,a0,2936
  0x01000693,  #  3140: li    a3,16
  0xf31ff06f,  #  3144: j     2936
  0x00000693,  #  3148: li    a3,0
  0x00060c63,  #  3152: beqz  a2,3176
  0x000107b7,  #  3156: lui   a5,0x10
  0x0cf67a63,  #  3160: bgeu  a2,a5,3372
  0x10063693,  #  3164: sltiu a3,a2,256
  0x0016b693,  #  3168: seqz  a3,a3
  0x00369693,  #  3172: slli  a3,a3,0x3
  0x00d657b3,  #  3176: srl   a5,a2,a3
  0x00f585b3,  #  3180: add   a1,a1,a5
  0x0005c783,  #  3184: lbu   a5,0(a1)
  0x00d787b3,  #  3188: add   a5,a5,a3
  0x02000693,  #  3192: li    a3,32
  0x40f685b3,  #  3196: sub   a1,a3,a5
  0x0cf69063,  #  3200: bne   a3,a5,3392
  0x40ce07b3,  #  3204: sub   a5,t3,a2
  0x00100593,  #  3208: li    a1,1
  0x01075313,  #  3212: srli  t1,a4,0x10
  0x0267deb3,  #  3216: divu  t4,a5,t1
  0x01071613,  #  3220: slli  a2,a4,0x10
  0x01065613,  #  3224: srli  a2,a2,0x10
  0x01085693,  #  3228: srli  a3,a6,0x10
  0x0267f7b3,  #  3232: remu  a5,a5,t1
  0x000e8513,  #  3236: mv    a0,t4
  0x03d60e33,  #  3240: mul   t3,a2,t4
  0x01079793,  #  3244: slli  a5,a5,0x10
  0x00f6e7b3,  #  3248: or    a5,a3,a5
  0x01c7fe63,  #  3252: bgeu  a5,t3,3280
  0x00f707b3,  #  3256: add   a5,a4,a5
  0xfffe8513,  #  3260: addi  a0,t4,-1
  0x00e7e863,  #  3264: bltu  a5,a4,3280
  0x01c7f663,  #  3268: bgeu  a5,t3,3280
  0xffee8513,  #  3272: addi  a0,t4,-2
  0x00e787b3,  #  3276: add   a5,a5,a4
  0x41c787b3,  #  3280: sub   a5,a5,t3
  0x0267de33,  #  3284: divu  t3,a5,t1
  0x01081813,  #  3288: slli  a6,a6,0x10
  0x01085813,  #  3292: srli  a6,a6,0x10
  0x0267f7b3,  #  3296: remu  a5,a5,t1
  0x03c606b3,  #  3300: mul   a3,a2,t3
  0x01079793,  #  3304: slli  a5,a5,0x10
  0x00f86833,  #  3308: or    a6,a6,a5
  0x000e0793,  #  3312: mv    a5,t3
  0x00d87c63,  #  3316: bgeu  a6,a3,3340
  0x01070833,  #  3320: add   a6,a4,a6
  0xfffe0793,  #  3324: addi  a5,t3,-1
  0x00e86663,  #  3328: bltu  a6,a4,3340
  0x00d87463,  #  3332: bgeu  a6,a3,3340
  0xffee0793,  #  3336: addi  a5,t3,-2
  0x01051513,  #  3340: slli  a0,a0,0x10
  0x00f56533,  #  3344: or    a0,a0,a5
  0x00088a63,  #  3348: beqz  a7,3368
  0x00a037b3,  #  3352: snez  a5,a0
  0x40b005b3,  #  3356: neg   a1,a1
  0x40f585b3,  #  3360: sub   a1,a1,a5
  0x40a00533,  #  3364: neg   a0,a0
  0x00008067,  #  3368: ret
  0x010007b7,  #  3372: lui   a5,0x1000
  0x01800693,  #  3376: li    a3,24
  0xf2f67ae3,  #  3380: bgeu  a2,a5,3176
  0x01000693,  #  3384: li    a3,16
  0xf2dff06f,  #  3388: j     3176
  0x00b61733,  #  3392: sll   a4,a2,a1
  0x00fe56b3,  #  3396: srl   a3,t3,a5
  0x01075513,  #  3400: srli  a0,a4,0x10
  0x00be1e33,  #  3404: sll   t3,t3,a1
  0x00f357b3,  #  3408: srl   a5,t1,a5
  0x01c7e7b3,  #  3412: or    a5,a5,t3
  0x02a6de33,  #  3416: divu  t3,a3,a0
  0x01071613,  #  3420: slli  a2,a4,0x10
  0x01065613,  #  3424: srli  a2,a2,0x10
  0x00b31833,  #  3428: sll   a6,t1,a1
  0x02a6f6b3,  #  3432: remu  a3,a3,a0
  0x03c60333,  #  3436: mul   t1,a2,t3
  0x01069593,  #  3440: slli  a1,a3,0x10
  0x0107d693,  #  3444: srli  a3,a5,0x10
  0x00b6e6b3,  #  3448: or    a3,a3,a1
  0x000e0593,  #  3452: mv    a1,t3
  0x0066fe63,  #  3456: bgeu  a3,t1,3484
  0x00d706b3,  #  3460: add   a3,a4,a3
  0xfffe0593,  #  3464: addi  a1,t3,-1
  0x00e6e863,  #  3468: bltu  a3,a4,3484
  0x0066f663,  #  3472: bgeu  a3,t1,3484
  0xffee0593,  #  3476: addi  a1,t3,-2
  0x00e686b3,  #  3480: add   a3,a3,a4
  0x406686b3,  #  3484: sub   a3,a3,t1
  0x02a6d333,  #  3488: divu  t1,a3,a0
  0x01079793,  #  3492: slli  a5,a5,0x10
  0x0107d793,  #  3496: srli  a5,a5,0x10
  0x02a6f6b3,  #  3500: remu  a3,a3,a0
  0x02660633,  #  3504: mul   a2,a2,t1
  0x01069693,  #  3508: slli  a3,a3,0x10
  0x00d7e7b3,  #  3512: or    a5,a5,a3
  0x00030693,  #  3516: mv    a3,t1
  0x00c7fe63,  #  3520: bgeu  a5,a2,3548
  0x00f707b3,  #  3524: add   a5,a4,a5
  0xfff30693,  #  3528: addi  a3,t1,-1
  0x00e7e863,  #  3532: bltu  a5,a4,3548
  0x00c7f663,  #  3536: bgeu  a5,a2,3548
  0xffe30693,  #  3540: addi  a3,t1,-2
  0x00e787b3,  #  3544: add   a5,a5,a4
  0x01059593,  #  3548: slli  a1,a1,0x10
  0x40c787b3,  #  3552: sub   a5,a5,a2
  0x00d5e5b3,  #  3556: or    a1,a1,a3
  0xea5ff06f,  #  3560: j     3212
  0x18de6663,  #  3564: bltu  t3,a3,3960
  0x000107b7,  #  3568: lui   a5,0x10
  0x04f6f463,  #  3572: bgeu  a3,a5,3644
  0x1006b713,  #  3576: sltiu a4,a3,256
  0x00173713,  #  3580: seqz  a4,a4
  0x00371713,  #  3584: slli  a4,a4,0x3
  0x00e6d5b3,  #  3588: srl   a1,a3,a4
  0x00000797,  #  3592: auipc a5,0x0
  0x5ac78793,  #  3596: addi  a5,a5,1452
  0x00b787b3,  #  3600: add   a5,a5,a1
  0x0007c783,  #  3604: lbu   a5,0(a5)
  0x00e787b3,  #  3608: add   a5,a5,a4
  0x02000713,  #  3612: li    a4,32
  0x40f705b3,  #  3616: sub   a1,a4,a5
  0x02f71663,  #  3620: bne   a4,a5,3664
  0x00100513,  #  3624: li    a0,1
  0xefc6e4e3,  #  3628: bltu  a3,t3,3348
  0x00c33533,  #  3632: sltu  a0,t1,a2
  0x00153513,  #  3636: seqz  a0,a0
  0xeddff06f,  #  3640: j     3348
  0x010007b7,  #  3644: lui   a5,0x1000
  0x01800713,  #  3648: li    a4,24
  0xfcf6f0e3,  #  3652: bgeu  a3,a5,3588
  0x01000713,  #  3656: li    a4,16
  0xfb9ff06f,  #  3660: j     3588
  0x00f65733,  #  3664: srl   a4,a2,a5
  0x00b696b3,  #  3668: sll   a3,a3,a1
  0x00d766b3,  #  3672: or    a3,a4,a3
  0x00fe5733,  #  3676: srl   a4,t3,a5
  0x00be1e33,  #  3680: sll   t3,t3,a1
  0x00f357b3,  #  3684: srl   a5,t1,a5
  0x01c7e7b3,  #  3688: or    a5,a5,t3
  0x0106de13,  #  3692: srli  t3,a3,0x10
  0x03c75f33,  #  3696: divu  t5,a4,t3
  0x01069813,  #  3700: slli  a6,a3,0x10
  0x01085813,  #  3704: srli  a6,a6,0x10
  0x00b61633,  #  3708: sll   a2,a2,a1
  0x03c77733,  #  3712: remu  a4,a4,t3
  0x03e80eb3,  #  3716: mul   t4,a6,t5
  0x01071513,  #  3720: slli  a0,a4,0x10
  0x0107d713,  #  3724: srli  a4,a5,0x10
  0x00a76733,  #  3728: or    a4,a4,a0
  0x000f0513,  #  3732: mv    a0,t5
  0x01d77e63,  #  3736: bgeu  a4,t4,3764
  0x00e68733,  #  3740: add   a4,a3,a4
  0xffff0513,  #  3744: addi  a0,t5,-1
  0x00d76863,  #  3748: bltu  a4,a3,3764
  0x01d77663,  #  3752: bgeu  a4,t4,3764
  0xffef0513,  #  3756: addi  a0,t5,-2
  0x00d70733,  #  3760: add   a4,a4,a3
  0x41d70733,  #  3764: sub   a4,a4,t4
  0x03c75eb3,  #  3768: divu  t4,a4,t3
  0x01079793,  #  3772: slli  a5,a5,0x10
  0x0107d793,  #  3776: srli  a5,a5,0x10
  0x03c77733,  #  3780: remu  a4,a4,t3
  0x03d80833,  #  3784: mul   a6,a6,t4
  0x01071713,  #  3788: slli  a4,a4,0x10
  0x00e7e7b3,  #  3792: or    a5,a5,a4
  0x000e8713,  #  3796: mv    a4,t4
  0x0107fe63,  #  3800: bgeu  a5,a6,3828
  0x00f687b3,  #  3804: add   a5,a3,a5
  0xfffe8713,  #  3808: addi  a4,t4,-1
  0x00d7e863,  #  3812: bltu  a5,a3,3828
  0x0107f663,  #  3816: bgeu  a5,a6,3828
  0xffee8713,  #  3820: addi  a4,t4,-2
  0x00d787b3,  #  3824: add   a5,a5,a3
  0x01051513,  #  3828: slli  a0,a0,0x10
  0x00010eb7,  #  3832: lui   t4,0x10
  0x00e56533,  #  3836: or    a0,a0,a4
  0xfffe8693,  #  3840: addi  a3,t4,-1
  0x00d57733,  #  3844: and   a4,a0,a3
  0x410787b3,  #  3848: sub   a5,a5,a6
  0x00d676b3,  #  3852: and   a3,a2,a3
  0x01055813,  #  3856: srli  a6,a0,0x10
  0x01065613,  #  3860: srli  a2,a2,0x10
  0x02d70e33,  #  3864: mul   t3,a4,a3
  0x02d806b3,  #  3868: mul   a3,a6,a3
  0x02c70733,  #  3872: mul   a4,a4,a2
  0x02c80833,  #  3876: mul   a6,a6,a2
  0x00d70633,  #  3880: add   a2,a4,a3
  0x010e5713,  #  3884: srli  a4,t3,0x10
  0x00c70733,  #  3888: add   a4,a4,a2
  0x00d77463,  #  3892: bgeu  a4,a3,3900
  0x01d80833,  #  3896: add   a6,a6,t4
  0x01075693,  #  3900: srli  a3,a4,0x10
  0x010686b3,  #  3904: add   a3,a3,a6
  0x02d7e663,  #  3908: bltu  a5,a3,3952
  0xced794e3,  #  3912: bne   a5,a3,3120
  0x000107b7,  #  3916: lui   a5,0x10
  0xfff78793,  #  3920: addi  a5,a5,-1
  0x00f77733,  #  3924: and   a4,a4,a5
  0x01071713,  #  3928: slli  a4,a4,0x10
  0x00fe7e33,  #  3932: and   t3,t3,a5
  0x00b31333,  #  3936: sll   t1,t1,a1
  0x01c70733,  #  3940: add   a4,a4,t3
  0x00000593,  #  3944: li    a1,0
  0xdae374e3,  #  3948: bgeu  t1,a4,3348
  0xfff50513,  #  3952: addi  a0,a0,-1
  0xcbdff06f,  #  3956: j     3120
  0x00000593,  #  3960: li    a1,0
  0x00000513,  #  3964: li    a0,0
  0xd95ff06f,  #  3968: j     3348
  # __udivdi3:
  0x00050893,  #  3972: mv    a7,a0
  0x00058313,  #  3976: mv    t1,a1
  0x00060713,  #  3980: mv    a4,a2
  0x00050813,  #  3984: mv    a6,a0
  0x00058793,  #  3988: mv    a5,a1
  0x28069263,  #  3992: bnez  a3,4636
  0x00000597,  #  3996: auipc a1,0x0
  0x41858593,  #  4000: addi  a1,a1,1048
  0x0ec37663,  #  4004: bgeu  t1,a2,4240
  0x000106b7,  #  4008: lui   a3,0x10
  0x0cd67863,  #  4012: bgeu  a2,a3,4220
  0x10063693,  #  4016: sltiu a3,a2,256
  0x0016b693,  #  4020: seqz  a3,a3
  0x00369693,  #  4024: slli  a3,a3,0x3
  0x00d65533,  #  4028: srl   a0,a2,a3
  0x00a585b3,  #  4032: add   a1,a1,a0
  0x0005c583,  #  4036: lbu   a1,0(a1)
  0x02000513,  #  4040: li    a0,32
  0x00d586b3,  #  4044: add   a3,a1,a3
  0x40d505b3,  #  4048: sub   a1,a0,a3
  0x00d50c63,  #  4052: beq   a0,a3,4076
  0x00b317b3,  #  4056: sll   a5,t1,a1
  0x00d8d6b3,  #  4060: srl   a3,a7,a3
  0x00b61733,  #  4064: sll   a4,a2,a1
  0x00f6e7b3,  #  4068: or    a5,a3,a5
  0x00b89833,  #  4072: sll   a6,a7,a1
  0x01075593,  #  4076: srli  a1,a4,0x10
  0x02b7d333,  #  4080: divu  t1,a5,a1
  0x01071613,  #  4084: slli  a2,a4,0x10
  0x01065613,  #  4088: srli  a2,a2,0x10
  0x02b7f7b3,  #  4092: remu  a5,a5,a1
  0x00030513,  #  4096: mv    a0,t1
  0x026608b3,  #  4100: mul   a7,a2,t1
  0x01079693,  #  4104: slli  a3,a5,0x10
  0x01085793,  #  4108: srli  a5,a6,0x10
  0x00d7e7b3,  #  4112: or    a5,a5,a3
  0x0117fe63,  #  4116: bgeu  a5,a7,4144
  0x00f707b3,  #  4120: add   a5,a4,a5
  0xfff30513,  #  4124: addi  a0,t1,-1
  0x00e7e863,  #  4128: bltu  a5,a4,4144
  0x0117f663,  #  4132: bgeu  a5,a7,4144
  0xffe30513,  #  4136: addi  a0,t1,-2
  0x00e787b3,  #  4140: add   a5,a5,a4
  0x411787b3,  #  4144: sub   a5,a5,a7
  0x02b7d8b3,  #  4148: divu  a7,a5,a1
  0x01081813,  #  4152: slli  a6,a6,0x10
  0x01085813,  #  4156: srli  a6,a6,0x10
  0x02b7f7b3,  #  4160: remu  a5,a5,a1
  0x031606b3,  #  4164: mul   a3,a2,a7
  0x01079793,  #  4168: slli  a5,a5,0x10
  0x00f86833,  #  4172: or    a6,a6,a5
  0x00088793,  #  4176: mv    a5,a7
  0x00d87c63,  #  4180: bgeu  a6,a3,4204
  0x01070833,  #  4184: add   a6,a4,a6
  0xfff88793,  #  4188: addi  a5,a7,-1
  0x00e86663,  #  4192: bltu  a6,a4,4204
  0x00d87463,  #  4196: bgeu  a6,a3,4204
  0xffe88793,  #  4200: addi  a5,a7,-2
  0x01051513,  #  4204: slli  a0,a0,0x10
  0x00f56533,  #  4208: or    a0,a0,a5
  0x00000593,  #  4212: li    a1,0
  0x00008067,  #  4216: ret
  0x01000537,  #  4220: lui   a0,0x1000
  0x01800693,  #  4224: li    a3,24
  0xf2a67ce3,  #  4228: bgeu  a2,a0,4028
  0x01000693,  #  4232: li    a3,16
  0xf31ff06f,  #  4236: j     4028
  0x00000693,  #  4240: li    a3,0
  0x00060c63,  #  4244: beqz  a2,4268
  0x000107b7,  #  4248: lui   a5,0x10
  0x0cf67063,  #  4252: bgeu  a2,a5,4444
  0x10063693,  #  4256: sltiu a3,a2,256
  0x0016b693,  #  4260: seqz  a3,a3
  0x00369693,  #  4264: slli  a3,a3,0x3
  0x00d657b3,  #  4268: srl   a5,a2,a3
  0x00f585b3,  #  4272: add   a1,a1,a5
  0x0005c783,  #  4276: lbu   a5,0(a1)
  0x00d787b3,  #  4280: add   a5,a5,a3
  0x02000693,  #  4284: li    a3,32
  0x40f685b3,  #  4288: sub   a1,a3,a5
  0x0af69663,  #  4292: bne   a3,a5,4464
  0x40c307b3,  #  4296: sub   a5,t1,a2
  0x00100593,  #  4300: li    a1,1
  0x01075893,  #  4304: srli  a7,a4,0x10
  0x0317de33,  #  4308: divu  t3,a5,a7
  0x01071613,  #  4312: slli  a2,a4,0x10
  0x01065613,  #  4316: srli  a2,a2,0x10
  0x01085693,  #  4320: srli  a3,a6,0x10
  0x0317f7b3,  #  4324: remu  a5,a5,a7
  0x000e0513,  #  4328: mv    a0,t3
  0x03c60333,  #  4332: mul   t1,a2,t3
  0x01079793,  #  4336: slli  a5,a5,0x10
  0x00f6e7b3,  #  4340: or    a5,a3,a5
  0x0067fe63,  #  4344: bgeu  a5,t1,4372
  0x00f707b3,  #  4348: add   a5,a4,a5
  0xfffe0513,  #  4352: addi  a0,t3,-1
  0x00e7e863,  #  4356: bltu  a5,a4,4372
  0x0067f663,  #  4360: bgeu  a5,t1,4372
  0xffee0513,  #  4364: addi  a0,t3,-2
  0x00e787b3,  #  4368: add   a5,a5,a4
  0x406787b3,  #  4372: sub   a5,a5,t1
  0x0317d333,  #  4376: divu  t1,a5,a7
  0x01081813,  #  4380: slli  a6,a6,0x10
  0x01085813,  #  4384: srli  a6,a6,0x10
  0x0317f7b3,  #  4388: remu  a5,a5,a7
  0x026606b3,  #  4392: mul   a3,a2,t1
  0x01079793,  #  4396: slli  a5,a5,0x10
  0x00f86833,  #  4400: or    a6,a6,a5
  0x00030793,  #  4404: mv    a5,t1
  0x00d87c63,  #  4408: bgeu  a6,a3,4432
  0x01070833,  #  4412: add   a6,a4,a6
  0xfff30793,  #  4416: addi  a5,t1,-1
  0x00e86663,  #  4420: bltu  a6,a4,4432
  0x00d87463,  #  4424: bgeu  a6,a3,4432
  0xffe30793,  #  4428: addi  a5,t1,-2
  0x01051513,  #  4432: slli  a0,a0,0x10
  0x00f56533,  #  4436: or    a0,a0,a5
  0x00008067,  #  4440: ret
  0x010007b7,  #  4444: lui   a5,0x1000
  0x01800693,  #  4448: li    a3,24
  0xf4f674e3,  #  4452: bgeu  a2,a5,4268
  0x01000693,  #  4456: li    a3,16
  0xf41ff06f,  #  4460: j     4268
  0x00b61733,  #  4464: sll   a4,a2,a1
  0x00f356b3,  #  4468: srl   a3,t1,a5
  0x01075513,  #  4472: srli  a0,a4,0x10
  0x00b31333,  #  4476: sll   t1,t1,a1
  0x00f8d7b3,  #  4480: srl   a5,a7,a5
  0x0067e7b3,  #  4484: or    a5,a5,t1
  0x02a6d333,  #  4488: divu  t1,a3,a0
  0x01071613,  #  4492: slli  a2,a4,0x10
  0x01065613,  #  4496: srli  a2,a2,0x10
  0x00b89833,  #  4500: sll   a6,a7,a1
  0x02a6f6b3,  #  4504: remu  a3,a3,a0
  0x026608b3,  #  4508: mul   a7,a2,t1
  0x01069593,  #  4512: slli  a1,a3,0x10
  0x0107d693,  #  4516: srli  a3,a5,0x10
  0x00b6e6b3,  #  4520: or    a3,a3,a1
  0x00030593,  #  4524: mv    a1,t1
  0x0116fe63,  #  4528: bgeu  a3,a7,4556
  0x00d706b3,  #  4532: add   a3,a4,a3
  0xfff30593,  #  4536: addi  a1,t1,-1
  0x00e6e863,  #  4540: bltu  a3,a4,4556
  0x0116f663,  #  4544: bgeu  a3,a7,4556
  0xffe30593,  #  4548: addi  a1,t1,-2
  0x00e686b3,  #  4552: add   a3,a3,a4
  0x411686b3,  #  4556: sub   a3,a3,a7
  0x02a6d8b3,  #  4560: divu  a7,a3,a0
  0x01079793,  #  4564: slli  a5,a5,0x10
  0x0107d793,  #  4568: srli  a5,a5,0x10
  0x02a6f6b3,  #  4572: remu  a3,a3,a0
  0x03160633,  #  4576: mul   a2,a2,a7
  0x01069693,  #  4580: slli  a3,a3,0x10
  0x00d7e7b3,  #  4584: or    a5,a5,a3
  0x00088693,  #  4588: mv    a3,a7
  0x00c7fe63,  #  4592: bgeu  a5,a2,4620
  0x00f707b3,  #  4596: add   a5,a4,a5
  0xfff88693,  #  4600: addi  a3,a7,-1
  0x00e7e863,  #  4604: bltu  a5,a4,4620
  0x00c7f663,  #  4608: bgeu  a5,a2,4620
  0xffe88693,  #  4612: addi  a3,a7,-2
  0x00e787b3,  #  4616: add   a5,a5,a4
  0x01059593,  #  4620: slli  a1,a1,0x10
  0x40c787b3,  #  4624: sub   a5,a5,a2
  0x00d5e5b3,  #  4628: or    a1,a1,a3
  0xeb9ff06f,  #  4632: j     4304
  0x18d5e663,  #  4636: bltu  a1,a3,5032
  0x000107b7,  #  4640: lui   a5,0x10
  0x04f6f463,  #  4644: bgeu  a3,a5,4716
  0x1006b713,  #  4648: sltiu a4,a3,256
  0x00173713,  #  4652: seqz  a4,a4
  0x00371713,  #  4656: slli  a4,a4,0x3
  0x00e6d5b3,  #  4660: srl   a1,a3,a4
  0x00000797,  #  4664: auipc a5,0x0
  0x17c78793,  #  4668: addi  a5,a5,380
  0x00b787b3,  #  4672: add   a5,a5,a1
  0x0007c783,  #  4676: lbu   a5,0(a5)
  0x00e787b3,  #  4680: add   a5,a5,a4
  0x02000713,  #  4684: li    a4,32
  0x40f705b3,  #  4688: sub   a1,a4,a5
  0x02f71663,  #  4692: bne   a4,a5,4736
  0x00100513,  #  4696: li    a0,1
  0xe066eee3,  #  4700: bltu  a3,t1,4216
  0x00c8b533,  #  4704: sltu  a0,a7,a2
  0x00153513,  #  4708: seqz  a0,a0
  0x00008067,  #  4712: ret
  0x010007b7,  #  4716: lui   a5,0x1000
  0x01800713,  #  4720: li    a4,24
  0xfcf6f0e3,  #  4724: bgeu  a3,a5,4660
  0x01000713,  #  4728: li    a4,16
  0xfb9ff06f,  #  4732: j     4660
  0x00f65733,  #  4736: srl   a4,a2,a5
  0x00b696b3,  #  4740: sll   a3,a3,a1
  0x00d766b3,  #  4744: or    a3,a4,a3
  0x00f35733,  #  4748: srl   a4,t1,a5
  0x00b31333,  #  4752: sll   t1,t1,a1
  0x00f8d7b3,  #  4756: srl   a5,a7,a5
  0x0067e7b3,  #  4760: or    a5,a5,t1
  0x0106d313,  #  4764: srli  t1,a3,0x10
  0x02675eb3,  #  4768: divu  t4,a4,t1
  0x01069813,  #  4772: slli  a6,a3,0x10
  0x01085813,  #  4776: srli  a6,a6,0x10
  0x00b61633,  #  4780: sll   a2,a2,a1
  0x02677733,  #  4784: remu  a4,a4,t1
  0x03d80e33,  #  4788: mul   t3,a6,t4
  0x01071513,  #  4792: slli  a0,a4,0x10
  0x0107d713,  #  4796: srli  a4,a5,0x10
  0x00a76733,  #  4800: or    a4,a4,a0
  0x000e8513,  #  4804: mv    a0,t4
  0x01c77e63,  #  4808: bgeu  a4,t3,4836
  0x00e68733,  #  4812: add   a4,a3,a4
  0xfffe8513,  #  4816: addi  a0,t4,-1
  0x00d76863,  #  4820: bltu  a4,a3,4836
  0x01c77663,  #  4824: bgeu  a4,t3,4836
  0xffee8513,  #  4828: addi  a0,t4,-2
  0x00d70733,  #  4832: add   a4,a4,a3
  0x41c70733,  #  4836: sub   a4,a4,t3
  0x02675e33,  #  4840: divu  t3,a4,t1
  0x01079793,  #  4844: slli  a5,a5,0x10
  0x0107d793,  #  4848: srli  a5,a5,0x10
  0x02677733,  #  4852: remu  a4,a4,t1
  0x03c80833,  #  4856: mul   a6,a6,t3
  0x01071713,  #  4860: slli  a4,a4,0x10
  0x00e7e7b3,  #  4864: or    a5,a5,a4
  0x000e0713,  #  4868: mv    a4,t3
  0x0107fe63,  #  4872: bgeu  a5,a6,4900
  0x00f687b3,  #  4876: add   a5,a3,a5
  0xfffe0713,  #  4880: addi  a4,t3,-1
  0x00d7e863,  #  4884: bltu  a5,a3,4900
  0x0107f663,  #  4888: bgeu  a5,a6,4900
  0xffee0713,  #  4892: addi  a4,t3,-2
  0x00d787b3,  #  4896: add   a5,a5,a3
  0x01051513,  #  4900: slli  a0,a0,0x10
  0x00010e37,  #  4904: lui   t3,0x10
  0x00e56533,  #  4908: or    a0,a0,a4
  0xfffe0693,  #  4912: addi  a3,t3,-1
  0x00d57733,  #  4916: and   a4,a0,a3
  0x410787b3,  #  4920: sub   a5,a5,a6
  0x00d676b3,  #  4924: and   a3,a2,a3
  0x01055813,  #  4928: srli  a6,a0,0x10
  0x01065613,  #  4932: srli  a2,a2,0x10
  0x02d70333,  #  4936: mul   t1,a4,a3
  0x02d806b3,  #  4940: mul   a3,a6,a3
  0x02c70733,  #  4944: mul   a4,a4,a2
  0x02c80833,  #  4948: mul   a6,a6,a2
  0x00d70633,  #  4952: add   a2,a4,a3
  0x01035713,  #  4956: srli  a4,t1,0x10
  0x00c70733,  #  4960: add   a4,a4,a2
  0x00d77463,  #  4964: bgeu  a4,a3,4972
  0x01c80833,  #  4968: add   a6,a6,t3
  0x01075693,  #  4972: srli  a3,a4,0x10
  0x010686b3,  #  4976: add   a3,a3,a6
  0x02d7e663,  #  4980: bltu  a5,a3,5024
  0xced79ee3,  #  4984: bne   a5,a3,4212
  0x000107b7,  #  4988: lui   a5,0x10
  0xfff78793,  #  4992: addi  a5,a5,-1
  0x00f77733,  #  4996: and   a4,a4,a5
  0x01071713,  #  5000: slli  a4,a4,0x10
  0x00f37333,  #  5004: and   t1,t1,a5
  0x00b898b3,  #  5008: sll   a7,a7,a1
  0x00670733,  #  5012: add   a4,a4,t1
  0x00000593,  #  5016: li    a1,0
  0xcce8fee3,  #  5020: bgeu  a7,a4,4216
  0xfff50513,  #  5024: addi  a0,a0,-1
  0xcd1ff06f,  #  5028: j     4212
  0x00000593,  #  5032: li    a1,0
  0x00000513,  #  5036: li    a0,0
  0x00008067,  #  5040: ret
  # ---- data ----
  0x02020100,  #  5044: "\0..."
  0x03030303,  #  5048: "...."
  0x04040404,  #  5052: "...."
  0x04040404,  #  5056: "...."
  0x05050505,  #  5060: "...."
  0x05050505,  #  5064: "...."
  0x05050505,  #  5068: "...."
  0x05050505,  #  5072: "...."
  0x06060606,  #  5076: "...."
  0x06060606,  #  5080: "...."
  0x06060606,  #  5084: "...."
  0x06060606,  #  5088: "...."
  0x06060606,  #  5092: "...."
  0x06060606,  #  5096: "...."
  0x06060606,  #  5100: "...."
  0x06060606,  #  5104: "...."
  0x07070707,  #  5108: "...."
  0x07070707,  #  5112: "...."
  0x07070707,  #  5116: "...."
  0x07070707,  #  5120: "...."
  0x07070707,  #  5124: "...."
  0x07070707,  #  5128: "...."
  0x07070707,  #  5132: "...."
  0x07070707,  #  5136: "...."
  0x07070707,  #  5140: "...."
  0x07070707,  #  5144: "...."
  0x07070707,  #  5148: "...."
  0x07070707,  #  5152: "...."
  0x07070707,  #  5156: "...."
  0x07070707,  #  5160: "...."
  0x07070707,  #  5164: "...."
  0x07070707,  #  5168: "...."
  0x08080808,  #  5172: "...."
  0x08080808,  #  5176: "...."
  0x08080808,  #  5180: "...."
  0x08080808,  #  5184: "...."
  0x08080808,  #  5188: "...."
  0x08080808,  #  5192: "...."
  0x08080808,  #  5196: "...."
  0x08080808,  #  5200: "...."
  0x08080808,  #  5204: "...."
  0x08080808,  #  5208: "...."
  0x08080808,  #  5212: "...."
  0x08080808,  #  5216: "...."
  0x08080808,  #  5220: "...."
  0x08080808,  #  5224: "...."
  0x08080808,  #  5228: "...."
  0x08080808,  #  5232: "...."
  0x08080808,  #  5236: "...."
  0x08080808,  #  5240: "...."
  0x08080808,  #  5244: "...."
  0x08080808,  #  5248: "...."
  0x08080808,  #  5252: "...."
  0x08080808,  #  5256: "...."
  0x08080808,  #  5260: "...."
  0x08080808,  #  5264: "...."
  0x08080808,  #  5268: "...."
  0x08080808,  #  5272: "...."
  0x08080808,  #  5276: "...."
  0x08080808,  #  5280: "...."
  0x08080808,  #  5284: "...."
  0x08080808,  #  5288: "...."
  0x08080808,  #  5292: "...."
  0x08080808,  #  5296: "...."
  0x00000010,  #  5300: ".\0\0\0"
  0x00000000,  #  5304: "\0\0\0\0"
  0x00527a03,  #  5308: ".zR\0"
  0x01017c01,  #  5312: ".|.."
  0x00020d1b,  #  5316: "...\0"
  0x00000010,  #  5320: ".\0\0\0"
  0x00000018,  #  5324: ".\0\0\0"
  0xfffff63c,  #  5328: "<..."
  0x00000478,  #  5332: "x.\0\0"
  0x00000000,  #  5336: "\0\0\0\0"
  0x00000010,  #  5340: ".\0\0\0"
  0x0000002c,  #  5344: ",\0\0\0"
  0xfffffaa0,  #  5348: "...."
  0x00000430,  #  5352: "0.\0\0"
  0x00000000]  #  5356: "\0\0\0\0"

# zero-initialized data (.bss), not part of the image:
#    5360: _end

m = machine(mem_size=0x400000)
m.write_i32_vec(prog, 0)
m.run(start=0)
