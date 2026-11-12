from machine import *

# Library Checker "Counting Primes" (https://judge.yosupo.jp/problem/counting_primes,
# N <= 1e11): fast accepted submission 50137 by grumpygordon, ported to nanofive.
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
#   echo 100000000 | python3 counting_primes_grumpygordon.py   ->  5761455
#
# C++ source:
#
#   // Library Checker "Counting Primes", submission 50137 by grumpygordon (14 ms):
#   // https://judge.yosupo.jp/submission/50137
#   // Lucy_Hedgehog-style prime counting over the odd "rough" numbers, O(N^(3/4)/log N).
#   // Port changes (marked //*): runtime from rt.h instead of <cstdio>/<vector>/<cmath>,
#   // no avx2/O3 attribute, the double division in divide() is an exact integer
#   // division (rv32im has no FPU), and one N is read instead of looping to EOF.
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
#   using namespace std;
#
#   using i64 = long long;
#
#   int isqrt(i64 n) {
#     return isqrt64(n);  //* sqrtl(n)
#   }
#
#   i64 prime_pi(const i64 N) {  //* __attribute__((target("avx2"), optimize("O3", "unroll-loops")))
#     if (N <= 1) return 0;
#     if (N == 2) return 1;
#     const int v = isqrt(N);
#     int s = (v + 1) / 2;
#     vector<int> smalls(s); for (int i = 1; i < s; ++i) smalls[i] = i;
#     vector<int> roughs(s); for (int i = 0; i < s; ++i) roughs[i] = 2 * i + 1;
#     vector<i64> larges(s); for (int i = 0; i < s; ++i) larges[i] = (N / (2 * i + 1) - 1) / 2;
#     vector<bool> skip(v + 1);
#     const auto divide = [] (i64 n, i64 d) -> int { return n / d; };  //* double(n) / d
#     const auto half = [] (int n) -> int { return (n - 1) >> 1; };
#     int pc = 0;
#     for (int p = 3; p <= v; p += 2) if (!skip[p]) {
#       int q = p * p;
#       if (i64(q) * q > N) break;
#       skip[p] = true;
#       for (int i = q; i <= v; i += 2 * p) skip[i] = true;
#       int ns = 0;
#       for (int k = 0; k < s; ++k) {
#         int i = roughs[k];
#         if (skip[i]) continue;
#         i64 d = i64(i) * p;
#         larges[ns] = larges[k] - (d <= v ? larges[smalls[d >> 1] - pc] : smalls[half(divide(N, d))]) + pc;
#         roughs[ns++] = i;
#       }
#       s = ns;
#       for (int i = half(v), j = ((v / p) - 1) | 1; j >= p; j -= 2) {
#         int c = smalls[j >> 1] - pc;
#         for (int e = (j * p) >> 1; i >= e; --i) smalls[i] -= c;
#       }
#       ++pc;
#     }
#     larges[0] += i64(s + 2 * (pc - 1)) * (s - 1) / 2;
#     for (int k = 1; k < s; ++k) larges[0] -= larges[k];
#     for (int l = 1; l < s; ++l) {
#       int q = roughs[l];
#       i64 M = N / q;
#       int e = smalls[half(M / q)] - pc;
#       if (e < l + 1) break;
#       i64 t = 0;
#       for (int k = l + 1; k <= e; ++k) t += smalls[half(divide(M, roughs[k]))];
#       larges[0] += t - i64(e - l) * (pc + l - 1);
#     }
#     return larges[0] + 1;
#   }
#
#   int main() {
#     i64 N = read_u64();          //* while (~scanf("%lld", &N))
#     print_u64(prime_pi(N));      //* printf("%lld\n", ...)
#   }

prog = [
  # _start:
  0x00400137,  #     0: lui   sp,0x400
  0x125000ef,  #     4: jal   2344 <main>
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
  # isqrt(long long):
  0xfe010113,  #    48: addi  sp,sp,-32
  0x00812c23,  #    52: sw    s0,24(sp)
  0x00150413,  #    56: addi  s0,a0,1
  0x00912a23,  #    60: sw    s1,20(sp)
  0x00a434b3,  #    64: sltu  s1,s0,a0
  0x00b484b3,  #    68: add   s1,s1,a1
  0x01f49793,  #    72: slli  a5,s1,0x1f
  0x01212823,  #    76: sw    s2,16(sp)
  0x01312623,  #    80: sw    s3,12(sp)
  0x00145413,  #    84: srli  s0,s0,0x1
  0x00112e23,  #    88: sw    ra,28(sp)
  0x0014d493,  #    92: srli  s1,s1,0x1
  0x00058913,  #    96: mv    s2,a1
  0x00050993,  #   100: mv    s3,a0
  0x0087e433,  #   104: or    s0,a5,s0
  0x06b4f463,  #   108: bgeu  s1,a1,212
  0x00040613,  #   112: mv    a2,s0
  0x00048693,  #   116: mv    a3,s1
  0x00098513,  #   120: mv    a0,s3
  0x00090593,  #   124: mv    a1,s2
  0x67d000ef,  #   128: jal   3836 <__udivdi3>
  0x00850733,  #   132: add   a4,a0,s0
  0x009585b3,  #   136: add   a1,a1,s1
  0x00a73533,  #   140: sltu  a0,a4,a0
  0x00b507b3,  #   144: add   a5,a0,a1
  0x00048693,  #   148: mv    a3,s1
  0x00040513,  #   152: mv    a0,s0
  0x01f79613,  #   156: slli  a2,a5,0x1f
  0x00175413,  #   160: srli  s0,a4,0x1
  0x0017d493,  #   164: srli  s1,a5,0x1
  0x00866433,  #   168: or    s0,a2,s0
  0xfcd4e2e3,  #   172: bltu  s1,a3,112
  0x00969463,  #   176: bne   a3,s1,184
  0xfaa46ee3,  #   180: bltu  s0,a0,112
  0x01c12083,  #   184: lw    ra,28(sp)
  0x01812403,  #   188: lw    s0,24(sp)
  0x01412483,  #   192: lw    s1,20(sp)
  0x01012903,  #   196: lw    s2,16(sp)
  0x00c12983,  #   200: lw    s3,12(sp)
  0x02010113,  #   204: addi  sp,sp,32
  0x00008067,  #   208: ret
  0xfe9592e3,  #   212: bne   a1,s1,184
  0xf8a46ce3,  #   216: bltu  s0,a0,112
  0xfddff06f,  #   220: j     184
  # prime_pi(long long):
  0xf9010113,  #   224: addi  sp,sp,-112
  0x06112623,  #   228: sw    ra,108(sp)
  0x00b12223,  #   232: sw    a1,4(sp)
  0x00a12023,  #   236: sw    a0,0(sp)
  0x76b05e63,  #   240: blez  a1,2156
  0x00012703,  #   244: lw    a4,0(sp)
  0x00200793,  #   248: li    a5,2
  0x7cf70a63,  #   252: beq   a4,a5,2256
  0x00012783,  #   256: lw    a5,0(sp)
  0x00412703,  #   260: lw    a4,4(sp)
  0x06812423,  #   264: sw    s0,104(sp)
  0x00178413,  #   268: addi  s0,a5,1
  0x06912223,  #   272: sw    s1,100(sp)
  0x00f434b3,  #   276: sltu  s1,s0,a5
  0x00e484b3,  #   280: add   s1,s1,a4
  0x01f49793,  #   284: slli  a5,s1,0x1f
  0x00145413,  #   288: srli  s0,s0,0x1
  0x07212023,  #   292: sw    s2,96(sp)
  0x05312e23,  #   296: sw    s3,92(sp)
  0x05412c23,  #   300: sw    s4,88(sp)
  0x05512a23,  #   304: sw    s5,84(sp)
  0x05612823,  #   308: sw    s6,80(sp)
  0x05712623,  #   312: sw    s7,76(sp)
  0x05812423,  #   316: sw    s8,72(sp)
  0x05912223,  #   320: sw    s9,68(sp)
  0x05a12023,  #   324: sw    s10,64(sp)
  0x03b12e23,  #   328: sw    s11,60(sp)
  0x0014d493,  #   332: srli  s1,s1,0x1
  0x0087e433,  #   336: or    s0,a5,s0
  0x7ae4fa63,  #   340: bgeu  s1,a4,2312
  0x00012503,  #   344: lw    a0,0(sp)
  0x00412583,  #   348: lw    a1,4(sp)
  0x00048693,  #   352: mv    a3,s1
  0x00040613,  #   356: mv    a2,s0
  0x595000ef,  #   360: jal   3836 <__udivdi3>
  0x008507b3,  #   364: add   a5,a0,s0
  0x009585b3,  #   368: add   a1,a1,s1
  0x00a7b533,  #   372: sltu  a0,a5,a0
  0x00b50533,  #   376: add   a0,a0,a1
  0x00040293,  #   380: mv    t0,s0
  0x00048713,  #   384: mv    a4,s1
  0x01f51693,  #   388: slli  a3,a0,0x1f
  0x0017d413,  #   392: srli  s0,a5,0x1
  0x00155493,  #   396: srli  s1,a0,0x1
  0x0086e433,  #   400: or    s0,a3,s0
  0xfce4e2e3,  #   404: bltu  s1,a4,344
  0x00971463,  #   408: bne   a4,s1,416
  0xfa546ee3,  #   412: bltu  s0,t0,344
  0x00128a13,  #   416: addi  s4,t0,1
  0x000014b7,  #   420: lui   s1,0x1
  0x4684a783,  #   424: lw    a5,1128(s1)
  0x01fa5413,  #   428: srli  s0,s4,0x1f
  0x01440433,  #   432: add   s0,s0,s4
  0x40145413,  #   436: srai  s0,s0,0x1
  0x00778793,  #   440: addi  a5,a5,7
  0x00241613,  #   444: slli  a2,s0,0x2
  0xff87fb13,  #   448: andi  s6,a5,-8
  0x00760d13,  #   452: addi  s10,a2,7
  0x01ab0d33,  #   456: add   s10,s6,s10
  0xff8d7d13,  #   460: andi  s10,s10,-8
  0x72060463,  #   464: beqz  a2,2296
  0x00cb05b3,  #   468: add   a1,s6,a2
  0x000b0713,  #   472: mv    a4,s6
  0x00070023,  #   476: sb    zero,0(a4)
  0x00170713,  #   480: addi  a4,a4,1
  0xfeb71ce3,  #   484: bne   a4,a1,476
  0x00300713,  #   488: li    a4,3
  0x01475e63,  #   492: bge   a4,s4,520
  0x004b0693,  #   496: addi  a3,s6,4
  0x00100713,  #   500: li    a4,1
  0x00e6a023,  #   504: sw    a4,0(a3)
  0x00170713,  #   508: addi  a4,a4,1
  0x00468693,  #   512: addi  a3,a3,4
  0xfe874ae3,  #   516: blt   a4,s0,504
  0x00cd0633,  #   520: add   a2,s10,a2
  0x000d0713,  #   524: mv    a4,s10
  0x00070023,  #   528: sb    zero,0(a4)
  0x00170713,  #   532: addi  a4,a4,1
  0xfec71ce3,  #   536: bne   a4,a2,528
  0x00760613,  #   540: addi  a2,a2,7
  0xff867b93,  #   544: andi  s7,a2,-8
  0x00341593,  #   548: slli  a1,s0,0x3
  0x00100713,  #   552: li    a4,1
  0x000b8993,  #   556: mv    s3,s7
  0x00bb8cb3,  #   560: add   s9,s7,a1
  0x67475063,  #   564: bge   a4,s4,2196
  0x000d0613,  #   568: mv    a2,s10
  0x00100693,  #   572: li    a3,1
  0x00000713,  #   576: li    a4,0
  0x00d62023,  #   580: sw    a3,0(a2)
  0x00170713,  #   584: addi  a4,a4,1
  0x00268693,  #   588: addi  a3,a3,2
  0x00460613,  #   592: addi  a2,a2,4
  0xfe8748e3,  #   596: blt   a4,s0,580
  0x00058e63,  #   600: beqz  a1,628
  0x000b8713,  #   604: mv    a4,s7
  0x00070023,  #   608: sb    zero,0(a4)
  0x00170713,  #   612: addi  a4,a4,1
  0xff971ce3,  #   616: bne   a4,s9,608
  0x00100713,  #   620: li    a4,1
  0x63475663,  #   624: bge   a4,s4,2204
  0x00100913,  #   628: li    s2,1
  0x00000c13,  #   632: li    s8,0
  0x01412623,  #   636: sw    s4,12(sp)
  0x00012d83,  #   640: lw    s11,0(sp)
  0x000c0a13,  #   644: mv    s4,s8
  0x00090c13,  #   648: mv    s8,s2
  0x00412903,  #   652: lw    s2,4(sp)
  0x00000a93,  #   656: li    s5,0
  0x00098793,  #   660: mv    a5,s3
  0x00512423,  #   664: sw    t0,8(sp)
  0x000a8993,  #   668: mv    s3,s5
  0x00078a93,  #   672: mv    s5,a5
  0x000c0613,  #   676: mv    a2,s8
  0x000a0693,  #   680: mv    a3,s4
  0x000d8513,  #   684: mv    a0,s11
  0x00090593,  #   688: mv    a1,s2
  0x7d0000ef,  #   692: jal   2692 <__divdi3>
  0x00153793,  #   696: seqz  a5,a0
  0x40f585b3,  #   700: sub   a1,a1,a5
  0x01f5d713,  #   704: srli  a4,a1,0x1f
  0xfff50793,  #   708: addi  a5,a0,-1
  0x00f707b3,  #   712: add   a5,a4,a5
  0x00e7b733,  #   716: sltu  a4,a5,a4
  0x00b70733,  #   720: add   a4,a4,a1
  0x01f71593,  #   724: slli  a1,a4,0x1f
  0x0017d793,  #   728: srli  a5,a5,0x1
  0x002c0613,  #   732: addi  a2,s8,2
  0x00f5e7b3,  #   736: or    a5,a1,a5
  0x40175713,  #   740: srai  a4,a4,0x1
  0x018635b3,  #   744: sltu  a1,a2,s8
  0x00faa023,  #   748: sw    a5,0(s5)
  0x00eaa223,  #   752: sw    a4,4(s5)
  0x00198993,  #   756: addi  s3,s3,1
  0x00060c13,  #   760: mv    s8,a2
  0x01458a33,  #   764: add   s4,a1,s4
  0x008a8a93,  #   768: addi  s5,s5,8
  0xfa89c0e3,  #   772: blt   s3,s0,676
  0x00c12a03,  #   776: lw    s4,12(sp)
  0x00812283,  #   780: lw    t0,8(sp)
  0x000c8f93,  #   784: mv    t6,s9
  0x014c8733,  #   788: add   a4,s9,s4
  0x46e4a423,  #   792: sw    a4,1128(s1)
  0x014f8a33,  #   796: add   s4,t6,s4
  0x000f8713,  #   800: mv    a4,t6
  0x00170713,  #   804: addi  a4,a4,1
  0xfe070fa3,  #   808: sb    zero,-1(a4)
  0xff471ce3,  #   812: bne   a4,s4,804
  0x00200713,  #   816: li    a4,2
  0x5e575463,  #   820: bge   a4,t0,2332
  0xfff28713,  #   824: addi  a4,t0,-1
  0x003f8c13,  #   828: addi  s8,t6,3
  0x00000313,  #   832: li    t1,0
  0xffcb0993,  #   836: addi  s3,s6,-4
  0x40175c93,  #   840: srai  s9,a4,0x1
  0xffa00793,  #   844: li    a5,-6
  0x000c0d93,  #   848: mv    s11,s8
  0x000d0493,  #   852: mv    s1,s10
  0x00030c13,  #   856: mv    s8,t1
  0x00098a13,  #   860: mv    s4,s3
  0x000b8313,  #   864: mv    t1,s7
  0x00412d03,  #   868: lw    s10,4(sp)
  0x00300913,  #   872: li    s2,3
  0x00000393,  #   876: li    t2,0
  0x00100e13,  #   880: li    t3,1
  0x41f2de93,  #   884: srai  t4,t0,0x1f
  0x00078f13,  #   888: mv    t5,a5
  0x000f8b93,  #   892: mv    s7,t6
  0x000c8993,  #   896: mv    s3,s9
  0x0200006f,  #   900: j     932
  0x00290793,  #   904: addi  a5,s2,2
  0x0127b733,  #   908: sltu  a4,a5,s2
  0x002d8d93,  #   912: addi  s11,s11,2
  0x00078913,  #   916: mv    s2,a5
  0xffcf0f13,  #   920: addi  t5,t5,-4
  0x007703b3,  #   924: add   t2,a4,t2
  0x24f2ca63,  #   928: blt   t0,a5,1524
  0x000dc783,  #   932: lbu   a5,0(s11)
  0xfe0790e3,  #   936: bnez  a5,904
  0x032907b3,  #   940: mul   a5,s2,s2
  0x02f79733,  #   944: mulh  a4,a5,a5
  0x02f786b3,  #   948: mul   a3,a5,a5
  0x22ed4e63,  #   952: blt   s10,a4,1524
  0x53a70863,  #   956: beq   a4,s10,2284
  0x01cd8023,  #   960: sb    t3,0(s11)
  0x00f2ca63,  #   964: blt   t0,a5,984
  0x00fb8733,  #   968: add   a4,s7,a5
  0x01c70023,  #   972: sb    t3,0(a4)
  0x41e787b3,  #   976: sub   a5,a5,t5
  0xfef2dae3,  #   980: bge   t0,a5,968
  0x4a805a63,  #   984: blez  s0,2188
  0x00241413,  #   988: slli  s0,s0,0x2
  0x009408b3,  #   992: add   a7,s0,s1
  0x00000413,  #   996: li    s0,0
  0x03312023,  #  1000: sw    s3,32(sp)
  0x03e12223,  #  1004: sw    t5,36(sp)
  0x00040993,  #  1008: mv    s3,s0
  0x03b12423,  #  1012: sw    s11,40(sp)
  0x00048413,  #  1016: mv    s0,s1
  0x000b0d93,  #  1020: mv    s11,s6
  0x00048f13,  #  1024: mv    t5,s1
  0x000d0713,  #  1028: mv    a4,s10
  0x03412623,  #  1032: sw    s4,44(sp)
  0x000b8d13,  #  1036: mv    s10,s7
  0x41fc5f93,  #  1040: srai  t6,s8,0x1f
  0x00088b13,  #  1044: mv    s6,a7
  0x00030493,  #  1048: mv    s1,t1
  0x00512e23,  #  1052: sw    t0,28(sp)
  0x00030b93,  #  1056: mv    s7,t1
  0x00090a13,  #  1060: mv    s4,s2
  0x0800006f,  #  1064: j     1192
  0x01d61663,  #  1068: bne   a2,t4,1080
  0x01c12603,  #  1072: lw    a2,28(sp)
  0x0af66c63,  #  1076: bltu  a2,a5,1260
  0x0017d793,  #  1080: srli  a5,a5,0x1
  0x00279793,  #  1084: slli  a5,a5,0x2
  0x00fd87b3,  #  1088: add   a5,s11,a5
  0x0007a683,  #  1092: lw    a3,0(a5)
  0x418686b3,  #  1096: sub   a3,a3,s8
  0x00369693,  #  1100: slli  a3,a3,0x3
  0x00db86b3,  #  1104: add   a3,s7,a3
  0x0006a783,  #  1108: lw    a5,0(a3)
  0x0046a683,  #  1112: lw    a3,4(a3)
  0x40f907b3,  #  1116: sub   a5,s2,a5
  0x00f93933,  #  1120: sltu  s2,s2,a5
  0x40dc8cb3,  #  1124: sub   s9,s9,a3
  0x018785b3,  #  1128: add   a1,a5,s8
  0x412c8cb3,  #  1132: sub   s9,s9,s2
  0x00399613,  #  1136: slli  a2,s3,0x3
  0x00f5b7b3,  #  1140: sltu  a5,a1,a5
  0x01fc8cb3,  #  1144: add   s9,s9,t6
  0x00cb8633,  #  1148: add   a2,s7,a2
  0x019787b3,  #  1152: add   a5,a5,s9
  0x00299693,  #  1156: slli  a3,s3,0x2
  0x00f62223,  #  1160: sw    a5,4(a2)
  0x00b62023,  #  1164: sw    a1,0(a2)
  0x00df07b3,  #  1168: add   a5,t5,a3
  0x0157a023,  #  1172: sw    s5,0(a5)
  0x00198993,  #  1176: addi  s3,s3,1
  0x00440413,  #  1180: addi  s0,s0,4
  0x00848493,  #  1184: addi  s1,s1,8
  0x088b0c63,  #  1188: beq   s6,s0,1340
  0x00042a83,  #  1192: lw    s5,0(s0)
  0x00012503,  #  1196: lw    a0,0(sp)
  0x00070593,  #  1200: mv    a1,a4
  0x015d06b3,  #  1204: add   a3,s10,s5
  0x0006c683,  #  1208: lbu   a3,0(a3)
  0x41fad793,  #  1212: srai  a5,s5,0x1f
  0xfc069ee3,  #  1216: bnez  a3,1180
  0x035386b3,  #  1220: mul   a3,t2,s5
  0x0004a903,  #  1224: lw    s2,0(s1)
  0x0044ac83,  #  1228: lw    s9,4(s1)
  0x034787b3,  #  1232: mul   a5,a5,s4
  0x034ab633,  #  1236: mulhu a2,s5,s4
  0x00d787b3,  #  1240: add   a5,a5,a3
  0x00c78633,  #  1244: add   a2,a5,a2
  0x00060693,  #  1248: mv    a3,a2
  0x034a87b3,  #  1252: mul   a5,s5,s4
  0xf4ced2e3,  #  1256: bge   t4,a2,1068
  0x00078613,  #  1260: mv    a2,a5
  0x01d12c23,  #  1264: sw    t4,24(sp)
  0x01f12a23,  #  1268: sw    t6,20(sp)
  0x00e12823,  #  1272: sw    a4,16(sp)
  0x00712623,  #  1276: sw    t2,12(sp)
  0x01e12423,  #  1280: sw    t5,8(sp)
  0x580000ef,  #  1284: jal   2692 <__divdi3>
  0xfff50793,  #  1288: addi  a5,a0,-1
  0x4017d793,  #  1292: srai  a5,a5,0x1
  0x00279793,  #  1296: slli  a5,a5,0x2
  0x00fd87b3,  #  1300: add   a5,s11,a5
  0x0007a783,  #  1304: lw    a5,0(a5)
  0x01812e83,  #  1308: lw    t4,24(sp)
  0x01412f83,  #  1312: lw    t6,20(sp)
  0x01012703,  #  1316: lw    a4,16(sp)
  0x00c12383,  #  1320: lw    t2,12(sp)
  0x00812f03,  #  1324: lw    t5,8(sp)
  0x41f7d693,  #  1328: srai  a3,a5,0x1f
  0x00100e13,  #  1332: li    t3,1
  0xf25ff06f,  #  1336: j     1116
  0x00098413,  #  1340: mv    s0,s3
  0x000d8b13,  #  1344: mv    s6,s11
  0x000f0493,  #  1348: mv    s1,t5
  0x000a0913,  #  1352: mv    s2,s4
  0x02012983,  #  1356: lw    s3,32(sp)
  0x02812d83,  #  1360: lw    s11,40(sp)
  0x02412f03,  #  1364: lw    t5,36(sp)
  0x01c12283,  #  1368: lw    t0,28(sp)
  0x02c12a03,  #  1372: lw    s4,44(sp)
  0x000b8313,  #  1376: mv    t1,s7
  0x000d0b93,  #  1380: mv    s7,s10
  0x00070d13,  #  1384: mv    s10,a4
  0x0322c5b3,  #  1388: div   a1,t0,s2
  0xfff58593,  #  1392: addi  a1,a1,-1
  0x0015e593,  #  1396: ori   a1,a1,1
  0x0525ce63,  #  1400: blt   a1,s2,1492
  0x03258833,  #  1404: mul   a6,a1,s2
  0x00098793,  #  1408: mv    a5,s3
  0x4015d713,  #  1412: srai  a4,a1,0x1
  0x00271713,  #  1416: slli  a4,a4,0x2
  0x00eb0733,  #  1420: add   a4,s6,a4
  0x00072603,  #  1424: lw    a2,0(a4)
  0x40185513,  #  1428: srai  a0,a6,0x1
  0x41860633,  #  1432: sub   a2,a2,s8
  0x02a7c663,  #  1436: blt   a5,a0,1480
  0x00279793,  #  1440: slli  a5,a5,0x2
  0x00251693,  #  1444: slli  a3,a0,0x2
  0x016787b3,  #  1448: add   a5,a5,s6
  0x014686b3,  #  1452: add   a3,a3,s4
  0x0007a703,  #  1456: lw    a4,0(a5)
  0xffc78793,  #  1460: addi  a5,a5,-4
  0x40c70733,  #  1464: sub   a4,a4,a2
  0x00e7a223,  #  1468: sw    a4,4(a5)
  0xfef698e3,  #  1472: bne   a3,a5,1456
  0xfff50793,  #  1476: addi  a5,a0,-1
  0xffe58593,  #  1480: addi  a1,a1,-2
  0x01e80833,  #  1484: add   a6,a6,t5
  0xfb25dae3,  #  1488: bge   a1,s2,1412
  0x00290793,  #  1492: addi  a5,s2,2
  0x0127b733,  #  1496: sltu  a4,a5,s2
  0x001c0c13,  #  1500: addi  s8,s8,1
  0x00078913,  #  1504: mv    s2,a5
  0x002d8d93,  #  1508: addi  s11,s11,2
  0xffcf0f13,  #  1512: addi  t5,t5,-4
  0x007703b3,  #  1516: add   t2,a4,t2
  0xdaf2dae3,  #  1520: bge   t0,a5,932
  0xfffc0713,  #  1524: addi  a4,s8,-1
  0x00030b93,  #  1528: mv    s7,t1
  0x00048d13,  #  1532: mv    s10,s1
  0x000c0313,  #  1536: mv    t1,s8
  0x00171713,  #  1540: slli  a4,a4,0x1
  0xfff40693,  #  1544: addi  a3,s0,-1
  0x00e40733,  #  1548: add   a4,s0,a4
  0x02d71633,  #  1552: mulh  a2,a4,a3
  0x000baf83,  #  1556: lw    t6,0(s7)
  0x004ba503,  #  1560: lw    a0,4(s7)
  0x00100593,  #  1564: li    a1,1
  0x02d70733,  #  1568: mul   a4,a4,a3
  0x01f65693,  #  1572: srli  a3,a2,0x1f
  0x00e68733,  #  1576: add   a4,a3,a4
  0x00d736b3,  #  1580: sltu  a3,a4,a3
  0x00c686b3,  #  1584: add   a3,a3,a2
  0x01f69613,  #  1588: slli  a2,a3,0x1f
  0x00175713,  #  1592: srli  a4,a4,0x1
  0x00e66733,  #  1596: or    a4,a2,a4
  0x01f70fb3,  #  1600: add   t6,a4,t6
  0x4016d693,  #  1604: srai  a3,a3,0x1
  0x00efb733,  #  1608: sltu  a4,t6,a4
  0x00a686b3,  #  1612: add   a3,a3,a0
  0x00d70f33,  #  1616: add   t5,a4,a3
  0x01fba023,  #  1620: sw    t6,0(s7)
  0x01eba223,  #  1624: sw    t5,4(s7)
  0x000f8d93,  #  1628: mv    s11,t6
  0x1a85d863,  #  1632: bge   a1,s0,2064
  0x00341513,  #  1636: slli  a0,s0,0x3
  0x008b8713,  #  1640: addi  a4,s7,8
  0x00ab8533,  #  1644: add   a0,s7,a0
  0x00072783,  #  1648: lw    a5,0(a4)
  0x00472603,  #  1652: lw    a2,4(a4)
  0x00870713,  #  1656: addi  a4,a4,8
  0x40fd87b3,  #  1660: sub   a5,s11,a5
  0x00fdb6b3,  #  1664: sltu  a3,s11,a5
  0x40cf0f33,  #  1668: sub   t5,t5,a2
  0x40df0f33,  #  1672: sub   t5,t5,a3
  0x00fba023,  #  1676: sw    a5,0(s7)
  0x01eba223,  #  1680: sw    t5,4(s7)
  0x00078d93,  #  1684: mv    s11,a5
  0xfce51ce3,  #  1688: bne   a0,a4,1648
  0x004d0293,  #  1692: addi  t0,s10,4
  0x41f35793,  #  1696: srai  a5,t1,0x1f
  0x00030c13,  #  1700: mv    s8,t1
  0x00f12623,  #  1704: sw    a5,12(sp)
  0x00100a93,  #  1708: li    s5,1
  0x01712c23,  #  1712: sw    s7,24(sp)
  0x00812e23,  #  1716: sw    s0,28(sp)
  0x00612a23,  #  1720: sw    t1,20(sp)
  0x02512023,  #  1724: sw    t0,32(sp)
  0x00028a13,  #  1728: mv    s4,t0
  0x01e12423,  #  1732: sw    t5,8(sp)
  0x000a2403,  #  1736: lw    s0,0(s4)
  0x00012503,  #  1740: lw    a0,0(sp)
  0x00412583,  #  1744: lw    a1,4(sp)
  0x41f45493,  #  1748: srai  s1,s0,0x1f
  0x00040613,  #  1752: mv    a2,s0
  0x00048693,  #  1756: mv    a3,s1
  0x3a4000ef,  #  1760: jal   2692 <__divdi3>
  0x00040613,  #  1764: mv    a2,s0
  0x00048693,  #  1768: mv    a3,s1
  0x00050913,  #  1772: mv    s2,a0
  0x00058993,  #  1776: mv    s3,a1
  0x390000ef,  #  1780: jal   2692 <__divdi3>
  0xfff50793,  #  1784: addi  a5,a0,-1
  0x4017d793,  #  1788: srai  a5,a5,0x1
  0x00279793,  #  1792: slli  a5,a5,0x2
  0x00fb07b3,  #  1796: add   a5,s6,a5
  0x0007a403,  #  1800: lw    s0,0(a5)
  0x01412783,  #  1804: lw    a5,20(sp)
  0x40f40433,  #  1808: sub   s0,s0,a5
  0x0e8adc63,  #  1812: bge   s5,s0,2060
  0x001a8b93,  #  1816: addi  s7,s5,1
  0x13744e63,  #  1820: blt   s0,s7,2136
  0x004a0793,  #  1824: addi  a5,s4,4
  0x00f12823,  #  1828: sw    a5,16(sp)
  0x00078a13,  #  1832: mv    s4,a5
  0x02012783,  #  1836: lw    a5,32(sp)
  0x00241493,  #  1840: slli  s1,s0,0x2
  0x00000d13,  #  1844: li    s10,0
  0x00f484b3,  #  1848: add   s1,s1,a5
  0x00000c93,  #  1852: li    s9,0
  0x000a2603,  #  1856: lw    a2,0(s4)
  0x00090513,  #  1860: mv    a0,s2
  0x00098593,  #  1864: mv    a1,s3
  0x41f65693,  #  1868: srai  a3,a2,0x1f
  0x334000ef,  #  1872: jal   2692 <__divdi3>
  0xfff50793,  #  1876: addi  a5,a0,-1
  0x4017d793,  #  1880: srai  a5,a5,0x1
  0x00279793,  #  1884: slli  a5,a5,0x2
  0x00fb07b3,  #  1888: add   a5,s6,a5
  0x0007a783,  #  1892: lw    a5,0(a5)
  0x004a0a13,  #  1896: addi  s4,s4,4
  0x00fd06b3,  #  1900: add   a3,s10,a5
  0x41f7d793,  #  1904: srai  a5,a5,0x1f
  0x01a6b633,  #  1908: sltu  a2,a3,s10
  0x00fc87b3,  #  1912: add   a5,s9,a5
  0x00068d13,  #  1916: mv    s10,a3
  0x00f60cb3,  #  1920: add   s9,a2,a5
  0xfb449ee3,  #  1924: bne   s1,s4,1856
  0x00c12583,  #  1928: lw    a1,12(sp)
  0x41540433,  #  1932: sub   s0,s0,s5
  0x001c0693,  #  1936: addi  a3,s8,1
  0x0186b733,  #  1940: sltu  a4,a3,s8
  0x41f45793,  #  1944: srai  a5,s0,0x1f
  0x02858633,  #  1948: mul   a2,a1,s0
  0x00b70733,  #  1952: add   a4,a4,a1
  0x00e12623,  #  1956: sw    a4,12(sp)
  0x01012a03,  #  1960: lw    s4,16(sp)
  0x038787b3,  #  1964: mul   a5,a5,s8
  0x03840733,  #  1968: mul   a4,s0,s8
  0x00c787b3,  #  1972: add   a5,a5,a2
  0x03843433,  #  1976: mulhu s0,s0,s8
  0x40ed0733,  #  1980: sub   a4,s10,a4
  0x00068c13,  #  1984: mv    s8,a3
  0x00812683,  #  1988: lw    a3,8(sp)
  0x00ed3833,  #  1992: sltu  a6,s10,a4
  0x00ed8733,  #  1996: add   a4,s11,a4
  0x01b73633,  #  2000: sltu  a2,a4,s11
  0x00070d93,  #  2004: mv    s11,a4
  0x01812703,  #  2008: lw    a4,24(sp)
  0x008787b3,  #  2012: add   a5,a5,s0
  0x40fc87b3,  #  2016: sub   a5,s9,a5
  0x410787b3,  #  2020: sub   a5,a5,a6
  0x00f687b3,  #  2024: add   a5,a3,a5
  0x00f607b3,  #  2028: add   a5,a2,a5
  0x00f12423,  #  2032: sw    a5,8(sp)
  0x00f72223,  #  2036: sw    a5,4(a4)
  0x01c12783,  #  2040: lw    a5,28(sp)
  0x01b72023,  #  2044: sw    s11,0(a4)
  0x00fb8663,  #  2048: beq   s7,a5,2060
  0x000b8a93,  #  2052: mv    s5,s7
  0xec1ff06f,  #  2056: j     1736
  0x00812f03,  #  2060: lw    t5,8(sp)
  0x06812403,  #  2064: lw    s0,104(sp)
  0x06c12083,  #  2068: lw    ra,108(sp)
  0x001d8513,  #  2072: addi  a0,s11,1
  0x01b535b3,  #  2076: sltu  a1,a0,s11
  0x06412483,  #  2080: lw    s1,100(sp)
  0x06012903,  #  2084: lw    s2,96(sp)
  0x05c12983,  #  2088: lw    s3,92(sp)
  0x05812a03,  #  2092: lw    s4,88(sp)
  0x05412a83,  #  2096: lw    s5,84(sp)
  0x05012b03,  #  2100: lw    s6,80(sp)
  0x04c12b83,  #  2104: lw    s7,76(sp)
  0x04812c03,  #  2108: lw    s8,72(sp)
  0x04412c83,  #  2112: lw    s9,68(sp)
  0x04012d03,  #  2116: lw    s10,64(sp)
  0x03c12d83,  #  2120: lw    s11,60(sp)
  0x01e585b3,  #  2124: add   a1,a1,t5
  0x07010113,  #  2128: addi  sp,sp,112
  0x00008067,  #  2132: ret
  0x004a0793,  #  2136: addi  a5,s4,4
  0x00000d13,  #  2140: li    s10,0
  0x00000c93,  #  2144: li    s9,0
  0x00f12823,  #  2148: sw    a5,16(sp)
  0xf21ff06f,  #  2152: j     1928
  0x00059663,  #  2156: bnez  a1,2168
  0x00100793,  #  2160: li    a5,1
  0x88a7e0e3,  #  2164: bltu  a5,a0,244
  0x06c12083,  #  2168: lw    ra,108(sp)
  0x00000513,  #  2172: li    a0,0
  0x00000593,  #  2176: li    a1,0
  0x07010113,  #  2180: addi  sp,sp,112
  0x00008067,  #  2184: ret
  0x00000413,  #  2188: li    s0,0
  0xcddff06f,  #  2192: j     1388
  0x9c0594e3,  #  2196: bnez  a1,604
  0x000c8b93,  #  2200: mv    s7,s9
  0x014c8733,  #  2204: add   a4,s9,s4
  0x46e4a423,  #  2208: sw    a4,1128(s1)
  0x000c8f93,  #  2212: mv    t6,s9
  0xa60a1ae3,  #  2216: bnez  s4,796
  0x000ba783,  #  2220: lw    a5,0(s7)
  0x004ba703,  #  2224: lw    a4,4(s7)
  0x00178f93,  #  2228: addi  t6,a5,1
  0x00ffb7b3,  #  2232: sltu  a5,t6,a5
  0x00e78f33,  #  2236: add   t5,a5,a4
  0x000f8d93,  #  2240: mv    s11,t6
  0x01fba023,  #  2244: sw    t6,0(s7)
  0x01eba223,  #  2248: sw    t5,4(s7)
  0xf45ff06f,  #  2252: j     2064
  0x00412783,  #  2256: lw    a5,4(sp)
  0x820796e3,  #  2260: bnez  a5,256
  0x06c12083,  #  2264: lw    ra,108(sp)
  0x00100513,  #  2268: li    a0,1
  0x00000593,  #  2272: li    a1,0
  0x07010113,  #  2276: addi  sp,sp,112
  0x00008067,  #  2280: ret
  0x00012703,  #  2284: lw    a4,0(sp)
  0xacd778e3,  #  2288: bgeu  a4,a3,960
  0xd01ff06f,  #  2292: j     1524
  0x00300713,  #  2296: li    a4,3
  0x8f474ae3,  #  2300: blt   a4,s4,496
  0x000d0613,  #  2304: mv    a2,s10
  0x919ff06f,  #  2308: j     540
  0x00971663,  #  2312: bne   a4,s1,2324
  0x00012783,  #  2316: lw    a5,0(sp)
  0x84f464e3,  #  2320: bltu  s0,a5,344
  0x00012283,  #  2324: lw    t0,0(sp)
  0x889ff06f,  #  2328: j     416
  0xffe00713,  #  2332: li    a4,-2
  0x00000313,  #  2336: li    t1,0
  0xce5ff06f,  #  2340: j     1544
  # main:
  0xfd010113,  #  2344: addi  sp,sp,-48
  0x02112623,  #  2348: sw    ra,44(sp)
  0x00c00893,  #  2352: li    a7,12
  0x00000073,  #  2356: ecall
  0x00900793,  #  2360: li    a5,9
  0xfd050513,  #  2364: addi  a0,a0,-48
  0x00a7fa63,  #  2368: bgeu  a5,a0,2388
  0x00c00893,  #  2372: li    a7,12
  0x00000073,  #  2376: ecall
  0xfd050513,  #  2380: addi  a0,a0,-48
  0xfea7eae3,  #  2384: bltu  a5,a0,2372
  0x00000793,  #  2388: li    a5,0
  0x00000593,  #  2392: li    a1,0
  0x00900813,  #  2396: li    a6,9
  0x01e7d613,  #  2400: srli  a2,a5,0x1e
  0x00279713,  #  2404: slli  a4,a5,0x2
  0x00259693,  #  2408: slli  a3,a1,0x2
  0x00f707b3,  #  2412: add   a5,a4,a5
  0x00d666b3,  #  2416: or    a3,a2,a3
  0x00b686b3,  #  2420: add   a3,a3,a1
  0x00e7b733,  #  2424: sltu  a4,a5,a4
  0x00d70733,  #  2428: add   a4,a4,a3
  0x00171713,  #  2432: slli  a4,a4,0x1
  0x01f7d693,  #  2436: srli  a3,a5,0x1f
  0x00179793,  #  2440: slli  a5,a5,0x1
  0x00f507b3,  #  2444: add   a5,a0,a5
  0x00e6e733,  #  2448: or    a4,a3,a4
  0x41f55593,  #  2452: srai  a1,a0,0x1f
  0x00e585b3,  #  2456: add   a1,a1,a4
  0x00a7b533,  #  2460: sltu  a0,a5,a0
  0x00b505b3,  #  2464: add   a1,a0,a1
  0x00c00893,  #  2468: li    a7,12
  0x00000073,  #  2472: ecall
  0xfd050513,  #  2476: addi  a0,a0,-48
  0xfaa878e3,  #  2480: bgeu  a6,a0,2400
  0x00078513,  #  2484: mv    a0,a5
  0xf28ff0ef,  #  2488: jal   224 <prime_pi(long long)>
  0xccccd637,  #  2492: lui   a2,0xccccd
  0xccccde37,  #  2496: lui   t3,0xccccd
  0x00000813,  #  2500: li    a6,0
  0x00c10313,  #  2504: addi  t1,sp,12
  0x00500e93,  #  2508: li    t4,5
  0xccd60613,  #  2512: addi  a2,a2,-819
  0xccce0e13,  #  2516: addi  t3,t3,-820
  0x00900f13,  #  2520: li    t5,9
  0x00b507b3,  #  2524: add   a5,a0,a1
  0x00a7b733,  #  2528: sltu  a4,a5,a0
  0x00e787b3,  #  2532: add   a5,a5,a4
  0x03d7f7b3,  #  2536: remu  a5,a5,t4
  0x00058893,  #  2540: mv    a7,a1
  0x00180813,  #  2544: addi  a6,a6,1
  0x010306b3,  #  2548: add   a3,t1,a6
  0x00050293,  #  2552: mv    t0,a0
  0x40f507b3,  #  2556: sub   a5,a0,a5
  0x00f53733,  #  2560: sltu  a4,a0,a5
  0x40e585b3,  #  2564: sub   a1,a1,a4
  0x03c78fb3,  #  2568: mul   t6,a5,t3
  0x02c585b3,  #  2572: mul   a1,a1,a2
  0x02c7b733,  #  2576: mulhu a4,a5,a2
  0x01f585b3,  #  2580: add   a1,a1,t6
  0x02c787b3,  #  2584: mul   a5,a5,a2
  0x00e585b3,  #  2588: add   a1,a1,a4
  0x01f59713,  #  2592: slli  a4,a1,0x1f
  0x0015d593,  #  2596: srli  a1,a1,0x1
  0x0017d793,  #  2600: srli  a5,a5,0x1
  0x00f767b3,  #  2604: or    a5,a4,a5
  0x00279713,  #  2608: slli  a4,a5,0x2
  0x00f70733,  #  2612: add   a4,a4,a5
  0x00171713,  #  2616: slli  a4,a4,0x1
  0x40e50733,  #  2620: sub   a4,a0,a4
  0x03070713,  #  2624: addi  a4,a4,48
  0xfee68fa3,  #  2628: sb    a4,-1(a3)
  0x00078513,  #  2632: mv    a0,a5
  0xf80898e3,  #  2636: bnez  a7,2524
  0xf85f66e3,  #  2640: bltu  t5,t0,2524
  0x00068793,  #  2644: mv    a5,a3
  0xfff7c503,  #  2648: lbu   a0,-1(a5)
  0x00b00893,  #  2652: li    a7,11
  0x00000073,  #  2656: ecall
  0xfff78793,  #  2660: addi  a5,a5,-1
  0xfef318e3,  #  2664: bne   t1,a5,2648
  0x00a00513,  #  2668: li    a0,10
  0x00000073,  #  2672: ecall
  0x02c12083,  #  2676: lw    ra,44(sp)
  0x00000513,  #  2680: li    a0,0
  0x03010113,  #  2684: addi  sp,sp,48
  0x00008067,  #  2688: ret
  # __divdi3:
  0x00050313,  #  2692: mv    t1,a0
  0x00058e13,  #  2696: mv    t3,a1
  0x00000893,  #  2700: li    a7,0
  0x0005dc63,  #  2704: bgez  a1,2728
  0x00a037b3,  #  2708: snez  a5,a0
  0x40b00e33,  #  2712: neg   t3,a1
  0x40fe0e33,  #  2716: sub   t3,t3,a5
  0x40a00333,  #  2720: neg   t1,a0
  0xfff00893,  #  2724: li    a7,-1
  0x0006dc63,  #  2728: bgez  a3,2752
  0x00c037b3,  #  2732: snez  a5,a2
  0x40d006b3,  #  2736: neg   a3,a3
  0xfff8c893,  #  2740: not   a7,a7
  0x40f686b3,  #  2744: sub   a3,a3,a5
  0x40c00633,  #  2748: neg   a2,a2
  0x00060713,  #  2752: mv    a4,a2
  0x00030813,  #  2756: mv    a6,t1
  0x000e0793,  #  2760: mv    a5,t3
  0x28069c63,  #  2764: bnez  a3,3428
  0x00001597,  #  2768: auipc a1,0x1
  0x85c58593,  #  2772: addi  a1,a1,-1956
  0x0ece7663,  #  2776: bgeu  t3,a2,3012
  0x000106b7,  #  2780: lui   a3,0x10
  0x0cd67863,  #  2784: bgeu  a2,a3,2992
  0x10063693,  #  2788: sltiu a3,a2,256
  0x0016b693,  #  2792: seqz  a3,a3
  0x00369693,  #  2796: slli  a3,a3,0x3
  0x00d65533,  #  2800: srl   a0,a2,a3
  0x00a585b3,  #  2804: add   a1,a1,a0
  0x0005c583,  #  2808: lbu   a1,0(a1)
  0x02000513,  #  2812: li    a0,32
  0x00d586b3,  #  2816: add   a3,a1,a3
  0x40d505b3,  #  2820: sub   a1,a0,a3
  0x00d50c63,  #  2824: beq   a0,a3,2848
  0x00be17b3,  #  2828: sll   a5,t3,a1
  0x00d356b3,  #  2832: srl   a3,t1,a3
  0x00b61733,  #  2836: sll   a4,a2,a1
  0x00f6e7b3,  #  2840: or    a5,a3,a5
  0x00b31833,  #  2844: sll   a6,t1,a1
  0x01075593,  #  2848: srli  a1,a4,0x10
  0x02b7de33,  #  2852: divu  t3,a5,a1
  0x01071613,  #  2856: slli  a2,a4,0x10
  0x01065613,  #  2860: srli  a2,a2,0x10
  0x02b7f7b3,  #  2864: remu  a5,a5,a1
  0x000e0513,  #  2868: mv    a0,t3
  0x03c60333,  #  2872: mul   t1,a2,t3
  0x01079693,  #  2876: slli  a3,a5,0x10
  0x01085793,  #  2880: srli  a5,a6,0x10
  0x00d7e7b3,  #  2884: or    a5,a5,a3
  0x0067fe63,  #  2888: bgeu  a5,t1,2916
  0x00f707b3,  #  2892: add   a5,a4,a5
  0xfffe0513,  #  2896: addi  a0,t3,-1
  0x00e7e863,  #  2900: bltu  a5,a4,2916
  0x0067f663,  #  2904: bgeu  a5,t1,2916
  0xffee0513,  #  2908: addi  a0,t3,-2
  0x00e787b3,  #  2912: add   a5,a5,a4
  0x406787b3,  #  2916: sub   a5,a5,t1
  0x02b7d333,  #  2920: divu  t1,a5,a1
  0x01081813,  #  2924: slli  a6,a6,0x10
  0x01085813,  #  2928: srli  a6,a6,0x10
  0x02b7f7b3,  #  2932: remu  a5,a5,a1
  0x026606b3,  #  2936: mul   a3,a2,t1
  0x01079793,  #  2940: slli  a5,a5,0x10
  0x00f86833,  #  2944: or    a6,a6,a5
  0x00030793,  #  2948: mv    a5,t1
  0x00d87c63,  #  2952: bgeu  a6,a3,2976
  0x01070833,  #  2956: add   a6,a4,a6
  0xfff30793,  #  2960: addi  a5,t1,-1
  0x00e86663,  #  2964: bltu  a6,a4,2976
  0x00d87463,  #  2968: bgeu  a6,a3,2976
  0xffe30793,  #  2972: addi  a5,t1,-2
  0x01051513,  #  2976: slli  a0,a0,0x10
  0x00f56533,  #  2980: or    a0,a0,a5
  0x00000593,  #  2984: li    a1,0
  0x0e00006f,  #  2988: j     3212
  0x01000537,  #  2992: lui   a0,0x1000
  0x01800693,  #  2996: li    a3,24
  0xf2a67ce3,  #  3000: bgeu  a2,a0,2800
  0x01000693,  #  3004: li    a3,16
  0xf31ff06f,  #  3008: j     2800
  0x00000693,  #  3012: li    a3,0
  0x00060c63,  #  3016: beqz  a2,3040
  0x000107b7,  #  3020: lui   a5,0x10
  0x0cf67a63,  #  3024: bgeu  a2,a5,3236
  0x10063693,  #  3028: sltiu a3,a2,256
  0x0016b693,  #  3032: seqz  a3,a3
  0x00369693,  #  3036: slli  a3,a3,0x3
  0x00d657b3,  #  3040: srl   a5,a2,a3
  0x00f585b3,  #  3044: add   a1,a1,a5
  0x0005c783,  #  3048: lbu   a5,0(a1)
  0x00d787b3,  #  3052: add   a5,a5,a3
  0x02000693,  #  3056: li    a3,32
  0x40f685b3,  #  3060: sub   a1,a3,a5
  0x0cf69063,  #  3064: bne   a3,a5,3256
  0x40ce07b3,  #  3068: sub   a5,t3,a2
  0x00100593,  #  3072: li    a1,1
  0x01075313,  #  3076: srli  t1,a4,0x10
  0x0267deb3,  #  3080: divu  t4,a5,t1
  0x01071613,  #  3084: slli  a2,a4,0x10
  0x01065613,  #  3088: srli  a2,a2,0x10
  0x01085693,  #  3092: srli  a3,a6,0x10
  0x0267f7b3,  #  3096: remu  a5,a5,t1
  0x000e8513,  #  3100: mv    a0,t4
  0x03d60e33,  #  3104: mul   t3,a2,t4
  0x01079793,  #  3108: slli  a5,a5,0x10
  0x00f6e7b3,  #  3112: or    a5,a3,a5
  0x01c7fe63,  #  3116: bgeu  a5,t3,3144
  0x00f707b3,  #  3120: add   a5,a4,a5
  0xfffe8513,  #  3124: addi  a0,t4,-1
  0x00e7e863,  #  3128: bltu  a5,a4,3144
  0x01c7f663,  #  3132: bgeu  a5,t3,3144
  0xffee8513,  #  3136: addi  a0,t4,-2
  0x00e787b3,  #  3140: add   a5,a5,a4
  0x41c787b3,  #  3144: sub   a5,a5,t3
  0x0267de33,  #  3148: divu  t3,a5,t1
  0x01081813,  #  3152: slli  a6,a6,0x10
  0x01085813,  #  3156: srli  a6,a6,0x10
  0x0267f7b3,  #  3160: remu  a5,a5,t1
  0x03c606b3,  #  3164: mul   a3,a2,t3
  0x01079793,  #  3168: slli  a5,a5,0x10
  0x00f86833,  #  3172: or    a6,a6,a5
  0x000e0793,  #  3176: mv    a5,t3
  0x00d87c63,  #  3180: bgeu  a6,a3,3204
  0x01070833,  #  3184: add   a6,a4,a6
  0xfffe0793,  #  3188: addi  a5,t3,-1
  0x00e86663,  #  3192: bltu  a6,a4,3204
  0x00d87463,  #  3196: bgeu  a6,a3,3204
  0xffee0793,  #  3200: addi  a5,t3,-2
  0x01051513,  #  3204: slli  a0,a0,0x10
  0x00f56533,  #  3208: or    a0,a0,a5
  0x00088a63,  #  3212: beqz  a7,3232
  0x00a037b3,  #  3216: snez  a5,a0
  0x40b005b3,  #  3220: neg   a1,a1
  0x40f585b3,  #  3224: sub   a1,a1,a5
  0x40a00533,  #  3228: neg   a0,a0
  0x00008067,  #  3232: ret
  0x010007b7,  #  3236: lui   a5,0x1000
  0x01800693,  #  3240: li    a3,24
  0xf2f67ae3,  #  3244: bgeu  a2,a5,3040
  0x01000693,  #  3248: li    a3,16
  0xf2dff06f,  #  3252: j     3040
  0x00b61733,  #  3256: sll   a4,a2,a1
  0x00fe56b3,  #  3260: srl   a3,t3,a5
  0x01075513,  #  3264: srli  a0,a4,0x10
  0x00be1e33,  #  3268: sll   t3,t3,a1
  0x00f357b3,  #  3272: srl   a5,t1,a5
  0x01c7e7b3,  #  3276: or    a5,a5,t3
  0x02a6de33,  #  3280: divu  t3,a3,a0
  0x01071613,  #  3284: slli  a2,a4,0x10
  0x01065613,  #  3288: srli  a2,a2,0x10
  0x00b31833,  #  3292: sll   a6,t1,a1
  0x02a6f6b3,  #  3296: remu  a3,a3,a0
  0x03c60333,  #  3300: mul   t1,a2,t3
  0x01069593,  #  3304: slli  a1,a3,0x10
  0x0107d693,  #  3308: srli  a3,a5,0x10
  0x00b6e6b3,  #  3312: or    a3,a3,a1
  0x000e0593,  #  3316: mv    a1,t3
  0x0066fe63,  #  3320: bgeu  a3,t1,3348
  0x00d706b3,  #  3324: add   a3,a4,a3
  0xfffe0593,  #  3328: addi  a1,t3,-1
  0x00e6e863,  #  3332: bltu  a3,a4,3348
  0x0066f663,  #  3336: bgeu  a3,t1,3348
  0xffee0593,  #  3340: addi  a1,t3,-2
  0x00e686b3,  #  3344: add   a3,a3,a4
  0x406686b3,  #  3348: sub   a3,a3,t1
  0x02a6d333,  #  3352: divu  t1,a3,a0
  0x01079793,  #  3356: slli  a5,a5,0x10
  0x0107d793,  #  3360: srli  a5,a5,0x10
  0x02a6f6b3,  #  3364: remu  a3,a3,a0
  0x02660633,  #  3368: mul   a2,a2,t1
  0x01069693,  #  3372: slli  a3,a3,0x10
  0x00d7e7b3,  #  3376: or    a5,a5,a3
  0x00030693,  #  3380: mv    a3,t1
  0x00c7fe63,  #  3384: bgeu  a5,a2,3412
  0x00f707b3,  #  3388: add   a5,a4,a5
  0xfff30693,  #  3392: addi  a3,t1,-1
  0x00e7e863,  #  3396: bltu  a5,a4,3412
  0x00c7f663,  #  3400: bgeu  a5,a2,3412
  0xffe30693,  #  3404: addi  a3,t1,-2
  0x00e787b3,  #  3408: add   a5,a5,a4
  0x01059593,  #  3412: slli  a1,a1,0x10
  0x40c787b3,  #  3416: sub   a5,a5,a2
  0x00d5e5b3,  #  3420: or    a1,a1,a3
  0xea5ff06f,  #  3424: j     3076
  0x18de6663,  #  3428: bltu  t3,a3,3824
  0x000107b7,  #  3432: lui   a5,0x10
  0x04f6f463,  #  3436: bgeu  a3,a5,3508
  0x1006b713,  #  3440: sltiu a4,a3,256
  0x00173713,  #  3444: seqz  a4,a4
  0x00371713,  #  3448: slli  a4,a4,0x3
  0x00e6d5b3,  #  3452: srl   a1,a3,a4
  0x00000797,  #  3456: auipc a5,0x0
  0x5ac78793,  #  3460: addi  a5,a5,1452
  0x00b787b3,  #  3464: add   a5,a5,a1
  0x0007c783,  #  3468: lbu   a5,0(a5)
  0x00e787b3,  #  3472: add   a5,a5,a4
  0x02000713,  #  3476: li    a4,32
  0x40f705b3,  #  3480: sub   a1,a4,a5
  0x02f71663,  #  3484: bne   a4,a5,3528
  0x00100513,  #  3488: li    a0,1
  0xefc6e4e3,  #  3492: bltu  a3,t3,3212
  0x00c33533,  #  3496: sltu  a0,t1,a2
  0x00153513,  #  3500: seqz  a0,a0
  0xeddff06f,  #  3504: j     3212
  0x010007b7,  #  3508: lui   a5,0x1000
  0x01800713,  #  3512: li    a4,24
  0xfcf6f0e3,  #  3516: bgeu  a3,a5,3452
  0x01000713,  #  3520: li    a4,16
  0xfb9ff06f,  #  3524: j     3452
  0x00f65733,  #  3528: srl   a4,a2,a5
  0x00b696b3,  #  3532: sll   a3,a3,a1
  0x00d766b3,  #  3536: or    a3,a4,a3
  0x00fe5733,  #  3540: srl   a4,t3,a5
  0x00be1e33,  #  3544: sll   t3,t3,a1
  0x00f357b3,  #  3548: srl   a5,t1,a5
  0x01c7e7b3,  #  3552: or    a5,a5,t3
  0x0106de13,  #  3556: srli  t3,a3,0x10
  0x03c75f33,  #  3560: divu  t5,a4,t3
  0x01069813,  #  3564: slli  a6,a3,0x10
  0x01085813,  #  3568: srli  a6,a6,0x10
  0x00b61633,  #  3572: sll   a2,a2,a1
  0x03c77733,  #  3576: remu  a4,a4,t3
  0x03e80eb3,  #  3580: mul   t4,a6,t5
  0x01071513,  #  3584: slli  a0,a4,0x10
  0x0107d713,  #  3588: srli  a4,a5,0x10
  0x00a76733,  #  3592: or    a4,a4,a0
  0x000f0513,  #  3596: mv    a0,t5
  0x01d77e63,  #  3600: bgeu  a4,t4,3628
  0x00e68733,  #  3604: add   a4,a3,a4
  0xffff0513,  #  3608: addi  a0,t5,-1
  0x00d76863,  #  3612: bltu  a4,a3,3628
  0x01d77663,  #  3616: bgeu  a4,t4,3628
  0xffef0513,  #  3620: addi  a0,t5,-2
  0x00d70733,  #  3624: add   a4,a4,a3
  0x41d70733,  #  3628: sub   a4,a4,t4
  0x03c75eb3,  #  3632: divu  t4,a4,t3
  0x01079793,  #  3636: slli  a5,a5,0x10
  0x0107d793,  #  3640: srli  a5,a5,0x10
  0x03c77733,  #  3644: remu  a4,a4,t3
  0x03d80833,  #  3648: mul   a6,a6,t4
  0x01071713,  #  3652: slli  a4,a4,0x10
  0x00e7e7b3,  #  3656: or    a5,a5,a4
  0x000e8713,  #  3660: mv    a4,t4
  0x0107fe63,  #  3664: bgeu  a5,a6,3692
  0x00f687b3,  #  3668: add   a5,a3,a5
  0xfffe8713,  #  3672: addi  a4,t4,-1
  0x00d7e863,  #  3676: bltu  a5,a3,3692
  0x0107f663,  #  3680: bgeu  a5,a6,3692
  0xffee8713,  #  3684: addi  a4,t4,-2
  0x00d787b3,  #  3688: add   a5,a5,a3
  0x01051513,  #  3692: slli  a0,a0,0x10
  0x00010eb7,  #  3696: lui   t4,0x10
  0x00e56533,  #  3700: or    a0,a0,a4
  0xfffe8693,  #  3704: addi  a3,t4,-1
  0x00d57733,  #  3708: and   a4,a0,a3
  0x410787b3,  #  3712: sub   a5,a5,a6
  0x00d676b3,  #  3716: and   a3,a2,a3
  0x01055813,  #  3720: srli  a6,a0,0x10
  0x01065613,  #  3724: srli  a2,a2,0x10
  0x02d70e33,  #  3728: mul   t3,a4,a3
  0x02d806b3,  #  3732: mul   a3,a6,a3
  0x02c70733,  #  3736: mul   a4,a4,a2
  0x02c80833,  #  3740: mul   a6,a6,a2
  0x00d70633,  #  3744: add   a2,a4,a3
  0x010e5713,  #  3748: srli  a4,t3,0x10
  0x00c70733,  #  3752: add   a4,a4,a2
  0x00d77463,  #  3756: bgeu  a4,a3,3764
  0x01d80833,  #  3760: add   a6,a6,t4
  0x01075693,  #  3764: srli  a3,a4,0x10
  0x010686b3,  #  3768: add   a3,a3,a6
  0x02d7e663,  #  3772: bltu  a5,a3,3816
  0xced794e3,  #  3776: bne   a5,a3,2984
  0x000107b7,  #  3780: lui   a5,0x10
  0xfff78793,  #  3784: addi  a5,a5,-1
  0x00f77733,  #  3788: and   a4,a4,a5
  0x01071713,  #  3792: slli  a4,a4,0x10
  0x00fe7e33,  #  3796: and   t3,t3,a5
  0x00b31333,  #  3800: sll   t1,t1,a1
  0x01c70733,  #  3804: add   a4,a4,t3
  0x00000593,  #  3808: li    a1,0
  0xdae374e3,  #  3812: bgeu  t1,a4,3212
  0xfff50513,  #  3816: addi  a0,a0,-1
  0xcbdff06f,  #  3820: j     2984
  0x00000593,  #  3824: li    a1,0
  0x00000513,  #  3828: li    a0,0
  0xd95ff06f,  #  3832: j     3212
  # __udivdi3:
  0x00050893,  #  3836: mv    a7,a0
  0x00058313,  #  3840: mv    t1,a1
  0x00060713,  #  3844: mv    a4,a2
  0x00050813,  #  3848: mv    a6,a0
  0x00058793,  #  3852: mv    a5,a1
  0x28069263,  #  3856: bnez  a3,4500
  0x00000597,  #  3860: auipc a1,0x0
  0x41858593,  #  3864: addi  a1,a1,1048
  0x0ec37663,  #  3868: bgeu  t1,a2,4104
  0x000106b7,  #  3872: lui   a3,0x10
  0x0cd67863,  #  3876: bgeu  a2,a3,4084
  0x10063693,  #  3880: sltiu a3,a2,256
  0x0016b693,  #  3884: seqz  a3,a3
  0x00369693,  #  3888: slli  a3,a3,0x3
  0x00d65533,  #  3892: srl   a0,a2,a3
  0x00a585b3,  #  3896: add   a1,a1,a0
  0x0005c583,  #  3900: lbu   a1,0(a1)
  0x02000513,  #  3904: li    a0,32
  0x00d586b3,  #  3908: add   a3,a1,a3
  0x40d505b3,  #  3912: sub   a1,a0,a3
  0x00d50c63,  #  3916: beq   a0,a3,3940
  0x00b317b3,  #  3920: sll   a5,t1,a1
  0x00d8d6b3,  #  3924: srl   a3,a7,a3
  0x00b61733,  #  3928: sll   a4,a2,a1
  0x00f6e7b3,  #  3932: or    a5,a3,a5
  0x00b89833,  #  3936: sll   a6,a7,a1
  0x01075593,  #  3940: srli  a1,a4,0x10
  0x02b7d333,  #  3944: divu  t1,a5,a1
  0x01071613,  #  3948: slli  a2,a4,0x10
  0x01065613,  #  3952: srli  a2,a2,0x10
  0x02b7f7b3,  #  3956: remu  a5,a5,a1
  0x00030513,  #  3960: mv    a0,t1
  0x026608b3,  #  3964: mul   a7,a2,t1
  0x01079693,  #  3968: slli  a3,a5,0x10
  0x01085793,  #  3972: srli  a5,a6,0x10
  0x00d7e7b3,  #  3976: or    a5,a5,a3
  0x0117fe63,  #  3980: bgeu  a5,a7,4008
  0x00f707b3,  #  3984: add   a5,a4,a5
  0xfff30513,  #  3988: addi  a0,t1,-1
  0x00e7e863,  #  3992: bltu  a5,a4,4008
  0x0117f663,  #  3996: bgeu  a5,a7,4008
  0xffe30513,  #  4000: addi  a0,t1,-2
  0x00e787b3,  #  4004: add   a5,a5,a4
  0x411787b3,  #  4008: sub   a5,a5,a7
  0x02b7d8b3,  #  4012: divu  a7,a5,a1
  0x01081813,  #  4016: slli  a6,a6,0x10
  0x01085813,  #  4020: srli  a6,a6,0x10
  0x02b7f7b3,  #  4024: remu  a5,a5,a1
  0x031606b3,  #  4028: mul   a3,a2,a7
  0x01079793,  #  4032: slli  a5,a5,0x10
  0x00f86833,  #  4036: or    a6,a6,a5
  0x00088793,  #  4040: mv    a5,a7
  0x00d87c63,  #  4044: bgeu  a6,a3,4068
  0x01070833,  #  4048: add   a6,a4,a6
  0xfff88793,  #  4052: addi  a5,a7,-1
  0x00e86663,  #  4056: bltu  a6,a4,4068
  0x00d87463,  #  4060: bgeu  a6,a3,4068
  0xffe88793,  #  4064: addi  a5,a7,-2
  0x01051513,  #  4068: slli  a0,a0,0x10
  0x00f56533,  #  4072: or    a0,a0,a5
  0x00000593,  #  4076: li    a1,0
  0x00008067,  #  4080: ret
  0x01000537,  #  4084: lui   a0,0x1000
  0x01800693,  #  4088: li    a3,24
  0xf2a67ce3,  #  4092: bgeu  a2,a0,3892
  0x01000693,  #  4096: li    a3,16
  0xf31ff06f,  #  4100: j     3892
  0x00000693,  #  4104: li    a3,0
  0x00060c63,  #  4108: beqz  a2,4132
  0x000107b7,  #  4112: lui   a5,0x10
  0x0cf67063,  #  4116: bgeu  a2,a5,4308
  0x10063693,  #  4120: sltiu a3,a2,256
  0x0016b693,  #  4124: seqz  a3,a3
  0x00369693,  #  4128: slli  a3,a3,0x3
  0x00d657b3,  #  4132: srl   a5,a2,a3
  0x00f585b3,  #  4136: add   a1,a1,a5
  0x0005c783,  #  4140: lbu   a5,0(a1)
  0x00d787b3,  #  4144: add   a5,a5,a3
  0x02000693,  #  4148: li    a3,32
  0x40f685b3,  #  4152: sub   a1,a3,a5
  0x0af69663,  #  4156: bne   a3,a5,4328
  0x40c307b3,  #  4160: sub   a5,t1,a2
  0x00100593,  #  4164: li    a1,1
  0x01075893,  #  4168: srli  a7,a4,0x10
  0x0317de33,  #  4172: divu  t3,a5,a7
  0x01071613,  #  4176: slli  a2,a4,0x10
  0x01065613,  #  4180: srli  a2,a2,0x10
  0x01085693,  #  4184: srli  a3,a6,0x10
  0x0317f7b3,  #  4188: remu  a5,a5,a7
  0x000e0513,  #  4192: mv    a0,t3
  0x03c60333,  #  4196: mul   t1,a2,t3
  0x01079793,  #  4200: slli  a5,a5,0x10
  0x00f6e7b3,  #  4204: or    a5,a3,a5
  0x0067fe63,  #  4208: bgeu  a5,t1,4236
  0x00f707b3,  #  4212: add   a5,a4,a5
  0xfffe0513,  #  4216: addi  a0,t3,-1
  0x00e7e863,  #  4220: bltu  a5,a4,4236
  0x0067f663,  #  4224: bgeu  a5,t1,4236
  0xffee0513,  #  4228: addi  a0,t3,-2
  0x00e787b3,  #  4232: add   a5,a5,a4
  0x406787b3,  #  4236: sub   a5,a5,t1
  0x0317d333,  #  4240: divu  t1,a5,a7
  0x01081813,  #  4244: slli  a6,a6,0x10
  0x01085813,  #  4248: srli  a6,a6,0x10
  0x0317f7b3,  #  4252: remu  a5,a5,a7
  0x026606b3,  #  4256: mul   a3,a2,t1
  0x01079793,  #  4260: slli  a5,a5,0x10
  0x00f86833,  #  4264: or    a6,a6,a5
  0x00030793,  #  4268: mv    a5,t1
  0x00d87c63,  #  4272: bgeu  a6,a3,4296
  0x01070833,  #  4276: add   a6,a4,a6
  0xfff30793,  #  4280: addi  a5,t1,-1
  0x00e86663,  #  4284: bltu  a6,a4,4296
  0x00d87463,  #  4288: bgeu  a6,a3,4296
  0xffe30793,  #  4292: addi  a5,t1,-2
  0x01051513,  #  4296: slli  a0,a0,0x10
  0x00f56533,  #  4300: or    a0,a0,a5
  0x00008067,  #  4304: ret
  0x010007b7,  #  4308: lui   a5,0x1000
  0x01800693,  #  4312: li    a3,24
  0xf4f674e3,  #  4316: bgeu  a2,a5,4132
  0x01000693,  #  4320: li    a3,16
  0xf41ff06f,  #  4324: j     4132
  0x00b61733,  #  4328: sll   a4,a2,a1
  0x00f356b3,  #  4332: srl   a3,t1,a5
  0x01075513,  #  4336: srli  a0,a4,0x10
  0x00b31333,  #  4340: sll   t1,t1,a1
  0x00f8d7b3,  #  4344: srl   a5,a7,a5
  0x0067e7b3,  #  4348: or    a5,a5,t1
  0x02a6d333,  #  4352: divu  t1,a3,a0
  0x01071613,  #  4356: slli  a2,a4,0x10
  0x01065613,  #  4360: srli  a2,a2,0x10
  0x00b89833,  #  4364: sll   a6,a7,a1
  0x02a6f6b3,  #  4368: remu  a3,a3,a0
  0x026608b3,  #  4372: mul   a7,a2,t1
  0x01069593,  #  4376: slli  a1,a3,0x10
  0x0107d693,  #  4380: srli  a3,a5,0x10
  0x00b6e6b3,  #  4384: or    a3,a3,a1
  0x00030593,  #  4388: mv    a1,t1
  0x0116fe63,  #  4392: bgeu  a3,a7,4420
  0x00d706b3,  #  4396: add   a3,a4,a3
  0xfff30593,  #  4400: addi  a1,t1,-1
  0x00e6e863,  #  4404: bltu  a3,a4,4420
  0x0116f663,  #  4408: bgeu  a3,a7,4420
  0xffe30593,  #  4412: addi  a1,t1,-2
  0x00e686b3,  #  4416: add   a3,a3,a4
  0x411686b3,  #  4420: sub   a3,a3,a7
  0x02a6d8b3,  #  4424: divu  a7,a3,a0
  0x01079793,  #  4428: slli  a5,a5,0x10
  0x0107d793,  #  4432: srli  a5,a5,0x10
  0x02a6f6b3,  #  4436: remu  a3,a3,a0
  0x03160633,  #  4440: mul   a2,a2,a7
  0x01069693,  #  4444: slli  a3,a3,0x10
  0x00d7e7b3,  #  4448: or    a5,a5,a3
  0x00088693,  #  4452: mv    a3,a7
  0x00c7fe63,  #  4456: bgeu  a5,a2,4484
  0x00f707b3,  #  4460: add   a5,a4,a5
  0xfff88693,  #  4464: addi  a3,a7,-1
  0x00e7e863,  #  4468: bltu  a5,a4,4484
  0x00c7f663,  #  4472: bgeu  a5,a2,4484
  0xffe88693,  #  4476: addi  a3,a7,-2
  0x00e787b3,  #  4480: add   a5,a5,a4
  0x01059593,  #  4484: slli  a1,a1,0x10
  0x40c787b3,  #  4488: sub   a5,a5,a2
  0x00d5e5b3,  #  4492: or    a1,a1,a3
  0xeb9ff06f,  #  4496: j     4168
  0x18d5e663,  #  4500: bltu  a1,a3,4896
  0x000107b7,  #  4504: lui   a5,0x10
  0x04f6f463,  #  4508: bgeu  a3,a5,4580
  0x1006b713,  #  4512: sltiu a4,a3,256
  0x00173713,  #  4516: seqz  a4,a4
  0x00371713,  #  4520: slli  a4,a4,0x3
  0x00e6d5b3,  #  4524: srl   a1,a3,a4
  0x00000797,  #  4528: auipc a5,0x0
  0x17c78793,  #  4532: addi  a5,a5,380
  0x00b787b3,  #  4536: add   a5,a5,a1
  0x0007c783,  #  4540: lbu   a5,0(a5)
  0x00e787b3,  #  4544: add   a5,a5,a4
  0x02000713,  #  4548: li    a4,32
  0x40f705b3,  #  4552: sub   a1,a4,a5
  0x02f71663,  #  4556: bne   a4,a5,4600
  0x00100513,  #  4560: li    a0,1
  0xe066eee3,  #  4564: bltu  a3,t1,4080
  0x00c8b533,  #  4568: sltu  a0,a7,a2
  0x00153513,  #  4572: seqz  a0,a0
  0x00008067,  #  4576: ret
  0x010007b7,  #  4580: lui   a5,0x1000
  0x01800713,  #  4584: li    a4,24
  0xfcf6f0e3,  #  4588: bgeu  a3,a5,4524
  0x01000713,  #  4592: li    a4,16
  0xfb9ff06f,  #  4596: j     4524
  0x00f65733,  #  4600: srl   a4,a2,a5
  0x00b696b3,  #  4604: sll   a3,a3,a1
  0x00d766b3,  #  4608: or    a3,a4,a3
  0x00f35733,  #  4612: srl   a4,t1,a5
  0x00b31333,  #  4616: sll   t1,t1,a1
  0x00f8d7b3,  #  4620: srl   a5,a7,a5
  0x0067e7b3,  #  4624: or    a5,a5,t1
  0x0106d313,  #  4628: srli  t1,a3,0x10
  0x02675eb3,  #  4632: divu  t4,a4,t1
  0x01069813,  #  4636: slli  a6,a3,0x10
  0x01085813,  #  4640: srli  a6,a6,0x10
  0x00b61633,  #  4644: sll   a2,a2,a1
  0x02677733,  #  4648: remu  a4,a4,t1
  0x03d80e33,  #  4652: mul   t3,a6,t4
  0x01071513,  #  4656: slli  a0,a4,0x10
  0x0107d713,  #  4660: srli  a4,a5,0x10
  0x00a76733,  #  4664: or    a4,a4,a0
  0x000e8513,  #  4668: mv    a0,t4
  0x01c77e63,  #  4672: bgeu  a4,t3,4700
  0x00e68733,  #  4676: add   a4,a3,a4
  0xfffe8513,  #  4680: addi  a0,t4,-1
  0x00d76863,  #  4684: bltu  a4,a3,4700
  0x01c77663,  #  4688: bgeu  a4,t3,4700
  0xffee8513,  #  4692: addi  a0,t4,-2
  0x00d70733,  #  4696: add   a4,a4,a3
  0x41c70733,  #  4700: sub   a4,a4,t3
  0x02675e33,  #  4704: divu  t3,a4,t1
  0x01079793,  #  4708: slli  a5,a5,0x10
  0x0107d793,  #  4712: srli  a5,a5,0x10
  0x02677733,  #  4716: remu  a4,a4,t1
  0x03c80833,  #  4720: mul   a6,a6,t3
  0x01071713,  #  4724: slli  a4,a4,0x10
  0x00e7e7b3,  #  4728: or    a5,a5,a4
  0x000e0713,  #  4732: mv    a4,t3
  0x0107fe63,  #  4736: bgeu  a5,a6,4764
  0x00f687b3,  #  4740: add   a5,a3,a5
  0xfffe0713,  #  4744: addi  a4,t3,-1
  0x00d7e863,  #  4748: bltu  a5,a3,4764
  0x0107f663,  #  4752: bgeu  a5,a6,4764
  0xffee0713,  #  4756: addi  a4,t3,-2
  0x00d787b3,  #  4760: add   a5,a5,a3
  0x01051513,  #  4764: slli  a0,a0,0x10
  0x00010e37,  #  4768: lui   t3,0x10
  0x00e56533,  #  4772: or    a0,a0,a4
  0xfffe0693,  #  4776: addi  a3,t3,-1
  0x00d57733,  #  4780: and   a4,a0,a3
  0x410787b3,  #  4784: sub   a5,a5,a6
  0x00d676b3,  #  4788: and   a3,a2,a3
  0x01055813,  #  4792: srli  a6,a0,0x10
  0x01065613,  #  4796: srli  a2,a2,0x10
  0x02d70333,  #  4800: mul   t1,a4,a3
  0x02d806b3,  #  4804: mul   a3,a6,a3
  0x02c70733,  #  4808: mul   a4,a4,a2
  0x02c80833,  #  4812: mul   a6,a6,a2
  0x00d70633,  #  4816: add   a2,a4,a3
  0x01035713,  #  4820: srli  a4,t1,0x10
  0x00c70733,  #  4824: add   a4,a4,a2
  0x00d77463,  #  4828: bgeu  a4,a3,4836
  0x01c80833,  #  4832: add   a6,a6,t3
  0x01075693,  #  4836: srli  a3,a4,0x10
  0x010686b3,  #  4840: add   a3,a3,a6
  0x02d7e663,  #  4844: bltu  a5,a3,4888
  0xced79ee3,  #  4848: bne   a5,a3,4076
  0x000107b7,  #  4852: lui   a5,0x10
  0xfff78793,  #  4856: addi  a5,a5,-1
  0x00f77733,  #  4860: and   a4,a4,a5
  0x01071713,  #  4864: slli  a4,a4,0x10
  0x00f37333,  #  4868: and   t1,t1,a5
  0x00b898b3,  #  4872: sll   a7,a7,a1
  0x00670733,  #  4876: add   a4,a4,t1
  0x00000593,  #  4880: li    a1,0
  0xcce8fee3,  #  4884: bgeu  a7,a4,4080
  0xfff50513,  #  4888: addi  a0,a0,-1
  0xcd1ff06f,  #  4892: j     4076
  0x00000593,  #  4896: li    a1,0
  0x00000513,  #  4900: li    a0,0
  0x00008067,  #  4904: ret
  # ---- data ----
  0x02020100,  #  4908: "\0..."
  0x03030303,  #  4912: "...."
  0x04040404,  #  4916: "...."
  0x04040404,  #  4920: "...."
  0x05050505,  #  4924: "...."
  0x05050505,  #  4928: "...."
  0x05050505,  #  4932: "...."
  0x05050505,  #  4936: "...."
  0x06060606,  #  4940: "...."
  0x06060606,  #  4944: "...."
  0x06060606,  #  4948: "...."
  0x06060606,  #  4952: "...."
  0x06060606,  #  4956: "...."
  0x06060606,  #  4960: "...."
  0x06060606,  #  4964: "...."
  0x06060606,  #  4968: "...."
  0x07070707,  #  4972: "...."
  0x07070707,  #  4976: "...."
  0x07070707,  #  4980: "...."
  0x07070707,  #  4984: "...."
  0x07070707,  #  4988: "...."
  0x07070707,  #  4992: "...."
  0x07070707,  #  4996: "...."
  0x07070707,  #  5000: "...."
  0x07070707,  #  5004: "...."
  0x07070707,  #  5008: "...."
  0x07070707,  #  5012: "...."
  0x07070707,  #  5016: "...."
  0x07070707,  #  5020: "...."
  0x07070707,  #  5024: "...."
  0x07070707,  #  5028: "...."
  0x07070707,  #  5032: "...."
  0x08080808,  #  5036: "...."
  0x08080808,  #  5040: "...."
  0x08080808,  #  5044: "...."
  0x08080808,  #  5048: "...."
  0x08080808,  #  5052: "...."
  0x08080808,  #  5056: "...."
  0x08080808,  #  5060: "...."
  0x08080808,  #  5064: "...."
  0x08080808,  #  5068: "...."
  0x08080808,  #  5072: "...."
  0x08080808,  #  5076: "...."
  0x08080808,  #  5080: "...."
  0x08080808,  #  5084: "...."
  0x08080808,  #  5088: "...."
  0x08080808,  #  5092: "...."
  0x08080808,  #  5096: "...."
  0x08080808,  #  5100: "...."
  0x08080808,  #  5104: "...."
  0x08080808,  #  5108: "...."
  0x08080808,  #  5112: "...."
  0x08080808,  #  5116: "...."
  0x08080808,  #  5120: "...."
  0x08080808,  #  5124: "...."
  0x08080808,  #  5128: "...."
  0x08080808,  #  5132: "...."
  0x08080808,  #  5136: "...."
  0x08080808,  #  5140: "...."
  0x08080808,  #  5144: "...."
  0x08080808,  #  5148: "...."
  0x08080808,  #  5152: "...."
  0x08080808,  #  5156: "...."
  0x08080808,  #  5160: "...."
  0x00000010,  #  5164: ".\0\0\0"
  0x00000000,  #  5168: "\0\0\0\0"
  0x00527a03,  #  5172: ".zR\0"
  0x01017c01,  #  5176: ".|.."
  0x00020d1b,  #  5180: "...\0"
  0x00000010,  #  5184: ".\0\0\0"
  0x00000018,  #  5188: ".\0\0\0"
  0xfffff63c,  #  5192: "<..."
  0x00000478,  #  5196: "x.\0\0"
  0x00000000,  #  5200: "\0\0\0\0"
  0x00000010,  #  5204: ".\0\0\0"
  0x0000002c,  #  5208: ",\0\0\0"
  0xfffffaa0,  #  5212: "...."
  0x00000430,  #  5216: "0.\0\0"
  0x00000000,  #  5220: "\0\0\0\0"
  # heap:
  0x00001470]  #  5224: "p.\0\0"

# zero-initialized data (.bss), not part of the image:
#    5232: _end

m = machine(mem_size=0x400000)
m.write_i32_vec(prog, 0)
m.run(start=0)
