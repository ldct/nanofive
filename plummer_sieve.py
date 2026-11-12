from machine import *

# Dave Plummer's "Primes" software drag race, PrimeC/solution_1 by Mike Koss:
# https://github.com/PlummersSoftwareLLC/Primes/tree/drag-race/PrimeC/solution_1
# Bit-packed sieve that only tracks numbers = 1,7,11,13,17,19,23,29 (mod 30).
# One pass over 1..1000000, validated against the 78498 from prime-check.h.
# Compiled to RV32IM machine code (no libc; output via ecalls, RARS
# convention, see machine.ECALL) with riscv64-unknown-elf-gcc 13.2:
#   gcc -march=rv32im -mabi=ilp32 -O2 -ffreestanding -nostdlib
#       -fno-tree-loop-distribute-patterns -DMEM_SIZE=0x20000
# and laid out flat from address 0: code, then read-only data. Zeroed data
# (.bss) follows the image; the stack grows down from the top of memory.
# Startup code:
#   _start: li sp, MEM_SIZE; call main; li a7, 93; ecall   (exit(main()))
# print_int(v) is "ecall" with a0=v, a7=1; print_str(s) with a0=s, a7=4.
#
# C source:
#
#   /* Dave Plummer's "Primes" drag race, PrimeC/solution_1/sieve.c by Mike Koss
#      (April 2021): bit-packed 8-of-30 wheel sieve, 64-bit words.
#      https://github.com/PlummersSoftwareLLC/Primes/tree/drag-race/PrimeC/solution_1
#      usqrt(), primes8of30() and countPrimes() are verbatim except that calloc()
#      is replaced by static storage. The timing loop, argument parsing and printf
#      are replaced by one pass checked against prime-check.h. */
#   #include "rt.h"
#   #include <stdint.h>
#
#   #define TRUE (1)
#   #define FALSE (0)
#   #define BOOL int
#
#   #define WORD uint64_t
#   #define BITS_PER_WORD (int)(sizeof(WORD) * 8)
#   #define BYTE unsigned char
#
#   #define indexOf(n) ((n) / 2 / BITS_PER_WORD)
#   #define maskOf(n) (WORD)1 << (n / 2) % BITS_PER_WORD
#   #define allocOf(n) indexOf(n) + 1
#
#   #define MAX_NUMBER 1000000
#   int maxNumber = MAX_NUMBER;
#   BOOL fDebug = FALSE;
#   #define printf(...) /* fDebug output dropped */
#
#   typedef struct {
#       int maxNumber;
#       WORD *buffer;
#   } SIEVE;
#
#   static WORD sieve_buffer[allocOf(MAX_NUMBER)];
#   static SIEVE sieve_obj;
#
#   unsigned int usqrt(int n)
#   {
#       unsigned int x;
#       unsigned int xLast;
#
#       xLast = 0;
#       x = n / 2;
#
#       while (x != xLast) {
#           xLast = x;
#           x = (x + n / x) / 2;
#       }
#       return x;
#   }
#
#   //
#   // Prime number sieve - full bitmapped but ignoring
#   // multiples of 2, 3, and 5.  Only testing numbers
#   // congruent to:
#   //
#   //   1, 7, 11, 13, 17, 19, 23, and 29 (mod 30)
#   //
#   // maxNumber - find all primes strictly LESS than this number.
#   //
#   SIEVE *primes8of30(int maxNumber) {
#       // Starts off zero-initialized.
#       WORD *buffer = sieve_buffer;  // was calloc(allocOf(maxNumber), sizeof(WORD))
#       for (int i = 0; i < allocOf(maxNumber); i++) buffer[i] = 0;
#       unsigned int maxFactor = usqrt(maxNumber) + 1;
#
#       // Allocate sieve "object"
#       SIEVE *psieve = &sieve_obj;   // was calloc(1, sizeof(SIEVE))
#       psieve->buffer = buffer;
#       psieve->maxNumber = maxNumber;
#
#       // Only numbers congruent to candidates mod 30 can be prime.
#       unsigned int candidates[8] = {1, 7, 11, 13, 17, 19, 23, 29};
#
#       // Cached bitmaps and index offsets for bit twiddling loop.
#       WORD masks[BITS_PER_WORD];
#       unsigned int offsets[BITS_PER_WORD];
#
#       // Build a stepping map.
#       unsigned int steps[8];
#       for (int i = 0; i < 8; i++) {
#           steps[i] = (candidates[(i + 1) % 8] - candidates[i] + 30) % 30;
#       }
#
#       // We get 2, 3 and 5 for "free" since we ignore their multiples.
#       int count = 3;
#       unsigned int p;
#
#       // First step is from 7 to 11 (steps[1]).
#       unsigned int step = 1;
#
#       // Look for next prime
#       for (p = 7; p <= maxFactor; p += steps[step], step = (step + 1) % 8) {
#           // A 1 bit means it's composite - keep searching.
#           if (buffer[indexOf(p)] & maskOf(p)) {
#               continue;
#           }
#
#           count++;
#           // if (p < 1000) printf("%d, ", p);
#
#           // The following loop is the hotspot for this algorithm.
#           // No need to start less than p^2 since all those
#           // multiples have already been marked.
#
#           // Performance optimization: since the bit mask we or
#           // into the word (and the index offset added to the base)
#           // RECUR every 64 iterations of this loop (for 64-bit words), we
#           // can precalculate them and use them over and over until the end
#           // of the sieve array.
#
#           unsigned int base = indexOf(p * p);
#           unsigned int cumOffset = 0;
#
#           for (int i = 0; i < BITS_PER_WORD; i++) {
#               masks[i] = 0;
#           }
#
#           int iUsed = 0;
#           int offset = 0;
#
#           for (int i = 0, m = p * p; i < BITS_PER_WORD; i++, m += 2 * p) {
#               masks[iUsed] |= maskOf(m);
#               offset = indexOf(m + 2 * p) - indexOf(m);
#               // Don't advance to a new word unless the next
#               // bit is in the same word!
#               if (offset != 0) {
#                   offsets[iUsed] = offset;
#                   iUsed++;
#                   cumOffset += offset;
#               }
#           }
#
#           // In this case, the bits in the last word can just
#           // be merged to the first.
#           if (offset == 0) {
#               masks[0] |= masks[iUsed];
#           }
#
#           // In all cases, iUsed will be 1 BEYOND the last mask used.
#
#           // Now just rip through the array or-ing in these masks in an
#           // identical pattern.
#           unsigned int iStop = indexOf(maxNumber);
#           unsigned int i = base;
#           for (; i <= iStop - cumOffset;) {
#               for (int j = 0; j < iUsed; j++) {
#                   buffer[i] |= masks[j];
#                   i = i + offsets[j];
#               }
#           }
#
#           // Finish last few words being careful about array bounds.
#           for (int j = 0; j < iUsed && i <= iStop; j++) {
#               buffer[i] |= masks[j];
#               i = i + offsets[j];
#           }
#       }
#
#       // The wrap-around buffer pattern is expected to overwrite the
#       // 7 and 11 primes as composite, erroneously.
#       buffer[indexOf(7)] &= ~maskOf(7);
#       buffer[indexOf(11)] &= ~maskOf(11);
#
#       return psieve;
#   }
#
#   int countPrimes(SIEVE *psieve) {
#       WORD *buffer = psieve->buffer;
#       int maxNumber = psieve->maxNumber;
#
#       // 2, 3, and 5 are known prime
#       int count = 3;
#       if (fDebug) {
#           printf("2, 3, 5, ");
#       }
#
#       // Only numbers congruent to candidates mod 30 can be prime.
#       unsigned int candidates[8] = {1, 7, 11, 13, 17, 19, 23, 29};
#
#       // Build a stepping map.
#       unsigned int steps[8];
#       for (int i = 0; i < 8; i++) {
#           steps[i] = (candidates[(i + 1) % 8] - candidates[i] + 30) % 30;
#       }
#
#       // First step is from 7 to 11 (steps[1]).
#       unsigned int step = 1;
#
#       for (unsigned int p = 7; p < maxNumber; p += steps[step], step = (step + 1) % 8) {
#           if ((buffer[indexOf(p)] & maskOf(p)) == 0) {
#               count++;
#               if (fDebug && p < 1000) {
#                   printf("%d, ", p);
#               }
#           }
#       }
#
#       if (fDebug) {
#           printf("...\n");
#       }
#
#       return count;
#   }
#
#   int main() {
#       int primeCount = countPrimes(primes8of30(maxNumber));
#       print_int(primeCount); print_str(" primes below "); print_int(maxNumber);
#       /* prime-check.h: {1e6, 78498} */
#       if (primeCount != 78498) { print_str(" -- expected 78498!\n"); return 1; }
#       print_str("\nmckoss-c830;1;algorithm=wheel,faithful=yes,bits=1\n");
#       return 0;
#   }

prog = [
  # _start:
  0x00020137,  #     0: lui   sp,0x20
  0x55c000ef,  #     4: jal   1376 <main>
  0x05d00893,  #     8: li    a7,93
  0x00000073,  #    12: ecall
  # usqrt:
  0x01f55793,  #    16: srli  a5,a0,0x1f
  0x00a787b3,  #    20: add   a5,a5,a0
  0x4017d793,  #    24: srai  a5,a5,0x1
  0x00050693,  #    28: mv    a3,a0
  0x00078e63,  #    32: beqz  a5,60
  0x02f6d733,  #    36: divu  a4,a3,a5
  0x00078513,  #    40: mv    a0,a5
  0x00f707b3,  #    44: add   a5,a4,a5
  0x0017d793,  #    48: srli  a5,a5,0x1
  0xfea798e3,  #    52: bne   a5,a0,36
  0x00008067,  #    56: ret
  0x00000513,  #    60: li    a0,0
  0x00008067,  #    64: ret
  # primes8of30:
  0x41f55293,  #    68: srai  t0,a0,0x1f
  0xc9010113,  #    72: addi  sp,sp,-880
  0x07f2f293,  #    76: andi  t0,t0,127
  0x01f55f13,  #    80: srli  t5,a0,0x1f
  0x00a282b3,  #    84: add   t0,t0,a0
  0x00af0f33,  #    88: add   t5,t5,a0
  0x36812623,  #    92: sw    s0,876(sp)
  0x36912423,  #    96: sw    s1,872(sp)
  0x37212223,  #   100: sw    s2,868(sp)
  0x37312023,  #   104: sw    s3,864(sp)
  0x35412e23,  #   108: sw    s4,860(sp)
  0x35512c23,  #   112: sw    s5,856(sp)
  0x35612a23,  #   116: sw    s6,852(sp)
  0x35712823,  #   120: sw    s7,848(sp)
  0x35812623,  #   124: sw    s8,844(sp)
  0xf8100793,  #   128: li    a5,-127
  0x00050693,  #   132: mv    a3,a0
  0x4072d293,  #   136: srai  t0,t0,0x7
  0x401f5f13,  #   140: srai  t5,t5,0x1
  0x38f54663,  #   144: blt   a0,a5,1052
  0x67000893,  #   148: li    a7,1648
  0x67000713,  #   152: li    a4,1648
  0x00000793,  #   156: li    a5,0
  0x00000593,  #   160: li    a1,0
  0x00000613,  #   164: li    a2,0
  0x00b72023,  #   168: sw    a1,0(a4)
  0x00c72223,  #   172: sw    a2,4(a4)
  0x00178793,  #   176: addi  a5,a5,1
  0x00870713,  #   180: addi  a4,a4,8
  0xfef2d4e3,  #   184: bge   t0,a5,160
  0x360f0463,  #   188: beqz  t5,1060
  0x03e6d733,  #   192: divu  a4,a3,t5
  0x000f0793,  #   196: mv    a5,t5
  0x01e70f33,  #   200: add   t5,a4,t5
  0x001f5f13,  #   204: srli  t5,t5,0x1
  0xfeff18e3,  #   208: bne   t5,a5,192
  0x001f0f13,  #   212: addi  t5,t5,1
  0x63800793,  #   216: li    a5,1592
  0x00c7a303,  #   220: lw    t1,12(a5)
  0x0107a803,  #   224: lw    a6,16(a5)
  0x0187a603,  #   228: lw    a2,24(a5)
  0x01c7a703,  #   232: lw    a4,28(a5)
  0x0007af83,  #   236: lw    t6,0(a5)
  0x0047ae83,  #   240: lw    t4,4(a5)
  0x0087ae03,  #   244: lw    t3,8(a5)
  0x0147a583,  #   248: lw    a1,20(a5)
  0x66000793,  #   252: li    a5,1632
  0x00d7a023,  #   256: sw    a3,0(a5)
  0x00612623,  #   260: sw    t1,12(sp)
  0x01012823,  #   264: sw    a6,16(sp)
  0x00c12c23,  #   268: sw    a2,24(sp)
  0x00e12e23,  #   272: sw    a4,28(sp)
  0x0117a223,  #   276: sw    a7,4(a5)
  0x01f12023,  #   280: sw    t6,0(sp)
  0x01d12223,  #   284: sw    t4,4(sp)
  0x01c12423,  #   288: sw    t3,8(sp)
  0x00b12a23,  #   292: sw    a1,20(sp)
  0x00010613,  #   296: mv    a2,sp
  0x02010693,  #   300: addi  a3,sp,32
  0x00000713,  #   304: li    a4,0
  0x01e00313,  #   308: li    t1,30
  0x00800813,  #   312: li    a6,8
  0x00170713,  #   316: addi  a4,a4,1
  0x00777793,  #   320: andi  a5,a4,7
  0x00279793,  #   324: slli  a5,a5,0x2
  0x34078793,  #   328: addi  a5,a5,832
  0x002787b3,  #   332: add   a5,a5,sp
  0xcc07a783,  #   336: lw    a5,-832(a5)
  0x00062583,  #   340: lw    a1,0(a2)
  0x00468693,  #   344: addi  a3,a3,4
  0x01e78793,  #   348: addi  a5,a5,30
  0x40b787b3,  #   352: sub   a5,a5,a1
  0x0267f7b3,  #   356: remu  a5,a5,t1
  0x00460613,  #   360: addi  a2,a2,4
  0xfef6ae23,  #   364: sw    a5,-4(a3)
  0xfd0716e3,  #   368: bne   a4,a6,316
  0x00600793,  #   372: li    a5,6
  0x00100393,  #   376: li    t2,1
  0x00700f93,  #   380: li    t6,7
  0x23e7fc63,  #   384: bgeu  a5,t5,952
  0x01f00413,  #   388: li    s0,31
  0x34010313,  #   392: addi  t1,sp,832
  0x00100e13,  #   396: li    t3,1
  0x0240006f,  #   400: j     436
  0x00239793,  #   404: slli  a5,t2,0x2
  0x34078793,  #   408: addi  a5,a5,832
  0x002787b3,  #   412: add   a5,a5,sp
  0xce07a783,  #   416: lw    a5,-800(a5)
  0x00138393,  #   420: addi  t2,t2,1
  0x0073f393,  #   424: andi  t2,t2,7
  0x00ff8fb3,  #   428: add   t6,t6,a5
  0x21ff6463,  #   432: bltu  t5,t6,952
  0x001fd713,  #   436: srli  a4,t6,0x1
  0x007fd793,  #   440: srli  a5,t6,0x7
  0x03f77713,  #   444: andi  a4,a4,63
  0x00379793,  #   448: slli  a5,a5,0x3
  0xfe070693,  #   452: addi  a3,a4,-32
  0x00f887b3,  #   456: add   a5,a7,a5
  0x2206c463,  #   460: bltz  a3,1012
  0x0047a783,  #   464: lw    a5,4(a5)
  0x00d7d7b3,  #   468: srl   a5,a5,a3
  0x0017f793,  #   472: andi  a5,a5,1
  0xfa079ce3,  #   476: bnez  a5,404
  0x03ff86b3,  #   480: mul   a3,t6,t6
  0x14010e93,  #   484: addi  t4,sp,320
  0x000e8793,  #   488: mv    a5,t4
  0x0076d613,  #   492: srli  a2,a3,0x7
  0x00000913,  #   496: li    s2,0
  0x00000993,  #   500: li    s3,0
  0x0127a023,  #   504: sw    s2,0(a5)
  0x0137a223,  #   508: sw    s3,4(a5)
  0x00878793,  #   512: addi  a5,a5,8
  0xfef316e3,  #   516: bne   t1,a5,496
  0x001f9993,  #   520: slli  s3,t6,0x1
  0x04000813,  #   524: li    a6,64
  0x00000593,  #   528: li    a1,0
  0x0700006f,  #   532: j     644
  0x015e1ab3,  #   536: sll   s5,t3,s5
  0x00000713,  #   540: li    a4,0
  0x340a0793,  #   544: addi  a5,s4,832
  0x002787b3,  #   548: add   a5,a5,sp
  0xe007ac03,  #   552: lw    s8,-512(a5)
  0xe047ab83,  #   556: lw    s7,-508(a5)
  0x41f6d793,  #   560: srai  a5,a3,0x1f
  0x07f7f793,  #   564: andi  a5,a5,127
  0x01368a33,  #   568: add   s4,a3,s3
  0x00d787b3,  #   572: add   a5,a5,a3
  0x00ec6c33,  #   576: or    s8,s8,a4
  0x015be6b3,  #   580: or    a3,s7,s5
  0x00259713,  #   584: slli  a4,a1,0x2
  0xe0db2223,  #   588: sw    a3,-508(s6)
  0x4077d793,  #   592: srai  a5,a5,0x7
  0x007a5693,  #   596: srli  a3,s4,0x7
  0x34070713,  #   600: addi  a4,a4,832
  0xe18b2023,  #   604: sw    s8,-512(s6)
  0xfff80813,  #   608: addi  a6,a6,-1
  0x00270733,  #   612: add   a4,a4,sp
  0x40f68ab3,  #   616: sub   s5,a3,a5
  0x00f68863,  #   620: beq   a3,a5,636
  0xd1572023,  #   624: sw    s5,-768(a4)
  0x00158593,  #   628: addi  a1,a1,1
  0x01590933,  #   632: add   s2,s2,s5
  0x000a0693,  #   636: mv    a3,s4
  0x02080a63,  #   640: beqz  a6,692
  0x01f6d793,  #   644: srli  a5,a3,0x1f
  0x00d787b3,  #   648: add   a5,a5,a3
  0x4017d793,  #   652: srai  a5,a5,0x1
  0x03f7f793,  #   656: andi  a5,a5,63
  0x00359a13,  #   660: slli  s4,a1,0x3
  0x340a0713,  #   664: addi  a4,s4,832
  0xfe078a93,  #   668: addi  s5,a5,-32
  0x00270b33,  #   672: add   s6,a4,sp
  0xf60adae3,  #   676: bgez  s5,536
  0x00000a93,  #   680: li    s5,0
  0x00fe1733,  #   684: sll   a4,t3,a5
  0xf71ff06f,  #   688: j     544
  0x020a9863,  #   692: bnez  s5,740
  0x00359793,  #   696: slli  a5,a1,0x3
  0x34078793,  #   700: addi  a5,a5,832
  0x002787b3,  #   704: add   a5,a5,sp
  0xe007a803,  #   708: lw    a6,-512(a5)
  0xe047a683,  #   712: lw    a3,-508(a5)
  0x14012703,  #   716: lw    a4,320(sp)
  0x14412783,  #   720: lw    a5,324(sp)
  0x01076733,  #   724: or    a4,a4,a6
  0x00d7e7b3,  #   728: or    a5,a5,a3
  0x14e12023,  #   732: sw    a4,320(sp)
  0x14f12223,  #   736: sw    a5,324(sp)
  0x41228933,  #   740: sub   s2,t0,s2
  0x04c96c63,  #   744: bltu  s2,a2,832
  0x00359b93,  #   748: slli  s7,a1,0x3
  0x01db8bb3,  #   752: add   s7,s7,t4
  0x12b05063,  #   756: blez  a1,1044
  0x04010993,  #   760: addi  s3,sp,64
  0x000e8713,  #   764: mv    a4,t4
  0x00361793,  #   768: slli  a5,a2,0x3
  0x00f887b3,  #   772: add   a5,a7,a5
  0x0007a803,  #   776: lw    a6,0(a5)
  0x00072b03,  #   780: lw    s6,0(a4)
  0x0047a683,  #   784: lw    a3,4(a5)
  0x00472a83,  #   788: lw    s5,4(a4)
  0x0009aa03,  #   792: lw    s4,0(s3)
  0x01686833,  #   796: or    a6,a6,s6
  0x0156e6b3,  #   800: or    a3,a3,s5
  0x0107a023,  #   804: sw    a6,0(a5)
  0x00d7a223,  #   808: sw    a3,4(a5)
  0x00870713,  #   812: addi  a4,a4,8
  0x01460633,  #   816: add   a2,a2,s4
  0x00498993,  #   820: addi  s3,s3,4
  0xfceb94e3,  #   824: bne   s7,a4,768
  0xfac97ee3,  #   828: bgeu  s2,a2,760
  0xe4b05ae3,  #   832: blez  a1,404
  0xe4c2e8e3,  #   836: bltu  t0,a2,404
  0x04010913,  #   840: addi  s2,sp,64
  0x00000813,  #   844: li    a6,0
  0x0100006f,  #   848: j     864
  0x008e8e93,  #   852: addi  t4,t4,8
  0x00490913,  #   856: addi  s2,s2,4
  0xe2c2ece3,  #   860: bltu  t0,a2,404
  0x00361793,  #   864: slli  a5,a2,0x3
  0x00f887b3,  #   868: add   a5,a7,a5
  0x0007a683,  #   872: lw    a3,0(a5)
  0x0047a703,  #   876: lw    a4,4(a5)
  0x000eaa83,  #   880: lw    s5,0(t4)
  0x004eaa03,  #   884: lw    s4,4(t4)
  0x00092983,  #   888: lw    s3,0(s2)
  0x0156e6b3,  #   892: or    a3,a3,s5
  0x01476733,  #   896: or    a4,a4,s4
  0x00d7a023,  #   900: sw    a3,0(a5)
  0x00e7a223,  #   904: sw    a4,4(a5)
  0x00180813,  #   908: addi  a6,a6,1
  0x01360633,  #   912: add   a2,a2,s3
  0xfd0590e3,  #   916: bne   a1,a6,852
  0x00239793,  #   920: slli  a5,t2,0x2
  0x34078793,  #   924: addi  a5,a5,832
  0x002787b3,  #   928: add   a5,a5,sp
  0xce07a783,  #   932: lw    a5,-800(a5)
  0x00138393,  #   936: addi  t2,t2,1
  0x0073f393,  #   940: andi  t2,t2,7
  0x00ff8fb3,  #   944: add   t6,t6,a5
  0xe1ff70e3,  #   948: bgeu  t5,t6,436
  0x67002783,  #   952: lw    a5,1648(zero)
  0x36c12403,  #   956: lw    s0,876(sp)
  0x36412903,  #   960: lw    s2,868(sp)
  0xfc07f793,  #   964: andi  a5,a5,-64
  0x66f02823,  #   968: sw    a5,1648(zero)
  0x36012983,  #   972: lw    s3,864(sp)
  0x35c12a03,  #   976: lw    s4,860(sp)
  0x35812a83,  #   980: lw    s5,856(sp)
  0x35412b03,  #   984: lw    s6,852(sp)
  0x35012b83,  #   988: lw    s7,848(sp)
  0x34c12c03,  #   992: lw    s8,844(sp)
  0x66000513,  #   996: li    a0,1632
  0x36812483,  #  1000: lw    s1,872(sp)
  0x37010113,  #  1004: addi  sp,sp,880
  0x00008067,  #  1008: ret
  0x0047a683,  #  1012: lw    a3,4(a5)
  0x0007a783,  #  1016: lw    a5,0(a5)
  0x40e40633,  #  1020: sub   a2,s0,a4
  0x00169693,  #  1024: slli  a3,a3,0x1
  0x00c696b3,  #  1028: sll   a3,a3,a2
  0x00e7d7b3,  #  1032: srl   a5,a5,a4
  0x00f6e7b3,  #  1036: or    a5,a3,a5
  0xdc9ff06f,  #  1040: j     472
  0xeec970e3,  #  1044: bgeu  s2,a2,756
  0xf29ff06f,  #  1048: j     832
  0x67000893,  #  1052: li    a7,1648
  0xca1ff06f,  #  1056: j     192
  0x00100f13,  #  1060: li    t5,1
  0xcb1ff06f,  #  1064: j     216
  # countPrimes:
  0x63800793,  #  1068: li    a5,1592
  0x0087a303,  #  1072: lw    t1,8(a5)
  0x00c7a883,  #  1076: lw    a7,12(a5)
  0x0107a603,  #  1080: lw    a2,16(a5)
  0x0147a683,  #  1084: lw    a3,20(a5)
  0x0187a703,  #  1088: lw    a4,24(a5)
  0x0007ae83,  #  1092: lw    t4,0(a5)
  0x0047ae03,  #  1096: lw    t3,4(a5)
  0x01c7a783,  #  1100: lw    a5,28(a5)
  0x00452803,  #  1104: lw    a6,4(a0)
  0x00052583,  #  1108: lw    a1,0(a0)
  0xfc010113,  #  1112: addi  sp,sp,-64
  0x00612423,  #  1116: sw    t1,8(sp)
  0x01112623,  #  1120: sw    a7,12(sp)
  0x00c12823,  #  1124: sw    a2,16(sp)
  0x00d12a23,  #  1128: sw    a3,20(sp)
  0x00e12c23,  #  1132: sw    a4,24(sp)
  0x01d12023,  #  1136: sw    t4,0(sp)
  0x01c12223,  #  1140: sw    t3,4(sp)
  0x00f12e23,  #  1144: sw    a5,28(sp)
  0x00010613,  #  1148: mv    a2,sp
  0x02010693,  #  1152: addi  a3,sp,32
  0x00000713,  #  1156: li    a4,0
  0x01e00313,  #  1160: li    t1,30
  0x00800893,  #  1164: li    a7,8
  0x00170713,  #  1168: addi  a4,a4,1
  0x00777793,  #  1172: andi  a5,a4,7
  0x00279793,  #  1176: slli  a5,a5,0x2
  0x04078793,  #  1180: addi  a5,a5,64
  0x002787b3,  #  1184: add   a5,a5,sp
  0xfc07a783,  #  1188: lw    a5,-64(a5)
  0x00062503,  #  1192: lw    a0,0(a2)
  0x00468693,  #  1196: addi  a3,a3,4
  0x01e78793,  #  1200: addi  a5,a5,30
  0x40a787b3,  #  1204: sub   a5,a5,a0
  0x0267f7b3,  #  1208: remu  a5,a5,t1
  0x00460613,  #  1212: addi  a2,a2,4
  0xfef6ae23,  #  1216: sw    a5,-4(a3)
  0xfd1716e3,  #  1220: bne   a4,a7,1168
  0x00700793,  #  1224: li    a5,7
  0x08b7f463,  #  1228: bgeu  a5,a1,1364
  0x00700613,  #  1232: li    a2,7
  0x00100693,  #  1236: li    a3,1
  0x00300513,  #  1240: li    a0,3
  0x01f00e13,  #  1244: li    t3,31
  0x0380006f,  #  1248: j     1304
  0x0047a783,  #  1252: lw    a5,4(a5)
  0x0117d7b3,  #  1256: srl   a5,a5,a7
  0x00269713,  #  1260: slli  a4,a3,0x2
  0x04070713,  #  1264: addi  a4,a4,64
  0x00270733,  #  1268: add   a4,a4,sp
  0xfe072703,  #  1272: lw    a4,-32(a4)
  0x0017f793,  #  1276: andi  a5,a5,1
  0x0017b793,  #  1280: seqz  a5,a5
  0x00168693,  #  1284: addi  a3,a3,1
  0x00e60633,  #  1288: add   a2,a2,a4
  0x00f50533,  #  1292: add   a0,a0,a5
  0x0076f693,  #  1296: andi  a3,a3,7
  0x04b67263,  #  1300: bgeu  a2,a1,1368
  0x00165713,  #  1304: srli  a4,a2,0x1
  0x03f77713,  #  1308: andi  a4,a4,63
  0x00765793,  #  1312: srli  a5,a2,0x7
  0x00379793,  #  1316: slli  a5,a5,0x3
  0xfe070893,  #  1320: addi  a7,a4,-32
  0x40ee0333,  #  1324: sub   t1,t3,a4
  0x00f807b3,  #  1328: add   a5,a6,a5
  0xfa08d8e3,  #  1332: bgez  a7,1252
  0x0047a883,  #  1336: lw    a7,4(a5)
  0x0007a783,  #  1340: lw    a5,0(a5)
  0x00189893,  #  1344: slli  a7,a7,0x1
  0x006898b3,  #  1348: sll   a7,a7,t1
  0x00e7d7b3,  #  1352: srl   a5,a5,a4
  0x00f8e7b3,  #  1356: or    a5,a7,a5
  0xf9dff06f,  #  1360: j     1260
  0x00300513,  #  1364: li    a0,3
  0x04010113,  #  1368: addi  sp,sp,64
  0x00008067,  #  1372: ret
  # main:
  0xff010113,  #  1376: addi  sp,sp,-16
  0x00812423,  #  1380: sw    s0,8(sp)
  0x65802503,  #  1384: lw    a0,1624(zero)
  0x00112623,  #  1388: sw    ra,12(sp)
  0xad5ff0ef,  #  1392: jal   68 <primes8of30>
  0xeb9ff0ef,  #  1396: jal   1068 <countPrimes>
  0x00050713,  #  1400: mv    a4,a0
  0x00100893,  #  1404: li    a7,1
  0x00000073,  #  1408: ecall
  0x5dc00513,  #  1412: li    a0,1500
  0x00400893,  #  1416: li    a7,4
  0x00000073,  #  1420: ecall
  0x00100893,  #  1424: li    a7,1
  0x65802503,  #  1428: lw    a0,1624(zero)
  0x00000073,  #  1432: ecall
  0x000137b7,  #  1436: lui   a5,0x13
  0x2a278793,  #  1440: addi  a5,a5,674
  0x02f70263,  #  1444: beq   a4,a5,1480
  0x5ec00513,  #  1448: li    a0,1516
  0x00400893,  #  1452: li    a7,4
  0x00000073,  #  1456: ecall
  0x00100513,  #  1460: li    a0,1
  0x00c12083,  #  1464: lw    ra,12(sp)
  0x00812403,  #  1468: lw    s0,8(sp)
  0x01010113,  #  1472: addi  sp,sp,16
  0x00008067,  #  1476: ret
  0x60400513,  #  1480: li    a0,1540
  0x00400893,  #  1484: li    a7,4
  0x00000073,  #  1488: ecall
  0x00000513,  #  1492: li    a0,0
  0xfe1ff06f,  #  1496: j     1464
  # ---- data ----
  0x69727020,  #  1500: " pri"
  0x2073656d,  #  1504: "mes "
  0x6f6c6562,  #  1508: "belo"
  0x00002077,  #  1512: "w \0\0"
  0x202d2d20,  #  1516: " -- "
  0x65707865,  #  1520: "expe"
  0x64657463,  #  1524: "cted"
  0x34383720,  #  1528: " 784"
  0x0a213839,  #  1532: "98!\n"
  0x00000000,  #  1536: "\0\0\0\0"
  0x6b636d0a,  #  1540: "\nmck"
  0x2d73736f,  #  1544: "oss-"
  0x30333863,  #  1548: "c830"
  0x613b313b,  #  1552: ";1;a"
  0x726f676c,  #  1556: "lgor"
  0x6d687469,  #  1560: "ithm"
  0x6568773d,  #  1564: "=whe"
  0x662c6c65,  #  1568: "el,f"
  0x68746961,  #  1572: "aith"
  0x3d6c7566,  #  1576: "ful="
  0x2c736579,  #  1580: "yes,"
  0x73746962,  #  1584: "bits"
  0x000a313d,  #  1588: "=1\n\0"
  0x00000001,  #  1592: ".\0\0\0"
  0x00000007,  #  1596: ".\0\0\0"
  0x0000000b,  #  1600: ".\0\0\0"
  0x0000000d,  #  1604: ".\0\0\0"
  0x00000011,  #  1608: ".\0\0\0"
  0x00000013,  #  1612: ".\0\0\0"
  0x00000017,  #  1616: ".\0\0\0"
  0x0000001d,  #  1620: ".\0\0\0"
  # maxNumber:
  0x000f4240]  #  1624: "@B.\0"

# zero-initialized data (.bss), not part of the image:
#    1632: sieve_obj
#    1640: fDebug
#    1648: sieve_buffer

m = machine(mem_size=0x20000)
m.write_i32_vec(prog, 0)
m.run(start=0)
print('exit code: ' + str(m.exit_code))
