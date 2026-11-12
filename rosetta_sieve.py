from machine import *

# Rosetta Code "Sieve of Eratosthenes", C entry (plain sieve without any
# optimizations): https://rosettacode.org/wiki/Sieve_of_Eratosthenes#C
# Sieves up to 10000, prints the primes below 100 and the count (1229).
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
#   /* Rosetta Code, "Sieve of Eratosthenes", C: "Plain sieve, without any
#      optimizations". https://rosettacode.org/wiki/Sieve_of_Eratosthenes#C
#      Changes for a freestanding build: calloc -> static array (zeroed .bss),
#      (int)sqrt(n) -> integer square root; main() added. */
#   #include "rt.h"
#   #define N 10000
#   static char sieve_buf[N + 1];
#
#   static int isqrt(int n) { int m = 0; while ((m + 1) * (m + 1) <= n) m++; return m; }
#
#   char*
#   eratosthenes(int n, int *c)
#   {
#      char* sieve;
#      int i, j, m;
#
#      if(n < 2)
#         return 0;
#
#      *c = n-1;     /* primes count */
#      m = isqrt(n);
#
#      sieve = sieve_buf;
#      sieve[0] = 1;
#      sieve[1] = 1;
#      for(i = 2; i <= m; i++)
#         if(!sieve[i])
#            for (j = i*i; j <= n; j += i)
#               if(!sieve[j]){
#                  sieve[j] = 1;
#                  --(*c);
#               }
#      return sieve;
#   }
#
#   int main() {
#       int c, i;
#       char *s = eratosthenes(N, &c);
#       for (i = 0; i < 100; i++)
#           if (!s[i]) { print_int(i); print_str(" "); }
#       print_str("\n");
#       print_int(c); print_str(" primes up to "); print_int(N); print_str("\n");
#       return 0;
#   }

prog = [
  # _start:
  0x00020137,  #     0: lui   sp,0x20
  0x0bc000ef,  #     4: jal   192 <main>
  0x05d00893,  #     8: li    a7,93
  0x00000073,  #    12: ecall
  # eratosthenes.part.0:
  0x00000793,  #    16: li    a5,0
  0x00078813,  #    20: mv    a6,a5
  0x00178793,  #    24: addi  a5,a5,1
  0x02f78733,  #    28: mul   a4,a5,a5
  0xfee55ae3,  #    32: bge   a0,a4,20
  0x10100793,  #    36: li    a5,257
  0x18f01223,  #    40: sh    a5,388(zero)
  0x00100793,  #    44: li    a5,1
  0x0707d663,  #    48: bge   a5,a6,156
  0x18600893,  #    52: li    a7,390
  0x00200793,  #    56: li    a5,2
  0x18400e93,  #    60: li    t4,388
  0x00100313,  #    64: li    t1,1
  0x0140006f,  #    68: j     88
  0x00178713,  #    72: addi  a4,a5,1
  0x00188893,  #    76: addi  a7,a7,1
  0x04f80663,  #    80: beq   a6,a5,156
  0x00070793,  #    84: mv    a5,a4
  0x0008c703,  #    88: lbu   a4,0(a7)
  0xfe0716e3,  #    92: bnez  a4,72
  0x02f786b3,  #    96: mul   a3,a5,a5
  0xfed542e3,  #   100: blt   a0,a3,72
  0x01d68733,  #   104: add   a4,a3,t4
  0x00074603,  #   108: lbu   a2,0(a4)
  0x00f686b3,  #   112: add   a3,a3,a5
  0x00061a63,  #   116: bnez  a2,136
  0x00670023,  #   120: sb    t1,0(a4)
  0x0005a603,  #   124: lw    a2,0(a1)
  0xfff60613,  #   128: addi  a2,a2,-1
  0x00c5a023,  #   132: sw    a2,0(a1)
  0x00f70733,  #   136: add   a4,a4,a5
  0xfed550e3,  #   140: bge   a0,a3,108
  0x00178713,  #   144: addi  a4,a5,1
  0x00188893,  #   148: addi  a7,a7,1
  0xfaf81ee3,  #   152: bne   a6,a5,84
  0x18400513,  #   156: li    a0,388
  0x00008067,  #   160: ret
  # eratosthenes:
  0x00100693,  #   164: li    a3,1
  0x00a6d863,  #   168: bge   a3,a0,184
  0xfff50793,  #   172: addi  a5,a0,-1
  0x00f5a023,  #   176: sw    a5,0(a1)
  0xf5dff06f,  #   180: j     16 <eratosthenes.part.0>
  0x00000513,  #   184: li    a0,0
  0x00008067,  #   188: ret
  # main:
  0xfe010113,  #   192: addi  sp,sp,-32
  0x000027b7,  #   196: lui   a5,0x2
  0x00002537,  #   200: lui   a0,0x2
  0x70f78793,  #   204: addi  a5,a5,1807
  0x00c10593,  #   208: addi  a1,sp,12
  0x71050513,  #   212: addi  a0,a0,1808
  0x00f12623,  #   216: sw    a5,12(sp)
  0x00112e23,  #   220: sw    ra,28(sp)
  0xf31ff0ef,  #   224: jal   16 <eratosthenes.part.0>
  0x00050693,  #   228: mv    a3,a0
  0x00000793,  #   232: li    a5,0
  0x06400613,  #   236: li    a2,100
  0x00f68733,  #   240: add   a4,a3,a5
  0x00074703,  #   244: lbu   a4,0(a4)
  0x00078513,  #   248: mv    a0,a5
  0x00100893,  #   252: li    a7,1
  0x00071a63,  #   256: bnez  a4,276
  0x00000073,  #   260: ecall
  0x00400893,  #   264: li    a7,4
  0x16c00513,  #   268: li    a0,364
  0x00000073,  #   272: ecall
  0x00178793,  #   276: addi  a5,a5,1
  0xfcc79ce3,  #   280: bne   a5,a2,240
  0x17000513,  #   284: li    a0,368
  0x00400893,  #   288: li    a7,4
  0x00000073,  #   292: ecall
  0x00100893,  #   296: li    a7,1
  0x00c12503,  #   300: lw    a0,12(sp)
  0x00000073,  #   304: ecall
  0x17400513,  #   308: li    a0,372
  0x00400893,  #   312: li    a7,4
  0x00000073,  #   316: ecall
  0x00002537,  #   320: lui   a0,0x2
  0x71050513,  #   324: addi  a0,a0,1808
  0x00100893,  #   328: li    a7,1
  0x00000073,  #   332: ecall
  0x00400893,  #   336: li    a7,4
  0x17000513,  #   340: li    a0,368
  0x00000073,  #   344: ecall
  0x01c12083,  #   348: lw    ra,28(sp)
  0x00000513,  #   352: li    a0,0
  0x02010113,  #   356: addi  sp,sp,32
  0x00008067,  #   360: ret
  # ---- data ----
  0x00000020,  #   364: " \0\0\0"
  0x0000000a,  #   368: "\n\0\0\0"
  0x69727020,  #   372: " pri"
  0x2073656d,  #   376: "mes "
  0x74207075,  #   380: "up t"
  0x0000206f]  #   384: "o \0\0"

# zero-initialized data (.bss), not part of the image:
#     388: sieve_buf

m = machine(mem_size=0x20000)
m.write_i32_vec(prog, 0)
m.run(start=0)
print('exit code: ' + str(m.exit_code))
