from machine import *

# BYTE Sieve benchmark (Jim Gilbreath, "A High-Level Language Benchmark", BYTE
# magazine, September 1981): 10 iterations of the Sieve of Eratosthenes over the
# odd numbers 3..16383; prints "1899 primes".
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
#   /* BYTE Sieve, Jim Gilbreath, "A High-Level Language Benchmark", BYTE Sep 1981.
#      The classic C listing; odd numbers only: flags[i] stands for 2*i+3. */
#   #include "rt.h"
#   #define true 1
#   #define false 0
#   #define size 8190
#   #define sizepl 8191
#   char flags[sizepl];
#   int main() {
#       int i, prime, k, count, iter;
#       print_str("10 iterations\n");
#       for (iter = 1; iter <= 10; iter++) {
#           count = 0;
#           for (i = 0; i <= size; i++)
#               flags[i] = true;
#           for (i = 0; i <= size; i++) {
#               if (flags[i]) {
#                   prime = i + i + 3;
#                   k = i + prime;
#                   while (k <= size) {
#                       flags[k] = false;
#                       k += prime;
#                   }
#                   count = count + 1;
#               }
#           }
#       }
#       print_int(count); print_str(" primes\n");
#       return 0;
#   }

prog = [
  # _start:
  0x00020137,  #     0: lui   sp,0x20
  0x00c000ef,  #     4: jal   16 <main>
  0x05d00893,  #     8: li    a7,93
  0x00000073,  #    12: ecall
  # main:
  0x0e000513,  #    16: li    a0,224
  0x00400893,  #    20: li    a7,4
  0x00000073,  #    24: ecall
  0x00002837,  #    28: lui   a6,0x2
  0x00002337,  #    32: lui   t1,0x2
  0x00a00f13,  #    36: li    t5,10
  0x0ff00293,  #    40: li    t0,255
  0x0fc00f93,  #    44: li    t6,252
  0x0fb30313,  #    48: addi  t1,t1,251
  0x00100e13,  #    52: li    t3,1
  0x00006eb7,  #    56: lui   t4,0x6
  0xffe80813,  #    60: addi  a6,a6,-2
  0x000f8593,  #    64: mv    a1,t6
  0x000f8793,  #    68: mv    a5,t6
  0x01c78023,  #    72: sb    t3,0(a5)
  0x00178793,  #    76: addi  a5,a5,1
  0xfe679ce3,  #    80: bne   a5,t1,72
  0x00028893,  #    84: mv    a7,t0
  0x00300693,  #    88: li    a3,3
  0x00300613,  #    92: li    a2,3
  0x00000513,  #    96: li    a0,0
  0x0005c783,  #   100: lbu   a5,0(a1)
  0x02079e63,  #   104: bnez  a5,164
  0x00360613,  #   108: addi  a2,a2,3
  0x00158593,  #   112: addi  a1,a1,1
  0x00388893,  #   116: addi  a7,a7,3
  0x00268693,  #   120: addi  a3,a3,2
  0xffd614e3,  #   124: bne   a2,t4,100
  0xffff0f13,  #   128: addi  t5,t5,-1
  0xfa0f1ee3,  #   132: bnez  t5,64
  0x00100893,  #   136: li    a7,1
  0x00000073,  #   140: ecall
  0x0f000513,  #   144: li    a0,240
  0x00400893,  #   148: li    a7,4
  0x00000073,  #   152: ecall
  0x00000513,  #   156: li    a0,0
  0x00008067,  #   160: ret
  0x00060793,  #   164: mv    a5,a2
  0x02c86863,  #   168: bltu  a6,a2,216
  0x00088713,  #   172: mv    a4,a7
  0x00070023,  #   176: sb    zero,0(a4)
  0x00d787b3,  #   180: add   a5,a5,a3
  0x00d70733,  #   184: add   a4,a4,a3
  0xfef85ae3,  #   188: bge   a6,a5,176
  0x00150513,  #   192: addi  a0,a0,1
  0x00158593,  #   196: addi  a1,a1,1
  0x00360613,  #   200: addi  a2,a2,3
  0x00388893,  #   204: addi  a7,a7,3
  0x00268693,  #   208: addi  a3,a3,2
  0xf91ff06f,  #   212: j     100
  0x00150513,  #   216: addi  a0,a0,1
  0xf91ff06f,  #   220: j     108
  # ---- data ----
  0x69203031,  #   224: "10 i"
  0x61726574,  #   228: "tera"
  0x6e6f6974,  #   232: "tion"
  0x00000a73,  #   236: "s\n\0\0"
  0x69727020,  #   240: " pri"
  0x0a73656d,  #   244: "mes\n"
  0x00000000]  #   248: "\0\0\0\0"

# zero-initialized data (.bss), not part of the image:
#     252: flags

m = machine(mem_size=0x20000)
m.write_i32_vec(prog, 0)
m.run(start=0)
print('exit code: ' + str(m.exit_code))
