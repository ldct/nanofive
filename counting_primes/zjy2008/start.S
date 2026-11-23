  # Driver for pi of src/zjy2008.cpp. The host puts N in a0, as for
  # every counting_primes program; this calls prime_pi(N), prints the result
  # (ecall 1) and a newline (ecall 11), and exits with status 0 (ecall 10).
  # Every instruction is written out so that the encoding is fixed.
  .section .text.init
  .option norvc
  .globl _start
_start:
  lui  sp, 0x400              # sp = 0x400000, the top of the 4 MiB memory
  jal  ra, _Z2pix       # a0 = pi(a0)
  addi a7, zero, 1            # print a0 as an integer
  ecall
  addi a0, zero, 10           # print a newline
  addi a7, zero, 11
  ecall
  addi a7, zero, 10           # exit 0
  ecall
