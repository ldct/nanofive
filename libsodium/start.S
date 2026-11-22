  # A stand-alone driver for libsodium's crypto_core_salsa20 (crypto_core/salsa/ref).
  # It reads the 16 input, 32 key and 16 constant bytes from standard input
  # (TinyFive ecall 12, one byte per call), calls
  #   crypto_core_salsa20(out = 0x80000, in = 0x80100, k = 0x80200, c = 0x80300),
  # prints the 64 output bytes (ecall 11) and exits with status 0 (ecall 10).
  # Every instruction is written out so that the encoding is fixed.
  .section .text.init
  .option norvc
  .globl _start
_start:
  lui  sp, 0x100              # sp = 0x100000, the top of memory
  addi a7, zero, 12           # read a byte
  lui  t0, 0x80
  addi t0, t0, 0x100          # input, 16 bytes
  addi t1, t0, 16
  jal  t2, readn
  lui  t0, 0x80
  addi t0, t0, 0x200          # key, 32 bytes
  addi t1, t0, 32
  jal  t2, readn
  lui  t0, 0x80
  addi t0, t0, 0x300          # constant, 16 bytes
  addi t1, t0, 16
  jal  t2, readn
  lui  a0, 0x80               # output
  addi a1, a0, 0x100
  addi a2, a0, 0x200
  addi a3, a0, 0x300
  jal  ra, crypto_core_salsa20
  lui  t0, 0x80
  addi t1, t0, 64
  addi a7, zero, 11           # print a byte
print:
  lbu  a0, 0(t0)
  ecall
  addi t0, t0, 1
  bne  t0, t1, print
  addi a7, zero, 10           # exit 0
  ecall
readn:                        # read bytes into [t0, t1), return to t2
  ecall
  sb   a0, 0(t0)
  addi t0, t0, 1
  bne  t0, t1, readn
  jalr zero, 0(t2)
