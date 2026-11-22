  # A stand-alone driver for Nettle's _nettle_salsa20_core (salsa20-core-internal.c).
  # It reads the 16 input, 32 key and 16 constant bytes from standard input
  # (TinyFive ecall 12, one byte per call) into the 64-byte Salsa20 state at 0x80100,
  # where they lie as in the specification's initial state:
  #   constant[0:4]  -> 0x80100   key[0:16]   -> 0x80104   constant[4:8]   -> 0x80114
  #   input[0:16]    -> 0x80118   constant[8:12] -> 0x80128   key[16:32] -> 0x8012c
  #   constant[12:16] -> 0x8013c
  # then calls _nettle_salsa20_core(dst = 0x80000, src = 0x80100, rounds = 20),
  # prints the 64 output bytes (ecall 11) and exits with status 0 (ecall 10).
  # Every instruction is written out so that the encoding is fixed.
  .section .text.init
  .option norvc
  .globl _start
_start:
  lui  sp, 0x100              # sp = 0x100000, the top of memory
  addi a7, zero, 12           # read a byte
  lui  t0, 0x80
  addi t0, t0, 0x118          # input, 16 bytes
  addi t1, t0, 16
  jal  t2, readn
  lui  t0, 0x80
  addi t0, t0, 0x104          # key[0:16]
  addi t1, t0, 16
  jal  t2, readn
  lui  t0, 0x80
  addi t0, t0, 0x12c          # key[16:32]
  addi t1, t0, 16
  jal  t2, readn
  lui  t0, 0x80
  addi t0, t0, 0x100          # constant[0:4]
  addi t1, t0, 4
  jal  t2, readn
  lui  t0, 0x80
  addi t0, t0, 0x114          # constant[4:8]
  addi t1, t0, 4
  jal  t2, readn
  lui  t0, 0x80
  addi t0, t0, 0x128          # constant[8:12]
  addi t1, t0, 4
  jal  t2, readn
  lui  t0, 0x80
  addi t0, t0, 0x13c          # constant[12:16]
  addi t1, t0, 4
  jal  t2, readn
  lui  a0, 0x80               # dst
  addi a1, a0, 0x100          # src
  addi a2, zero, 20           # rounds
  jal  ra, _nettle_salsa20_core
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
