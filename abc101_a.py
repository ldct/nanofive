from machine import *

# AtCoder ABC101 A - Eating Symbols Easy
# https://atcoder.jp/contests/abc101/tasks/abc101_a
# Start from 0; read a string of '+'/'-', add 1 for each '+', subtract 1 for
# each '-', and print the result. Runs as RV32I machine code; I/O via ecalls
# (RARS convention, see machine.ECALL). Assembled with riscv64-unknown-elf-as.

prog = [
  0x00000293,  #  0: li   t0, 0           t0 <- running total
  # loop:
  0x00c00893,  #  4: li   a7, 12          (read_char)
  0x00000073,  #  8: ecall                a0 <- next char, -1 at end of input
  0x02b00313,  # 12: li   t1, '+'
  0x00650863,  # 16: beq  a0, t1, plus
  0x02d00313,  # 20: li   t1, '-'
  0x00650863,  # 24: beq  a0, t1, minus
  0x0140006f,  # 28: j    done            newline or end of input
  # plus:
  0x00128293,  # 32: addi t0, t0, 1
  0xfe1ff06f,  # 36: j    loop
  # minus:
  0xfff28293,  # 40: addi t0, t0, -1
  0xfd9ff06f,  # 44: j    loop
  # done:
  0x00028513,  # 48: mv   a0, t0
  0x00100893,  # 52: li   a7, 1           (print_int)
  0x00000073,  # 56: ecall
  0x00a00513,  # 60: li   a0, '\n'
  0x00b00893,  # 64: li   a7, 11          (print_char)
  0x00000073,  # 68: ecall
  0x00a00893,  # 72: li   a7, 10          (exit)
  0x00000073]  # 76: ecall

m = machine(mem_size=256)
m.write_i32_vec(prog, 0)
m.run(start=0)
