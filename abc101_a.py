from machine import *

# AtCoder ABC101 A - Eating Symbols Easy
# https://atcoder.jp/contests/abc101/tasks/abc101_a
# Start from 0; read a string of '+'/'-', add 1 for each '+', subtract 1 for
# each '-', and print the result. Runs as RV32I machine code; I/O via ecalls
# (RARS convention, see machine.ECALL).

class asm:
  def _itype(opcode, funct3, rd, rs1, imm):
    assert -2048 <= imm < 2048, 'imm must fit in 12 bits (signed)'
    return ((imm & 0xfff) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode

  def _stype(opcode, funct3, rs2, imm, rs1):
    assert -2048 <= imm < 2048, 'imm must fit in 12 bits (signed)'
    imm &= 0xfff
    return ((imm >> 5) << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | \
           ((imm & 0x1f) << 7) | opcode

  def _btype(opcode, funct3, rs1, rs2, imm):
    assert -4096 <= imm < 4096 and imm % 2 == 0, 'imm must be even and fit in 13 bits (signed)'
    imm &= 0x1fff
    return (((imm >> 12) & 1) << 31) | (((imm >> 5) & 0x3f) << 25) | (rs2 << 20) | \
           (rs1 << 15) | (funct3 << 12) | (((imm >> 1) & 0xf) << 8) | \
           (((imm >> 11) & 1) << 7) | opcode

  def _jtype(opcode, rd, imm):
    assert -2**20 <= imm < 2**20 and imm % 2 == 0, 'imm must be even and fit in 21 bits (signed)'
    imm &= 0x1fffff
    return (((imm >> 20) & 1) << 31) | (((imm >> 1) & 0x3ff) << 21) | \
           (((imm >> 11) & 1) << 20) | (((imm >> 12) & 0xff) << 12) | (rd << 7) | opcode

  # operands in assembly order: ADDI(rd, rs1, imm), SW(rs2, imm, rs1),
  # BEQ(rs1, rs2, imm), JAL(rd, imm) -- same as machine.ADDI etc
  def make_itype(opcode, funct3): return lambda *ops: asm._itype(opcode, funct3, *ops)
  def make_stype(opcode, funct3): return lambda *ops: asm._stype(opcode, funct3, *ops)
  def make_btype(opcode, funct3): return lambda *ops: asm._btype(opcode, funct3, *ops)
  def make_jtype(opcode):         return lambda *ops: asm._jtype(opcode, *ops)

  ECALL = lambda: 0x00000073
  ADDI = make_itype(0b0010011, 0b000)
  BEQ  = make_btype(0b1100011, 0b000)
  JAL  = make_jtype(0b1101111)

  def LI(rd, imm): return asm.ADDI(rd, 0, imm) # short LI, only for small imm
  def J(offset): return asm.JAL(zero, offset)
  def MV(rd, rs): return asm.ADDI(rd, rs, 0)

prog = [
  asm.LI(t0, 0),   #  0:t0 <- running total
  
  # loop:
  asm.LI(a7, 12),  #  4: (read_char)
  asm.ECALL(),     #  8: a0 <- next char, -1 at end of input
  asm.LI(t1, 43),  # 12: t1 <- '+'
  asm.BEQ(a0, t1, 16),  # 16: beq  a0, t1, plus
  asm.LI(t1, 45),  # 20: t1 <- '-'
  asm.BEQ(a0, t1, 16),  # 24: beq  a0, t1, minus
  asm.J(20),   # 28: j done (newline or end of input)

  # plus:
  asm.ADDI(t0, t0, 1),
  asm.J(-32),  # 36: j loop
  
  # minus:
  asm.ADDI(t0, t0, -1),  # 40
  asm.J(-40),  # 44: j loop
  
  # done:
  asm.MV(a0, t0),  # 48: mv   a0, t0
  asm.LI(a7, 1),  # 52: (print_int)
  asm.ECALL(),  # 56: ecall
  asm.LI(a0, 10),  # 60: a0 <- '\n'
  asm.LI(a7, 11),  # 64: (print_char)
  asm.ECALL(),  # 68: ecall
  asm.LI(a7, 10),  # 72: (exit)
  asm.ECALL()  # 76
]

if __name__ == "__main__":
  m = machine(mem_size=256)
  m.write_i32_vec(prog, 0)
  m.run(start=0)
