from machine import *

# Minimal reverse Polish calculator.
# Reads characters from stdin: decimal digits build a number, which is pushed
# onto the stack at the next non-digit; '+', '-', '*' pop two numbers and push
# the result; 'p' prints the top of the stack and a newline. Every other
# character (space, newline) only ends a number. Arithmetic wraps at 32 bits.
# Example: echo '3 4 + 5 * p' | python rpn.py  ->  35
# Runs as RV32IM machine code; I/O via ecalls (RARS convention, see
# machine.ECALL). The stack grows down from address 1024.

class asm:
  def _rtype(opcode, funct3, funct7, rd, rs1, rs2):
    return (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode

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

  # operands in assembly order: ADD(rd, rs1, rs2), ADDI(rd, rs1, imm),
  # LW(rd, imm, rs1), SW(rs2, imm, rs1), BEQ(rs1, rs2, imm), JAL(rd, imm)
  # -- same as machine.ADD etc
  def make_rtype(opcode, funct3, funct7): return lambda *ops: asm._rtype(opcode, funct3, funct7, *ops)
  def make_itype(opcode, funct3): return lambda *ops: asm._itype(opcode, funct3, *ops)
  def make_load (opcode, funct3): return lambda rd, imm, rs1: asm._itype(opcode, funct3, rd, rs1, imm)
  def make_stype(opcode, funct3): return lambda *ops: asm._stype(opcode, funct3, *ops)
  def make_btype(opcode, funct3): return lambda *ops: asm._btype(opcode, funct3, *ops)
  def make_jtype(opcode):         return lambda *ops: asm._jtype(opcode, *ops)

  ECALL = lambda: 0x00000073
  ADD  = make_rtype(0b0110011, 0b000, 0b0000000)
  SUB  = make_rtype(0b0110011, 0b000, 0b0100000)
  MUL  = make_rtype(0b0110011, 0b000, 0b0000001)
  ADDI = make_itype(0b0010011, 0b000)
  LW   = make_load (0b0000011, 0b010)
  SW   = make_stype(0b0100011, 0b010)
  BEQ  = make_btype(0b1100011, 0b000)
  BLT  = make_btype(0b1100011, 0b100)
  BLTU = make_btype(0b1100011, 0b110)
  JAL  = make_jtype(0b1101111)

  def LI(rd, imm): return asm.ADDI(rd, 0, imm) # short LI, only for small imm
  def J(offset): return asm.JAL(zero, offset)

prog = [
  asm.LI(sp, 1024),         #   0: sp <- top of stack (empty)
  asm.LI(t2, 0),            #   4: t2 <- number being read
  asm.LI(t3, 0),            #   8: t3 <- 1 if t2 holds unpushed digits

  # loop:
  asm.LI(a7, 12),           #  12: (read_char)
  asm.ECALL(),              #  16: a0 <- next char, -1 at end of input
  asm.ADDI(t4, a0, -48),    #  20: t4 <- a0 - '0'
  asm.LI(t5, 10),           #  24:
  asm.BLTU(t4, t5, 64),     #  28: bltu t4, t5, digit
  asm.BEQ(t3, zero, 20),    #  32: beq  t3, zero, op (nothing to push)
  asm.ADDI(sp, sp, -4),     #  36: push t2
  asm.SW(t2, 0, sp),        #  40:
  asm.LI(t2, 0),            #  44:
  asm.LI(t3, 0),            #  48:

  # op:
  asm.LI(t5, 43),           #  52: t5 <- '+'
  asm.BEQ(a0, t5, 56),      #  56: beq  a0, t5, plus
  asm.LI(t5, 45),           #  60: t5 <- '-'
  asm.BEQ(a0, t5, 64),      #  64: beq  a0, t5, minus
  asm.LI(t5, 42),           #  68: t5 <- '*'
  asm.BEQ(a0, t5, 72),      #  72: beq  a0, t5, times
  asm.LI(t5, 112),          #  76: t5 <- 'p'
  asm.BEQ(a0, t5, 92),      #  80: beq  a0, t5, print
  asm.BLT(a0, zero, 116),   #  84: blt  a0, zero, done (end of input)
  asm.J(-76),               #  88: j loop (any other char)

  # digit:
  asm.LI(t5, 10),           #  92:
  asm.MUL(t2, t2, t5),      #  96: t2 <- 10*t2 + t4
  asm.ADD(t2, t2, t4),      # 100:
  asm.LI(t3, 1),            # 104:
  asm.J(-96),               # 108: j loop

  # plus:
  asm.LW(t1, 0, sp),        # 112: t1 <- top, t0 <- the one below
  asm.LW(t0, 4, sp),        # 116:
  asm.ADD(t0, t0, t1),      # 120:
  asm.J(36),                # 124: j store

  # minus:
  asm.LW(t1, 0, sp),        # 128:
  asm.LW(t0, 4, sp),        # 132:
  asm.SUB(t0, t0, t1),      # 136:
  asm.J(20),                # 140: j store

  # times:
  asm.LW(t1, 0, sp),        # 144:
  asm.LW(t0, 4, sp),        # 148:
  asm.MUL(t0, t0, t1),      # 152:
  asm.J(4),                 # 156: j store

  # store: pop two, push t0
  asm.ADDI(sp, sp, 4),      # 160:
  asm.SW(t0, 0, sp),        # 164:
  asm.J(-156),              # 168: j loop

  # print:
  asm.LW(a0, 0, sp),        # 172: a0 <- top (not popped)
  asm.LI(a7, 1),            # 176: (print_int)
  asm.ECALL(),              # 180:
  asm.LI(a0, 10),           # 184: a0 <- '\n'
  asm.LI(a7, 11),           # 188: (print_char)
  asm.ECALL(),              # 192:
  asm.J(-184),              # 196: j loop

  # done:
  asm.LI(a7, 10),           # 200: (exit)
  asm.ECALL()               # 204
]

if __name__ == "__main__":
  m = machine(mem_size=1024)
  m.write_i32_vec(prog, 0)
  m.run(start=0)
