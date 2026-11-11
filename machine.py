# NanoFive - a RISC-V RV32IM emulator, forked from https://github.com/OpenMachine-ai/tinyfive?

# Each instruction is a method that
# updates the CPU state (registers x[], memory mem[], program counter pc).
# Either call the methods directly, or write machine code into mem[] (e.g. with
# write_i32_vec) and execute it with run(). There is no assembler.

import sys

#-------------------------------------------------------------------------------
# Python ints are unbounded, so every register write is wrapped to 32 bits here,
# like hardware does

def _i32(v): return ((v + 0x80000000) & 0xffffffff) - 0x80000000  # wrap to int32

class _XRegs(list):
  """integer regfile; writes wrap to signed int32"""
  def __setitem__(s, i, v): super().__setitem__(i, _i32(v))

class machine:
  def __init__(s, mem_size):  # for brevity we use 's' instead of 'self'
    """create state of CPU: memory mem[], regfile x[], program counter 'pc'"""
    s.mem = bytearray(mem_size)   # memory 'mem[]' is unsigned int8
    s.x   = _XRegs([0] * 32)      # regfile 'x[]' is signed int32
    s.pc  = 0                     # program counter (PC) is uint32
    s.halted = False              # set by the exit system call

  def i8(s,x): return ((x + 0x80) & 0xff) - 0x80  # convert to 8-bit signed
  def u (s,x): return x & 0xffffffff              # convert to 32-bit unsigned

  def ipc(s, incr=4):
    """increment pc by 'incr' and make sure that x[0] is always 0"""
    s.x[0] = 0
    s.pc = s.u(s.pc + incr)

  #-------------------------------------------------------------------------------
  # Base instructions (RV32I)

  # arithmetic
  def ADD (s,rd,rs1,rs2): s.x[rd] = s.x[rs1] + s.x[rs2]; s.ipc()
  def ADDI(s,rd,rs1,imm): s.x[rd] = s.x[rs1] + imm;      s.ipc()
  def SUB (s,rd,rs1,rs2): s.x[rd] = s.x[rs1] - s.x[rs2]; s.ipc()

  # bitwise logical
  def XOR (s,rd,rs1,rs2): s.x[rd] = s.x[rs1] ^ s.x[rs2]; s.ipc()
  def XORI(s,rd,rs1,imm): s.x[rd] = s.x[rs1] ^ imm;      s.ipc()
  def OR  (s,rd,rs1,rs2): s.x[rd] = s.x[rs1] | s.x[rs2]; s.ipc()
  def ORI (s,rd,rs1,imm): s.x[rd] = s.x[rs1] | imm;      s.ipc()
  def AND (s,rd,rs1,rs2): s.x[rd] = s.x[rs1] & s.x[rs2]; s.ipc()
  def ANDI(s,rd,rs1,imm): s.x[rd] = s.x[rs1] & imm;      s.ipc()

  # shift (note: 0x1f ensures that only the 5 LSBs are used as shift-amount)
  # (For rv64, we would use the 6 LSBs, so 0x3f)
  def SLL (s,rd,rs1,rs2): s.x[rd] = s.x[rs1]      << (s.x[rs2] & 0x1f); s.ipc()
  def SRA (s,rd,rs1,rs2): s.x[rd] = s.x[rs1]      >> (s.x[rs2] & 0x1f); s.ipc()
  def SRL (s,rd,rs1,rs2): s.x[rd] = s.u(s.x[rs1]) >> (s.x[rs2] & 0x1f); s.ipc()
  def SLLI(s,rd,rs1,imm): s.x[rd] = s.x[rs1]      << imm;               s.ipc()
  def SRAI(s,rd,rs1,imm): s.x[rd] = s.x[rs1]      >> imm;               s.ipc()
  def SRLI(s,rd,rs1,imm): s.x[rd] = s.u(s.x[rs1]) >> imm;               s.ipc()

  # set to 1 if less than
  def SLT  (s,rd,rs1,rs2): s.x[rd] = 1 if s.x[rs1]      < s.x[rs2]      else 0; s.ipc()
  def SLTI (s,rd,rs1,imm): s.x[rd] = 1 if s.x[rs1]      < imm           else 0; s.ipc()
  def SLTU (s,rd,rs1,rs2): s.x[rd] = 1 if s.u(s.x[rs1]) < s.u(s.x[rs2]) else 0; s.ipc()
  def SLTIU(s,rd,rs1,imm): s.x[rd] = 1 if s.u(s.x[rs1]) < s.u(imm)      else 0; s.ipc()

  # branch
  def BEQ (s,rs1,rs2,imm): s.ipc(imm if s.x[rs1]      == s.x[rs2]      else 4)
  def BNE (s,rs1,rs2,imm): s.ipc(imm if s.x[rs1]      != s.x[rs2]      else 4)
  def BLT (s,rs1,rs2,imm): s.ipc(imm if s.x[rs1]      <  s.x[rs2]      else 4)
  def BGE (s,rs1,rs2,imm): s.ipc(imm if s.x[rs1]      >= s.x[rs2]      else 4)
  def BLTU(s,rs1,rs2,imm): s.ipc(imm if s.u(s.x[rs1]) <  s.u(s.x[rs2]) else 4)
  def BGEU(s,rs1,rs2,imm): s.ipc(imm if s.u(s.x[rs1]) >= s.u(s.x[rs2]) else 4)

  # jump
  def JAL (s,rd,imm): s.x[rd] = s.pc + 4; s.ipc(imm)
  def JALR(s,rd,rs1,imm): t = s.pc + 4; s.pc = s.u(s.x[rs1] + imm) & ~1; s.x[rd] = t; s.x[0] = 0

  # load immediate
  def LUI  (s,rd,imm): s.x[rd] = imm << 12;          s.ipc()
  def AUIPC(s,rd,imm): s.x[rd] = s.pc + (imm << 12); s.ipc()

  # Edge case: addresses are not checked for alignment, and a negative address
  # (rs1 + offset < 0) silently indexes from the end of mem[] (Python indexing)
  # instead of trapping. Addresses past the end of mem[] raise IndexError.

  # load, note the different argument order, example: 'lb rd, offset(rs1)'
  def LB (s,rd,imm,rs1): s.x[rd] =  s.i8(s.mem[s.x[rs1] + imm]);  s.ipc()
  def LBU(s,rd,imm,rs1): s.x[rd] =       s.mem[s.x[rs1] + imm];   s.ipc()
  def LH (s,rd,imm,rs1): s.x[rd] = (s.i8(s.mem[s.x[rs1] + imm+1]) << 8) + \
                                         s.mem[s.x[rs1] + imm];   s.ipc()
  def LHU(s,rd,imm,rs1): s.x[rd] =      (s.mem[s.x[rs1] + imm+1]  << 8) + \
                                         s.mem[s.x[rs1] + imm];   s.ipc()
  def LW (s,rd,imm,rs1): s.x[rd] = (s.i8(s.mem[s.x[rs1] + imm+3]) << 24) + \
                                        (s.mem[s.x[rs1] + imm+2]  << 16) + \
                                        (s.mem[s.x[rs1] + imm+1]  << 8)  + \
                                         s.mem[s.x[rs1] + imm];   s.ipc()

  # store, note the different argument order, example: 'sb rs2, offset(rs1)'
  def SB(s,rs2,imm,rs1): s.mem[s.x[rs1] + imm]   =  s.x[rs2] & 0xff; s.ipc()
  def SH(s,rs2,imm,rs1): s.mem[s.x[rs1] + imm]   =  s.x[rs2] & 0xff; s.ipc(); \
                         s.mem[s.x[rs1] + imm+1] = (s.x[rs2] >> 8)  & 0xff
  def SW(s,rs2,imm,rs1): s.mem[s.x[rs1] + imm]   =  s.x[rs2] & 0xff; s.ipc(); \
                         s.mem[s.x[rs1] + imm+1] = (s.x[rs2] >> 8)  & 0xff; \
                         s.mem[s.x[rs1] + imm+2] = (s.x[rs2] >> 16) & 0xff; \
                         s.mem[s.x[rs1] + imm+3] = (s.x[rs2] >> 24) & 0xff

  # system calls, using the convention of the RARS simulator: a7 selects the
  # service, arguments are in a0, a1, and results are returned in a0
  #   a7 = 1 : print a0 as a signed integer
  #   a7 = 4 : print the null-terminated string at address a0
  #   a7 = 5 : read an integer from a line of stdin into a0
  #   a7 = 8 : read a line of stdin into the buffer at a0, of size a1: keeps at
  #            most a1-1 bytes (including the newline) plus a null terminator,
  #            and discards the rest of the line
  #   a7 = 10: exit
  #   a7 = 11: print a0 as a character
  #   a7 = 12: read a character from stdin into a0 (-1 at end of input)
  #   a7 = 93: exit with code a0
  def ECALL(s):
    a0, a1, a7 = s.x[10], s.x[11], s.x[17]
    if   a7 == 1 : print(a0, end='')
    elif a7 == 4 : print(s.read_str(a0), end='')
    elif a7 == 5 : s.x[10] = int(sys.stdin.readline())
    elif a7 == 8 :
      data = sys.stdin.readline().encode()[:max(a1 - 1, 0)] + b'\0'
      s.mem[a0 : a0 + len(data)] = data
    elif a7 == 10: s.halted = True; s.exit_code = 0
    elif a7 == 11: print(chr(a0 & 0xff), end='')
    elif a7 == 12: c = sys.stdin.read(1); s.x[10] = ord(c) if c else -1
    elif a7 == 93: s.halted = True; s.exit_code = a0
    else: raise ValueError('unsupported ecall service %d at pc %d' % (a7, s.pc))
    s.ipc()

  # the 2 missing instructions FENCE and EBREAK are not needed here

  # TODO: when using the above uppercase instructions, then there is no check if
  # an immediate exceeds the 12-bit limit. Therefore, consider replacing 'imm'
  # by 'ci(imm)', where ci() is a def that raises an error flag if the immediate
  # exceeds the 12-bit limit.

  #-------------------------------------------------------------------------------
  # M-extension (RV32M)
  def MUL   (s,rd,rs1,rs2): s.x[rd] =      s.x[rs1]  *     s.x[rs2];         s.ipc()
  def MULH  (s,rd,rs1,rs2): s.x[rd] =     (s.x[rs1]  *     s.x[rs2])  >> 32; s.ipc()
  def MULHSU(s,rd,rs1,rs2): s.x[rd] =     (s.x[rs1]  * s.u(s.x[rs2])) >> 32; s.ipc()
  def MULHU (s,rd,rs1,rs2): s.x[rd] = (s.u(s.x[rs1]) * s.u(s.x[rs2])) >> 32; s.ipc()

  # RISC-V division rounds toward zero, while Python's '//' rounds toward -inf,
  # so divide the magnitudes and fix up the sign.
  # Edge cases (as the spec requires, division never traps):
  #   - division by zero: quotient is -1 (all ones, i.e. 0xffffffff for DIVU) and
  #     remainder is the dividend
  #   - signed overflow -2**31 / -1: quotient is 2**31, which the regfile wraps
  #     back to -2**31; remainder is 0
  def div(s,a,b):
    if b == 0: return -1
    q = abs(a) // abs(b)
    return q if (a < 0) == (b < 0) else -q
  def rem(s,a,b): return a if b == 0 else a - b * s.div(a, b)
  def DIV (s,rd,rs1,rs2): s.x[rd] = s.div(    s.x[rs1],      s.x[rs2]);  s.ipc()
  def DIVU(s,rd,rs1,rs2): s.x[rd] = s.div(s.u(s.x[rs1]), s.u(s.x[rs2])); s.ipc()
  def REM (s,rd,rs1,rs2): s.x[rd] = s.rem(   s.x[rs1],       s.x[rs2]);  s.ipc()
  def REMU(s,rd,rs1,rs2): s.x[rd] = s.rem(s.u(s.x[rs1]), s.u(s.x[rs2])); s.ipc()

  #-------------------------------------------------------------------------------
  # fetch, decode, execute machine code from mem[]

  # decode tables: funct3 (and funct7) -> instruction, see the opcode map in the
  # RV32I/RV32M chapters of the spec
  BRANCH = {0: BEQ, 1: BNE, 4: BLT, 5: BGE, 6: BLTU, 7: BGEU}
  LOAD   = {0: LB, 1: LH, 2: LW, 4: LBU, 5: LHU}
  STORE  = {0: SB, 1: SH, 2: SW}
  OP_IMM = {0: ADDI, 2: SLTI, 3: SLTIU, 4: XORI, 6: ORI, 7: ANDI}
  SHIFT_IMM = {(1, 0x00): SLLI, (5, 0x00): SRLI, (5, 0x20): SRAI}
  OP = {(0, 0x00): ADD, (0, 0x20): SUB, (1, 0x00): SLL, (2, 0x00): SLT,
        (3, 0x00): SLTU, (4, 0x00): XOR, (5, 0x00): SRL, (5, 0x20): SRA,
        (6, 0x00): OR, (7, 0x00): AND,
        (0, 0x01): MUL, (1, 0x01): MULH, (2, 0x01): MULHSU, (3, 0x01): MULHU,
        (4, 0x01): DIV, (5, 0x01): DIVU, (6, 0x01): REM, (7, 0x01): REMU}

  def step(s):
    """execute the instruction at address pc"""
    w = s.u(s.read_i32(s.pc))
    op, rd, f3 = w & 0x7f, (w >> 7) & 0x1f, (w >> 12) & 0x7
    rs1, rs2, f7 = (w >> 15) & 0x1f, (w >> 20) & 0x1f, w >> 25
    def sext(v, bits): return v - (1 << bits) if v >> (bits - 1) else v
    imm_i = sext(w >> 20, 12)
    imm_s = sext((f7 << 5) | rd, 12)
    imm_b = sext(((w >> 31) << 12) | (((w >> 7) & 1) << 11) |
                 (((w >> 25) & 0x3f) << 5) | (((w >> 8) & 0xf) << 1), 13)
    imm_u = sext(w >> 12, 20)
    imm_j = sext(((w >> 31) << 20) | (((w >> 12) & 0xff) << 12) |
                 (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3ff) << 1), 21)

    if   op == 0x37: s.LUI  (rd, imm_u)
    elif op == 0x17: s.AUIPC(rd, imm_u)
    elif op == 0x6f: s.JAL  (rd, imm_j)
    elif op == 0x67 and f3 == 0: s.JALR(rd, rs1, imm_i)
    elif op == 0x63 and f3 in s.BRANCH: s.BRANCH[f3](s, rs1, rs2, imm_b)
    elif op == 0x03 and f3 in s.LOAD:   s.LOAD[f3]  (s, rd,  imm_i, rs1)
    elif op == 0x23 and f3 in s.STORE:  s.STORE[f3] (s, rs2, imm_s, rs1)
    elif op == 0x13 and f3 not in (1, 5): s.OP_IMM[f3](s, rd, rs1, imm_i)
    elif op == 0x13 and (f3, f7) in s.SHIFT_IMM: s.SHIFT_IMM[f3, f7](s, rd, rs1, rs2)
    elif op == 0x33 and (f3, f7) in s.OP:        s.OP[f3, f7]       (s, rd, rs1, rs2)
    elif w == 0x00000073: s.ECALL()
    else: raise ValueError('unsupported instruction %08x at pc %d' % (w, s.pc))

  def run(s, start, end=None, steps=None):
    """execute from address 'start' until pc reaches 'end', 'steps' instructions
    have been executed, or the program exits via ecall, whichever comes first"""
    s.pc = start
    s.halted = False
    n = 0
    while s.pc != end and not s.halted and (steps is None or n < steps):
      s.step()
      n += 1

  #-------------------------------------------------------------------------------
  # memory access

  def write_i32(s, x, addr):
    """write 32-bit int to memory (takes 4 byte-addresses)"""
    for i in range(4): s.mem[addr + i] = (x >> (8*i)) & 0xff

  def read_str(s, addr):
    """read null-terminated string from memory"""
    return s.mem[addr : s.mem.index(0, addr)].decode()

  def read_i32(s, addr):
    """"read 32-bit int from memory"""
    ret = s.i8(s.mem[addr + 3]) << 3*8
    for i in range(3): ret += s.mem[addr + i] << i*8
    return ret

  #-------------------------------------------------------------------------------
  # pseudoinstructions

  def hi20(s, val): return (val + 0x800) >> 12  # higher 20 bits (+1 if val[11]==1)
  def lo12(s, val):
    return (val & 0x7ff) - (val & 0x800) # lower 12 bits and convert to signed int12
  # above functions are similar to LLVM
  # https://github.com/llvm/llvm-project/blob/main/lld/ELF/Arch/RISCV.cpp
  # note that ADDI interprets the immediate as a 12-bit signed. So if bit[11] is
  # set (i.e. value -2048 = -0x800), then we have to add +1 to the upper 20 bits
  # (i.e. +0x1000) so that (hi20 >> 12) + lo12 is the same as 'val'. The term
  # '(val + 0x800) >> 12' in hi20 def will only add +1 if bit val[11] is set.
  # Example: 0xdeadbeef -> hi20 = 0xdeadc; lo12 = -273

  def LI(s, rd, imm):
    s.LUI (rd,     s.hi20(imm))
    s.ADDI(rd, rd, s.lo12(imm))

  # TODO: add more pseudoinstructions

  #-------------------------------------------------------------------------------
  # useful functions for accessing state and memory

  def clear_cpu(s):
    s.x = _XRegs([0] * 32)
    s.pc = 0
    s.halted = False
    # TODO: add an option that initializes all registers with random data so we
    # can find bugs that are hidden by register initialization

  def clear_mem(s, start=0, end=None):
    """clear memory from address 'start' to 'end' (excluding 'end')"""
    if end is None:
      end = len(s.mem)  # use maximum memory address by default
    for i in range(start, end): s.mem[i] = 0

  # TODO: replace write_* and read_* defs by generic 'write_mem' and 'read_mem'
  # that work for any tensor.  For read, have a size-parameter that can be set
  # to e.g. (4, 4) for a 4x4 matrix
  def write_i32_vec(s, vec, start):
    """write i32-vector to memory address 'start'"""
    for i, x in enumerate(vec):
      s.write_i32(x, start + 4*i)

  def read_i32_vec(s, start, size):
    """read i32-vector of size 'size' from memory address 'start'"""
    return [s.read_i32(start + 4*i) for i in range(size)]

  def mem_dump(s, start, size):
    """for debug: dump memory from byteaddress 'start', dump out 'size' bytes"""
    for i in range(start, start + size, 4):
      print('%08x' % s.u(s.read_i32(i)))

  def dump_state(s):
    print('pc   : %4d' % s.pc)
    for i in range(0, 32, 4):
      print('x[%2d]: %4d, x[%2d]: %4d, x[%2d]: %4d, x[%2d]: %4d' %
            (i, s.x[i], i+1, s.x[i+1], i+2, s.x[i+2], i+3, s.x[i+3]))

#---------------------------------------------------------------------------------
# register names (ABI mnemonics)
#---------------------------------------------------------------------------------
x0  = 0;  x1  = 1;  x2  = 2;  x3  = 3;  x4  = 4;  x5  = 5;  x6  = 6;  x7  = 7
x8  = 8;  x9  = 9;  x10 = 10; x11 = 11; x12 = 12; x13 = 13; x14 = 14; x15 = 15
x16 = 16; x17 = 17; x18 = 18; x19 = 19; x20 = 20; x21 = 21; x22 = 22; x23 = 23
x24 = 24; x25 = 25; x26 = 26; x27 = 27; x28 = 28; x29 = 29; x30 = 30; x31 = 31
zero= 0;  ra  = 1;  sp  = 2;  gp  = 3;  tp  = 4;  t0  = 5;  t1  = 6;  t2  = 7; fp = 8
s0  = 8;  s1  = 9;  a0  = 10; a1  = 11; a2  = 12; a3  = 13; a4  = 14; a5  = 15
a6  = 16; a7  = 17; s2  = 18; s3  = 19; s4  = 20; s5  = 21; s6  = 22; s7  = 23
s8  = 24; s9  = 25; s10 = 26; s11 = 27; t3  = 28; t4  = 29; t5  = 30; t6  = 31
