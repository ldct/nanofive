from machine import *
from machine import _i32, _i64, _xregs64

# RV64IM tests for machine64: width-dependent RV32I instructions at 64 bits,
# the RV64-only instructions, and their decoding (the instruction words below
# were produced by riscv64-unknown-elf-as -march=rv64im). Also checks that the
# RV32 machine still rejects the RV64-only encodings.

MIN_I64, MAX_I64 = -2**63, 2**63 - 1
MIN_I32, MAX_I32 = -2**31, 2**31 - 1

# _i64 / regfile wrapping
for v in range(-10, 10): assert _i64(v) == v
assert _i64(MAX_I64 + 1) == MIN_I64 and _i64(MIN_I64 - 1) == MAX_I64
r = _xregs64([0, 0]); r[1] = 2**64 + 5; assert r[1] == 5

m = machine64(mem_size=4096)

def exe(word, a1=0, a2=0, mem=None):
  """execute one encoded instruction with a1, a2 preset, return a0"""
  m.clear_cpu()
  m.x[a1_], m.x[a2_] = a1, a2
  m.write_i32(word, 0)
  m.step()
  assert m.pc == 4
  return m.x[a0_]
a0_, a1_, a2_ = a0, a1, a2

def check(name, got, want):
  assert got == want, '%s: got %d (%#x), want %d (%#x)' % (name, got, got, want, want)

#-------------------------------------------------------------------------------
# RV32I instructions that change meaning at XLEN = 64 (direct method calls)
def op(f, a, b):
  m.clear_cpu(); m.x[1], m.x[2] = a, b; f(3, 1, 2); return m.x[3]
check('add wrap',  op(m.ADD, MAX_I64, 1), MIN_I64)
check('add no32',  op(m.ADD, MAX_I32, 1), 2**31)
check('sub',       op(m.SUB, MIN_I64, 1), MAX_I64)
check('sll 63',    op(m.SLL, 1, 63), MIN_I64)
check('sll mask',  op(m.SLL, 1, 64 + 3), 8)
check('srl',       op(m.SRL, -1, 60), 0xf)
check('sra',       op(m.SRA, MIN_I64, 63), -1)
check('sltu',      op(m.SLTU, 1, -1), 1)
check('mul',       op(m.MUL, 2**40, 2**30), _i64(2**70))
check('mulh',      op(m.MULH, MIN_I64, MIN_I64), 2**62)
check('mulhu',     op(m.MULHU, -1, -1), -2)                 # 2**64-2
check('mulhsu',    op(m.MULHSU, -1, -1), -1)
check('div ovf',   op(m.DIV, MIN_I64, -1), MIN_I64)
check('rem ovf',   op(m.REM, MIN_I64, -1), 0)
check('div 0',     op(m.DIV, 7, 0), -1)
check('divu',      op(m.DIVU, -1, 2), MAX_I64)
check('remu',      op(m.REMU, -1, 10), (2**64 - 1) % 10)
check('div trunc', op(m.DIV, -7, 2), -3)
m.clear_cpu(); m.LUI(1, 0x80000); check('lui sext', m.x[1], -2**31)
m.clear_cpu(); m.LUI(1, 0x7ffff); check('lui pos',  m.x[1], 0x7ffff000)
m.clear_cpu(); m.LI(1, 0xdeadbeef); check('li sext', m.x[1], _i32(0xdeadbeef))
m.clear_cpu(); m.pc = 0x1000; m.AUIPC(1, 0xfffff); check('auipc', m.x[1], 0)
m.clear_cpu(); m.x[1] = -1; m.SLTIU(2, 1, -1); check('sltiu', m.x[2], 0)

# loads/stores at 64 bits
m.clear_cpu(); m.x[1] = 0x100; m.x[2] = -0x123456789abcdef0
m.SD(2, 8, 1); m.LD(3, 8, 1); check('sd/ld', m.x[3], m.x[2])
m.LW(4, 12, 1); check('lw sext', m.x[4], _i32(m.x[2] >> 32))
m.LWU(5, 12, 1); check('lwu', m.x[5], (m.x[2] >> 32) & 0xffffffff)
m.SW(2, 0, 1); m.LD(6, 0, 1); check('sw low', m.x[6] & 0xffffffff, m.x[2] & 0xffffffff)

#-------------------------------------------------------------------------------
# decoding + RV64-only instructions
X = 0x123456789abcdef0
check('slli 40',   exe(0x02859513, a1=1), 2**40)
check('srli 63',   exe(0x03f5d513, a1=-1), 1)
check('srai 33',   exe(0x4215d513, a1=MIN_I64), -2**30)
check('addiw',     exe(0xfff5851b, a1=0x80000000), MAX_I32)     # wraps at 32
check('addiw sx',  exe(0xfff5851b, a1=X), _i32(0x9abcdeef))
check('slliw',     exe(0x01f5951b, a1=1), MIN_I32)
check('srliw',     exe(0x0015d51b, a1=-1), MAX_I32)
check('sraiw',     exe(0x4015d51b, a1=0x80000000), -2**30)
check('addw',      exe(0x00c5853b, a1=MAX_I32, a2=1), MIN_I32)
check('subw',      exe(0x40c5853b, a1=MIN_I32, a2=1), MAX_I32)
check('sllw',      exe(0x00c5953b, a1=1, a2=32 + 31), MIN_I32)  # 5-bit shamt
check('srlw',      exe(0x00c5d53b, a1=X, a2=4), 0x09abcdef)
check('sraw',      exe(0x40c5d53b, a1=X, a2=4), _i32(0xf9abcdef))
check('mulw',      exe(0x02c5853b, a1=0x10000, a2=0x18000), MIN_I32)
check('divw',      exe(0x02c5c53b, a1=-7, a2=2), -3)
check('divw ovf',  exe(0x02c5c53b, a1=MIN_I32, a2=-1), MIN_I32)
check('divw 0',    exe(0x02c5c53b, a1=5, a2=0), -1)
check('divw hi',   exe(0x02c5c53b, a1=2**32 + 10, a2=2**32 + 3), 3)  # ignores upper
check('divuw',     exe(0x02c5d53b, a1=-1, a2=2), MAX_I32)
check('divuw 0',   exe(0x02c5d53b, a1=5, a2=0), -1)
check('remw',      exe(0x02c5e53b, a1=-7, a2=2), -1)
check('remw ovf',  exe(0x02c5e53b, a1=MIN_I32, a2=-1), 0)
check('remw 0',    exe(0x02c5e53b, a1=-5, a2=0), -5)
check('remuw',     exe(0x02c5f53b, a1=-1, a2=10), (2**32 - 1) % 10)
check('remuw 0',   exe(0x02c5f53b, a1=0x80000000, a2=0), MIN_I32)    # sign-extends
m.write_i64(X, 0x208)
check('ld',        exe(0x0085b503, a1=0x200), X)
check('lwu',       exe(0x0045e503, a1=0x204), 0x9abcdef0)  # no sign-ext
exe(0xfec5bc23, a1=0x308, a2=-2); check('sd', m.read_i64(0x300), -2)

# illegal on RV64: slliw with shamt[5] set; illegal on RV32: everything RV64-only
def illegal(mach, word):
  mach.clear_cpu(); mach.write_i32(word, 0)
  try: mach.step()
  except ValueError: return
  raise AssertionError('%08x should be illegal' % word)
illegal(m, 0x0205951b)  # slliw a0,a1,32 (bit 25 set)
m32 = machine(mem_size=4096)
for w in (0x02859513, 0x03f5d513, 0x4215d513, 0xfff5851b, 0x00c5853b,
          0x02c5853b, 0x0085b503, 0xfec5bc23, 0x0045e503):
  illegal(m32, w)

print('tests64 PASS')
