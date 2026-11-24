"""Check the Lean images of NaCl's Salsa20 and HSalsa20 cores against the ELFs, and run them.

Build the ELF first with nacl/build.sh (it needs riscv64-unknown-elf-gcc). The test runs the
call `crypto_core_salsa20_ref` and the whole program of `start.S` on standard input, and compares both
with an independent Salsa20 reference; likewise `crypto_core_hsalsa20_ref` and `start_hsalsa20.S`
against HSalsa20.
"""
import contextlib
import collections
import hashlib
import io
from pathlib import Path
import re
import struct
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from elf import load_elf
from machine import machine64

ELF = HERE / 'build/nacl_salsa20.elf'
LEAN = HERE / 'lean/NaClSalsa20/Program.lean'
MEM_SIZE = 1 << 20
OUT, INP, KEY, CONST = 0x80000, 0x80100, 0x80200, 0x80300
RETURN = 0x4c          # the driver's return address, after its call
CALL_STEPS = 2316      # `Call.steps`
PROGRAM_STEPS = 2855   # the fuel of `IO.isCorrect`
FRAME_BYTES = 432      # `Call.frameBytes`
HSALSA20_ELF = HERE / 'build/nacl_hsalsa20.elf'
HSALSA20_LEAN = HERE / 'lean/NaClSalsa20/HSalsa20Program.lean'

# A linked function under test: its ELF, symbol, `Call.steps`, `Call.frameBytes`, the fuel of
# `IO.isCorrect`, and the independent reference it must match.
Target = collections.namedtuple(
  'Target', 'label elf symbol call_steps frame_bytes program_steps reference')


def salsa20_state(block_input, key, constant):
  return struct.unpack('<16I', constant[:4] + key[:16] + constant[4:8] +
                       block_input + constant[8:12] + key[16:] + constant[12:])


def salsa20_rounds(state):
  """The twenty Salsa20 rounds, column and row, modulo 2**32."""
  x = list(state)
  mask = 0xffffffff

  def rotl(value, count):
    return ((value << count) | (value >> (32 - count))) & mask

  def quarter(a, b, c, d):
    x[b] ^= rotl((x[a] + x[d]) & mask, 7)
    x[c] ^= rotl((x[b] + x[a]) & mask, 9)
    x[d] ^= rotl((x[c] + x[b]) & mask, 13)
    x[a] ^= rotl((x[d] + x[c]) & mask, 18)

  for _ in range(10):
    for a, b, c, d in ((0, 4, 8, 12), (5, 9, 13, 1), (10, 14, 2, 6), (15, 3, 7, 11),
                       (0, 1, 2, 3), (5, 6, 7, 4), (10, 11, 8, 9), (15, 12, 13, 14)):
      quarter(a, b, c, d)
  return x


def salsa20_reference(block_input, key, constant):
  """Salsa20/20 core: the rounds, then feed-forward."""
  state = salsa20_state(block_input, key, constant)
  return struct.pack('<16I', *((a + b) & 0xffffffff
                               for a, b in zip(salsa20_rounds(state), state)))


def hsalsa20_reference(block_input, key, constant):
  """HSalsa20: the rounds without feed-forward, then words 0, 5, 10, 15, 6, 7, 8, 9."""
  x = salsa20_rounds(salsa20_state(block_input, key, constant))
  return struct.pack('<8I', *(x[i] for i in (0, 5, 10, 15, 6, 7, 8, 9)))


def elf_symbols_and_text(elf):
  """The symbol table and the .text bytes of the ELF, which must start at address 0."""
  data = elf.read_bytes()
  shoff, = struct.unpack_from('<Q', data, 40)
  shentsize, shnum, shstrndx = struct.unpack_from('<HHH', data, 58)
  sections = [struct.unpack_from('<IIQQQQIIQQ', data, shoff + i * shentsize)
              for i in range(shnum)]

  def name(offset, table):
    return data[table + offset:data.index(b'\0', table + offset)].decode()

  by_name = {name(section[0], sections[shstrndx][4]): section for section in sections}
  text, symtab, strtab = by_name['.text'], by_name['.symtab'], by_name['.strtab']
  assert text[3] == 0, '.text must start at address 0'
  symbols = {}
  for offset in range(symtab[4], symtab[4] + symtab[5], 24):
    st_name, _, _, _, value, size = struct.unpack_from('<IBBHQQ', data, offset)
    symbols[name(st_name, strtab[4])] = value, size
  return symbols, data[text[4]:text[4] + text[5]]


def lean_words(source, name):
  words = re.search(rf'^def {name} : List \(BitVec 32\) :=\s*\[(.*?)\]', source, re.M | re.S)
  assert words, f'missing Lean definition {name}'
  return [int(word, 0) for word in re.sub(r'--[^\n]*', '', words[1]).split(',')]


def check_lean_image():
  """The Lean `prog` is the ELF's .text, and `coreEntry` is the function's address."""
  symbols, text = elf_symbols_and_text(ELF)
  source = LEAN.read_text()
  driver, core = lean_words(source, 'driverWords'), lean_words(source, 'coreWords')
  entry = int(re.search(r'^def coreEntry : Nat := (0x[0-9a-f]+)', source, re.M)[1], 0)
  address, size = symbols['crypto_core_salsa20_ref']
  assert (address, size) == (entry, 4 * len(core)) == (4 * len(driver), len(text) - entry), (
    'Lean entry or sizes differ from the ELF')
  assert b''.join(w.to_bytes(4, 'little') for w in driver + core) == text, (
    'Lean words differ from the ELF')
  assert symbols['readn'][0] == 0x70 and symbols['print'][0] == 0x58, 'driver layout moved'
  return driver + core


def check_hsalsa20_image():
  """The Lean HSalsa20 `prog` is the HSalsa20 ELF's .text, with `coreEntry` at the function."""
  symbols, text = elf_symbols_and_text(HSALSA20_ELF)
  source = HSALSA20_LEAN.read_text()
  driver, core = lean_words(source, 'driverWords'), lean_words(source, 'coreWords')
  entry = int(re.search(r'^def coreEntry : Nat := (0x[0-9a-f]+)', source, re.M)[1], 0)
  address, size = symbols['crypto_core_hsalsa20_ref']
  assert (address, size) == (entry, 4 * len(core)) == (4 * len(driver), len(text) - entry), (
    'HSalsa20 Lean entry or sizes differ from the ELF')
  assert b''.join(w.to_bytes(4, 'little') for w in driver + core) == text, (
    'HSalsa20 Lean words differ from the ELF')
  assert symbols['readn'][0] == 0x70 and symbols['print'][0] == 0x58, 'driver layout moved'
  return driver + core


def hsalsa20_cases():
  sigma = b'expand 32-byte k'
  # NaCl tests/core1.c and core2.c: the subkeys of crypto_box's example.
  shared = bytes.fromhex('4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742')
  first = bytes.fromhex('1b27556473e985d462cd51197a9a46c76009549eac6474f206c4ee0844f68389')
  nonce = bytes.fromhex('69696ee955b62b73cd62bda875fc73d6')
  second = bytes.fromhex('dc908dda0b9344a953629b733820778880f3ceb421bb61b91cbd4c3e66256ce4')
  assert hsalsa20_reference(bytes(16), shared, sigma) == first, 'HSalsa20 reference fails core1'
  assert hsalsa20_reference(nonce, first, sigma) == second, 'HSalsa20 reference fails core2'
  return [('core1', bytes(16), shared, sigma), ('core2', nonce, first, sigma), *cases()]


def cases():
  sigma = b'expand 32-byte k'
  # Bernstein, Salsa20 specification (2005-04-27), section 9, first example.
  vector = (bytes(range(101, 117)), bytes(range(1, 17)) + bytes(range(201, 217)), sigma)
  known_output = bytes.fromhex(
    '45254427290f6bc1ff8b7a06aae9d9625990b66a1533c841ef31de22d772287e'
    '68c507e1c5991f02664e4cb054f5f6b8b1a0858206489577c0c384ecea67f64a')
  assert salsa20_reference(*vector) == known_output, 'Salsa20 reference fails the spec vector'
  result = [
    ('spec vector', *vector),
    ('all zero', bytes(16), bytes(32), bytes(16)),
    ('all ones', b'\xff' * 16, b'\xff' * 32, b'\xff' * 16),
    ('high bits', b'\x00\x00\x00\x80' * 4, b'\xaa\x55' * 16, b'\x55\xaa' * 8),
    ('counter max', bytes(range(8)) + b'\xff' * 8, bytes(range(32)), sigma),
  ]
  for i in range(8):
    block = hashlib.sha512(f'NaCl Salsa20 case {i}'.encode()).digest()
    result.append((f'deterministic {i}', block[:16], block[16:48], block[48:]))
  return result


def test_call(target, name, block_input, key, constant):
  """Run the target function alone, under the assumptions of its `Call` theorem."""
  m = machine64(mem_size=MEM_SIZE)
  entry, _ = elf_symbols_and_text(target.elf)[0][target.symbol]
  load_elf(m, target.elf)
  for addr, data in ((INP, block_input), (KEY, key), (CONST, constant)):
    m.mem[addr:addr + len(data)] = data
  expected = target.reference(block_input, key, constant)
  out_end = OUT + len(expected)
  m.mem[OUT:out_end] = bytes(b ^ 0xff for b in expected)
  m.x[1], m.x[2] = RETURN, MEM_SIZE
  for register, value in enumerate((OUT, INP, KEY, CONST), 10):
    m.x[register] = value
  before = bytes(m.mem)
  m.pc, steps = entry, 0
  while m.pc != RETURN and not m.halted and steps < target.call_steps:
    m.step()
    steps += 1
  label = f'{target.label} call, {name}'
  assert not m.halted and m.pc == RETURN and steps == target.call_steps, f'{label}: bad return'
  assert m.x[10] == 0 and m.x[2] == MEM_SIZE, f'{label}: bad a0 or sp'
  assert m.mem[OUT:out_end] == expected, f'{label}: output differs'
  stack = MEM_SIZE - target.frame_bytes
  assert m.mem[:OUT] == before[:OUT] and m.mem[out_end:stack] == before[out_end:stack], (
    f'{label}: wrote outside the output and the stack frame')


def test_program(target, prog, name, block_input, key, constant):
  """Run the target's machine `initial`, whose words are `prog`, on standard input."""
  m = machine64(mem_size=MEM_SIZE)
  for i, word in enumerate(prog):
    m.write_i32(word, 4 * i)
  stdin, stdout = sys.stdin, io.StringIO()
  sys.stdin = io.StringIO(''.join(map(chr, block_input + key + constant)))
  try:
    with contextlib.redirect_stdout(stdout):
      m.run(0, steps=target.program_steps)
  finally:
    sys.stdin = stdin
  expected = ''.join(map(chr, target.reference(block_input, key, constant)))
  label = f'{target.label} program, {name}'
  assert m.halted and m.exit_code == 0, f'{label}: did not exit 0'
  assert stdout.getvalue() == expected, f'{label}: output differs'


def main():
  assert ELF.exists(), f'{ELF} is missing: run nacl/build.sh first'
  salsa20 = Target('Salsa20', ELF, 'crypto_core_salsa20_ref', CALL_STEPS, FRAME_BYTES, PROGRAM_STEPS,
                   salsa20_reference)
  hsalsa20 = Target('HSalsa20', HSALSA20_ELF, 'crypto_core_hsalsa20_ref', 2176, 432, 2587,
                    hsalsa20_reference)
  runs = [(salsa20, check_lean_image(), cases()), (hsalsa20, check_hsalsa20_image(), hsalsa20_cases())]
  for target, prog, target_cases in runs:
    for case in target_cases:
      test_call(target, *case)
      test_program(target, prog, *case)
  print(f'NaCl RV64IM: ELF and Lean code match; {len(runs[0][2])} Salsa20 and '
        f'{len(runs[1][2])} HSalsa20 cases passed as a call and as a program on standard input.')

if __name__ == '__main__':
  main()
