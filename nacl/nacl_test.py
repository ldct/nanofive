"""Check the Lean image of NaCl's Salsa20 core against the ELF, and run it in NanoFive.

Build the ELF first with nacl/build.sh (it needs riscv64-unknown-elf-gcc). The test runs the
call `crypto_core_salsa20_ref` and the whole program of `start.S` on standard input, and
compares both with an independent Salsa20 reference.
"""
import contextlib
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


def salsa20_reference(block_input, key, constant):
  """Salsa20/20 core: column and row rounds modulo 2**32, then feed-forward."""
  state = struct.unpack('<16I', constant[:4] + key[:16] + constant[4:8] +
                        block_input + constant[8:12] + key[16:] + constant[12:])
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
  return struct.pack('<16I', *((a + b) & mask for a, b in zip(x, state)))


def elf_symbols_and_text():
  """The symbol table and the .text bytes of the ELF, which must start at address 0."""
  data = ELF.read_bytes()
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
  symbols, text = elf_symbols_and_text()
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


def test_call(name, block_input, key, constant):
  """Run `crypto_core_salsa20_ref` alone, under the assumptions of `Call.salsa20_correct`."""
  m = machine64(mem_size=MEM_SIZE)
  entry, _ = elf_symbols_and_text()[0]['crypto_core_salsa20_ref']
  load_elf(m, ELF)
  for addr, data in ((INP, block_input), (KEY, key), (CONST, constant)):
    m.mem[addr:addr + len(data)] = data
  expected = salsa20_reference(block_input, key, constant)
  m.mem[OUT:OUT + 64] = bytes(b ^ 0xff for b in expected)
  m.x[1], m.x[2] = RETURN, MEM_SIZE
  for register, value in enumerate((OUT, INP, KEY, CONST), 10):
    m.x[register] = value
  before = bytes(m.mem)
  m.pc, steps = entry, 0
  while m.pc != RETURN and not m.halted and steps < CALL_STEPS:
    m.step()
    steps += 1
  label = f'call, {name}'
  assert not m.halted and m.pc == RETURN and steps == CALL_STEPS, f'{label}: bad return'
  assert m.x[10] == 0 and m.x[2] == MEM_SIZE, f'{label}: bad a0 or sp'
  assert m.mem[OUT:OUT + 64] == expected, f'{label}: output differs'
  stack = MEM_SIZE - FRAME_BYTES
  assert m.mem[:OUT] == before[:OUT] and m.mem[OUT + 64:stack] == before[OUT + 64:stack], (
    f'{label}: wrote outside the output and the stack frame')


def test_program(prog, name, block_input, key, constant):
  """Run the machine `initial` of `Program.lean` on standard input."""
  m = machine64(mem_size=MEM_SIZE)
  for i, word in enumerate(prog):
    m.write_i32(word, 4 * i)
  stdin, stdout = sys.stdin, io.StringIO()
  sys.stdin = io.StringIO(''.join(map(chr, block_input + key + constant)))
  try:
    with contextlib.redirect_stdout(stdout):
      m.run(0, steps=PROGRAM_STEPS)
  finally:
    sys.stdin = stdin
  expected = ''.join(map(chr, salsa20_reference(block_input, key, constant)))
  assert m.halted and m.exit_code == 0, f'program, {name}: did not exit 0'
  assert stdout.getvalue() == expected, f'program, {name}: output differs'


def main():
  assert ELF.exists(), f'{ELF} is missing: run nacl/build.sh first'
  prog = check_lean_image()
  all_cases = cases()
  for case in all_cases:
    test_call(*case)
    test_program(prog, *case)
  print(f'NaCl Salsa20 RV64IM: ELF and Lean code match; {len(all_cases)} cases passed as a call '
        f'({CALL_STEPS} steps) and as a program on standard input.')


if __name__ == '__main__':
  main()
