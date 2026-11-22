"""Check the Lean image of Nettle's Salsa20 core against the ELF, and run it in NanoFive.

Build the ELF first with nettle/build.sh (it needs riscv64-unknown-elf-gcc and picolibc). The
test runs the call `_nettle_salsa20_core` on a 64-byte state and the whole program of `start.S`
on standard input, and compares both with an independent Salsa20 reference.
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

ELF = HERE / 'build/nettle_salsa20.elf'
LEAN = HERE / 'lean/NettleSalsa20/Program.lean'
MEM_SIZE = 1 << 20
DST, SRC, ROUNDS = 0x80000, 0x80100, 20
RETURN = 0x88          # the driver's return address, after its call
CALL_STEPS = 2373      # `Call.steps`
PROGRAM_STEPS = 2931   # the fuel of `IO.isCorrect`
FRAME_BYTES = 192      # `Call.frameBytes`


def initial_state(block_input, key, constant):
  """The 64 bytes of the Salsa20 state, as start.S lays them out."""
  return (constant[:4] + key[:16] + constant[4:8] + block_input + constant[8:12] + key[16:] +
          constant[12:])


def salsa20_reference(block_input, key, constant):
  return salsa20_core_bytes(initial_state(block_input, key, constant))


def salsa20_core_bytes(block):
  """Salsa20/20 core: column and row rounds modulo 2**32, then feed-forward."""
  state = struct.unpack('<16I', block)
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


def elf_symbols_and_image():
  """The symbol table and the loaded image of the ELF, as nettle/gen_lean.py computes them."""
  sys.path.insert(0, str(HERE))
  from gen_lean import symbols_and_image
  return symbols_and_image(ELF.read_bytes())


def lean_words(source, name):
  words = re.search(rf'^def {name} : List \(BitVec 32\) :=\s*\[(.*?)\]', source, re.M | re.S)
  assert words, f'missing Lean definition {name}'
  return [int(word, 0) for word in re.sub(r'--[^\n]*', '', words[1]).split(',')]


def check_lean_image():
  """The Lean `prog` is the ELF's image, and `coreEntry` is the function's address."""
  symbols, image = elf_symbols_and_image()
  source = LEAN.read_text()
  driver, core = lean_words(source, 'driverWords'), lean_words(source, 'coreWords')
  entry = int(re.search(r'^def coreEntry : Nat := (0x[0-9a-f]+)', source, re.M)[1], 0)
  assert symbols['_nettle_salsa20_core'][0] == entry == 4 * len(driver), 'Lean entry differs'
  assert b''.join(w.to_bytes(4, 'little') for w in driver + core) == image, (
    'Lean words differ from the ELF')
  assert symbols['readn'][0] == 0xac and symbols['print'][0] == 0x94, 'driver layout moved'
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
    block = hashlib.sha512(f'Nettle Salsa20 case {i}'.encode()).digest()
    result.append((f'deterministic {i}', block[:16], block[16:48], block[48:]))
  return result


def test_call(name, block):
  """Run `_nettle_salsa20_core` alone, under the assumptions of `Call.salsa20_correct`."""
  m = machine64(mem_size=MEM_SIZE)
  entry, _ = elf_symbols_and_image()[0]['_nettle_salsa20_core']
  load_elf(m, ELF)
  m.mem[SRC:SRC + 64] = block
  expected = salsa20_core_bytes(block)
  m.mem[DST:DST + 64] = bytes(b ^ 0xff for b in expected)
  m.x[1], m.x[2] = RETURN, MEM_SIZE
  m.x[10], m.x[11], m.x[12] = DST, SRC, ROUNDS
  before = bytes(m.mem)
  m.pc, steps = entry, 0
  while m.pc != RETURN and not m.halted and steps < CALL_STEPS:
    m.step()
    steps += 1
  label = f'call, {name}'
  assert not m.halted and m.pc == RETURN and steps == CALL_STEPS, f'{label}: bad return'
  assert m.x[2] == MEM_SIZE, f'{label}: bad sp'
  assert m.mem[DST:DST + 64] == expected, f'{label}: output differs'
  stack = MEM_SIZE - FRAME_BYTES
  assert m.mem[:DST] == before[:DST] and m.mem[DST + 64:stack] == before[DST + 64:stack], (
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
  assert ELF.exists(), f'{ELF} is missing: run nettle/build.sh first'
  prog = check_lean_image()
  all_cases = cases()
  for name, *case in all_cases:
    test_call(name, initial_state(*case))
    test_program(prog, name, *case)
  for i in range(4):
    test_call(f'random state {i}', hashlib.sha512(f'Nettle state {i}'.encode()).digest())
  print(f'Nettle Salsa20 RV64IM: ELF and Lean code match; {len(all_cases)} cases passed as a call '
        f'({CALL_STEPS} steps) and as a program on standard input, 4 random states as a call.')


if __name__ == '__main__':
  main()
