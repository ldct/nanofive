"""Build the RV64IM fixture, check its Lean code image, and run it in NanoFive."""
import contextlib
import hashlib
import io
import os
from pathlib import Path
import re
import struct
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from elf import load_elf
from machine import machine64

ELF = HERE / 'build/tweetnacl.elf'
MEM_SIZE = 1 << 20
RETURN = 0x70000
LEFT, RIGHT = 0x80000, 0x80100


def fresh():
  m = machine64(mem_size=MEM_SIZE)
  entry = load_elf(m, ELF)
  return m, entry


def run_call(m, entry, args, fuel):
  m.x[1], m.x[2] = RETURN, MEM_SIZE
  for register, value in enumerate(args, 10):
    m.x[register] = value
  m.run(entry, end=RETURN, steps=fuel)


def check_lean_image(m, symbols, source, symbol, entry_def, words_def):
  entry = re.search(rf'^def {entry_def} : Nat :=\s*(0x[0-9a-fA-F]+|[0-9]+)\b',
                    source, re.M)
  words = re.search(rf'^def {words_def} : List \(BitVec 32\) :=\s*\[(.*?)\]',
                    source, re.M | re.S)
  assert entry and words, f'{symbol}: missing Lean image definitions'
  literals = re.sub(r'--[^\n]*', '', words[1]).strip().removesuffix(',').split(',')
  image = b''.join(int(word.strip(), 0).to_bytes(4, 'little') for word in literals)
  address, size = symbols[symbol]
  assert address == int(entry[1], 0) and size == len(image), (
    f'{symbol}: Lean symbol address or size differs')
  assert m.mem[address:address + size] == image, f'{symbol}: Lean instruction words differ'
  return address


def salsa20_reference(block_input, key, constant):
  """Salsa20's column/row double round, with arithmetic modulo 2**32."""
  state = struct.unpack('<16I', constant[:4] + key[:16] + constant[4:8] +
                        block_input + constant[8:12] + key[16:] + constant[12:])
  x = list(state)
  mask = 0xffffffff

  def rotl(value, count):
    value &= mask
    return ((value << count) | (value >> (32 - count))) & mask

  def quarter(a, b, c, d):
    x[b] ^= rotl(x[a] + x[d], 7)
    x[c] ^= rotl(x[b] + x[a], 9)
    x[d] ^= rotl(x[c] + x[b], 13)
    x[a] ^= rotl(x[d] + x[c], 18)

  for _ in range(10):
    quarter(0, 4, 8, 12)
    quarter(5, 9, 13, 1)
    quarter(10, 14, 2, 6)
    quarter(15, 3, 7, 11)
    quarter(0, 1, 2, 3)
    quarter(5, 6, 7, 4)
    quarter(10, 11, 8, 9)
    quarter(15, 12, 13, 14)
  return struct.pack('<16I', *((a + b) & mask for a, b in zip(x, state)))


def test_salsa20(m, symbols):
  source = (HERE / 'lean/TweetNaCl/Salsa20Program.lean').read_text()
  core = check_lean_image(m, symbols, source, 'core', 'coreEntry', 'coreWords')
  wrapper = check_lean_image(m, symbols, source, 'crypto_core_salsa20_tweet',
                             'entry', 'wrapperWords')
  sigma = b'expand 32-byte k'
  # Bernstein, Salsa20 specification (2005-04-27), section 9, first example.
  vector = (bytes(range(101, 117)), bytes(range(1, 17)) + bytes(range(201, 217)), sigma)
  known_output = bytes.fromhex(
    '45254427290f6bc1ff8b7a06aae9d9625990b66a1533c841ef31de22d772287e'
    '68c507e1c5991f02664e4cb054f5f6b8b1a0858206489577c0c384ecea67f64a')
  assert salsa20_reference(*vector) == known_output, 'Salsa20 reference fails known vector'

  cases = [
    ('spec vector', *vector),
    ('all zero', bytes(16), bytes(32), bytes(16)),
    ('all ones', b'\xff' * 16, b'\xff' * 32, b'\xff' * 16),
    ('high bits', b'\x00\x00\x00\x80' * 4, b'\xaa\x55' * 16, b'\x55\xaa' * 8),
    ('counter max', bytes(range(8)) + b'\xff' * 8, bytes(range(32)), sigma),
  ]
  for i in range(8):
    block = hashlib.sha512(f'Salsa20 differential case {i}'.encode()).digest()
    cases.append((f'deterministic {i}', block[:16], block[16:48], block[48:]))

  for name, block_input, key, constant in cases:
    expected = salsa20_reference(block_input, key, constant)
    # Measured by counting step() calls and tracking the lowest SP.
    for entry, extra_args, fuel, stack_bytes in (
        (core, [0], 11_541, 512), (wrapper, [], 11_550, 528)):
      label = f'Salsa20 {name} at {entry:#x}'
      m, _ = fresh()
      offset = 0 if name == 'spec vector' else 1  # Byte buffers need no alignment.
      out, inp, key_addr, const_addr = (addr + offset for addr in
                                        (LEFT, RIGHT, 0x80200, 0x80300))
      for addr, data in ((inp, block_input), (key_addr, key), (const_addr, constant)):
        m.mem[addr:addr + len(data)] = data
      out_end = out + len(expected)
      m.mem[out:out_end] = bytes(b ^ 0xff for b in expected)
      stack_bottom = MEM_SIZE - stack_bytes
      before = bytes(m.mem[:stack_bottom])
      m.x[14] = 1  # The wrapper must supply h=0 itself; the direct call passes it.
      run_call(m, entry, [out, inp, key_addr, const_addr, *extra_args], fuel)
      assert not m.halted and m.pc == RETURN and m.x[2] == MEM_SIZE, f'{label}: bad return'
      if entry == wrapper:
        assert m.x[10] == 0, f'{label}: wrapper returned nonzero'
      assert m.mem[out:out_end] == expected, f'{label}: output differs'
      assert m.mem[:out] == before[:out] and m.mem[out_end:stack_bottom] == before[out_end:], (
        f'{label}: wrote outside output and stack')
  return cases


def hsalsa20_reference(block_input, key, constant):
  """HSalsa20: the Salsa20 rounds without feed-forward, then words 0, 5, 10, 15, 6-9."""
  state = salsa20_reference(block_input, key, constant)
  words = struct.unpack('<16I', state)
  initial = struct.unpack('<16I', constant[:4] + key[:16] + constant[4:8] + block_input +
                          constant[8:12] + key[16:] + constant[12:])
  mixed = [(word - start) & 0xffffffff for word, start in zip(words, initial)]
  return struct.pack('<8I', *(mixed[i] for i in (0, 5, 10, 15, 6, 7, 8, 9)))


def test_hsalsa20(m, symbols, cases):
  """Run `crypto_core_hsalsa20_tweet` under the assumptions of `hsalsa20_correct`."""
  source = (HERE / 'lean/TweetNaCl/HSalsa20Program.lean').read_text()
  wrapper = check_lean_image(m, symbols, source, 'crypto_core_hsalsa20_tweet',
                             'entry', 'wrapperWords')
  sigma = b'expand 32-byte k'
  # NaCl tests/core1.c and core2.c: the subkeys of crypto_box's example.
  shared = bytes.fromhex('4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742')
  first = bytes.fromhex('1b27556473e985d462cd51197a9a46c76009549eac6474f206c4ee0844f68389')
  nonce = bytes.fromhex('69696ee955b62b73cd62bda875fc73d6')
  second = bytes.fromhex('dc908dda0b9344a953629b733820778880f3ceb421bb61b91cbd4c3e66256ce4')
  assert hsalsa20_reference(bytes(16), shared, sigma) == first, 'HSalsa20 reference fails core1'
  assert hsalsa20_reference(nonce, first, sigma) == second, 'HSalsa20 reference fails core2'
  cases = [('core1', bytes(16), shared, sigma), ('core2', nonce, first, sigma), *cases]
  for name, block_input, key, constant in cases:
    expected = hsalsa20_reference(block_input, key, constant)
    label = f'HSalsa20 {name}'
    m, _ = fresh()
    out, inp, key_addr, const_addr = LEFT, RIGHT, 0x80200, 0x80300
    for addr, data in ((inp, block_input), (key_addr, key), (const_addr, constant)):
      m.mem[addr:addr + len(data)] = data
    out_end = out + len(expected)
    m.mem[out:out_end] = bytes(b ^ 0xff for b in expected)
    stack_bottom = MEM_SIZE - 528
    before = bytes(m.mem[:stack_bottom])
    m.x[14] = 0  # The wrapper must supply h=1 itself.
    run_call(m, wrapper, [out, inp, key_addr, const_addr], 11_514)
    assert not m.halted and m.pc == RETURN and m.x[2] == MEM_SIZE, f'{label}: bad return'
    assert m.x[10] == 0, f'{label}: wrapper returned nonzero'
    assert m.mem[out:out_end] == expected, f'{label}: output differs'
    assert m.mem[:out] == before[:out] and m.mem[out_end:stack_bottom] == before[out_end:], (
      f'{label}: wrote outside output and stack')
  return cases


def lean_words(source, name):
  words = re.search(rf'^def {name} : List \(BitVec 32\) :=\s*\[(.*?)\]', source, re.M | re.S)
  assert words, f'missing Lean definition {name}'
  literals = re.sub(r'--[^\n]*', '', words[1]).strip().removesuffix(',').split(',')
  return [int(word.strip(), 0) for word in literals]


def test_salsa20_io(cases):
  """Run the stand-alone program of `Salsa20IOProgram.lean` on standard input."""
  lean = HERE / 'lean/TweetNaCl'
  core = (lean / 'Salsa20Program.lean').read_text()
  driver = (lean / 'Salsa20IOProgram.lean').read_text()
  prog = ([0x1700106f] + [0] * 11 + lean_words(core, 'coreWords') + [0] * 840 +
          lean_words(core, 'wrapperWords') + lean_words(driver, 'driverWords'))
  assert len(prog) == 1149 and 4 * prog.index(0x00100137) == 0x1170
  for name, block_input, key, constant in cases:
    m = machine64(mem_size=MEM_SIZE)
    for i, word in enumerate(prog):
      m.write_i32(word, 4 * i)
    stdin, stdout = sys.stdin, io.StringIO()
    sys.stdin = io.StringIO(''.join(map(chr, block_input + key + constant)))
    try:
      with contextlib.redirect_stdout(stdout):
        m.run(0, steps=12_090)
    finally:
      sys.stdin = stdin
    expected = ''.join(map(chr, salsa20_reference(block_input, key, constant)))
    assert m.halted and m.exit_code == 0, f'Salsa20 program {name}: did not exit 0'
    assert stdout.getvalue() == expected, f'Salsa20 program {name}: output differs'


def test_hsalsa20_io(cases):
  """Run the stand-alone program of `HSalsa20IOProgram.lean` on standard input."""
  lean = HERE / 'lean/TweetNaCl'
  core = (lean / 'Salsa20Program.lean').read_text()
  wrapper = (lean / 'HSalsa20Program.lean').read_text()
  driver = (lean / 'HSalsa20IOProgram.lean').read_text()
  prog = ([0x1940106f] + [0] * 11 + lean_words(core, 'coreWords') + [0] * 849 +
          lean_words(wrapper, 'wrapperWords') + lean_words(driver, 'driverWords'))
  assert len(prog) == 1158 and 4 * prog.index(0x00100137) == 0x1194
  for name, block_input, key, constant in cases:
    m = machine64(mem_size=MEM_SIZE)
    for i, word in enumerate(prog):
      m.write_i32(word, 4 * i)
    stdin, stdout = sys.stdin, io.StringIO()
    sys.stdin = io.StringIO(''.join(map(chr, block_input + key + constant)))
    try:
      with contextlib.redirect_stdout(stdout):
        m.run(0, steps=11_926)
    finally:
      sys.stdin = stdin
    expected = ''.join(map(chr, hsalsa20_reference(block_input, key, constant)))
    assert m.halted and m.exit_code == 0, f'HSalsa20 program {name}: did not exit 0'
    assert stdout.getvalue() == expected, f'HSalsa20 program {name}: output differs'


def main():
  subprocess.run([HERE / 'build.sh'], check=True)
  tool = os.environ.get('CROSS_COMPILE') or 'riscv64-unknown-elf-'
  symbols = {}
  for line in subprocess.check_output([tool + 'nm', '-S', '--defined-only', ELF],
                                      text=True).splitlines():
    fields = line.split()
    if len(fields) == 4:
      address, size, _, name = fields
      symbols[name] = int(address, 16), int(size, 16)

  m, entry = fresh()
  m.run(entry, steps=1000)
  assert m.halted and m.exit_code == 0, 'ELF smoke test failed'

  source = (HERE / 'lean/TweetNaCl/Verify32Program.lean').read_text()
  verify = check_lean_image(m, symbols, source, 'crypto_verify_32_tweet', 'entry', 'prog')
  salsa_cases = test_salsa20(m, symbols)
  test_salsa20_io(salsa_cases)
  hsalsa_cases = test_hsalsa20(m, symbols, salsa_cases)
  test_hsalsa20_io(hsalsa_cases)

  left = bytes(range(32))
  cases = [(RIGHT, left), (LEFT, left)]
  cases += [(RIGHT, left[:i] + bytes([left[i] ^ 0xff]) + left[i + 1:]) for i in range(32)]
  for right_addr, right in cases:
    m, _ = fresh()
    m.mem[LEFT:LEFT + 32] = left
    m.mem[right_addr:right_addr + 32] = right
    before = bytes(m.mem)
    run_call(m, verify, [LEFT, right_addr], 231)
    assert not m.halted and m.pc == RETURN and m.x[2] == MEM_SIZE
    assert m.x[10] == (0 if left == right else -1)
    assert m.mem == before

  hash_entry, _ = symbols['crypto_hash_sha512_tweet']
  messages = [b'abc'] + [bytes(range(n)) for n in (0, 111, 112, 127, 128, 255)]
  for message in messages:
    m, _ = fresh()
    m.mem[LEFT:LEFT + len(message)] = message
    run_call(m, hash_entry, [RIGHT, LEFT, len(message)], 100_000)
    assert not m.halted and m.pc == RETURN and m.x[2] == MEM_SIZE
    assert m.x[10] == 0
    assert m.mem[RIGHT:RIGHT + 64] == hashlib.sha512(message).digest()

  keypair, _ = symbols['crypto_box_curve25519xsalsa20poly1305_tweet_keypair']
  m, _ = fresh()
  run_call(m, keypair, [LEFT, RIGHT], 1000)
  assert m.halted and m.exit_code == 125, 'key generation must fail without entropy'
  print(f'TweetNaCl RV64IM: ELF and Lean code match; {len(cases)} verify and '
        f'{len(messages)} SHA-512 cases passed; {len(salsa_cases)} Salsa20 cases passed at '
        f'both entry points and as a program; {len(hsalsa_cases)} HSalsa20 cases passed as a '
        'call and as a program; key generation fails closed.')


if __name__ == '__main__':
  main()
