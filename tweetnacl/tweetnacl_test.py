"""Build the RV64IM fixture, check its Lean code image, and run it in NanoFive."""
import hashlib
import os
from pathlib import Path
import re
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

  verify, size = symbols['crypto_verify_32_tweet']
  source = (HERE / 'lean/TweetNaCl/Verify32Program.lean').read_text()
  expected_entry = int(re.search(r'def entry : Nat := (0x[0-9a-f]+)', source)[1], 16)
  words = re.search(r'def prog : List \(BitVec 32\) := \[(.*?)\]', source, re.S)[1]
  image = b''.join(int(word, 16).to_bytes(4, 'little')
                   for word in re.findall(r'0x[0-9a-f]{8}\b', words))
  assert verify == expected_entry and size == len(image), 'Lean symbol address or size differs'
  assert m.mem[verify:verify + size] == image, 'Lean instruction words differ'

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
        f'{len(messages)} SHA-512 cases passed; key generation fails closed.')


if __name__ == '__main__':
  main()
