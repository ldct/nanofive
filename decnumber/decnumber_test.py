"""Cross-build jq's decNumber, differential-test it, and check the Lean links."""
import argparse
import contextlib
from collections import Counter
from decimal import Context, Decimal, Inexact, ROUND_HALF_EVEN, Rounded
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))
from elf import load_elf
from machine import machine64

PIN = '34f7186b86743a083a589741b6cea95293524108'  # jq-1.8.2
TOOL = 'riscv64-unknown-elf-'
MEM_SIZE = 1 << 20
# Instruction words used by lean/DecContextClear.lean.
CLEAR_WORDS = (0x01452703, 0xfff5c593, 0x00b77733, 0x00e52a23, 0x00008067)


def vectors():
  rng = random.Random(642)
  def literal():
    coefficient = ''.join(str(rng.randrange(10)) for _ in range(rng.randint(1, 160)))
    point = rng.randrange(len(coefficient) + 1)
    return rng.choice(['', '-']) + coefficient[:point] + '.' + coefficient[point:] + 'e' + str(rng.randint(-200, 200))

  parses = ['0', '-0.000', '+000.00120', '9007199254740993', '1e999999999',
            '1e-999999999', '-Infinity', 'NaN', 'sNaN42', '1e+', '1.2.3',
            '9' * 160, '0.' + '0' * 158 + '1']
  compares = [('9007199254740992', '9007199254740993'), ('-0.000', '0'),
              ('001.200', '12e-1'), ('-3.02', '-3.0201'), ('1e999999999', '1e-999999999'),
              ('9' * 159 + '8', '9' * 160), ('1' + '0' * 159, '1e159'),
              ('1.' + '1' * 159, '1.111')]
  adds = [('0.1', '0.2'), ('99999999999999999', '1'), ('99999999999999999', '-99999999999999999'),
          ('1', '0.00000000000000005'), ('1.0000000000000001', '0.00000000000000005'),
          ('-0.000', '-0'), ('9' * 160, '1'), ('9' * 160, '-' + '9' * 160),
          ('1e100', '1e-100')]
  return ([('p', a, '') for a in parses + [literal() for _ in range(64)]]
          + [('c', a, b) for a, b in compares + [(literal(), literal()) for _ in range(64)]]
          + [('a', a, b) for a, b in adds + [(literal(), literal()) for _ in range(64)]])


def expected(op, a, b):
  status = 0
  if op == 'p':
    if a in ('1e+', '1.2.3'):
      status = 1  # DEC_Conversion_syntax
      result = Decimal('NaN')
    else:
      result = Decimal(a)
  elif op == 'c':
    result = Decimal((Decimal(a) > Decimal(b)) - (Decimal(a) < Decimal(b)))
  else:
    ctx = Context(prec=17, Emin=-999999999, Emax=999999999, rounding=ROUND_HALF_EVEN)
    result = ctx.add(Decimal(a), Decimal(b))
    status = (0x20 if ctx.flags[Inexact] else 0) | (0x800 if ctx.flags[Rounded] else 0)

  sign, digits, exponent = result.as_tuple()
  bits = 0x80 if sign else 0
  if not result.is_finite():
    # NaN payload units are not printed by the harness; do check its text.
    bits |= 0x40 if result.is_infinite() else 0x10 if result.is_snan() else 0x20
    return (str(result), status, max(1, len(digits)) if result.is_nan() else 1, 0, bits)
  coefficient = ''.join(map(str, digits))
  units = tuple(int(coefficient[max(0, i-3):i]) for i in range(len(coefficient), 0, -3))
  return (str(result), status, len(digits), exponent, bits, *units)


def build(jq, tmp, cases):
  source = jq / 'vendor' / 'decNumber'
  asm = ROOT / 'asm'
  vendor = ROOT / 'newlib' / 'vendor'
  arch = ['-march=rv64im', '-mabi=lp64', '-mcmodel=medany', '-O2']
  includes = ['-isystem', vendor / 'build/targ-include', '-isystem', vendor / 'libc/include',
              '-I', vendor / 'build', '-I', vendor, '-I', HERE / 'include', '-I', source, '-I', tmp]
  libc_flags = ['-D_LIBC', '-fno-builtin', '-DHAVE_CONFIG_H', '-DHAVE_NANOSLEEP',
                '-D__SINGLE_THREAD__', '-D__NO_SYSCALLS__', '-DNO_FLOATING_POINT', '-w']
  (tmp / 'cases.h').write_text('static const struct { char op; const char *a, *b; } cases[] = {\n'
    + ''.join(f"  {{'{op}', {json.dumps(a)}, {json.dumps(b)}}},\n" for op, a, b in cases) + '};\n')
  def compile(src, output, flags):
    subprocess.run([TOOL + 'gcc', *arch, *includes, *flags, '-c', src, '-o', output], check=True)

  libc = (vendor / 'SOURCES').read_text().split()
  objects = []
  dec_objects = []
  for i, (src, flags) in enumerate(
      [(vendor / f, libc_flags) for f in libc] +
      [(source / f, ['-DDECNUMDIGITS=1']) for f in ('decNumber.c', 'decContext.c')]):
    obj = tmp / f'{i}.o'
    compile(src, obj, ['-ffunction-sections', '-fdata-sections', *flags])
    objects.append(obj)
    if i >= len(libc):
      dec_objects.append(obj)
  elf = tmp / 'decnumber.elf'
  subprocess.run([TOOL + 'gcc', *arch, *includes, '-fno-builtin', '-nostdlib', '-nostartfiles',
      '-T', asm / 'link.ld', '-Wl,--gc-sections,--no-warn-rwx-segments',
      asm / 'crt0.S', asm / 'syscalls.c', HERE / 'harness.c', *objects, '-lgcc', '-o', elf], check=True)
  return elf, dec_objects


def text_symbols(*paths):
  output = subprocess.check_output([TOOL + 'nm', '-S', '--defined-only', *paths], text=True)
  for line in output.splitlines():
    fields = line.split()
    if len(fields) == 4 and fields[2] in ('T', 't'):
      addr, size, _, name = fields
      yield int(addr, 16), int(size, 16), name


def check_lean_decode(words):
  """Use TinyFive.decode itself, not a duplicate Python instruction classifier."""
  result = subprocess.run(['lake', 'exe', 'decnumber_decode'], cwd=ROOT,
                          input=''.join(f'{word}\n' for word in sorted(set(words))),
                          stdout=subprocess.PIPE, text=True, check=True)
  missing = {int(line) for line in result.stdout.splitlines()}
  if missing:
    raise AssertionError('Lean cannot decode exercised library words: '
                         + ', '.join(f'{word:08x}' for word in sorted(missing)))


def run(elf, dec_objects):
  m = machine64(mem_size=MEM_SIZE)
  m.pc = load_elf(m, elf)
  names = {name for _, _, name in text_symbols(*dec_objects)}
  linked = list(text_symbols(elf))
  addr, size = next((addr, size) for addr, size, name in linked if name == 'decContextClearStatus')
  words = tuple(m.read_i32(pc) & 0xffffffff for pc in range(addr, addr + size, 4))
  if words != CLEAR_WORDS:
    raise AssertionError(f'decContextClearStatus differs from the Lean proof: '
                         f'{", ".join(hex(word) for word in words)}')
  symbols = {pc: name for addr, size, name in linked if name in names
             for pc in range(addr, addr + size, 4)}
  out = io.StringIO()
  pcs = set()
  with contextlib.redirect_stdout(out):
    for steps in range(1, 10_000_001):
      pcs.add(m.pc)
      m.step()
      if m.halted:
        break
    else:
      raise RuntimeError(f'instruction budget exceeded at {m.pc:#x}')
  if m.exit_code != 0:
    raise RuntimeError(f'emulated harness exited {m.exit_code}')
  library_pcs = pcs & symbols.keys()
  check_lean_decode(m.read_i32(pc) & 0xffffffff for pc in library_pcs)
  return out.getvalue().splitlines(), steps, len(library_pcs), len({symbols[pc] for pc in library_pcs})


def main():
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument('--jq', type=Path, help='use an existing jq checkout instead of fetching the pin')
  parser.add_argument('--elf', type=Path, help='retain a copy of the ELF at this path')
  args = parser.parse_args()
  cases = vectors()
  with tempfile.TemporaryDirectory() as directory:
    tmp = Path(directory)
    jq = args.jq or tmp / 'jq'
    if args.jq is None:
      subprocess.run(['git', 'init', '-q', jq], check=True)
      subprocess.run(['git', '-C', jq, 'fetch', '-q', '--depth=1', 'https://github.com/jqlang/jq.git', PIN], check=True)
      subprocess.run(['git', '-C', jq, 'checkout', '-q', '--detach', 'FETCH_HEAD'], check=True)
    elf, dec_objects = build(jq, tmp, cases)
    if args.elf:
      args.elf.write_bytes(elf.read_bytes())
    lines, steps, sites, functions = run(elf, dec_objects)
  if len(lines) != len(cases):
    raise RuntimeError(f'expected {len(cases)} output records, got {len(lines)}')
  for case, line in zip(cases, lines):
    s, status, digits, exponent, bits, *units = line.split('\t')
    got = (s, int(status, 16), int(digits), int(exponent), int(bits, 16), *map(int, units))
    want = expected(*case)
    if got != want:
      raise AssertionError(f'{case}: got {got}, expected {want}')
  counts = Counter(op for op, _, _ in cases)
  print(f'PASS: {len(cases)} cases ({counts["p"]} parse/format, {counts["c"]} compare, {counts["a"]} add)')
  print(f'{steps:,} instructions, including {sites:,} distinct decNumber/decContext PCs in {functions} symbols')
  print('Lean decoded all exercised library sites')
  print('decContextClearStatus: ELF words match the Lean proof')


if __name__ == '__main__':
  main()
