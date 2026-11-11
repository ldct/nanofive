from machine import *
import io, os, struct, subprocess, sys, contextlib

# Run a C program, compiled with gcc against newlib (built for rv32im/ilp32),
# on nanofive. newlib's system calls (newlib/syscalls.c) are mapped onto
# nanofive's RARS-style ecalls (see machine.ECALL): _write prints each byte
# with a7=11, _read uses a7=12, _exit uses a7=93.
#
# Build newlib first (see newlib/README.md); this script then compiles
# newlib/hello.c into newlib/hello.elf, loads its ELF segments into mem[] and
# runs it from the ELF entry point.

HERE     = os.path.dirname(os.path.abspath(__file__))
SRC      = os.path.join(HERE, 'newlib')
PREFIX   = os.path.join(HERE, 'newlib-rv32im', 'riscv64-unknown-elf')
MEM_SIZE = 1 << 20  # must match MEM_SIZE in newlib/link.ld

def build(name):
  elf = os.path.join(SRC, name + '.elf')
  subprocess.run(['riscv64-unknown-elf-gcc', '-march=rv32im', '-mabi=ilp32',
    '-O2', '-nostdlib', '-nostartfiles', '-T', os.path.join(SRC, 'link.ld'),
    '-isystem', os.path.join(PREFIX, 'include'),
    os.path.join(SRC, 'crt0.S'), os.path.join(SRC, name + '.c'),
    os.path.join(SRC, 'syscalls.c'),
    os.path.join(PREFIX, 'lib', 'libc.a'), '-lgcc', '-Wl,--no-warn-rwx-segments', '-o', elf], check=True)
  return elf

def load_elf(m, path):
  """copy the PT_LOAD segments of a 32-bit little-endian RISC-V ELF into mem[],
  return the entry point"""
  data = open(path, 'rb').read()
  assert data[:4] == b'\x7fELF' and data[4] == 1 and data[5] == 1, 'not ELF32 LE'
  e_machine, = struct.unpack_from('<H', data, 18)
  assert e_machine == 243, 'not RISC-V'
  e_entry, e_phoff = struct.unpack_from('<II', data, 24)
  e_phentsize, e_phnum = struct.unpack_from('<HH', data, 42)
  for i in range(e_phnum):
    p_type, p_offset, _, p_paddr, p_filesz, p_memsz = \
      struct.unpack_from('<IIIIII', data, e_phoff + i * e_phentsize)
    if p_type != 1: continue  # PT_LOAD
    assert p_paddr + p_memsz <= len(m.mem), 'segment does not fit in memory'
    m.mem[p_paddr : p_paddr + p_filesz] = data[p_offset : p_offset + p_filesz]
    m.mem[p_paddr + p_filesz : p_paddr + p_memsz] = bytes(p_memsz - p_filesz)
  return e_entry

def run_elf(path):
  """run an ELF on a fresh machine, return (stdout text, exit code, #steps)"""
  m = machine(mem_size=MEM_SIZE)
  entry = load_elf(m, path)
  out = io.StringIO()
  steps = 0
  with contextlib.redirect_stdout(out):
    m.pc = entry
    while not m.halted:
      m.step()
      steps += 1
  return out.getvalue(), m.exit_code, steps

expected = '''Hello from newlib on nanofive!
int: 42 -17 0
unsigned/hex/oct: 3000000000 dead BEEF 10 0xff
long long: -1234567890123 123456789abcdef
width/prec: [   42] [42   ] [00042] [abc] [      hi] [hi      ]
char/str/pct: ok done 100%
''' + ''.join('%d! = %d\n' % (i, f) for i, f in
  enumerate([1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800])) + \
'''snprintf-7-ff (len 13)
malloc works
stderr too
'''

if __name__ == '__main__':
  out, code, steps = run_elf(build('hello'))
  sys.stdout.write(out)
  print('exit code: %d, instructions executed: %d' % (code, steps))
  ok = out == expected and code == 3
  print('PASS' if ok else 'FAIL')
  sys.exit(0 if ok else 1)
