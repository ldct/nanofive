import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # machine.py, elf.py
from machine import *
from elf import elf_machine, load_elf
import io, subprocess, contextlib

# Run a C program, compiled with gcc against newlib for rv32im/ilp32 and for
# rv64im/lp64, on nanofive (machine and machine64, picked from the ELF class). newlib's system calls (asm/syscalls.c) are mapped onto
# nanofive's RARS-style ecalls (see machine.ECALL): _write prints each byte
# with a7=11, _read uses a7=12, _exit uses a7=93.
#
# The parts of newlib that printf & co need are vendored in newlib/vendor (see
# README.md). This script compiles them together with hello.c into
# hello.elf (RV32) and hello64.elf (RV64), loads their ELF
# segments into mem[] and runs them from the ELF entry point. Without a RISC-V
# gcc, the checked-in ELFs are used.

import shutil, tempfile

HERE     = os.path.dirname(os.path.abspath(__file__))
SRC      = HERE
ASM      = os.path.join(os.path.dirname(HERE), 'asm')
VENDOR   = os.path.join(SRC, 'vendor')
MEM_SIZE = 1 << 20  # must match MEM_SIZE in asm/link.ld
GCC      = 'riscv64-unknown-elf-gcc'
ARCH     = {32: ['-march=rv32im', '-mabi=ilp32', '-mcmodel=medany', '-O2'],
            64: ['-march=rv64im', '-mabi=lp64',  '-mcmodel=medany', '-O2']}
ELF_NAME = {32: '%s.elf', 64: '%s64.elf'}
INCLUDES = ['-isystem', os.path.join(VENDOR, 'build', 'targ-include'),
            '-isystem', os.path.join(VENDOR, 'libc', 'include'),
            '-I', os.path.join(VENDOR, 'build'), '-I', VENDOR]
# the flags newlib's own build uses for these files
LIBC_FLAGS = ['-D_LIBC', '-fno-builtin', '-DHAVE_CONFIG_H', '-DHAVE_NANOSLEEP',
              '-D__SINGLE_THREAD__', '-D__NO_SYSCALLS__', '-DNO_FLOATING_POINT', '-w']

def build(name, xlen=32):
  elf = os.path.join(SRC, ELF_NAME[xlen] % name)
  arch = ARCH[xlen]
  # newlib/vendor/SOURCES lists the files to compile; the rest are headers or
  # .c files #included by them
  libc = [os.path.join(VENDOR, f) for f in
          open(os.path.join(VENDOR, 'SOURCES')).read().split()]
  with tempfile.TemporaryDirectory() as tmp:
    objs = []
    for i, f in enumerate(libc):  # compile vendored newlib
      o = os.path.join(tmp, '%d.o' % i); objs.append(o)
      subprocess.run([GCC] + arch + INCLUDES + LIBC_FLAGS + ['-c', f, '-o', o], check=True)
    subprocess.run([GCC] + arch + INCLUDES + ['-nostdlib', '-nostartfiles',
      '-T', os.path.join(ASM, 'link.ld'), '-Wl,--no-warn-rwx-segments',
      os.path.join(ASM, 'crt0.S'), os.path.join(SRC, name + '.c'),
      os.path.join(ASM, 'syscalls.c')] + objs + ['-lgcc', '-o', elf], check=True)
  return elf

def run_elf(path):
  """run an ELF on a fresh machine, return (stdout text, exit code, #steps)"""
  m = elf_machine(path, MEM_SIZE)
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
  have_gcc = shutil.which(GCC) is not None
  ok = True
  for xlen in (32, 64):
    elf = build('hello', xlen) if have_gcc else \
          os.path.join(SRC, ELF_NAME[xlen] % 'hello')
    if not have_gcc: print('(%s not found, using prebuilt %s)' % (GCC, elf))
    print('--- RV%dIM: %s' % (xlen, os.path.basename(elf)))
    out, code, steps = run_elf(elf)
    sys.stdout.write(out)
    print('exit code: %d, instructions executed: %d' % (code, steps))
    ok = ok and out == expected and code == 3
  print('PASS' if ok else 'FAIL')
  sys.exit(0 if ok else 1)
