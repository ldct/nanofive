from machine import *
from newlib_test import load_elf
import io, os, subprocess, sys, time, contextlib

# Run Michael Stoll's ratpoints (rational points on hyperelliptic curves
# y^2 = f(x)), compiled for RV32IM against newlib and GMP, on nanofive.
# See ratpoints/README.md for how ratpoints/ratpoints.elf is built.
#
# The emulator has no operating system, so command-line arguments are passed
# the way Linux does it: argc, the argv[] pointers, NULL and the strings are
# written to the top of memory and sp points at argc when the program starts;
# ratpoints/crt0.S picks them up and calls main(argc, argv).
#
#   python3 ratpoints_test.py                       # run the test curves
#   python3 ratpoints_test.py 'a0 a1 ... an' H [options]   # run ratpoints itself
#   python3 ratpoints_test.py --run prog.elf [args]  # run any such ELF
#
# The expected outputs in ratpoints/expected/ come from a native x86-64 build
# of the same ratpoints source (ratpoints/build.sh); if that build is present,
# it is run as well and compared live.

HERE     = os.path.dirname(os.path.abspath(__file__))
DIR      = os.path.join(HERE, 'ratpoints')
ELF      = os.path.join(DIR, 'ratpoints.elf')
NATIVE   = os.path.join(DIR, 'build', 'native', 'ratpoints')
MEM_SIZE = 8 << 20  # must match MEM_SIZE in ratpoints/build.sh

def setup_args(m, argv):
  """write argc, argv[], NULL and the strings to the top of memory, Linux
  style, and point sp at argc"""
  strs = [a.encode() + b'\0' for a in argv]
  top = len(m.mem) - sum(len(s) for s in strs)
  addrs, a = [], top
  for s in strs:
    m.mem[a : a + len(s)] = s; addrs.append(a); a += len(s)
  sp = (top - 4 * (len(argv) + 2)) & ~15
  m.write_i32_vec([len(argv)] + addrs + [0], sp)
  m.x[2] = sp

def run_elf(path, argv, stdin=''):
  """run an ELF with arguments argv (argv[0] = program name) on a fresh
  machine; return (stdout text, exit code, #instructions, seconds)"""
  m = machine(mem_size=MEM_SIZE)
  m.pc = load_elf(m, path)
  setup_args(m, argv)
  out, steps, t = io.StringIO(), 0, time.time()
  old_stdin, sys.stdin = sys.stdin, io.StringIO(stdin)
  try:
    with contextlib.redirect_stdout(out):
      while not m.halted:
        m.step()
        steps += 1
  finally:
    sys.stdin = old_stdin
  return out.getvalue(), m.exit_code, steps, time.time() - t

# test curves: (name, arguments after the program name). The coefficients are
# a_0 a_1 ... a_n of f(x) = a_0 + a_1 x + ... + a_n x^n; the second argument is
# the height bound. Points are printed as (a : y : b), x = a/b.
TESTS = [
  # y^2 = x^6 + x^4 - 3x^2 + 1: 10 points, e.g. x = +-3, y = +-28; full output
  # including the search intervals (printed with %f)
  ('genus2',   ['1 0 -3 0 1 0 1', '50']),
  # y^2 = x^5 - 3x^3 + 1: (2 : +-3 : 1) and (4 : +-633 : 9), i.e. x = 4/9
  ('quintic',  ['1 0 0 -3 0 1', '100']),
  # y^2 = x^5 - x + 1: 11 points up to x = 7/9
  ('quintic2', ['1 -1 0 0 0 1', '200', '-q']),
  # the elliptic curve y^2 = x^3 - 2: (3, +-5) and x = 129/100
  ('elliptic', ['-2 0 0 1', '1000', '-q']),
  # y^2 = 3x^6 + x^5 + x - 6: no rational points (with real ones, so the
  # sieve really runs)
  ('nopoints', ['-6 1 0 0 0 1 3', '300']),
  # the first curve on 0 <= x <= 5 only (the bounds are parsed with
  # sscanf("%lf"))
  ('interval', ['1 0 -3 0 1 0 1', '300', '-l', '0', '-u', '5', '-q']),
  # y^2 = 7x^6 + 6x^5 + ... + 1, verbose: sieving parameters, Sturm sequence
  ('verbose',  ['1 2 3 4 5 6 7', '10', '-v']),
]

def expected(name):
  return open(os.path.join(DIR, 'expected', name + '.out')).read()

if __name__ == '__main__':
  if len(sys.argv) > 1 and sys.argv[1] == '--run':
    out, code, steps, sec = run_elf(sys.argv[2], sys.argv[2:])
    sys.stdout.write(out)
    print('exit code %d, %d instructions, %.1f s' % (code, steps, sec), file=sys.stderr)
    sys.exit(code)
  if len(sys.argv) > 1:
    out, code, steps, sec = run_elf(ELF, ['ratpoints'] + sys.argv[1:])
    sys.stdout.write(out)
    print('exit code %d, %d instructions, %.1f s' % (code, steps, sec), file=sys.stderr)
    sys.exit(code)
  native = os.path.exists(NATIVE)
  ok = True
  for name, args in TESTS:
    exp = expected(name)
    out, code, steps, sec = run_elf(ELF, ['ratpoints'] + args)
    good = out == exp and code == 0
    if native:
      nat = subprocess.run([NATIVE] + args, capture_output=True, text=True).stdout
      good = good and nat == exp
    npts = sum(1 for l in out.splitlines() if l.startswith('('))
    print('%-10s %-34s %3d points  %10d instructions  %6.1f s  %s' % (name,
          ' '.join(repr(a) if ' ' in a else a for a in args), npts, steps, sec,
          ('PASS' if good else 'FAIL') + (' (native too)' if native else '')))
    if not good:
      sys.stdout.write(out)
    ok = ok and good
  print('PASS' if ok else 'FAIL')
  sys.exit(0 if ok else 1)
