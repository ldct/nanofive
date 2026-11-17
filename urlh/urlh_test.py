import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # machine.py, elf.py
from elf import load_elf, elf_machine
import contextlib, io, os, subprocess, sys

# Run jwerle/url.h, a small C URL parser, compiled for RV32IM against newlib,
# on nanofive. See README.md for how the ELFs are built.
#
#   python3 urlh_test.py               # run both programs, check their output
#   echo 'https://a.b/c?q=1' | python3 urlh_test.py --inspect
#
# url_test.elf is url.h's own test.c: it asserts 30-odd facts about two URLs
# and exits 0 only if all hold. url_inspect.elf (urlh/inspect.c) parses each
# line of urlh/urls.txt and prints every part. The expected outputs in
# urlh/expected/ come from a native build of the same source; if that build
# can run here, it is run as well and compared live.
#
# The emulator's I/O is text with one character per byte (read_char returns
# ord(c), print_char prints chr(byte)), so bytes are mapped to and from
# characters with latin-1 and UTF-8 in the URLs passes through untouched.

HERE     = os.path.dirname(os.path.abspath(__file__))
DIR      = HERE
NATIVE   = os.path.join(DIR, 'build', 'native')
MEM_SIZE = 1 << 20  # must match MEM_SIZE in urlh/build.sh

def run_elf(path, stdin=b''):
  """run an ELF on a fresh machine with stdin; return (stdout bytes, exit code,
  #instructions). stderr goes to stdout, as both are ecall 11"""
  m = elf_machine(path, MEM_SIZE)
  m.pc = load_elf(m, path)
  out, steps = io.StringIO(), 0
  old_stdin, sys.stdin = sys.stdin, io.StringIO(stdin.decode('latin-1'))
  try:
    with contextlib.redirect_stdout(out):
      while not m.halted:
        m.step()
        steps += 1
  finally:
    sys.stdin = old_stdin
  return out.getvalue().encode('latin-1'), m.exit_code, steps

def run_native(name, stdin=b''):
  """stdout+stderr of the native build, or None if it cannot run here"""
  exe = os.path.join(NATIVE, name)
  if not os.path.exists(exe): return None
  try:
    r = subprocess.run([exe], input=stdin, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
  except OSError:  # e.g. a Linux binary on macOS
    return None
  return r.stdout if r.returncode == 0 else None

def read(name):
  return open(os.path.join(DIR, name), 'rb').read()

LEAN     = os.path.join(DIR, 'lean', 'UrlDecode.lean')
DECODE   = 0x374  # decode_percent in url_inspect.elf; `base` in UrlDecode.lean

def lean_prog():
  """the words of decode_percent that UrlDecode.lean proves things about"""
  src = open(LEAN).read()
  body = src[src.index('def prog'):]
  body = body[body.index('[') + 1:body.index(']')]
  return [int(w, 16) for w in body.replace(',', ' ').split()]

def decode_percent_spec(s):
  """decodePercent of UrlDecode.lean: the decoded bytes, or None for NULL"""
  hexval = lambda b: int(chr(b), 16) if chr(b) in '0123456789ABCDEFabcdef' else None
  out, i = bytearray(), 0
  while i < len(s):
    if s[i] != ord('%'):
      out.append(s[i]); i += 1
      continue
    hi, lo = (hexval(s[i + 1]), hexval(s[i + 2])) if i + 2 < len(s) else (None, None)
    if hi is None or lo is None: return None
    out.append(hi * 16 + lo); i += 3
  return bytes(out)

def run_decode_percent(s):
  """call decode_percent in url_inspect.elf on s on nanofive: the bytes it
  leaves at s up to the first NUL, or None if it returns NULL"""
  path = os.path.join(DIR, 'url_inspect.elf')
  m = elf_machine(path, MEM_SIZE)
  load_elf(m, path)
  addr, ret = 0x80000, 0x10
  m.mem[addr:addr + len(s) + 1] = s + b'\0'
  m.x[10], m.x[1] = addr, ret
  m.run(DECODE, end=ret, steps=10 * len(s) + 100)
  assert m.pc == ret, 'decode_percent did not return'
  if m.x[10] == 0: return None
  assert m.x[10] == addr
  return bytes(m.mem[addr:m.mem.index(0, addr)])

DECODE_CASES = [b'', b'abc', b'a%20b', b'%41%42%43', b'%7e%7E', b'%', b'%4', b'a%4',
                b'%G0', b'%0G', b'100%', b'%00A', b'%25%32', b'/p%C3%A9th']

def check_decode_percent():
  """the ELF holds the code the Lean proof is about, and running that code
  agrees with the Lean spec decodePercent (truncated at a decoded NUL, as C
  sees it)"""
  path = os.path.join(DIR, 'url_inspect.elf')
  m = elf_machine(path, MEM_SIZE)
  load_elf(m, path)
  words = [int.from_bytes(m.mem[DECODE + 4*k:DECODE + 4*k + 4], 'little')
           for k in range(len(lean_prog()))]
  ok = words == lean_prog()
  for s in DECODE_CASES:
    want = decode_percent_spec(s)
    want = want if want is None else want.split(b'\0')[0]
    got = run_decode_percent(s)
    if got != want:
      print(f'decode_percent({s!r}) = {got!r}, spec says {want!r}')
      ok = False
  print(f'decode_percent  {len(words)} words match Lean, {len(DECODE_CASES)} inputs  ' +
        ('PASS' if ok else 'FAIL'))
  return ok

if __name__ == '__main__':
  if sys.argv[1:] == ['--inspect']:
    out, code, steps = run_elf(os.path.join(DIR, 'url_inspect.elf'), sys.stdin.buffer.read())
    sys.stdout.buffer.write(out)
    print(f'exit code {code}, {steps} instructions', file=sys.stderr)
    sys.exit(code)
  ok = True
  for prog, stdin_name in [('test', None), ('inspect', 'urls.txt')]:
    stdin = read(stdin_name) if stdin_name else b''
    expected = read(os.path.join('expected', prog + '.out'))
    out, code, steps = run_elf(os.path.join(DIR, f'url_{prog}.elf'), stdin)
    good = out == expected and code == 0
    native = run_native('url_' + prog, stdin)
    if native is not None:
      good = good and native == expected
    print(f'url_{prog}.elf  {steps:9d} instructions  exit {code}  ' +
          ('PASS' if good else 'FAIL') + (' (native too)' if native is not None else ''))
    if not good:
      sys.stdout.buffer.write(out)
    ok = ok and good
  ok = check_decode_percent() and ok
  print('PASS' if ok else 'FAIL')
  sys.exit(0 if ok else 1)
