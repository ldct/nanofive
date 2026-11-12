import os, subprocess, sys

# Runs the ported Library Checker "Counting Primes" submissions
# (counting_primes_*.py) on nanofive for several N and checks pi(N).

HERE = os.path.dirname(os.path.abspath(__file__))
PROGS = ['counting_primes_lpha.py', 'counting_primes_grumpygordon.py',
         'counting_primes_zjy2008.py']

def pi(n):  # reference: plain sieve
  if n < 2: return 0
  s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
  for i in range(2, int(n ** .5) + 1):
    if s[i]: s[i*i::i] = bytes(len(range(i*i, n + 1, i)))
  return sum(s)

# N = 1e8, 1e9 also pass (5761455, 50847534) but take ~15 s / ~65 s each
cases = [(n, pi(n)) for n in [0, 1, 2, 3, 10, 49, 121, 1000, 99991, 10**6]] + \
        [(10**7, 664579)]
fails = 0
for f in PROGS:
  bad = []
  for n, want in cases:
    got = subprocess.run([sys.executable, os.path.join(HERE, f)], input='%d\n' % n,
                         capture_output=True, text=True, cwd=HERE).stdout
    if got != '%d\n' % want: bad.append('N=%d: got %r, want %d' % (n, got, want))
  fails += len(bad)
  print('%-32s %s' % (f, 'PASS' if not bad else 'FAIL ' + '; '.join(bad)))
sys.exit(1 if fails else 0)
