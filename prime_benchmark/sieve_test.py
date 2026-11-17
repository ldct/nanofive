import os, subprocess, sys

# Runs the sieve programs (byte_sieve.py, rosetta_sieve.py, plummer_sieve.py)
# on nanofive and checks their output. plummer_sieve.py takes ~25 s.

HERE = os.path.dirname(os.path.abspath(__file__))
expected = {
  'byte_sieve.py':    '10 iterations\n1899 primes\nexit code: 0\n',
  'rosetta_sieve.py': ' '.join(map(str, [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
                        43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97])) +
                      ' \n1229 primes up to 10000\nexit code: 0\n',
  'plummer_sieve.py': '78498 primes below 1000000\n'
                      'mckoss-c830;1;algorithm=wheel,faithful=yes,bits=1\nexit code: 0\n',
}
fails = 0
for f, want in expected.items():
  got = subprocess.run([sys.executable, os.path.join(HERE, f)], capture_output=True,
                       text=True, cwd=HERE).stdout
  ok = got == want
  fails += not ok
  print('%-17s %s' % (f, 'PASS' if ok else 'FAIL\n' + got))
sys.exit(1 if fails else 0)
