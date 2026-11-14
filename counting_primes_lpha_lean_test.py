import os, re, sys

# Ties counting_primes_lpha.py to its Lean correctness proof
# (lean/TinyFive/CountingPrimesLpha.lean): the machine code that Lean reasons about is the
# machine code in 'prog'. (The Python file runs the program when imported, so 'prog' is
# read from its source text.)

HERE = os.path.dirname(os.path.abspath(__file__))

def words(path, pattern):
  with open(path) as f:
    body = re.search(pattern, f.read(), re.S | re.M).group(1)
  body = re.sub(r'(#|--).*', '', body)  # drop comments
  return [int(w, 16) for w in re.findall(r'0x[0-9a-fA-F]{8}', body)]

py = words(os.path.join(HERE, 'counting_primes_lpha.py'), r'^prog = \[(.*?)\]')
lean = words(os.path.join(HERE, 'lean', 'TinyFive', 'CountingPrimesLpha', 'Code.lean'),
             r'def prog : List \(BitVec 32\) := \[(.*?)\]')
ok = py == lean
print('%-28s %s' % ('same machine code', 'PASS' if ok else 'FAIL'))
sys.exit(0 if ok else 1)
