import os, random, re, subprocess, sys

# Ties abc101_a.py to its Lean correctness proof (lean/TinyFive/Abc101a.lean):
#   1. the machine code that Lean proves correct is the machine code in 'prog'
#   2. the Lean machine model and machine.py print the same thing for the same
#      input, at both register widths of the model
# Needs 'lake' (the Lean build tool) on the PATH.

import abc101_a

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, 'lean')
fails = 0

def check(name, ok, detail=''):
  global fails
  fails += not ok
  print('%-28s %s' % (name, 'PASS' if ok else 'FAIL ' + detail))

with open(os.path.join(LEAN, 'TinyFive', 'Abc101a.lean')) as f:
  lean_prog = re.search(r'def prog : List \(BitVec 32\) := \[(.*?)\]', f.read(), re.S).group(1)
check('same machine code', [int(w, 16) for w in lean_prog.split(',')] == abc101_a.prog)

subprocess.run(['lake', 'build'], cwd=LEAN, check=True, capture_output=True)

rng = random.Random(0)
inputs = ['', '\n', '+-++\n', '----\n', '++++', '+-x+\n', '+ +\n', 'é+\n', '-' * 300 + '\n']
inputs += [''.join(rng.choice('++--\n x') for _ in range(rng.randrange(40))) for _ in range(50)]

def run(cmd, text):
  return subprocess.run(cmd, input=text, capture_output=True, text=True, encoding='utf-8',
                        cwd=HERE, env={**os.environ, 'PYTHONIOENCODING': 'utf-8'}).stdout

exe = os.path.join(LEAN, '.lake', 'build', 'bin', 'abc101a')
for width in ['32', '64']:
  bad = [t for t in inputs
         if run([sys.executable, 'abc101_a.py'], t) != run([exe, width], t)]
  check('model%s agrees with machine' % width, not bad, repr(bad[:3]))
sys.exit(1 if fails else 0)
