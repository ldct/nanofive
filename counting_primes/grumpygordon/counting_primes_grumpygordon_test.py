"""Regress the verified algorithm (not a verification of the RV32 image)."""
from itertools import accumulate
from math import isqrt
from pathlib import Path
from random import Random
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def sieve_counts(n):
    flags = bytearray([1]) * (n + 1)
    flags[:2] = b'\0\0'
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            flags[p*p::p] = bytes(1 + (n - p*p) // p)
    return accumulate(flags)


def main():
    subprocess.run(['lake', 'build', 'counting_primes_grumpygordon'], cwd=ROOT, check=True)
    subprocess.run(['lake', 'env', 'lean', str(HERE / 'GrumpyRegression.lean')], cwd=ROOT, check=True)
    cases = set(range(1025))
    rng = Random(50137)
    cases.update(rng.randrange(10**6) for _ in range(150))
    # Squares (table boundary), cubes (triple correction), fourth powers
    # (sieve-stage boundary); test both prime and skipped composite bases.
    for k in (3, 5, 7, 9, 11, 13, 15, 19, 25, 29, 31):
        cases.update(k**e + d for e in (2, 3, 4) for d in (-1, 0, 1))
    expected = {n: c for n, c in enumerate(sieve_counts(max(cases))) if n in cases}
    # Known pi(10^k) regression values, not a reference sieve at the endpoint.
    expected.update({10**7: 664579, 10**8: 5761455, 10**9: 50847534,
                     10**10: 455052511, 10**11: 4118054813})
    inputs = sorted(expected)
    result = subprocess.run([ROOT / '.lake/build/bin/counting_primes_grumpygordon'],
                            input=''.join(f'{n}\n' for n in inputs), text=True,
                            capture_output=True, check=True, timeout=60)
    assert not result.stderr, result.stderr
    lines = result.stdout.splitlines()
    assert len(lines) == len(inputs), (len(lines), len(inputs))
    for n, line in zip(inputs, lines):
        assert line == str(expected[n]), (n, line, expected[n])
    # A few cross-checks of the actual local port, separate from the theorem.
    for n in (0, 2, 80, 81, 624, 625, 1000, 2401):
        port = subprocess.check_output([sys.executable, ROOT / 'prime_benchmark/counting_primes_grumpygordon.py'],
                                       input=f'{n}\n', text=True, timeout=30)
        assert port.strip() == str(expected[n]), (n, port)
    print(f'{len(inputs)} Lean model cases passed, including pi(10^11) = {expected[10**11]}; 8 RV32 spot checks')


if __name__ == '__main__':
    main()
