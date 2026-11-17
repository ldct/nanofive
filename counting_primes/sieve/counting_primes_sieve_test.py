"""Test the RV32I sieve, its flag memory, and the Python/Lean boundary.

Run: python counting_primes_sieve_test.py
Requires the pinned Lean toolchain (`lake` on PATH).
"""

import contextlib
import io
from math import isqrt
from pathlib import Path
import random
import re
import subprocess
import sys

import counting_primes_sieve as sieve

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LEAN = HERE / "lean"


def reference(n):
    flags = bytearray([1]) * (n + 1)
    flags[:min(2, n + 1)] = bytes(min(2, n + 1))
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            flags[p*p::p] = bytes(len(range(p*p, n + 1, p)))
    return flags


def instruction_budget(n, primes=None):
    """Independent evaluation of the budget in TinyFive.SieveCost."""
    if primes is None:
        primes = reference(n)
    return 13 + sum(9 + 5 * (n // p - 1) if primes[p] else 6
                    for p in range(2, n + 1))


def dyadic_upper_bound(n):
    """29 divisor buckets covering the complete supported input range."""
    return 13 + 9 * ((1 << 30) - 2) + 145 * n


def run_python(n):
    m = sieve.initial(n)
    code = bytes(m.mem[:sieve.BASE])
    steps = 0
    step = m.step

    def counted_step():
        nonlocal steps
        steps += 1
        step()

    m.step = counted_step
    output = io.StringIO()
    with contextlib.redirect_stdout(output):
        m.run(start=0)
    assert m.halted and m.exit_code == 0
    assert len(m.mem) == sieve.BASE + n + 1
    assert bytes(m.mem[:sieve.BASE]) == code, "store changed code/padding"
    primes = reference(n)
    composite = bytearray(n + 1)
    for k in range(2, n + 1):
        composite[k] = 1 - primes[k]
    assert m.mem[sieve.BASE:] == composite, f"wrong composite flags for N={n}"
    assert output.getvalue() == f"{sum(primes)}\n", f"wrong count for N={n}"
    budget = instruction_budget(n, primes)
    assert steps == budget, f"step count {steps} != budget {budget} for N={n}"
    assert budget <= 13 + max(0, n - 1) * (9 + 5 * n)
    assert budget <= dyadic_upper_bound(n) <= 165_356_240_746 < (1 << 38)
    if n <= 600:
        assert steps < 10_000
    return output.getvalue()


def main():
    source = (LEAN / "CountingPrimesSieve.lean").read_text()
    body = re.search(r"def prog : List \(BitVec 32\) := \[(.*?)\]", source, re.S)
    assert body, "Lean instruction list not found"
    words = re.findall(r"0x[0-9a-fA-F]+", body.group(1))
    assert [int(w, 16) for w in words] == sieve.prog
    assert len(sieve.prog) == 25
    print("same machine code: PASS (25 words / 100 bytes)", flush=True)

    for n in [-1, sieve.MAX_N + 1]:
        try:
            sieve.initial(n)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted out-of-range input {n}")
    print("input boundaries: PASS", flush=True)

    rng = random.Random(0)
    cases = sorted(set(range(201)) | {289, 500, 600, 997, 1000, 2000, 10_000, 100_000} |
                   {rng.randrange(201, 2000) for _ in range(20)})
    for n in cases:
        run_python(n)
    print(f"machine count, flags, code isolation, and instruction budget: PASS ({len(cases)} cases)",
          flush=True)
    assert instruction_budget(600) == 9529
    assert instruction_budget(2000) == 33671
    print("10,000-instruction examples: PASS (N=600: 9529; N=2000: 33671)",
          flush=True)
    assert dyadic_upper_bound(sieve.MAX_N) == 165_356_240_746
    for n in [0, 1, 2, sieve.MAX_N - 1, sieve.MAX_N]:
        assert dyadic_upper_bound(n) <= 165_356_240_746 < (1 << 38)
    print("full-domain dyadic bound: PASS (at most 165356240746 < 2^38)",
          flush=True)

    cli = subprocess.run([sys.executable, str(HERE / "counting_primes_sieve.py")],
                         input="100\n", capture_output=True, text=True, check=True)
    assert cli.stdout == "25\n" and not cli.stderr
    subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    exe = ROOT / ".lake" / "build" / "bin" / "counting_primes_sieve"
    for n in [0, 1, 2, 3, 4, 9, 25, 49, 97, 121, 200, 1000, 10_000]:
        result = subprocess.run([str(exe)], input=f"{n}\n", capture_output=True,
                                text=True, check=True)
        assert result.stdout == f"{sum(reference(n))}\n", f"Lean model N={n}"
        assert not result.stderr
    print("Lean proof build and executable machine model: PASS", flush=True)


if __name__ == "__main__":
    main()
