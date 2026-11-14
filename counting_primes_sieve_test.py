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
LEAN = HERE / "lean"


def reference(n):
    flags = bytearray([1]) * (n + 1)
    flags[:min(2, n + 1)] = bytes(min(2, n + 1))
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            flags[p*p::p] = bytes(len(range(p*p, n + 1, p)))
    return flags


def run_python(n):
    m = sieve.initial(n)
    code = bytes(m.mem[:sieve.BASE])
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
    return output.getvalue()


def main():
    source = (LEAN / "TinyFive" / "CountingPrimesSieve.lean").read_text()
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
    cases = sorted(set(range(201)) | {289, 997, 1000, 10_000, 100_000} |
                   {rng.randrange(201, 2000) for _ in range(20)})
    for n in cases:
        run_python(n)
    print(f"machine count, flags, and code isolation: PASS ({len(cases)} cases)",
          flush=True)

    cli = subprocess.run([sys.executable, str(HERE / "counting_primes_sieve.py")],
                         input="100\n", capture_output=True, text=True, check=True)
    assert cli.stdout == "25\n" and not cli.stderr
    subprocess.run(["lake", "build"], cwd=LEAN, check=True)
    exe = LEAN / ".lake" / "build" / "bin" / "counting_primes_sieve"
    for n in [0, 1, 2, 3, 4, 9, 25, 49, 97, 121, 200, 1000, 10_000]:
        result = subprocess.run([str(exe)], input=f"{n}\n", capture_output=True,
                                text=True, check=True)
        assert result.stdout == f"{sum(reference(n))}\n", f"Lean model N={n}"
        assert not result.stderr
    print("Lean proof build and executable machine model: PASS", flush=True)


if __name__ == "__main__":
    main()
