"""Check the RV64I wheel, complete flags, immutable table, and Lean boundary.

Run: python counting_primes_wheel_test.py
Requires the pinned Lean toolchain (`lake` on PATH).
"""

import contextlib
import io
from math import gcd, isqrt
from pathlib import Path
import random
import re
import subprocess
import sys

import counting_primes_wheel as wheel

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LEAN = HERE / "lean"


def reference(n):
    """Independent ordinary sieve; one means prime."""
    primes = bytearray([1]) * (n + 1)
    primes[:min(2, n + 1)] = bytes(min(2, n + 1))
    for p in range(2, isqrt(n) + 1):
        if primes[p]:
            primes[p*p::p] = bytes(len(range(p*p, n + 1, p)))
    return primes


def candidate(p):
    return p in (2, 3, 5) or (p >= 7 and gcd(p, 30) == 1)


def instruction_count(n, primes):
    """Independent path count, not a Lean-proved runtime theorem."""
    return 15 + sum(
        9 + (3 + 5 * (n // p - 1) if primes[p] else 0)
        + (2 if p % 30 == 1 else 0)
        for p in range(2, n + 1) if candidate(p)
    )


def budget(n):
    """The budget in CountingPrimesWheel.correct."""
    return 15 + 191 * n


def plain_sieve_count(n, primes):
    return 13 + sum(9 + 5 * (n // p - 1) if primes[p] else 6
                    for p in range(2, n + 1))


def run_python(n):
    m = wheel.initial(n)
    image = bytes(m.mem[:wheel.BASE])
    assert image[128:139] == bytes(wheel.GAPS)
    assert image[139] == 0
    steps = 0
    trace = []
    step = m.step

    def counted_step():
        nonlocal steps
        steps += 1
        if m.pc == 24:  # Candidate header, including the final N < p check.
            trace.append(m.x[5])
        step()

    m.step = counted_step
    output = io.StringIO()
    with contextlib.redirect_stdout(output):
        m.run(start=0)
    assert m.halted and m.exit_code == 0
    assert len(m.mem) == wheel.BASE + n + 1
    assert bytes(m.mem[:wheel.BASE]) == image, "store changed code/table/padding"
    primes = reference(n)
    composite = bytearray(n + 1)
    for k in range(2, n + 1):
        composite[k] = 1 - primes[k]
    assert m.mem[wheel.BASE:] == composite, f"wrong composite flags for N={n}"
    assert output.getvalue() == f"{sum(primes)}\n", f"wrong count for N={n}"
    expected = [p for p in range(2, n + 1) if candidate(p)]
    final = max(2, n + 1)
    while not candidate(final):
        final += 1
    assert trace == expected + [final], f"wrong wheel candidate trace for N={n}"
    assert steps == instruction_count(n, primes), f"wrong path count for N={n}"
    assert steps <= budget(n), f"budget exceeded for N={n}"
    return steps


def main():
    source = (LEAN / "WheelProgram.lean").read_text()
    body = re.search(r"def prog : List \(BitVec 32\) := \[(.*?)\]", source, re.S)
    assert body, "Lean instruction/data list not found"
    words = re.findall(r"0x[0-9a-fA-F]+", body.group(1))
    assert [int(w, 16) for w in words] == wheel.prog
    assert len(wheel.prog) == 35
    assert wheel.GAPS == (1, 2, 2, 4, 2, 4, 2, 4, 6, 2, 6)
    assert wheel.BASE == 256 and wheel.MAX_N == 10**11 - 1
    print("same machine code/data: PASS (128-byte code + 12-byte table)", flush=True)

    for n in [-1, wheel.MAX_N + 1]:
        try:
            wheel.initial(n)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted out-of-range input {n}")
    print("input boundaries: PASS", flush=True)

    rng = random.Random(30)
    cases = sorted(set(range(241)) |
                   {289, 500, 600, 840, 841, 960, 961, 997, 1000, 1369,
                    2000, 10_000, 100_000} |
                   {rng.randrange(241, 2000) for _ in range(20)})
    counts = {n: run_python(n) for n in cases}
    print(f"count, all flags, wheel trace, table isolation, steps, and budget: PASS "
          f"({len(cases)} cases)", flush=True)
    for n in [100, 1000, 10_000, 100_000]:
        plain = plain_sieve_count(n, reference(n))
        assert counts[n] < plain
        print(f"N={n}: wheel {counts[n]}, plain sieve {plain} instructions", flush=True)

    cli = subprocess.run([sys.executable, str(HERE / "counting_primes_wheel.py")],
                         input="100\n", capture_output=True, text=True, check=True)
    assert cli.stdout == "25\n" and not cli.stderr
    subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    exe = ROOT / ".lake" / "build" / "bin" / "counting_primes_wheel"
    for n in [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 29, 30, 31, 32, 36, 37,
              49, 121, 1000, 10_000]:
        result = subprocess.run([str(exe)], input=f"{n}\n", capture_output=True,
                                text=True, check=True)
        assert result.stdout == f"{sum(reference(n))}\n", f"Lean model N={n}"
        assert not result.stderr
    for text in ["-1\n", "not a number\n", f"{wheel.MAX_N + 1}\n"]:
        result = subprocess.run([str(exe)], input=text, capture_output=True, text=True)
        assert result.returncode != 0 and result.stderr and not result.stdout
    print("Lean proof build and executable machine model: PASS", flush=True)


if __name__ == "__main__":
    main()
