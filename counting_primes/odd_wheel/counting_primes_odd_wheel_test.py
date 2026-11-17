"""Check the mod-6 wheel sieve against a reference sieve and report step counts.

Run: python3 counting_primes/odd_wheel/counting_primes_odd_wheel_test.py
"""

import contextlib
import io
from math import isqrt
from pathlib import Path
import random
import subprocess
import sys

import counting_primes_odd_wheel as wheel

HERE = Path(__file__).resolve().parent
BENCH = [100, 1000, 10_000, 100_000, 1_000_000]


def reference(n):
    """Independent ordinary sieve; one means prime."""
    primes = bytearray([1]) * (n + 1)
    primes[:min(2, n + 1)] = bytes(min(2, n + 1))
    for p in range(2, isqrt(n) + 1):
        if primes[p]:
            primes[p*p::p] = bytes(len(range(p*p, n + 1, p)))
    return primes


def check_instruction_set():
    """Only RV32I-encoded base instructions: no M extension, ld/sd/lwu, or *W."""
    for addr, word in enumerate(wheel.prog):
        opcode, f3, f7 = word & 0x7f, (word >> 12) & 7, word >> 25
        is_allowed = (
            opcode in (0x37, 0x17, 0x6f)
            or (opcode == 0x67 and f3 == 0)
            or (opcode == 0x63 and f3 not in (2, 3))
            or (opcode == 0x03 and f3 in (0, 1, 2, 4, 5))
            or (opcode == 0x23 and f3 in (0, 1, 2))
            or (opcode == 0x13 and (f3 not in (1, 5) or f7 & ~1 in (0x00, 0x20)))
            or (opcode == 0x33 and f7 in (0x00, 0x20) and (f7 == 0 or f3 in (0, 5)))
            or word == 0x73
        )
        assert is_allowed, f"instruction {word:08x} at {4 * addr} is outside the base set"


def run(n):
    """Run the program on n, check everything observable, and return the step count."""
    m = wheel.initial(n)
    image = bytes(m.mem[:wheel.BASE])
    assert image[4 * len(wheel.prog):] == bytes(wheel.BASE - 4 * len(wheel.prog))
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
    primes = reference(n)
    assert m.halted and m.exit_code == 0, f"bad exit for N={n}"
    assert output.getvalue() == f"{sum(primes)}\n", f"wrong count for N={n}"
    assert bytes(m.mem[:wheel.BASE]) == image, f"store below the flags for N={n}"

    flags = m.mem[wheel.BASE:]
    assert set(flags) <= {0, 1}
    candidates = [(3 * i + 1) | 1 for i in range(len(flags))]
    if n >= 3:
        # Every flag that counts is exact, and marks past N are still composites.
        for number, flag in zip(candidates, flags):
            if number <= n:
                assert flag == (0 if number == 1 else 1 - primes[number]), (n, number)
            elif flag:
                assert any(number % p == 0 for p in range(5, isqrt(number) + 1)), (n, number)
    else:
        assert not any(flags), f"N={n} must not touch memory"
    return steps


def main():
    check_instruction_set()
    assert 4 * len(wheel.prog) <= wheel.BASE - 16, "the count pass reads up to 15 bytes below BASE"
    print(f"program: {len(wheel.prog)} instructions, {4 * len(wheel.prog)} bytes, no table; "
          f"base RV32I encodings only: PASS", flush=True)

    for n in [-1, wheel.MAX_N + 1]:
        try:
            wheel.initial(n)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted out-of-range input {n}")

    # The shift-add division by 3, replayed in Python over the whole input range.
    rng = random.Random(6)
    samples = (list(range(100_000)) + [wheel.MAX_N - i for i in range(1000)]
               + [rng.randrange(wheel.MAX_N + 1) for _ in range(200_000)])
    for n in samples:
        y = ((n + 3) >> 1) * 0x5555
        assert (y + ((y + (y >> 16)) >> 16)) >> 15 == ((n + 1) | 1) // 3, n
    print(f"flag count E by shifts and adds: PASS ({len(samples)} values up to MAX_N)", flush=True)

    cases = sorted(set(range(2001)) | set(BENCH)
                   | {q * q + d for q in (31, 37, 41, 97, 101, 103, 311, 313, 997)
                      for d in (-2, -1, 0, 1)})
    counts = {n: run(n) for n in cases}
    print(f"count, exit code, flags, and code isolation: PASS ({len(cases)} cases, "
          f"every N in 0..2000 and up to {max(cases)})", flush=True)

    cli = subprocess.run([sys.executable, str(HERE / "counting_primes_odd_wheel.py")],
                         input="100\n", capture_output=True, text=True, check=True)
    assert cli.stdout == "25\n" and not cli.stderr
    print("command line: PASS", flush=True)

    print(f"{'N':>9}  {'pi(N)':>6}  {'instructions':>12}  {'per N':>6}")
    for n in BENCH:
        print(f"{n:>9}  {sum(reference(n)):>6}  {counts[n]:>12}  {counts[n] / n:>6.3f}")


if __name__ == "__main__":
    main()
