"""Test and lightly benchmark the O(sqrt N)-memory prime counter.

Run: python3 counting_primes/lucy/counting_primes_lucy_test.py
Compares the machine's output with a plain sieve, checks the instruction
budget that lean/CountingPrimesLucy.lean proves, checks that the Lean proof is
about the same instruction words, compares the executable Lean model (which
exercises mul, divu, ld and sd) with the Python machine, and prints how many
instructions the program executes for a few N.
Requires the pinned Lean toolchain (`lake` on PATH).
"""

import contextlib
import io
from math import isqrt
from pathlib import Path
import re
import subprocess
import sys

import counting_primes_lucy as lucy

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LEAN = HERE / "lean"
CODE_BYTES = 4 * len(lucy.prog)
SIEVE_LIMIT = 10**7
EDGE_CASES = [3001, 3024, 3025, 3026, 3480, 3481, 3482, 10_000, 10_200, 10_201, 10_202,
              99_999, 100_000, 999_999, 1_000_000, 1_000_001, 1_002_001, SIEVE_LIMIT]
KNOWN = {10**8: 5_761_455, 10**9: 50_847_534}
BENCHMARK = [100, 1000, 10_000, 100_000, 1_000_000, 10**7, 10**8, 10**9]


def prime_counts(limit):
    """pi(n) for every n in [0, limit], from a byte sieve."""
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p*p::p] = bytes(len(range(p*p, limit + 1, p)))
    counts, total = [], 0
    for flag in flags:
        total += flag
        counts.append(total)
    return counts


def budget(n):
    """The budget in CountingPrimesLucy.correct."""
    return 26 + 41 * n


def run_machine(n):
    """Run the program on N = n and return (stdout, executed instructions)."""
    m = lucy.initial(n)
    code = bytes(m.mem[:CODE_BYTES])
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
    assert m.halted and m.exit_code == 0, f"bad exit for N={n}"
    assert len(m.mem) == lucy.BASE + 8 * (isqrt(n) + 1)
    assert bytes(m.mem[:CODE_BYTES]) == code, f"store changed the code for N={n}"
    assert not any(m.mem[CODE_BYTES:lucy.BASE]), f"store hit the padding for N={n}"
    assert steps <= budget(n), f"budget exceeded for N={n}"
    return output.getvalue(), steps


def main():
    assert CODE_BYTES <= lucy.BASE - 8
    print(f"program size: {len(lucy.prog)} instructions / {CODE_BYTES} bytes", flush=True)

    source = (LEAN / "LucyProgram.lean").read_text()
    body = re.search(r"def prog : List \(BitVec 32\) := \[(.*?)\]", source, re.S)
    assert body, "Lean instruction list not found"
    words = re.findall(r"0x[0-9a-fA-F]+", body.group(1))
    assert [int(w, 16) for w in words] == lucy.prog
    assert lucy.BASE == 512 and lucy.MAX_N == 10**11 - 1
    print("same machine code: PASS", flush=True)

    for n in [-1, lucy.MAX_N + 1]:
        try:
            lucy.initial(n)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted out-of-range input {n}")
    print("input boundaries: PASS", flush=True)

    counts = prime_counts(SIEVE_LIMIT)
    squares = [k*k + delta for k in range(2, 60) for delta in (-1, 0, 1)]
    cases = sorted(set(range(3001)) | set(squares) | {31*31, 1024, 37*37} | set(EDGE_CASES))
    steps_by_n = {}
    for n in cases:
        output, steps_by_n[n] = run_machine(n)
        assert output == f"{counts[n]}\n", f"wrong count for N={n}: {output!r}"
    print(f"count, exit code, code isolation, and budget: PASS ({len(cases)} cases)",
          flush=True)

    cli = subprocess.run([sys.executable, str(HERE / "counting_primes_lucy.py")],
                         input="1000\n", capture_output=True, text=True, check=True)
    assert cli.stdout == "168\n" and not cli.stderr
    print("command line: PASS", flush=True)

    subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    exe = ROOT / ".lake" / "build" / "bin" / "counting_primes_lucy"
    for n in [0, 1, 2, 3, 4, 5, 8, 9, 10, 24, 25, 26, 48, 49, 120, 121, 624, 625, 1000,
              3481, 10_000, 99_999, 1_000_000]:
        result = subprocess.run([str(exe)], input=f"{n}\n", capture_output=True,
                                text=True, check=True)
        assert result.stdout == f"{counts[n]}\n", f"Lean model N={n}"
        assert not result.stderr
    for text in ["-1\n", "not a number\n", f"{lucy.MAX_N + 1}\n"]:
        result = subprocess.run([str(exe)], input=text, capture_output=True, text=True)
        assert result.returncode != 0 and result.stderr and not result.stdout
    print("Lean proof build and executable machine model: PASS", flush=True)

    print("executed instructions:")
    print(f"  {'N':>13}  {'pi(N)':>10}  {'instructions':>12}")
    for n in BENCHMARK:
        expected = counts[n] if n <= SIEVE_LIMIT else KNOWN[n]
        if n in steps_by_n:
            steps = steps_by_n[n]
        else:
            output, steps = run_machine(n)
            assert output == f"{expected}\n", f"wrong count for N={n}: {output!r}"
        print(f"  {n:>13,}  {expected:>10,}  {steps:>12,}", flush=True)
    assert steps_by_n[1000] == 562
    print("all tests: PASS")


if __name__ == "__main__":
    main()
