"""Test and lightly benchmark the odds-only sieve.

Run: python3 counting_primes/odd_sieve/counting_primes_odd_sieve_test.py
Requires the pinned Lean toolchain (`lake` on PATH).
"""

import contextlib
import io
from math import isqrt
from pathlib import Path
import re
import subprocess
import sys

import counting_primes_odd_sieve as odd

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LEAN = HERE / "lean"

# Allowed (opcode, funct3, funct7-or-None) shapes: base instructions that
# RV32I and RV64I share with the same encoding.
LOADS = {0, 1, 2, 4, 5}        # lb lh lw lbu lhu (no ld, lwu)
STORES = {0, 1, 2}             # sb sh sw (no sd)
BRANCHES = {0, 1, 4, 5, 6, 7}
OPS = {(0, 0x00), (0, 0x20), (1, 0x00), (2, 0x00), (3, 0x00), (4, 0x00),
       (5, 0x00), (5, 0x20), (6, 0x00), (7, 0x00)}


def allowed(w):
    opcode, f3, f7 = w & 0x7f, (w >> 12) & 7, w >> 25
    if opcode in (0x37, 0x17, 0x6f):          # lui auipc jal
        return True
    if opcode == 0x67:                        # jalr
        return f3 == 0
    if opcode == 0x63:
        return f3 in BRANCHES
    if opcode == 0x03:
        return f3 in LOADS
    if opcode == 0x23:
        return f3 in STORES
    if opcode == 0x13:                        # shifts: 6-bit shamt on RV64
        return (f7 >> 1) == 0 if f3 == 1 else (f7 >> 1) in (0, 0x10) if f3 == 5 else True
    if opcode == 0x33:                        # excludes M (funct7 = 1)
        return (f3, f7) in OPS
    return w == 0x00000073                    # ecall


def reference(n):
    """Plain sieve over all of 0..n, independent of the odd-index layout."""
    flags = bytearray([1]) * (n + 1)
    flags[:min(2, n + 1)] = bytes(min(2, n + 1))
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            flags[p*p::p] = bytes(len(range(p*p, n + 1, p)))
    return flags


def budget(n):
    """The budget in CountingPrimesOddSieve.correct."""
    return 72 + 33 * n


def run(n):
    """Run the machine; check output, exit code and memory; return steps."""
    m = odd.initial(n)
    code = bytes(m.mem[:odd.BASE])
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
    primes = reference(n)
    assert output.getvalue() == f"{sum(primes)}\n", \
        f"N={n}: got {output.getvalue()!r}, want {sum(primes)}"
    assert bytes(m.mem[:odd.BASE]) == code, f"store changed code/padding for N={n}"
    k = (n + 1) // 2 if n > 1 else 0
    want = bytearray(len(m.mem) - odd.BASE)
    for i in range(1, k):
        want[i] = 1 - primes[2*i + 1]
    assert m.mem[odd.BASE:] == want, f"wrong flags for N={n}"
    assert steps <= budget(n), f"budget exceeded for N={n}"
    return steps


def main():
    source = (LEAN / "CountingPrimesOddSieve.lean").read_text()
    body = re.search(r"def prog : List \(BitVec 32\) := \[(.*?)\]", source, re.S)
    assert body, "Lean instruction list not found"
    words = re.findall(r"0x[0-9a-fA-F]+", body.group(1))
    assert [int(w, 16) for w in words] == odd.prog
    assert odd.BASE == 256 and odd.PAD == 16 and odd.MAX_N == 10**11 - 1
    print("same machine code as the Lean proof: PASS", flush=True)

    assert all(allowed(w) for w in odd.prog), "instruction outside the shared base set"
    assert 4 * len(odd.prog) <= odd.BASE
    print(f"instruction set: PASS ({len(odd.prog)} words / {4 * len(odd.prog)} bytes)",
          flush=True)

    for n in [-1, odd.MAX_N + 1]:
        try:
            odd.initial(n)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted out-of-range input {n}")
    print("input boundaries: PASS", flush=True)

    cases = list(range(2001)) + [10_000, 100_000, 1_000_000]
    for p in [31, 37, 101, 113, 127, 317, 997]:   # around squares of primes
        cases += [p*p - 2, p*p - 1, p*p, p*p + 1]
    cases = sorted(set(cases))
    steps = {n: run(n) for n in cases}
    print(f"count, exit code, flags, code isolation and budget: PASS ({len(cases)} cases)",
          flush=True)

    cli = subprocess.run([sys.executable, str(HERE / "counting_primes_odd_sieve.py")],
                         input="100\n", capture_output=True, text=True, check=True)
    assert cli.stdout == "25\n" and not cli.stderr
    print("command line: PASS", flush=True)

    subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    exe = ROOT / ".lake" / "build" / "bin" / "counting_primes_odd_sieve"
    for n in [0, 1, 2, 3, 4, 5, 8, 9, 10, 24, 25, 26, 31, 32, 33, 49, 121, 991, 992, 993,
              1000, 10_000]:
        result = subprocess.run([str(exe)], input=f"{n}\n", capture_output=True,
                                text=True, check=True)
        assert result.stdout == f"{sum(reference(n))}\n", f"Lean model N={n}"
        assert not result.stderr
    for text in ["-1\n", "not a number\n", f"{odd.MAX_N + 1}\n"]:
        result = subprocess.run([str(exe)], input=text, capture_output=True, text=True)
        assert result.returncode != 0 and result.stderr and not result.stdout
    print("Lean proof build and executable machine model: PASS", flush=True)

    print(f"\n{'N':>9}  {'pi(N)':>6}  {'instructions':>12}  {'per N':>6}")
    for n in [100, 1000, 10_000, 100_000, 1_000_000]:
        print(f"{n:>9}  {sum(reference(n)):>6}  {steps[n]:>12}  {steps[n] / n:>6.3f}")


if __name__ == "__main__":
    main()
