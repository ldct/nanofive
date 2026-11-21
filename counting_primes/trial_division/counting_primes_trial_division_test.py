"""Regression tests and the Python/Lean instruction-word boundary.

Run: python counting_primes_trial_division_test.py
Requires the pinned Lean toolchain (`lake` on PATH).
"""

import contextlib
import io
from pathlib import Path
import random
import re
import subprocess
import sys

import counting_primes_trial_division as trial_division

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LEAN = HERE / "lean"


def sieve(n):
    flags = bytearray([1]) * (n + 1)
    flags[:min(2, n + 1)] = bytes(min(2, n + 1))
    for p in range(2, n + 1):
        if flags[p]:
            for multiple in range(p * p, n + 1, p):
                flags[multiple] = 0
    return sum(flags)


def instruction_bound(n):
    """Overcount every candidate by a full divisor scan of the input N."""
    scan = sum(6 + 3 * (n // d) for d in range(2, n))
    return 11 + max(0, n - 1) * (6 + scan)


def budget(n):
    """The budget in CountingPrimesTrialDivision.correct."""
    return 11 + 114 * n * n


def reference_instructions(n):
    """Count machine blocks using quotients, not repeated subtraction."""
    count = 11
    for k in range(2, n + 1):
        count += 4  # outer-loop setup and candidate increment
        for d in range(2, k):
            count += 3 + 3 * (k // d)  # trial setup and remainder loop
            if k % d == 0:
                count += 1  # composite branch
                break
            count += 3  # nonzero branch, increment divisor, jump
        else:
            count += 2  # prime branch and count increment
    return count


def run_python(n):
    m = trial_division.initial(n)
    code = bytes(m.mem)
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
    assert bytes(m.mem) == code, "program must not write memory"
    assert steps == reference_instructions(n), f"instruction count mismatch for N={n}"
    assert steps <= instruction_bound(n) <= budget(n), f"budget exceeded for N={n}"
    return output.getvalue()


def main():
    source = (LEAN / "CountingPrimesTrialDivision.lean").read_text()
    body = re.search(r"def prog : List \(BitVec 32\) := \[(.*?)\]", source, re.S)
    assert body, "Lean instruction list not found"
    words = re.findall(r"0x[0-9a-fA-F]+", body.group(1))
    assert [int(w, 16) for w in words] == trial_division.prog
    assert len(trial_division.prog) == 23
    print("same machine code: PASS (23 words / 92 bytes)")

    for n in [-1, trial_division.MAX_N + 1]:
        try:
            trial_division.initial(n)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted out-of-range input {n}")
    assert trial_division.initial(trial_division.MAX_N).x[10] == trial_division.MAX_N
    print("input boundaries: PASS")

    rng = random.Random(0)
    cases = sorted(set(range(101)) | {121, 169, 289, 997, 1000} |
                   {rng.randrange(101, 300) for _ in range(5)})
    for n in cases:
        assert run_python(n) == f"{sieve(n)}\n", f"N={n}"
    print(f"machine vs sieve, instruction counts, and budget: PASS ({len(cases)} cases)",
          flush=True)
    assert [reference_instructions(n) for n in range(4)] == [11, 11, 17, 32]

    cli = subprocess.run([sys.executable, str(HERE / "counting_primes_trial_division.py")],
                         input="100\n", capture_output=True, text=True, check=True)
    assert cli.stdout == "25\n" and not cli.stderr
    subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    exe = ROOT / ".lake" / "build" / "bin" / "counting_primes_trial_division"
    for n in [0, 1, 2, 3, 4, 9, 25, 49, 97, 121, 200, 1000]:
        result = subprocess.run([str(exe)], input=f"{n}\n", capture_output=True,
                                text=True, check=True)
        assert result.stdout == f"{sieve(n)}\n", f"Lean model N={n}"
        assert not result.stderr
    print("Lean build and executable model: PASS")


if __name__ == "__main__":
    main()
