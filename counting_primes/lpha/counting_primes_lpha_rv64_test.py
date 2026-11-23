"""Test the recompiled RV64IM lpha image that lean/LphaBinary proves correct.

Run: python3 counting_primes/lpha/counting_primes_lpha_rv64_test.py
Checks that the Lean proof is about the same instruction words as the Python program,
then compares the machine's output with a plain sieve (small inputs, and the neighbours of
squares, cubes and fourth powers, where the tables and the sieve cutoff change), checks the
exit code and that the code is never overwritten, and checks known values of pi(10^k).
The proof does not depend on any of these outputs.
"""

import contextlib
import io
from math import isqrt
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import counting_primes_lpha_rv64 as rv64  # noqa: E402

CODE_BYTES = 1536  # the code
SIEVE_LIMIT = 2 * 10**6
KNOWN = {10**7: 664_579, 10**8: 5_761_455, 10**9: 50_847_534}


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


def run_machine(n):
    """Run the image on N = n and return its output."""
    m = rv64.initial(n)
    code = bytes(m.mem[:CODE_BYTES])
    output = io.StringIO()
    with contextlib.redirect_stdout(output):
        m.run(start=0)
    assert m.halted and m.exit_code == 0, f"bad exit for N={n}"
    assert bytes(m.mem[:CODE_BYTES]) == code, f"store changed the code for N={n}"
    return output.getvalue()


def main():
    source = (HERE / "lean" / "LphaBinary" / "Program.lean").read_text()
    body = re.search(r"def prog : List \(BitVec 32\) := \[(.*?)\]", source, re.S)
    assert body, "Lean instruction list not found"
    words = [int(w, 16) for w in re.findall(r"0x[0-9a-fA-F]+", body.group(1))]
    assert words == rv64.prog, "Lean and Python images differ"
    assert 4 * len(words) == 1536 and rv64.MEM_SIZE == 4194304
    print("same machine code: PASS", flush=True)

    counts = prime_counts(SIEVE_LIMIT)
    powers = [k**e + d for k in range(2, 40) for e in (2, 3, 4) for d in (-1, 0, 1)
              if k**e + d <= SIEVE_LIMIT]
    cases = sorted(set(range(2001)) | set(powers) | {10**5, 10**6, SIEVE_LIMIT})
    for n in cases:
        assert run_machine(n) == f"{counts[n]}\n", f"wrong count for N={n}"
    print(f"count, exit code and code isolation: PASS ({len(cases)} cases)", flush=True)

    for n, expected in KNOWN.items():
        assert run_machine(n) == f"{expected}\n", f"wrong count for N={n}"
    print("known values up to pi(10^9): PASS")
    print("all tests: PASS")


if __name__ == "__main__":
    main()
