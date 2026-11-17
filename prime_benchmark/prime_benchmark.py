"""Measure all nine prime counters on a common input.

python prime_benchmark.py --n 1000 --repair-plummer --json prime_benchmark_results.json

Counts actual emulator steps, including startup, input/output, and exit.
Fixed-size programs need the explicit adapters in prime_benchmark_fixed.py.
The optional Plummer bounds repair is measured separately from the original.
No original program files are changed.
"""

import argparse
import ast
import contextlib
import importlib
import io
import json
from math import isqrt
from pathlib import Path
import re
from unittest.mock import patch

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # machine.py, elf.py
from machine import machine
from prime_benchmark_fixed import prepare

HERE = Path(__file__).resolve().parent
PROVEN = (
    "counting_primes_simple.py",
    "counting_primes_sieve.py",
    "counting_primes_wheel.py",
)
STDIN = (
    "counting_primes_lpha.py",
    "counting_primes_grumpygordon.py",
    "counting_primes_zjy2008.py",
)
FIXED = ("byte_sieve.py", "rosetta_sieve.py", "plummer_sieve.py")
PROGRAMS = PROVEN + STDIN + FIXED
# The proved programs are projects of their own, in ../<name without .py>/.
for name in PROVEN:
    sys.path.insert(0, str(HERE.parent / Path(name).stem))


def path(name):
    """Where the program `name` (one of PROGRAMS) is."""
    if name in PROVEN:
        return HERE.parent / Path(name).stem / name
    return HERE / name


def reference_count(n):
    primes = bytearray([1]) * (n + 1)
    primes[:min(2, n + 1)] = bytes(min(2, n + 1))
    for p in range(2, isqrt(n) + 1):
        if primes[p]:
            primes[p*p::p] = bytes(len(range(p*p, n + 1, p)))
    return sum(primes)


def load_words(name):
    """Read the literal image without running a module's top-level program."""
    for node in ast.parse(path(name).read_text()).body:
        if isinstance(node, ast.Assign) and any(
                isinstance(target, ast.Name) and target.id == "prog"
                for target in node.targets):
            words = ast.literal_eval(node.value)
            assert isinstance(words, list) and all(isinstance(w, int) for w in words)
            return words
    raise ValueError(f"literal prog not found in {name}")


def run_one(name, n, expected, max_steps, repair_plummer=False):
    row = {
        "program": name,
        "variant": "bounds-repaired" if repair_plummer else
                   "input-adapted" if name in FIXED else "original",
        "proved": name in PROVEN,
        "notes": [],
    }
    try:
        if name in PROVEN:
            module = importlib.import_module(Path(name).stem)
            m = module.initial(n)
            notes = ["Unmodified proved RV32I image; N is preloaded in a0."]
        elif name in STDIN:
            m = machine(mem_size=0x400000)
            m.write_i32_vec(load_words(name), 0)
            notes = ["Unmodified compiled RV32IM image; reads N from stdin."]
        else:
            m, notes = prepare(name, n, expected, repair_plummer=repair_plummer)
    except Exception as exc:
        row.update(status="not-run", error=f"{type(exc).__name__}: {exc}",
                   instructions=0, output="", pc=None)
        return row
    row["notes"] = notes

    instructions = 0
    step = m.step

    def counted_step():
        nonlocal instructions
        step()
        instructions += 1

    m.step = counted_step
    output = io.StringIO()

    try:
        with patch("sys.stdin", io.StringIO(f"{n}\n")), contextlib.redirect_stdout(output):
            m.run(start=0, steps=max_steps)
        if not m.halted:
            raise RuntimeError(f"exceeded {max_steps:,} instructions")
        if m.exit_code != 0:
            raise RuntimeError(f"exit code {m.exit_code}")
        text = output.getvalue()
        if name in FIXED:
            match = re.search(r"(\d+) primes", text)
            if match is None:
                raise AssertionError(f"no prime count in {text!r}")
            count = int(match.group(1))
        else:
            count = int(text.strip())
        if count != expected:
            raise AssertionError(f"pi({n}) = {count}, expected {expected}")
        row.update(status="ok", count=count)
    except Exception as exc:
        row.update(status="failed", error=f"{type(exc).__name__}: {exc}", pc=m.pc)
    row.update(instructions=instructions, output=output.getvalue())
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=1000)
    parser.add_argument("--program", choices=PROGRAMS, action="append")
    parser.add_argument("--max-steps", type=int, default=100_000_000)
    parser.add_argument("--repair-plummer", action="store_true",
                        help="also measure a separate Plummer row with its small-input bounds repair")
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    if args.n < 0 or args.max_steps < 1:
        parser.error("N must be nonnegative and max-steps must be positive")
    selected = list(args.program or PROGRAMS)
    if args.repair_plummer and "plummer_sieve.py" not in selected:
        selected.append("plummer_sieve.py")
    if any(name in FIXED for name in selected) and not 100 <= args.n <= 100_000:
        parser.error("fixed-image adapters support 100 <= N <= 100000")
    expected = reference_count(args.n)
    print(f"N = {args.n:,}; pi(N) = {expected:,}; full-program RV32 instruction counts",
          flush=True)
    results = []
    for name in selected:
        row = run_one(name, args.n, expected, args.max_steps)
        results.append(row)
        if row["status"] == "ok":
            print(f"{name:38} {row['instructions']:>14,}  "
                  f"{'proved' if row['proved'] else 'unproved'}", flush=True)
        else:
            print(f"{name:38} {row['status'].upper()} after {row['instructions']:,}: "
                  f"{row['error']} (PC {row['pc']})", flush=True)
    if args.repair_plummer:
        row = run_one("plummer_sieve.py", args.n, expected, args.max_steps, True)
        results.append(row)
        print(f"{'plummer_sieve.py (bounds-repaired)':38} {row['instructions']:>14,}  "
              f"{row['status']}, unproved", flush=True)
    if args.json:
        args.json.write_text(json.dumps({
            "n": args.n,
            "expected_count": expected,
            "measurement": "Successful machine.step calls from PC 0 through exit or failure, including ecalls.",
            "caveats": [
                "Fixed-size programs use documented constant-only adapters.",
                "The optional bounds-repaired Plummer row additionally changes one branch; the original is also run.",
                "Startup and program-specific input/output are included and differ.",
                "Each ecall and M-extension instruction counts as one instruction, not one CPU cycle.",
                "Host allocation, loading, and reference checking are excluded.",
                "Proof status refers only to the three unmodified proved program images.",
            ],
            "results": sorted(results, key=lambda row: (row["status"] != "ok",
                                                       row["instructions"])),
        }, indent=2) + "\n")


if __name__ == "__main__":
    main()
