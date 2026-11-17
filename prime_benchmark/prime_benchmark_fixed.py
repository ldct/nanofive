"""Input adapters for the three fixed-size RV32 prime images.

``prepare(filename, n, expected, repair_plummer=False)`` returns an unexecuted
machine at PC 0 and human-readable patch notes. By default only constant loads
and constant data change. The optional Plummer branch repair is an explicit
NON-CONSTANT algorithmic bug fix, for a separately labeled measurement.
The original files are parsed, never imported or modified. All sieving,
counting and printing still execute in their RV32 code. The caller must
independently check the printed count, not just the exit code: ``expected``
changes Plummer's validation constant, never its calculated count.

Supported common range: 100 <= n <= 100000. The existing zeroed VM memory
accommodates the larger flag arrays without overlapping the stack.
Plummer additionally rejects n=k*k-2: its original integer Newton loop oscillates
for the exclusive bound n+1=k*k-1. We reject rather than repair that algorithm.
Its original unsigned bulk-loop bound also underflows for many small inputs
(including 1000), causing out-of-bounds accesses. That defect is NOT repaired
unless explicitly requested; 16384 and 20000 work without algorithm changes.
"""

import ast
from math import isqrt
from pathlib import Path

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # machine.py, elf.py
from machine import machine


NAMES = ("byte_sieve.py", "rosetta_sieve.py", "plummer_sieve.py")


def _addi(rd, rs1, value):
    assert -2048 <= value <= 2047
    return ((value & 0xFFF) << 20) | (rs1 << 15) | (rd << 7) | 0x13


def _lui(rd, value):
    return (value & 0xFFFFF000) | (rd << 7) | 0x37


def _split(value):
    """Upper multiple of 4096 and signed low immediate for LUI/ADDI."""
    upper = (value + 2048) & ~4095
    return upper, value - upper


def _image(name):
    tree = ast.parse(Path(__file__).with_name(name).read_text())
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(
            isinstance(target, ast.Name) and target.id == "prog"
            for target in node.targets
        ):
            return ast.literal_eval(node.value)
    raise ValueError(f"No literal prog image in {name}")


def prepare(name, n, expected, *, repair_plummer=False):
    """Prepare a one-pass pi(n) run; retain each program's original output I/O."""
    name = Path(name).name
    if name not in NAMES:
        raise ValueError(f"Unsupported fixed image: {name}")
    if repair_plummer and name != "plummer_sieve.py":
        raise ValueError("repair_plummer applies only to plummer_sieve.py")
    if type(n) is not int or not 100 <= n <= 100000:
        raise ValueError("Fixed-image adapters support integer 100 <= n <= 100000")
    if type(expected) is not int or not 0 <= expected <= n:
        raise ValueError("expected must be an independently computed prime count")
    if name == "plummer_sieve.py":
        root = isqrt(n + 1)
        if n + 1 == (root + 1) ** 2 - 1:
            raise ValueError("Original Plummer Newton loop oscillates for this n+1")

    m = machine(mem_size=0x20000)
    m.write_i32_vec(_image(name), 0)
    notes = [
        f"{name}: original RV32 image, PC 0, 0x20000 bytes; inclusive pi({n}).",
        "Entire startup, algorithm, original output and exit execute on the VM.",
    ]

    def patch(addr, old, new, reason):
        actual = m.read_i32(addr) & 0xFFFFFFFF
        if actual != old:
            raise ValueError(
                f"{name} image changed at {addr}: {actual:08x} != {old:08x}"
            )
        if new != old:
            m.write_i32(new, addr)
            notes.append(f"@{addr}: 0x{old:08x} -> 0x{new:08x}: {reason}")

    def pair(hi_addr, hi_old, lo_addr, lo_old, rd, value, reason):
        upper, lower = _split(value)
        patch(hi_addr, hi_old, _lui(rd, upper), reason + " (upper)")
        patch(lo_addr, lo_old, _addi(rd, rd, lower), reason + " (lower)")

    if name == "byte_sieve.py":
        # flags[i] represents 2*i+3, i=0..length-1. The compiler keeps
        # a6=length-1, t1=flags+length, and a2=3*(i+1), terminating when
        # a2 == t4 == 3*(length+1). a7=flags+3*(i+1) is unchanged.
        length = (n - 1) // 2
        end = 3 * (length + 1)
        patch(36, 0x00A00F13, _addi(30, 0, 1), "ten iterations -> one")
        pair(32, 0x00002337, 48, 0x0FB30313, 6, 252 + length,
             "flags initialization exclusive end")
        pair(28, 0x00002837, 60, 0xFFE80813, 16, length - 1,
             "last odd index")
        if end <= 2047:
            patch(56, 0x00006EB7, _addi(29, 0, end),
                  "folded 3*(length+1) loop sentinel")
            patch(224, 0x69203031, int.from_bytes(b" 1 i", "little"),
                  "heading '10 iterations' -> ' 1 iterations'")
        elif end % 4096 == 0:
            patch(56, 0x00006EB7, _lui(29, end),
                  "folded 3*(length+1) loop sentinel")
            patch(224, 0x69203031, int.from_bytes(b" 1 i", "little"),
                  "heading '10 iterations' -> ' 1 iterations'")
        else:
            # Keep the original one-instruction constant load, with its value
            # in unused heading space. The shorter heading terminates at 226.
            patch(224, 0x69203031, int.from_bytes(b"1\n\0\0", "little"),
                  "short one-pass heading frees unused data word at 228")
            patch(228, 0x61726574, end, "folded 3*(length+1) loop sentinel data")
            patch(56, 0x00006EB7, (228 << 20) | (2 << 12) | (29 << 7) | 3,
                  "load loop-sentinel constant: lw t4,228(zero)")
        patch(96, 0x00000513, _addi(10, 0, 1),
              "initialize count to one to include prime 2")

        notes.append(
            f"One pass over {length} odd candidates 3..{2 * length + 1}; "
            "prime 2 is included by the RV32 count initializer, not host correction."
        )
    elif name == "rosetta_sieve.py":
        pair(196, 0x000027B7, 204, 0x70F78793, 15, n - 1,
             "initial prime count n-1")
        pair(200, 0x00002537, 212, 0x71050513, 10, n,
             "eratosthenes inclusive argument n")
        pair(320, 0x00002537, 324, 0x71050513, 10, n,
             "printed inclusive bound")
        notes.append(
            "Original prime-list loop below 100 and all of its output overhead "
            "are retained; n>=100 keeps that loop within the sieved range."
        )
    else:
        patch(1624, 0x000F4240, n + 1,
              "exclusive maxNumber n+1 implements inclusive pi(n)")
        pair(1436, 0x000137B7, 1440, 0x2A278793, 15, expected,
             "validation comparison only; calculated count remains untouched")
        # Keep the failure diagnostic truthful too; no successful-run overhead.
        text = f" {expected}!\n".encode().ljust(12, b"\0")
        for offset, old in enumerate((0x34383720, 0x0A213839, 0x00000000)):
            new = int.from_bytes(text[offset * 4:offset * 4 + 4], "little")
            patch(1528 + 4 * offset, old, new, "expected-count failure diagnostic")
        notes.append(
            f"Original output correctly says 'primes below {n + 1}'; "
            f"this is exactly pi({n}). Original validation/metadata output retained."
        )
        if repair_plummer:
            # s2 = iStop-cumOffset can be negative. In our supported range,
            # both the original operands fit signed 32 bits; signed comparison
            # then correctly skips the bulk loop and uses the bounded tail.
            patch(744, 0x04C96C63, 0x04C94C63,
                  "NON-CONSTANT bounds bug fix: BLTU -> BLT; negative "
                  "iStop-cumOffset skips bulk loop and uses bounded tail")
            notes.append(
                "SEPARATE REPAIRED VARIANT, not original constant-only code. "
                "The unchanged program banner 'faithful=yes' is original output, "
                "not a claim that this branch-repaired image is unmodified."
            )
        elif n < 16384:
            notes.append(
                "WARNING: original unsigned iStop-cumOffset bulk bound can "
                "underflow on small inputs (including 1000); no logic repair "
                "is applied. This run may fail out of bounds."
            )
    return m, notes


def _self_test():
    """Independent reference validation, including prime and composite bounds."""
    import contextlib
    import io
    import re

    for n in (100, 101, 997, 1000, 1001, 2000, 4098, 16384, 20000):
        expected = sum(
            all(k % divisor for divisor in range(2, isqrt(k) + 1))
            for k in range(2, n + 1)
        )
        for name in NAMES:
            repaired = name == "plummer_sieve.py" and n < 16384
            m, _ = prepare(name, n, expected, repair_plummer=repaired)
            output, instructions = io.StringIO(), 0
            with contextlib.redirect_stdout(output):
                while not m.halted and instructions < 1_000_000:
                    m.step()
                    instructions += 1
            match = re.search(r"(\d+) primes", output.getvalue())
            assert m.halted and m.exit_code == 0, (name, n, instructions)
            assert match and int(match[1]) == expected, (
                name, n, expected, output.getvalue()
            )
            label = " (bounds repair)" if repaired else ""
            print(f"{name:19} n={n:4} pi={expected:3} "
                  f"instructions={instructions}{label}")
    # Deliberately verify and retain the original N=1000 failure. A signedness
    # repair would be an algorithm change, not a constant-only adapter.
    m, _ = prepare("plummer_sieve.py", 1000, 168)
    successful = 0
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            for _ in range(300_000):
                m.step()
                successful += 1
                assert not m.halted
    except IndexError:
        assert m.pc == 776 and successful == 251172
    else:
        raise AssertionError("Expected original small-input buffer overrun")
    try:
        prepare("plummer_sieve.py", 1022, 172)
    except ValueError as exc:
        assert "oscillates" in str(exc)
    else:
        raise AssertionError("Newton oscillation input must be rejected")


if __name__ == "__main__":
    _self_test()
