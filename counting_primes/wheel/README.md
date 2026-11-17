# RV32I mod-30 candidate-wheel sieve

```sh
printf '100\n' | python counting_primes_wheel.py
# 25
python counting_primes_wheel_test.py
```

This variant has **128 bytes of RV32I code and a 12-byte immutable gap
table**. The host allocates `256 + N + 1` zeroed bytes, loads that image,
and preloads `N` in `a0`. All candidate stepping, flag reads, composite
marking, counting, and output execute as RISC-V instructions.

The supported range is unchanged from the plain sieve:
**`0 ≤ N ≤ 2^30 - 1`**. Flags begin at address 256; zero means unmarked,
one means composite. Large inputs still require memory proportional to
`N`, and may exceed the host's available memory.

## What the wheel optimizes

The program processes 2, 3, and 5 first, then visits only the eight
residues coprime to 30:

```
7, 11, 13, 17, 19, 23, 29, 31, 37, 41, ...
```

From 7 onward its cyclic gaps are `4, 2, 4, 2, 4, 6, 2, 6`.
Three additional startup entries handle `2 → 3 → 5 → 7`.
The machine uses `lbu` to read the gap table at addresses 128 through 138,
and wraps the phase from 10 back to 3 after the step `31 → 37`.

This is specifically a **candidate wheel**. For an unmarked candidate
`p`, marking still visits `2*p, 3*p, ...` using a full byte array.
It does **not** pack flags into bits, compress addresses to wheel residues,
start at `p*p`, or use wheel-spaced marking. Those are separate possible
optimizations. This keeps the machine and proof small while skipping
unnecessary candidate checks. No multiplication, division, stack, or
external library is used.

## Loaded-machine proof

`lean/CountingPrimesWheel.lean` proves:

```lean
CountingPrimesWheel.correct (n : Nat) (hn : n ≤ 2^30 - 1) :
  ∃ fuel, (run fuel (initial n)).status = .exited 0 ∧
    (run fuel (initial n)).output =
      toString (CountingPrimes.countPrimes n) ++ "\n"
```

This is a theorem about the actual loaded instruction words and mutable
byte memory in `TinyFive.Machine`, not merely an abstract wheel algorithm.
It covers termination, exit status, and exact prime-count output for every
supported input, including 0 and 1. There is no fuel or termination premise.

The invariant states:

* the candidate and table phase match the startup or cyclic wheel sequence;
* the count equals `countPrimes (min N (p-1))`;
* each flag for `2 ≤ k ≤ N` records exactly whether a proper divisor
  below `p` divides `k`;
* capacity is unchanged and the first 140 bytes still match the loaded image.

Clipping the count with `min` handles a final wheel step that jumps past
`N`. `WheelMath.lean` proves every omitted integer has a proper divisor
2, 3, or 5 that has already been processed. Consequently omitting it
changes neither the count nor the flags that need to be set.

The machine proof includes decoding, actual table-byte loads, actual
flag-byte loads/stores, and preservation of both instructions and table.
The marking cursor advances by positive `p`; the candidate advances by a
gap between 1 and 6. Their recursive proofs establish termination.
The input bound prevents address and register wraparound.
The proof reuses `SieveMath.lean` and `SieveMemory.lean`, and contains no
`sorry`, custom axioms, or `native_decide`.

## Instruction measurements

The tests count executed emulator instructions, including one instruction
per modeled `ecall`:

| N | Plain sieve | Candidate-wheel sieve |
|---:|---:|---:|
| 100 | 1,412 | 1,078 |
| 10,000 | 179,049 | 143,735 |
| 100,000 | 1,912,823 | 1,559,509 |

At 100,000 the wheel saves about **18.5%** of instructions. Small inputs
can instead cost more because of the wheel's extra setup and phase update.
These are not CPU-cycle or wall-clock measurements.

The test's independent path-count formula is

```
15 + sum over wheel candidates p ≤ N of
    9 + (if prime(p) then 3 + 5*(floor(N/p)-1) else 0)
      + (if p % 30 = 1 then 2 else 0)
```

The fixed 15 is initialization (6) plus final branch/printing/exit (9).
A normal phase update takes five instructions; wrapping takes seven.
This formula is checked against execution, **not formally proved** as a
runtime theorem for this new variant. The correctness theorem proves
termination but does not provide a numerical instruction bound.

## Verification boundary

The tests check exact Python/Lean code-and-table identity, compare output
against an independent ordinary sieve, check every composite flag,
preserve code/table/padding, trace the exact coprime-to-30 candidate
sequence, and check instruction counts. They also build Lean and execute
its compiled machine-model driver, including small-input and wheel-wrap
boundaries.

The formal theorem applies to `TinyFive.Machine`. Host parsing/allocation,
equivalence to the Python emulator, and refinement to the official RISC-V
ISA or physical hardware are not formally proved. The executable checks
support those integration boundaries without claiming to prove them.
