# grumpygordon #50137: verified rough-number algorithm

`lean/GrumpyGordon.lean` proves, without an input bound:

```lean
TinyFive.GrumpyGordon.correct (N : Nat) :
  TinyFive.GrumpyGordon.primePi N = TinyFive.CountingPrimes.countPrimes N
```

This includes **N = 100,000,000,000**. The left side is the executable
algorithm modeled on `prime_pi` in the commented C++ of
[`counting_primes_grumpygordon.py`](../../prime_benchmark/counting_primes_grumpygordon.py).
It does not call the reference prime counter or trial-division primality test.

From the repository root:

```sh
lake build
printf '1000\n100000000000\n' | .lake/build/bin/counting_primes_grumpygordon
# 168
# 4118054813
python3 counting_primes/grumpygordon/counting_primes_grumpygordon_test.py
```

## What the tables mean

Write `v = ⌊√N⌋`. At stage `p`, `C p x` counts integers in `[3,x]` with no
**proper** divisor in `[2,p)`. Thus it still includes primes already
processed. `pc = C p (p-1)` is the count of those odd primes. The small
array holds `C p (2i+1)`. The large array holds `C p (N/d)` for the sentinel
`d = 1` followed by the surviving denominators `p ≤ d ≤ v` in order. For
a non-sentinel live `d`, its index is **`small(d) - pc`** (`rough_rank`).

Initially `p = 3`, the denominators are odd, and the count at `x` is
`⌊(x-1)/2⌋` for positive `x`. The loop visits odd candidates with
`p² ≤ v` (equivalently `p⁴ ≤ N`); a rise from `small(p-1)` to `small(p)`
identifies a prime. It discards the multiples of `p` from the rough list,
including `p` itself. For each retained entry, the count at `x` decreases by
`C p (x/p) - pc`, with a zero decrement if `x < p²`. For a large entry at
`x = N/d`, the cofactor lookup reads the **old** large entry at denominator
`d*p` if `d*p ≤ v`, otherwise the old small entry at `N/(d*p)`.
`step_valid` proves these reads give the right values and that repacking
preserves the table equations, `pc`, and the exact sorted rough list.

## Why the sieve can stop early

At the first unprocessed stage `a` with `a⁴ > N`, `v < a²`. Every remaining
rough denominator up to `v` is therefore prime. A surviving composite up to
`N` can still have two or three prime factors (with multiplicity), not four.
The algorithm **freezes the tables here**. It does not finish the sieve.

For each remaining prime `q`, subtract the number of composites whose least
prime factor is `q`: `C q (N/q) - C q (q-1)`. The latter entry at `q-1` is
already exact. The former entry starts at the frozen `large(q)` and needs a
triple correction. Put `m = N/q`. For each earlier rough prime `r < q`
with `r² ≤ m`, subtract `small(m/r) - small(r-1)` from `large(q)`.
These are cofactors with least factor `r`. Both lookups are final because
`r,q ≥ a` implies `N/(r*q) ≤ v < a²`. Finally add one for the prime 2.

This is the source's final arithmetic regrouped by the **larger** member
`q` of a correction pair rather than the smaller one. In its one-based rough
indices `k`, `small(q-1) = pc + k - 1`; summing that over `k = 1,…,s-1`
gives `(s + 2*(pc-1))*(s-1)/2`. Similarly `small(r-1) = pc + l - 1`
explains the offset in the source's inner sum. Combining each subtraction
with its correction avoids signed intermediates. `telescope` proves the
least-factor sum identity; `finish_correct` applies it twice to establish
this frozen-table formula without assuming the result of the prime count.

## Proof and verification boundary

| Module | Key facts |
|---|---|
| `GrumpyOdd` | Odd initialization and prime-step identity, including `p=3`; reuses `LucyMath` and `SieveMath`. |
| `GrumpyTables` | Compact index `rough_rank`; `init_valid`, `step_valid`, `skip_valid`. |
| `GrumpyResidual` | Stable entries below `a²`, telescoping identity, correctness of the two residual sums. |
| `GrumpyGordon` | Exact cutoff rough list, terminating odd-stage loop, unconditional `correct`. |

`correct` concerns **Lean code over natural numbers**, not C++ semantics
or a binary (see the RV64IM machine proof below). The model uses exact integer division and a verified integer
square root. It rebuilds tables from snapshots rather than proving in-place
compaction/update order. Divisibility filtering and a small-table prime test
replace the skip bitmap; the two final sums are regrouped as above, not a
line-by-line refinement of the C++ loops. There is no claim about floating
point in the original submission, overflow, compilers, RV32 instructions,
I/O, memory limits, or an instruction/time bound. `#print axioms
TinyFive.GrumpyGordon.correct` lists only `propext`, `Classical.choice`, and
`Quot.sound`.

The regression checks intermediate tables and a nonzero triple correction,
compares the Lean executable with an independent sieve on small and medium
inputs (including square, cube and fourth-power neighbors), checks known
large values through `π(10¹¹)`, and spot-checks the local RV32 port. The
large cases do not allocate a sieve of size `10¹¹`; the proof does not depend
on any of the test outputs.

## RV64IM machine proof

`lean/GrumpyBinary/` proves that a recompiled RV64IM image of `prime_pi`
meets the same specification as the other prime counters:

```lean
TinyFive.GrumpyBinary.isCorrect : CountingPrimes.IsCorrect GrumpyBinary.initial'
TinyFive.GrumpyBinary.programSize_eq : programSize GrumpyBinary.initial' = 1016
```

That is, for every `n < 10^11`, the loaded machine (4 MiB of memory, input
`toString n ++ "\n"`, starting at PC 0) exits with code zero after printing
`π(n)` and a newline. The fuel is existential: there is one fuel value that works
for every input, but no explicit instruction budget is proved. The image is
1248 bytes, with 1236 bytes of code and a 12-byte data table.

`src/grumpygordon.cpp` is the C++ of `prime_pi` as ported in
`prime_benchmark/`, in 64-bit integers. `build.sh` compiles it with
`riscv64-linux-gnu-g++ -Os -march=rv64im` and links it with `start.S`.
`gen_lean.py` then writes `lean/GrumpyBinary/Program.lean` and
`counting_primes_grumpygordon_rv64.py`. The proof is about the instruction words in
`Program.lean`, not about the compiler. It refines the machine states to
`GrumpyGordon`'s rough list, tables and sums, so it reuses the algorithm proof
above instead of proving primality again.

| Module | What it proves |
|---|---|
| `Program`, `Exec`, `Attr`, `Tactic`, `Arith` | The image, instruction fetch, stores, and the `gexec` symbolic executor |
| `Layout`, `Memset`, `Newton`, `Init` | Arrays in memory, `memset` and the vector constructor, the integer square root, and the table-filling loops |
| `Setup` | Entry, parsing, the small cases `N ≤ 2`, and the stage-3 invariant at the outer loop |
| `SkipMath`, `Compact`, `RoundMath`, `Update`, `Round` | One sieve round: the skip bitmap, compacting `roughs` and `larges`, and the `smalls` update |
| `Outer` | The outer loop, up to the stage `a` with `N < a⁴` |
| `Finish`, `FinishMath`, `FinishRun` | The final sums, the triple correction, and printing the count |
| `Correct` | `isCorrect` and `programSize_eq` |

`#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound` for
both theorems. The machine runs 2,988 instructions at N = 1,000, 170,152 at
N = 10⁶, and 12,864,819 at N = 10⁹ (measured, not proved).

`python3 counting_primes/grumpygordon/counting_primes_grumpygordon_rv64_test.py` checks that the
Lean and Python images are the same words. It also compares the machine with a sieve on 2,175 inputs up to
2×10⁶, including neighbours of squares, cubes and fourth powers, and checks
`π(10⁷)`, `π(10⁸)` and `π(10⁹)`.

[The binary verification plan](BINARY_PROOF_PLAN.md) was written for the
unchanged RV32IM port. It was adapted to this RV64IM recompile, where every value up to
`10^11` fits in one register.
