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

The theorem concerns **Lean code over natural numbers**, not C++ semantics
or a binary. The model uses exact integer division and a verified integer
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
