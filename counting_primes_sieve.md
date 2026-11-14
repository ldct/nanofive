# Small RISC-V sieve and correctness proof

```sh
printf '100\n' | python counting_primes_sieve.py
# 25
python counting_primes_sieve_test.py
```

The Sieve of Eratosthenes is **25 RV32I instructions (100 bytes)**.
The host reads `N`, allocates `128 + N + 1` zeroed bytes, loads the code,
and puts `N` in `a0`. All counting, flag loads, and composite marking
are performed by the RISC-V code—not by Python.

Flags start at address 128; a zero byte means unmarked, and one means
composite. The code scans candidates from 2 through `N`. For each unmarked
candidate `p`, it increments the count and marks `2*p, 3*p, ...` up to `N`.
Marked candidates are skipped. It prints the number of primes **at most N**
and a newline, then exits with code zero.

For simplicity it starts marking at `2*p`, not `p*p`, and scans through
`N` rather than stopping at its square root. It uses no multiplication,
division, stack, or external library.

Inputs satisfy `0 ≤ N ≤ 2^30 - 1`. This bound keeps all addresses,
candidate increments, marking increments, and the signed decimal count
in range. Memory use is linear in `N`; very large inputs require substantial
host memory.

## Proof

`lean/TinyFive/CountingPrimesSieve.lean` proves the **loaded machine code**
correct on the existing `TinyFive.Machine` model. Its `correct` theorem
establishes termination, exit code zero, and exact output
`toString (CountingPrimes.countPrimes N) ++ "\n"` for every supported input.
There is no assumed execution-fuel bound or termination premise.

The main invariant at candidate `p` is:

* the count equals the number of primes below `p`;
* for every `2 ≤ k ≤ N`, its flag is one exactly when a proper divisor
  `d` with `2 ≤ d < p` divides `k`;
* memory has the original capacity and all instruction bytes are unchanged.

Consequently an unmarked `p` is prime. Marking its proper multiples extends
the invariant from divisors below `p` to divisors below `p+1`. If `p` is
already marked, some smaller divisor `d` divides it; the same `d` divides
every multiple of `p`, so skipping `p` preserves the invariant.

The marking loop tracks which proper multiples lie below its current
index `j`. Each byte store marks exactly the next multiple; incrementing
`j` by positive `p` decreases the number of remaining iterations.
Increasing `p` terminates the candidate loop. The loader proof establishes
the initial zero flags; the memory proof shows that data stores preserve
instruction fetch and stay inside the allocated array.

Supporting modules:

* `SieveMath.lean`: divisor, skipping, and marking-progress lemmas.
* `SieveMemory.lean`: byte loads/stores, code-prefix preservation, and
  zero-initialized loader memory.
* `SieveCost.lean`: instruction budgets, monotonicity, and numerical bounds.
* `SieveCostBound.lean`: a tighter uniform bound using dyadic divisor blocks.

## Proved instruction bounds

There cannot be a 10,000-instruction cap over the entire valid input range:
even scanning all the candidates costs at least
`13 + 6 * max(N - 1, 0)` instructions.
`CountingPrimesSieve.still_running_10000` formally proves that input 2000
is still running after 10,000 instructions, without evaluating that long
execution in the proof.

The exact instruction count `SieveCost.instructionCount N` is:

```
13 + sum over p = 2..N of
    if p is prime then 9 + 5 * (floor(N/p) - 1)
    else 6
```

The 13 instructions are initialization (4) and final branch/printing/exit
(9). A composite candidate costs 6 instructions. A prime candidate costs
9, plus 5 for each composite-marking iteration. There are exactly
`floor(N/p) - 1` such iterations, starting at `2*p`.

`CountingPrimesSieve.correct_with_time` proves that running the actual
loaded machine for this budget exits successfully with the correct output.
`running_before` proves that every earlier state is still running;
`exited_iff_count_le` characterizes precisely which instruction budgets
have reached the exit. Thus the formula is the first-exit time, not merely
an oversized fuel allowance.
The cost lemmas also prove:

* **Every `0 ≤ N ≤ 600` finishes in at most 9,529 instructions**, strictly
  less than 10,000. The numerical budget at 600 is checked by Lean's kernel.
* For every supported input, a simple (deliberately loose) upper bound is
  `13 + max(N - 1, 0) * (9 + 5*N)`.
* **Every valid input `0 ≤ N ≤ 2^30 - 1` finishes in at most
  165,356,240,746 instructions**, strictly below `2^38`. This replaces
  `2^63` as the preferred uniform bound without restricting the input range.

The corresponding machine theorems are `correct_under_10000`,
`correct_bounded`, and `correct_bounded_rv32_dyadic` (or
`correct_under_rv32_dyadic_cap` for the rounded `2^38` bound).
The old `correct_under_rv32_cap` theorem remains available for compatibility.
The original valid input range and RISC-V instructions are unchanged.

### Why the tighter uniform bound is still simple

Partition candidates into 29 intervals `[a, 2*a)`, for
`a = 2, 4, ..., 2^29`. Each interval has `a` candidates and every quotient
`floor(N/p)` in it is at most `floor(N/a)`. Even overcounting by letting
**every** candidate mark multiples, its total cost is at most

```
a * (9 + 5*floor(N/a)) ≤ 9*a + 5*N.
```

Pad the scan to the end of these intervals; all added candidate costs
are nonnegative. Summing the interval bounds gives

```
T(N) ≤ 13 + 9*(2^30 - 2) + 145*N
     ≤ 165356240746                 for N ≤ 2^30 - 1.
```

This is a deterministic, conservative bound: no prime-density estimates,
probability assumptions, or evaluation at the maximum input are needed.
It uses only finite sums and elementary integer division. More generally,
`instructionCount_dyadic_upper` proves
`T(N) ≤ 13 + 9*(2^(k+1) - 2) + 5*k*N` whenever `N < 2^(k+1)`.

These bounds count executed RV32 instructions, including each `ecall` as
one instruction. They do **not** bound CPU cycles, Python/Lean interpreter
time, host-side input parsing or zero-initialized allocation, or the work
performed inside a modeled system call.

Tests count actual emulator instructions and compare them with the budget,
in addition to checking the prime counts and flag memory.

## Verification boundary

The proof covers the actual instruction words, decoding, wrapping
register arithmetic, memory operations, and modeled output/exit calls.
As with the trial-division proof, the model's equivalence to `machine.py`
and official RISC-V semantics is **not** proved. Input parsing and host
allocation are outside the machine theorem.

Tests check identical Python/Lean instruction words, counts against an
independent sieve, every final composite flag, preservation of code bytes,
and the executable Lean machine model. They support—but do not prove—the
Python/model correspondence.
