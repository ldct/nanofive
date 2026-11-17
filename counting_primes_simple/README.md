# Tiny prime counter

```
printf '100\n' | python counting_primes_simple.py
# 25
python counting_primes_simple_test.py
```

The payload is **23 RV32I instructions (92 bytes)** in a 128-byte machine.
It has no arrays, stack, memory writes, multiplication, or division.
Unlike the fast `counting_primes_*.py` submissions, it is intentionally
impractical for large inputs.

For a byte-array Sieve of Eratosthenes with its own RISC-V machine proof,
see `../counting_primes_sieve/`.

The Python adapter reads an integer `N`, checks `0 ≤ N ≤ 2147483646`,
loads it into `a0`, and starts the machine. The instructions themselves
count primes **less than or equal to N**, print the decimal count and a
newline, and exit. Input parsing is outside the proved machine program.

## Algorithm and proof idea

The code implements:

```
count = 0
for k = 2 .. N:
    d = 2
    while d < k:
        r = k
        while r >= d:
            r -= d
        if r == 0:
            break
        d += 1
    if d == k:
        count += 1
print(count)
```

* **Remainder loop (PC 24):** `r` is nonnegative and congruent to `k`
  modulo `d`. Subtraction preserves this invariant and strictly decreases
  `r`, since `d ≥ 2`. It exits with `r < d`, hence `r = k % d`.
* **Divisor loop (PC 16):** `2 ≤ d ≤ k` and no integer in `[2, d)`
  divides `k`. A zero remainder identifies a proper divisor, so the
  candidate is composite. Otherwise increasing `d` preserves the
  invariant and decreases `k - d`. Reaching `d = k` means exactly that
  `k` is prime; this also handles `k = 2` without a special case.
* **Candidate loop (PC 8):** `count` is the number of primes in
  `[2, k)`. The divisor loop increments it exactly when `k` is prime;
  increasing `k` preserves the invariant. There are at most
  `max(0, N - 1)` candidates, so this loop terminates too. When `k > N`,
  the count is precisely the number of primes at most `N`.
* **Machine arithmetic:** candidates reach at most `max(2, N + 1)`,
  divisors at most their candidate, and remainders never go negative.
  The input bound prevents register overflow and keeps the printed
  count within the signed 32-bit range. Branches use unsigned comparisons.

## Proved instruction bounds

For **every valid input `0 ≤ N ≤ 2^31 - 2`**, the loaded RISC-V program
terminates with the correct output within

```
11 + max(N - 1, 0) * (6 + 96*N)
```

instructions. Over the entire unchanged input range this is at most
**442,721,856,751,121,990,201 instructions**, strictly below `2^69`.
This is a conservative uniform bound, not an estimate of typical running time.

The machine proof first establishes the sharper input-dependent budget
`TrialDivisionCost.instructionBound N`:

```
11 + max(N - 1, 0) *
     (6 + sum over d = 2..N-1 of (6 + 3*floor(N/d)))
```

The eleven fixed instructions are initialization (2) and final
branch/printing/exit (9). For candidate `k` and divisor `d`, the remainder
loop executes exactly `1 + 3*floor(k/d)` instructions. Including the
divisor-test branches costs at most `6 + 3*floor(k/d)`.
We overcount by testing every possible divisor even when a composite
candidate would exit early, and by replacing every candidate with `N`.

To simplify the sum, partition the divisors into 30 intervals `[a, 2*a)`,
for `a = 2, 4, ..., 2^30`. Each contains `a` terms bounded by
`floor(N/a)`, so its quotient sum is at most
`a*floor(N/a) ≤ N`. Thus all quotient terms sum to at most `30*N`;
including the divisor-test overhead gives the `96*N` bound above.
No prime-density estimates or maximum-input execution are needed.

`../lean/TinyFive/TrialDivisionCost.lean` (shared with the sieve) proves the arithmetic bounds.
`CountingPrimes.correct_bounded`, `correct_quadratic_bound`, and
`correct_uniform_bound` connect them to termination and output of the
actual machine; `correct_numeric_bound` gives the literal uniform cap.
`correct_dyadic_bound` also allows fewer divisor buckets for smaller inputs.
The original `correct` theorem remains available.
Unlike the sieve's exact first-exit formula, these trial-division budgets
are upper bounds: they intentionally overcount early exits.

Each modeled `ecall` counts as one instruction. These are not bounds on
CPU cycles, interpreter wall-clock time, host input/allocation, or the
work performed inside system calls. Tests independently count emulator
steps, check a quotient-based reference count, and verify the bounds.

## Formal verification boundary

`lean/CountingPrimes.lean` contains the Lean proof against
`TinyFive.Machine`, the same small model used for `../abc101a/abc101_a.py`.
`CountingPrimes.correct` states that every supported input reaches a state
with exit code zero and output `toString (countPrimes N) ++ "\n"`.
`prime_iff_no_proper_divisor` connects its primality predicate to ordinary
natural-number divisibility.
The model includes instruction fetch/decode, wrapping registers, branches,
and printing/exit system calls. It is not a verified implementation of
`machine.py`, nor a proved refinement of the official RISC-V semantics.

`counting_primes_simple_test.py` checks that Python and Lean contain the
same instruction words, builds the proof with the pinned Lean toolchain,
compares the Python machine against an independent sieve, and checks the
executable Lean machine model. Tests support the Python/model connection;
they are not a proof of that connection.
