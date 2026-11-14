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
see `counting_primes_sieve.py` and `counting_primes_sieve.md`.

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

## Formal verification boundary

`lean/TinyFive/CountingPrimes.lean` contains the Lean proof against
`TinyFive.Machine`, the same small model used for `abc101_a.py`.
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
