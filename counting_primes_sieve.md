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

The proof covers the actual instruction words, decoding, wrapping
register arithmetic, memory operations, and modeled output/exit calls.
As with the trial-division proof, the model's equivalence to `machine.py`
and official RISC-V semantics is **not** proved. Input parsing and host
allocation are outside the machine theorem.

Tests check identical Python/Lean instruction words, counts against an
independent sieve, every final composite flag, preservation of code bytes,
and the executable Lean machine model. They support—but do not prove—the
Python/model correspondence.
