# Counting primes

Three RISC-V RV32I programs that read `N` and print π(N), the number of
primes at most `N`. Each one's loaded machine code is proved correct in Lean
against the same specification, `CountingPrimes.countPrimes` in
`../lean/TinyFive/Primes.lean`: for every supported `N` the machine
terminates, exits with code zero, and prints the count and a newline.

| Folder | Algorithm | Code | Supported `N` | Instructions at N = 1,000 |
|---|---|---|---|---:|
| `simple/` | trial division by repeated subtraction | 23 instructions (92 bytes) | `0 ≤ N ≤ 2^31 - 2` | 2,799,716 |
| `sieve/` | byte-array Sieve of Eratosthenes | 25 instructions (100 bytes) | `0 ≤ N ≤ 2^30 - 1` | 16,301 |
| `wheel/` | sieve visiting only candidates coprime to 30 | 128 bytes + 12-byte gap table | `0 ≤ N ≤ 2^30 - 1` | 12,787 |

None of them uses multiplication, division, a stack, or a library. In each,
the Python host only parses `N`, sets up memory and puts `N` in `a0`; the
counting and printing are done by the RISC-V code.

```sh
printf '100\n' | python3 counting_primes/sieve/counting_primes_sieve.py
# 25
python3 counting_primes/sieve/counting_primes_sieve_test.py
```

Each folder holds the program (`counting_primes_<variant>.py`), its test,
a README explaining the algorithm and proof, and the proofs in `lean/`.
Each test checks that the Python program and the Lean proof contain the same
instruction words, runs `lake build` at the repository root (so `lake` must be
on PATH), and compares the program against an ordinary sieve and against the
executable Lean model.

Lemmas used by more than one variant are in `../lean/TinyFive/`:
trial-division budgets (`TrialDivisionCost`), sieve facts (`SieveMath`) and
memory lemmas (`SieveMemory`).

`../prime_benchmark/` measures these three against six third-party prime
programs on a common input; the instruction counts above come from there.
