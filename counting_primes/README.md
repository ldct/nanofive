# Counting primes

Six RISC-V programs that read `N` and print π(N), the number of
primes at most `N`: five in RV64I and one, `lucy/`, that also uses `mul`,
`divu`, `ld` and `sd`. Each one's loaded machine code is proved correct in Lean
against the same specification, `CountingPrimes.countPrimes` in
`../lean/TinyFive/Primes.lean`. Each proof ends in a theorem `correct` of
the same shape:

```lean
theorem correct (n : Nat) (hn : n < 10^11) :
    ∃ fuel, fuel ≤ <budget> ∧
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n")
```

That is, for every `n < 10^11` the machine exits with code zero after
printing π(n) and a newline, within the budget's number of instructions.

| Folder | Algorithm | Code | Proved budget | Uniform bound (all `n < 10^11`) | Instructions at N = 1,000 |
|---|---|---|---|---|---:|
| `trial_division/` | trial division by repeated subtraction | 23 instructions (92 bytes) | `11 + 114*n*n` | `11 + 114*10^22` ≈ 1.14×10²⁴ | 2,799,716 |
| `sieve/` | byte-array Sieve of Eratosthenes | 25 instructions (100 bytes) | `13 + 189*n` | `13 + 189*10^11` ≈ 1.89×10¹³ | 16,301 |
| `wheel/` | sieve visiting only candidates coprime to 30 | 128 bytes + 12-byte gap table | `15 + 191*n` | `15 + 191*10^11` ≈ 1.91×10¹³ | 12,787 |
| `odd_sieve/` | odds-only sieve marking from p², counting 16 flags per iteration | 50 instructions (200 bytes) | `72 + 33*n` | `72 + 33*10^11` ≈ 3.3×10¹² | 1,846 |
| `lucy/` | Lucy_Hedgehog counting in O(√N) memory | 95 instructions (380 bytes) | `26 + 41*n` | `26 + 41*10^11` ≈ 4.1×10¹² | 562 |
| `odd_wheel/` | sieve storing only residues 1 and 5 mod 6 | 82 instructions (328 bytes) | `33 + 326*n + (15 + 10*(n+1))*(n+2)` | ≈ 1.0×10²³ | 725 |

The uniform bound is the budget at `n = 10^11`; each program's
`correct_uniform_fuel` proves that this one fuel value works for every input.

The budgets are loose upper bounds. The plain, mod-30, and odds-only
sieve budgets come from bounding a sum of quotients `n/d` by dyadic blocks
(`TrialDivisionCost.quotientSum_le_dyadic`): 36 blocks cover every input
below `10^11 < 2^37`, and `odd_sieve/` needs only 19 because it stops at
`√n`. The mod-6 wheel uses a coarser quadratic bound from charging each
candidate pair for up to `E+1` rounds in each marking loop, where `E` is
the number of live flags. The sieves use memory proportional to `n`, so
their proofs cover inputs too large for the ordinary tests.

`lucy/` needs only `8 * (isqrt(n) + 1)` bytes of tables; its budget
charges at most `11*r + 60` instructions to each of at most `r/2` stages,
where `r*r ≤ n`.

All but `lucy/` use no multiplication, division, stack, or library. They
use base instruction encodings; the proofs are for RV64. In each of the six,
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
quotient-sum and trial-division budgets (`TrialDivisionCost`), sieve facts
(`SieveMath`) and memory lemmas (`SieveMemory`). `is_exited_with_output` is
defined in `Machine`.

`../prime_benchmark/` measures the first three against six third-party prime
programs on a common input; the instruction counts above come from there,
except those of `odd_sieve/`, `lucy/`, and `odd_wheel/`, which their own tests measure.

## grumpygordon

[`grumpygordon/`](grumpygordon/README.md) verifies an executable Lean model
of the #50137 rough-number counter used in `prime_benchmark/`, for all
natural numbers. It also proves `IsCorrect` for an RV64IM recompile of the
same `prime_pi` (1016 bytes of `programSize`, 2,988 instructions at N = 1,000).
Unlike the table above, that proof uses existential fuel and has no explicit
instruction budget.

## zjy2008

[`zjy2008/`](zjy2008/README.md) proves `IsCorrect` for an RV64IM recompile of
zjy2008's `pi` (#346093), the fastest program in `prime_benchmark/` (1239 bytes
of `programSize`, 3,138 instructions at N = 1,000). It is grumpygordon's
algorithm with a mod-30 wheel over the sieving primes, so its machine proof
refines to the same tables and reuses grumpygordon's algorithm proof. Like
grumpygordon's, it uses existential fuel and has no explicit instruction budget.
