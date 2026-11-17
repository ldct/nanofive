# Counting primes

Four RISC-V RV64I programs that read `N` and print π(N), the number of
primes at most `N`. Each one's loaded machine code is proved correct in Lean
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
| `simple/` | trial division by repeated subtraction | 23 instructions (92 bytes) | `11 + 114*n*n` | `11 + 114*10^22` ≈ 1.14×10²⁴ | 2,799,716 |
| `sieve/` | byte-array Sieve of Eratosthenes | 25 instructions (100 bytes) | `13 + 189*n` | `13 + 189*10^11` ≈ 1.89×10¹³ | 16,301 |
| `wheel/` | sieve visiting only candidates coprime to 30 | 128 bytes + 12-byte gap table | `15 + 191*n` | `15 + 191*10^11` ≈ 1.91×10¹³ | 12,787 |
| `odd_sieve/` | odds-only sieve marking from p², counting 16 flags per iteration | 50 instructions (200 bytes) | `72 + 33*n` | `72 + 33*10^11` ≈ 3.3×10¹² | 1,846 |

The uniform bound is the budget at `n = 10^11`; each program's
`correct_uniform_fuel` proves that this one fuel value works for every input.

The budgets are loose upper bounds. Each one comes from bounding a sum of
quotients `n/d` by dyadic blocks (`TrialDivisionCost.quotientSum_le_dyadic`):
36 blocks cover every input below `10^11 < 2^37`, and `odd_sieve/` needs only
19 because it stops at `√n`. The three sieves need memory proportional to
`n` (50 to 100 GB near `10^11`), so the proofs cover inputs that no test can run.

None of them uses multiplication, division, a stack, or a library, and
they use only base instructions, so the same words also run on RV32. In each,
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
except `odd_sieve/`'s, which its own test measures.
