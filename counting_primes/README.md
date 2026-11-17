# Counting primes

Four RISC-V programs that read `N` and print π(N), the number of
primes at most `N`: three in RV64I and one, `lucy/`, that also uses `mul`,
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
| `simple/` | trial division by repeated subtraction | 23 instructions (92 bytes) | `11 + 114*n*n` | `11 + 114*10^22` ≈ 1.14×10²⁴ | 2,799,716 |
| `sieve/` | byte-array Sieve of Eratosthenes | 25 instructions (100 bytes) | `13 + 189*n` | `13 + 189*10^11` ≈ 1.89×10¹³ | 16,301 |
| `wheel/` | sieve visiting only candidates coprime to 30 | 128 bytes + 12-byte gap table | `15 + 191*n` | `15 + 191*10^11` ≈ 1.91×10¹³ | 12,787 |
| `lucy/` | Lucy_Hedgehog counting in O(√N) memory | 95 instructions (380 bytes) | `26 + 41*n` | `26 + 41*10^11` ≈ 4.1×10¹² | 562 |

The uniform bound is the budget at `n = 10^11`; each program's
`correct_uniform_fuel` proves that this one fuel value works for every input.

The budgets are loose upper bounds. Each of the first three comes from bounding a sum of
quotients `n/d` by 36 dyadic blocks (`TrialDivisionCost.quotientSum_le_dyadic`),
which cover every input below `10^11 < 2^37`. The sieve and wheel need
memory proportional to `n` (about 100 GB near `10^11`), so the proofs cover
inputs that no test can run.

`lucy/` needs only `8 * (isqrt(n) + 1)` bytes of tables; its budget
charges at most `11*r + 60` instructions to each of at most `r/2` stages,
where `r*r ≤ n`.

The first three use no multiplication, division, stack, or library, and
only base instructions, so the same words also run on RV32. In each of the four,
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

`../prime_benchmark/` measures these three against six third-party prime
programs on a common input; the instruction counts above come from there.
