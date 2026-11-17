# Odds-only sieve with a word-summing count

```sh
printf '100\n' | python counting_primes_odd_sieve.py
# 25
python counting_primes_odd_sieve_test.py
```

A Sieve of Eratosthenes in **50 RV64I instructions (200 bytes)**, written to
execute few instructions: **1,846 at N = 1,000**, against 16,301 for
`../sieve/` and 12,787 for `../wheel/`. Like them it uses only base
instructions (no multiplication, division, stack, or library), and its
loaded machine code is proved correct in Lean.

The host reads `N`, allocates `256 + (N+1)/2 + 16` zeroed bytes, loads the
code, and puts `N` in `a0`. Marking, counting and printing are RISC-V code.
Inputs satisfy `0 ≤ N < 10^11`; memory is about `N/2` bytes, so the proof
covers inputs (about 50 GB near `10^11`) that the tests cannot run.

## What makes it cheaper

| N | `../sieve/` | `../wheel/` | this program |
|---:|---:|---:|---:|
| 100 | 1,412 | 1,078 | 184 |
| 1,000 | 16,301 | 12,787 | 1,846 |
| 10,000 | 179,049 | 143,735 | 21,621 |
| 100,000 | 1,912,823 | 1,559,509 | 248,210 |

These are executed emulator instructions, one per modeled `ecall`; they are
not CPU cycles or wall-clock time.

* **Odd numbers only.** Flag byte `i`, at address `256 + i`, stands for the
  odd number `2*i + 1`: zero means unmarked, one means composite. With
  `K = (N + [N > 1]) >> 1` flags in use, index 0 (the number 1) is never
  marked and stands in for the prime 2, so `π(N) = K − (marked flags below K)`.
  The `[N > 1]` term makes `N = 0, 1, 2` come out right with no branch.
* **Marking starts at `p*p` and stops once `p*p > N`.** There is no multiply
  instruction, so the address of the flag of `p*p` is tracked by addition:
  `(p+2)² = p² + 4p + 4` moves it by `p + (p+2)`.
* **A three-instruction mark loop** over flag addresses, tested at the
  bottom: `sb; add; bltu`. A stride of `p` flags is `2p` in numbers, so only
  odd multiples are visited.
* **Counting sums sixteen flags per iteration** with four `lw`. Each byte is
  0 or 1, so adding words keeps four independent byte "lanes" as long as no
  lane exceeds 255. A chunk is at most 496 bytes (124 words), so every lane
  is at most 124, and a short fold adds the lanes and subtracts them from the
  count. The top byte of each word is at most 1, so `lw` never sign-extends a
  negative value.
* The last count iteration may read up to 15 bytes past the last flag. Those
  bytes are never written, which is why the host allocates 16 bytes of padding.

At N = 1,000 the 1,846 instructions are roughly 1,371 marking (457 marks),
344 counting, 115 outer loop, and 16 setup and output.

## Proof

`lean/CountingPrimesOddSieve.lean` proves, on `TinyFive.Machine` at register
width 64:

```lean
theorem correct (n : Nat) (hn : n < 10^11) :
    ∃ fuel, fuel ≤ 72 + 33*n ∧
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n")
```

That is, for every supported input the loaded instruction words exit with
code zero after printing π(n) and a newline, within `72 + 33*n`
instructions. `correct_uniform_fuel` gives one fuel value, `72 + 33*10^11`,
that works for every input. The proof has no `sorry`, custom axioms, or
`native_decide`.

How the proof handles the unusual parts:

* **Marking needs no primality.** For an unmarked candidate `p`, its odd
  multiples from `p*p` are added to the marked set; for a marked candidate
  they are already there. Primality only enters at the end, once `p*p` is
  out of range (`OddSieveMath.lean`).
* **The square's address.** With `p = 2h + 1`, the flag index of `p*p` is
  `2h(h+1)`, so "`p*p ≤ N`" is just "that index is below `K`".
* **Byte lanes.** The four lanes are tracked as four natural numbers, each
  at most 124 within a chunk. `read_word` shows that a sign-extended `lw` of
  four 0/1 bytes equals their little-endian sum, and `fold_lanes` proves the
  fold.
* **Reads past the flags.** The flag invariant covers `K + 16` bytes, the
  last 16 of which are never written and so stay zero.
* **Small inputs.** `N = 0, 1, 2` need no special case: the outer loop runs
  zero times.

The budget is loose: measured cost is about 2 to 3 instructions per unit of
`N`, against 33 proved. Each candidate `p` is charged at most `8 + 3*(K/p)`;
the quotients are summed with the dyadic lemma
`TrialDivisionCost.quotientSum_le_dyadic` shared with the other programs,
using 19 blocks because candidates stay below `2^19`. The count costs at
most `22 + 10*(K/16) + 12*(K/496)`.

## Verification boundary

`counting_primes_odd_sieve_test.py` checks that Python and Lean contain the
same instruction words and that only base instructions are used; compares
the output, exit code and every flag byte against an independent sieve for
all `N` up to 2,000 and selected larger values; checks that the code bytes
are unchanged; checks every measured instruction count against the proved
budget; and builds the proof and runs its executable machine model.

The theorem applies to `TinyFive.Machine`. Host parsing and allocation,
equivalence of that model with the Python emulator, and refinement to the
official RISC-V semantics are checked by tests or not at all; they are not
proved.
