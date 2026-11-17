# RV64IM Lucy_Hedgehog prime counter in O(√N) memory

```sh
printf '1000\n' | python counting_primes_lucy.py
# 168
python counting_primes_lucy_test.py
```

This variant has **95 instructions (380 bytes)** and uses `mul`, `divu`,
`ld` and `sd` beyond the base instructions. The host allocates
`512 + 8 * (isqrt(N) + 1)` zeroed bytes, loads the code, and preloads `N`
in `a0`. The supported range is **`0 ≤ N < 10^11`**; near `10^11` the
tables take about 2.5 MB, where the sieves need 100 GB.

## The algorithm

Let `r` be the largest odd number with `r * r ≤ N`. For a stage `p`, let
`S(v)` be the number of `n` in `[5, v]` that are prime or have no prime
factor below `p`. Two tables of 64-bit slots are interleaved from address
512: `small[i]` holds `S(2i+1)` for `2i+1 ≤ r`, and `large[k]` holds
`S(N // k)` for odd `k ≤ r`. They start at stage 5, the count of numbers
coprime to 6, and stage `p` applies `S(v) -= S(v // p) - S(p - 1)` to
every `v ≥ p*p` when `p` is prime. `p` is prime exactly when
`small[(p-1)/2]` exceeds the running count `c = S(p - 1)`. `large[1]` lives
in a register, `large[k]` for `1 < k ≤ p` is left stale, and once
`N // (p*p) < p + 2` a short tail loop updates only `large[1]`. The answer
is `large[1] + 2`, and `N >> 1` for `N < 3`.

## Loaded-machine proof

`lean/CountingPrimesLucy.lean` proves:

```lean
CountingPrimesLucy.correct (n : Nat) (hn : n < 10^11) :
  ∃ fuel, fuel ≤ 26 + 41 * n ∧
    is_exited_with_output (run fuel (initial n))
      (toString (CountingPrimes.countPrimes n) ++ "\n")
```

It is a theorem about the loaded instruction words and the byte memory of
`TinyFive.Machine`, with no fuel or termination premise.
`correct_uniform_fuel` gives one fuel value, `26 + 41*10^11`, for every
input. The budget is crude (at most `11 * r + 60` instructions for each of
at most `r / 2` stages); the program actually runs in about `N^(3/4)`
instructions, 562 at `N = 1000`.

- `lean/LucyMath.lean` is the arithmetic, without Mathlib: the definition
  of `S`, the initial count `S_init`, the stage update `S_prime_step` with
  `S_small` and `S_composite` for what a stage leaves alone, the primality
  test `S_self`, the answer `countPrimes_eq`, the integer square root, and
  the facts about `kmax` and the floor identities the loops use.
- `lean/LucyMemory.lean` is the 8-byte load and store on byte memory.
- `lean/CountingPrimesLucy.lean` executes each straight-line block
  symbolically on natural numbers, with `omega` discharging each no-wrap
  side condition, and proves the loops by well-founded recursion:
  `init_loop`, `first_loop`, `second_loop`, `third_loop`, `tail_loop` and
  `outer_loop`.

The test checks that the Lean proof and the Python program hold the same
words, that the Python machine stays within the proved budget, and that
the executable Lean model prints what the Python machine prints.
