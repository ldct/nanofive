# lpha #195894: RV64IM machine proof

`lean/LphaBinary/` proves that an RV64IM recompile of lpha's `prime_count`
(Library Checker submission 195894, as ported in
[`prime_benchmark/counting_primes_lpha.py`](../../prime_benchmark/counting_primes_lpha.py))
meets the same specification as the other prime counters:

```lean
TinyFive.LphaBinary.isCorrect : CountingPrimes.IsCorrect LphaBinary.initial'
TinyFive.LphaBinary.programSize_eq : programSize LphaBinary.initial' = 1353
```

That is, for every `n < 10^11`, the loaded machine (4 MiB of memory, `n` in
`a0`, starting at PC 0) exits with code zero after printing `π(n)` and a
newline. As for grumpygordon, the fuel is existential: one fuel value works
for every input, but no instruction budget is proved. The image is 1536 bytes
of code.

## The program

`src/lpha.cpp` is the port's `prime_count`, unchanged except for the port's
own changes (marked `//*`: an integer square root, plain 64-bit divisions for
`divide_p` and `invs[]`). `start.S` calls it with `N` in `a0`, zero-extends
the `uint32_t` result, prints it and a newline, and exits. `build.sh` compiles
it with `riscv64-linux-gnu-g++ -Os -march=rv64im` and links it with
`start.S`; `gen_lean.py` then writes `lean/LphaBinary/Program.lean` and
`counting_primes_lpha_rv64.py`. The proof is about the instruction words in
`Program.lean`, not about the compiler. The tables (`smalls`, `larges`,
`roughs` as `uint32_t`, `invs` as `uint64_t`, `smooth` as bytes) are arrays
on `prime_count`'s 3.3 MiB stack frame.

The algorithm is grumpygordon's rough-number counter, so the proof refines
the machine states to the tables of [`GrumpyGordon`](../grumpygordon/README.md)
and reuses its algorithm proof and the value of its final sums
(`finish_value`). What is new is the 32-bit arithmetic:

* `larges` holds `uint32_t` values, and the final sum `ret` is a `uint32_t`.
  The proof tracks `ret` as a sign-extended 32-bit word of an integer and
  shows it ends as `π(N)` modulo `2^32`. The driver prints it zero-extended,
  so the output is right because `π(n) < 2^32` for every `n < 10^11`
  (`PiBound.countPrimes_lt`; `π(10^11 - 1) = 4118054813`).
* `k2_max = smalls[N / p / p] - pc` is computed in 32 bits and zero-extended,
  so the triple loop is right only if the subtraction never wraps.
  `NoWrap.nowrap` proves `smalls(N / q²) ≥ pc` for every row the loop reaches,
  from the row before, Bertrand's postulate (`Bertrand`, checked by `decide`
  below 159389) and `P⁴ ≤ N` for the last sieving prime `P`.

### `native_decide`

No short certificate exists for an upper bound on `π`, so `PiBound` defines a
Lucy_Hedgehog count `lucy`, proves `lucy N = countPrimes N` from
`LucyMath.S`, and evaluates `lucy (10^11 - 1)` once with `native_decide`
(about 30 seconds). This is the only use of `native_decide` in
`counting_primes/`: `#print axioms` lists `propext`, `Classical.choice`,
`Quot.sound` and `PiBound.lucy_val._native.native_decide.ax_1_1` for
`isCorrect`, and only the first three for `programSize_eq`. Kernel reduction
cannot evaluate a count of this size.

## Modules

| Module | What it proves |
|---|---|
| `Program`, `Exec`, `Tactic` | The image, instruction fetch, and the `lexec` symbolic executor (`gexec` of the grumpygordon proof with this image, plus address simprocs for constant offsets) |
| `Memset`, `Setup` | `memset`, the entry and prologue, the small cases `n ≤ 1`, the Newton loop, zeroing `smooth`, the table loop, and the stage-3 invariant `Inv` |
| `Mark`, `Compact`, `Update`, `Round` | One round of the sieve loop at 544: marking `smooth`, both compaction loops of `roughs`, `larges` and `invs`, the `smalls` update, and the whole loop up to the stage `a` with `isqrt N < a²` |
| `Bertrand`, `NoWrap` | Bertrand's postulate below 159389 and the no-wrap lemma for `k2_max` |
| `PiBound` | `π(n) < 2^32` for `n < 10^11` |
| `Finish` | The final sums in 32-bit arithmetic, the return, and printing the count |
| `Correct` | `isCorrect` and `programSize_eq` |

The machine runs 1,266,620 instructions at N = 1,000, 1,391,734 at N = 10⁶
and 12,513,341 at N = 10⁹ (measured, not proved); at small N most of them
clear `smooth`.

## Tests

`python3 counting_primes/lpha/counting_primes_lpha_rv64_test.py` checks that
the Lean and Python images are the same words. It also compares the machine
with a sieve on 2,175 inputs up to 2×10⁶, including neighbours of squares,
cubes and fourth powers, checks that the code is never overwritten, and checks
`π(10⁷)`, `π(10⁸)` and `π(10⁹)`. The proof does not depend on any of these
outputs.
