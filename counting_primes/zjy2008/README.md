# zjy2008 #346093: RV64IM machine proof

`lean/ZjyBinary/` proves that an RV64IM recompile of zjy2008's `pi`
(Library Checker submission 346093, as ported in
[`prime_benchmark/counting_primes_zjy2008.py`](../../prime_benchmark/counting_primes_zjy2008.py))
meets the same specification as the other prime counters:

```lean
TinyFive.ZjyBinary.isCorrect : CountingPrimes.IsCorrect ZjyBinary.initial'
TinyFive.ZjyBinary.programSize_eq : programSize ZjyBinary.initial' = 1239
```

That is, for every `n < 10^11`, the loaded machine (4 MiB of memory, `n` in
`a0`, starting at PC 0) exits with code zero after printing `π(n)` and a
newline. As for grumpygordon, the fuel is existential: one fuel value works
for every input, but no instruction budget is proved. The image is 1520 bytes:
1480 bytes of code, the 32-byte wheel table at 1480 and the 8-byte heap cursor
at 1512.

## The program

`src/zjy2008.cpp` is the port's `pi` in 64-bit integers, with the port's two
changes (an exact integer division for `fdiv`, an integer square root for
`sqrtl`) and without `inline`, so that `start.S` can call it. `build.sh`
compiles it with `riscv64-linux-gnu-g++ -Os -march=rv64im` and links it with
`start.S`; `gen_lean.py` then writes `lean/ZjyBinary/Program.lean` and
`counting_primes_zjy2008_rv64.py`. The proof is about the instruction words in
`Program.lean`, not about the compiler.

The algorithm is grumpygordon's rough-number counter: the same `small`,
`rough` and `large` tables, the same compaction and update in each round, and
the same final sums. The differences are that zjy2008 sieves with `calc(3)`,
`calc(5)` and then a mod-30 wheel (`p = 7, 11, 13, …`), calling `calc(p)` only
when `skip[p]` is clear, and that `calc` is a lambda reading the tables through
a closure on `pi`'s stack. The wheel only skips multiples of 2, 3 and 5, and
`skip[p]` is clear exactly when `p` is prime, so the rounds are grumpygordon's:
one per odd prime `p` with `p⁴ ≤ N`. The proof therefore refines the machine
states to the tables of [`GrumpyGordon`](../grumpygordon/README.md) and reuses
its algorithm proof and its finish (`finish_value`), instead of proving
primality again.

## Modules

| Module | What it proves |
|---|---|
| `Program`, `Exec`, `Tactic` | The image, instruction fetch, and the `zexec` symbolic executor (`gexec` of the grumpygordon proof with this image) |
| `Mark`, `Compact`, `Update`, `Calc` | One call of `calc(p)` for a prime `p` with `p⁴ ≤ N`: marking `skip`, compacting `rough` and `large`, the `small` update, and the stage-`p` memory invariant `ZMem` |
| `Wheel` | The mod-30 wheel loop, up to the stage `a` with `N < a⁴` |
| `Memset`, `Setup` | `memset`, the vector constructor, the entry and prologue, the small cases `n ≤ 6`, both Newton loops, the four tables, the closure, `calc(3)` and `calc(5)` |
| `Finish`, `FinishRun` | The final sums and the triple correction, and printing the count |
| `Correct` | `isCorrect` and `programSize_eq` |

`#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound` for
both theorems. The machine runs 3,138 instructions at N = 1,000, 189,683 at
N = 10⁶, and 14,701,116 at N = 10⁹ (measured, not proved).

## Tests

`python3 counting_primes/zjy2008/counting_primes_zjy2008_rv64_test.py` checks
that the Lean and Python images are the same words. It also compares the
machine with a sieve on 2,175 inputs up to 2×10⁶, including neighbours of
squares, cubes and fourth powers, checks that the code and the wheel table are
never overwritten, and checks `π(10⁷)`, `π(10⁸)` and `π(10⁹)`. The proof does
not depend on any of these outputs.
