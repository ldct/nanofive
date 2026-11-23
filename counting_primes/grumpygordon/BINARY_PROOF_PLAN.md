# Verifying the grumpygordon RV32IM binary

> **Status:** this plan was adapted to an RV64IM recompile of the same
> `prime_pi` (`build.sh`, `src/grumpygordon.cpp`), and that proof is complete:
> see `lean/GrumpyBinary/Correct.lean` and the [README](README.md). The
> unchanged RV32IM port below is not verified.

## Target and acceptance criterion

Verify the **unchanged local RV32IM port** in
[`prime_benchmark/counting_primes_grumpygordon.py`](../../prime_benchmark/counting_primes_grumpygordon.py),
not a recompile, a smaller RV64 rewrite, or the original native Yosupo binary.
For every `n ≤ 10^11`, starting at PC 0 with the exact loaded image, 4 MiB of
memory, and canonical decimal input `toString n ++ "\n"`, prove that
`TinyFive.Machine 32` terminates without fault, exits with code zero, and
prints exactly `toString (countPrimes n) ++ "\n"`. The first whole-program
theorem can use existential fuel; prove a quantitative instruction bound
separately. Malformed input, native floating-point behavior, compiler
correctness, and refinement to hardware or to Python are out of scope.

The reference on the algorithm side is the existing theorem
`TinyFive.GrumpyGordon.correct`. The new work is the refinement from
machine states to the verified algorithm, not another primality proof.

## Image and proof boundaries

The image has 1,307 little-endian words (5,228 bytes). Its SHA-256 over the
packed words is `595b3361ef56d1a514af48c35f39c142c1c780453c8673ab9235ad39e4ce883e`.

| Byte address (decimal) | Boundary |
|---:|---|
| 0 | `_start` sets the stack pointer, calls `main`, exits via `ecall` 93 |
| 16 | `memset` |
| 48 | `isqrt` |
| 224 | `prime_pi` |
| 2344 | `main`; call at 2488, result handling starts at 2492 |
| 2692 | `__divdi3` |
| 3836 | `__udivdi3` |
| 4908 | Start of data; includes the division helper's lookup table |
| 5224 | Mutable heap cursor, initialized to 5232 |
| 5232 | Initial heap base |

## Milestones

1. **Pin and run the image in Lean.** Generate a Lean image from the
   Python literals and add a byte-for-byte identity check. Check decoding
   of the 1,227 instruction words before the data boundary, and verify
   fetch against a preserved read-only prefix. Do not include the heap
   cursor in that prefix. The shared model now implements the M operations
   this image uses, including `mulh`, `mulhu`, `div`, and `remu`; check
   the actual width-32 decode and semantics rather than assuming RV64
   coverage implies RV32 coverage. Run a Lean driver and compare selected
   outputs and register/memory checkpoints against Python. These are
   integration checks, not a correctness theorem.
2. **Prove reusable routine contracts.** Introduce a low/high register-pair
   interpretation and a call/return contract for registers, memory, and
   runtime state. Use `memset` as the first small machine proof. Then verify
   the actual `__udivdi3` and `__divdi3` instructions on the operand ranges
   reached by this program, including the lookup table and both-word
   paths. Prove integer square root using the division contract and the
   existing `isqrt_spec`. Independently verify the decimal input parser
   and printer; the printer uses an optimized division-by-ten sequence,
   not just a call to a verified division helper.
3. **Refine `prime_pi` phase by phase.** Relate live registers and memory
   regions to `GrumpyGordon.Valid` (defined in `GrumpyTables.lean`). Prove table allocation and zeroing,
   initialization, the bitmap's candidate/marking invariant, then one
   full outer-stage simulation. The abstract algorithm reads snapshots;
   the binary overwrites arrays. Track the scan and write cursors, prove
   every large-table source index is still readable when used, and prove
   the descending small-table updates read old cofactor values.
   Reuse `rough_rank`, `step_valid`, and `skip_valid` at stage boundaries.
4. **Prove the binary's finishing formula.** At the `p⁴ > n` cutoff, use
   `cutoff_roughs` to identify the remaining prime denominators. Prove that
   the binary's indexed, smaller-prime-first correction agrees with the
   larger-prime-first regrouping in `finish`, including the triangular
   term, the early break, and signed intermediate arithmetic. Connect
   the returned register pair to `finish_correct`.
5. **Compose from PC 0.** Chain startup, parsing, the `prime_pi` call,
   printing, and exit. Discharge all operand, memory, and termination
   premises from `n ≤ 10^11`; no assumed result for division, allocation,
   or the finishing formula may remain. Require `lake build`, an axiom
   audit, and regression checks for tiny inputs, fourth-power neighbors,
   a nonzero triple correction, and results above signed 32-bit range.
   Run the endpoint on the executable Lean machine when practical;
   any runtime cost of that test does not change the theorem's range.

## Bounds to establish early

- For `v = ⌊√n⌋` and `s = (v+1)/2`, the endpoint gives `v ≤ 316227`
  and `s ≤ 158114`. The three numeric arrays and the byte skip array use at
  most `16*s + (v+1)` bytes. Allowing seven alignment bytes per allocation
  puts the initial heap high-water bound at 2,851,312 bytes. Prove the
  actual allocation sequence and the stack's lowest reachable address
  before concluding that they never overlap.
- Audit every narrowing conversion, quotient, scale-to-byte-address,
  and signed/unsigned comparison under its branch guard. In particular,
  prove the large/small lookup split before narrowing a quotient to a
  small-table index. `π(10^11) = 4,118,054,813` is above `2^31-1`;
  do not interpret the return value as a signed single RV32 register.
- Keep ABI, memory, and arithmetic lemmas separate from control-flow
  proofs. Prove blocks between branch targets and summarize calls rather
  than symbolically unrolling the entire program. The first useful
  checkpoint is a byte-identical Lean harness and a verified `memset`;
  division and in-place stage refinement are the larger follow-on risks.
