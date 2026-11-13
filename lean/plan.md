# Plan: bridging the machine model to Sail

## Goal

`TinyFive/Abc101a.lean` proves `abc101_a` correct on the small machine model of
`TinyFive/Machine.lean`. That model is trusted: nothing says it is RISC-V. The bridge replaces
that trust with a proof that, for the instructions the program uses, one step of the small model
is one step of the Sail-generated RISC-V model.

After the bridge, what remains trusted is:

- the Sail model and its translation to Lean;
- the system-call handler (`TinyFive.ecall`), which Sail knows nothing about;
- the link between the Lean `prog` and the Python one, checked by `abc101_a_lean_test.py`.

## Target statement

Sail has no notion of the RARS system calls: an `ecall` traps to `mtvec`. So the machine the
final theorem talks about is a hybrid:

- at an `ecall`, apply `TinyFive.ecall` to the registers, input and output;
- at any other instruction, take one step of the Sail model.

The theorem is `Abc101a.correct` restated for the hybrid machine at `w = 64`: from a state with
`prog` in memory and the machine in the plain configuration described below, the hybrid machine
exits with code 0 having printed the tally.

## What exists to build on

`BasisResearch/ship-your-interpreter` proves a C interpreter binary correct against the same
Sail model. From its README, `docs/PORTING.md` and `Vsa/Machine.lean`, the reusable parts are:

| Part | Where | Use here |
| --- | --- | --- |
| Sail RV64D model in Lean, executable | `riscv-lean/` | the reference semantics |
| `Step`, `Halts`, `Diverges` over `stepOnce` | `Vsa/Machine.lean` | the Sail side of the hybrid step |
| `decodeW`: the Sail decoder simplified once | `Vsa/Sim/DecodeNF.lean` | decode facts for our words by `rfl` |
| one step rule per instruction class | `VsaIris/Vsa/StepRules.lean` | the Sail side of each instruction lemma |

Facts checked on 2026-11-13: it pins Lean `v4.34.0` (this project pins `v4.34.1`), it depends on
`iris-lean`, the repository is about 1,200 files with a long build, and GitHub reports no
license for it.

## Open questions, to answer before writing proofs

1. **License.** With no license on ship-your-interpreter, its code cannot be vendored or
   depended on without permission. The Sail model under `riscv-lean/` comes from
   `opencompl/sail-riscv-lean`; check that repository's license and depend on it directly if
   ship-your-interpreter stays unlicensed. In that case `Vsa/Machine.lean`, `decodeW` and the
   step rules serve as a design to follow, not as code to import.
2. **Shape of the step rules.** Are they stated as plain equations about `stepOnce` on a Sail
   state, or only inside the Iris machine logic? The bridge needs the former. If they are
   Iris-only, the instruction lemmas are proved directly against `stepOnce`.
3. **Memory map.** The small model loads `prog` at address 0. Does the Sail model, as
   configured there, have RAM at address 0, or only from `0x80000000`? See "Address offset"
   below.
4. **What `stepOnce` checks each step.** List what must hold for a step to be an ordinary
   fetch-decode-execute with no trap: privilege mode, `misa`, `mseccfg`, PMP, address
   translation, pending interrupts, the `tick` and `steps` arguments. This list is the plain
   configuration invariant.
5. **Build cost.** Measure the build of the Sail model alone. If it is long, keep the bridge in
   a separate Lake library so `TinyFive` and `Abc101a` still build in seconds.

## Design

### State relation

`Related (m : Machine 64) (σ : SailState)` holds when:

- registers `x1` to `x31` of `σ` equal `m.x.get`;
- the Sail `PC` equals `base + m.pc`;
- Sail memory at `base + a` equals `m.mem[a]` for every `a` in range;
- `σ` is in the plain configuration (question 4).

`m.input`, `m.output` and `m.status` have no Sail counterpart. They are carried by the hybrid
machine next to the Sail state.

### Address offset

If Sail RAM does not start at 0, then `base` is nonzero and the two machines disagree on
absolute addresses. `abc101_a` is unaffected: it uses only relative branches and jumps and never
loads or stores. Programs that take addresses (`JALR`, loads, stores, `AUIPC`) would need the
small model to load at `base` too. Decide this when a second program is bridged; for
`abc101_a` a relation with an offset is enough.

### Instruction lemmas

For each instruction class the program uses (`ADDI`, `BEQ`, `JAL`):

> if `Related m σ` and the word at `m.pc` decodes to `i`, then `stepOnce` on `σ` succeeds with
> some `σ'`, and `Related (exec i m) σ'`.

Each lemma is stated for the whole class (any registers and immediate), so it serves later
programs. Each must also show that the plain configuration is preserved.

Check first that the two decoders agree on the 20 words: `TinyFive.decode 64` against the Sail
decoder, by evaluation.

### Lifting

1. Define the hybrid step as above.
2. Prove: if `Related m σ` and `m` is running, a hybrid step from `(σ, m.input, m.output)`
   lands in a state related to `step m`. Non-`ecall` cases are the instruction lemmas; the
   `ecall` case holds by the definition of the hybrid step.
3. By induction on `n`, `run n m` is matched by `n` hybrid steps.
4. Transfer `Abc101a.correct`.

The proof of `Abc101a.correct` itself does not change.

## Steps

1. Answer the open questions. The answer to question 1 decides the dependency; the answers to 2
   and 4 decide how much is reused and how much is proved from scratch.
2. Add the Sail model as a dependency in a new Lake library (`TinyFiveSail`), and align the Lean
   toolchain with it.
3. Run `prog` on the executable Sail model through the hybrid step, on the inputs of
   `abc101_a_lean_test.py`, and compare with the small model. This tests the relation and the
   hybrid definition before any proof depends on them.
4. State the plain configuration and `Related`. Prove decoder agreement on the 20 words.
5. Prove the instruction lemma for `ADDI`. It exercises everything the others need: fetch,
   decode, register read and write, `PC` update, preservation of the configuration.
6. Prove the lemmas for `BEQ` and `JAL`.
7. Prove the lifting theorem and transfer `correct`.

Step 5 is where the difficulty is and where the plan could change. If one `ADDI` step against
`stepOnce` cannot be simplified in reasonable time, fall back to proving against the Sail
`execute` function for the instruction and treating fetch and the per-step checks as a second
stated assumption.

## Out of scope

- **Bridging the system calls.** Removing the handler from the trusted base means running real
  code at `mtvec` that implements the calls over HTIF, with the input placed in memory because
  Sail's HTIF has no input. That verifies a different image from the one in `abc101_a.py`, and
  needs trap entry and `mret` in the proof.
- **`w = 32`.** The Sail model in reach is RV64. The 32-bit theorem stays on the small model
  only.
- **Instructions beyond `ADDI`, `BEQ`, `JAL`.** Add a lemma per class when a program needs it.
  At `w = 64` the small model also lacks the RV64-only instructions, which a compiled RV64
  program would use.
