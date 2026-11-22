# NaCl's Salsa20 core on NanoFive

`vendor/` contains unmodified files from the NaCl release 20110221: the reference
implementation `crypto_core/salsa20/ref` and the inputs from which NaCl's `do` script
generates its headers. See `vendor/SOURCES` for provenance and hashes. `headers.sh` repeats
that part of `do`.

```sh
./nacl/build.sh             # needs riscv64-unknown-elf-gcc; or, with Docker:
docker run --rm -v "$PWD":/w -w /w nanofive-rvgcc ./nacl/build.sh
python3 nacl/gen_lean.py    # regenerate lean/NaClSalsa20/Program.lean from the ELF
python3 nacl/nacl_test.py
lake build NaClSalsa20
```

The build uses the flags of `tweetnacl/build.sh` (GCC 13.2.0, RV64IM, LP64, `-O2`), and links
`core.c` after the driver `start.S`. The driver reads 64 bytes from standard input, calls
`crypto_core_salsa20_ref`, prints the 64 output bytes and exits 0.

## Result

`lean/NaClSalsa20/ForHumans/Salsa20IOResult.lean` proves

```lean
example : IsCorrect NaClSalsa20.initial := NaClSalsa20.IO.isCorrect
```

with `IsCorrect` from `tweetnacl/lean/TweetNaCl/ForHumans/Salsa20IOSpec.lean`, the definition
also used for TweetNaCl, and `initial := load 64 prog memSize []`. The run takes 2,855
instructions, 2,316 of them in the call. `ForHumans/Salsa20Result.lean` states the call by
itself, as `tweetnacl/lean/TweetNaCl/ForHumans/Salsa20Result.lean` does for TweetNaCl.

## Proof

* `Call.lean`: the public replay of `TweetNaCl.Salsa20Replay` fixes the instruction, branch
  and address schedule of the call.
* `Wire.lean`, `Symbolic.lean`: over that schedule, each 32-bit value and memory byte becomes
  a normal form, bit by bit: a constant XOR bits of atoms, where atoms are input bytes and
  sums. Shifts, rotations, XOR and ORs of disjoint bits are rewiring, so the normal form does
  not depend on how GCC orders or associates them. `WireSound.lean` and `SymbolicSound.lean`
  prove the normal forms sound.
* `Reference.lean`: the definitions of `Salsa20Spec`, over an abstract algebra. Over normal
  forms it gives the normal form of each byte of the spec. Over `BitVec` it is
  `Salsa20Spec.core`, by `rfl`.
* `Call.lean` checks, with `native_decide`, that both give each output byte the same normal
  form. `IO.lean` adds the driver, following `TweetNaCl.Salsa20IO`.
