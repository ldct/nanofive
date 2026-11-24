# NaCl's Salsa20 and HSalsa20 cores on NanoFive

`vendor/` contains unmodified files from the NaCl release 20110221: the reference
implementations `crypto_core/salsa20/ref` and `crypto_core/hsalsa20/ref`, and the inputs from which NaCl's `do` script
generates its headers. See `vendor/SOURCES` for provenance and hashes. `headers.sh` repeats
that part of `do`.

```sh
./nacl/build.sh             # needs riscv64-unknown-elf-gcc; or, with Docker:
docker run --rm -v "$PWD":/w -w /w nanofive-rvgcc ./nacl/build.sh
python3 nacl/gen_lean.py    # regenerate the Program files of lean/NaClSalsa20 from the ELFs
python3 nacl/nacl_test.py
lake build NaClSalsa20
```

The build uses the flags of `tweetnacl/build.sh` (GCC 13.2.0, RV64IM, LP64, `-O2`), and links
`core.c` after the driver `start.S`. The driver reads 64 bytes from standard input, calls
`crypto_core_salsa20_ref`, prints the 64 output bytes and exits 0. `hsalsa20/ref/core.c` is linked the same way after
`start_hsalsa20.S`, which calls `crypto_core_hsalsa20_ref` and prints 32 bytes.

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

## HSalsa20

`ForHumans/HSalsa20IOResult.lean` proves `IsCorrect NaClSalsa20.HSalsa20.initial`, with
`IsCorrect` from `tweetnacl/lean/TweetNaCl/ForHumans/HSalsa20IOSpec.lean` and HSalsa20 from
`TweetNaCl/ForHumans/HSalsa20Spec.lean`. The run takes 2,587 instructions, 2,176 of them in
the call. `ForHumans/HSalsa20Result.lean` states the call by itself.

`hsalsa20/ref` adds the initial state back after the rounds and then subtracts the input and
constant words again. GCC cancels the two, so the code is the same as for `hsalsa20/ref2`,
which has no feed-forward. `HSalsa20Reference.lean` is therefore the spec over the same
abstract algebra, and `HSalsa20Call.lean` and `HSalsa20IO.lean` are `Call.lean` and `IO.lean`
with this function's output, addresses and counts.
