# TweetNaCl on NanoFive

`vendor/` contains the unmodified upstream C release 20140427; see
`vendor/SOURCES` for provenance and hashes.

```sh
./tweetnacl/build.sh
python3 tweetnacl/tweetnacl_test.py
lake build TweetNaCl
```

The offline build uses `riscv64-unknown-elf-gcc` and binutils (override the
tool prefix with `CROSS_COMPILE`). It produces `build/libtweetnacl.a` and a
symbolized `build/tweetnacl.elf` for RV64IM/LP64 without libc. The ELF entry
point is a comparison smoke test. The ELF has no entropy source: its
`randombytes` exits with status 125 instead of generating keys. The archive
leaves `randombytes` to the caller. The emulator tests also call the linked
comparison, SHA-512, and Salsa20 routines directly.

## Salsa20 binary proof

`lean/TweetNaCl/ForHumans/Salsa20Result.lean` states `salsa20_correct`. For
every 16-byte input, 32-byte key, and 16-byte constant at the fixture's ABI
addresses, the linked `crypto_core_salsa20_tweet` writes exactly the 64 bytes
of the independent Salsa20/20 spec in `ForHumans/Salsa20Spec.lean`. It
returns zero after 11,550 model instructions, restores `sp` and `ra`, changes
no memory outside the 64-byte output and 528-byte stack frame, and follows
the same instruction, branch, and data-address trace for all such inputs.
That last claim concerns the model, not physical timing or other side channels.

**Call assumptions.** Memory is 1 MiB, with output at `0x80000`, input at
`0x80100`, key at `0x80200`, constant at `0x80300`, entry `sp = 0x100000`,
and return PC `0x11bc` (the instruction after the call in the program below). Argument registers point to those buffers, and the
wrapper and helper bytes match `Salsa20Program.lean`. Other registers, output,
stack, and unspecified memory may have arbitrary initial contents.

**Proof and trust.** The proof checks one public execution schedule, then
lowers it to fixed-address data operations and compares symbolic output
expressions for *arbitrary* inputs. The comparison is structural, not a
sample of keys or messages. The wide-word lemmas prove that the low 32 bits
of the RV64 arithmetic implement the spec's quarter rounds, and that the
loop's transposed column layout implements a double round every two
iterations. The closed binary certificates use Lean's `native_decide`;
their soundness lemmas are kernel proofs. The emulator tests compare the
linked words with the Lean image and run 13 independent reference cases
at both the helper and wrapper entries. HSalsa20 is proved below; the
variable-length stream wrapper is not verified.

## Salsa20 as a program

`lean/TweetNaCl/ForHumans/Salsa20IOResult.lean` proves `IsCorrect` from
`ForHumans/Salsa20IOSpec.lean` for the machine `load 64 prog 0x100000 []`. Given the 16
input, 32 key and 16 constant bytes on standard input (`ecall` 12), the machine prints the 64
bytes of `Salsa20Spec.core` (`ecall` 11) and exits with code zero. One fuel bound, 12,090
instructions, works for every input. The statement doesn't mention addresses, registers or
calling conventions.

`prog` in `Salsa20IOProgram.lean` is the linked helper and wrapper words at their linked
addresses, a `j driver` at address 0, and a hand-assembled 33-instruction driver at `0x1170`.
The driver reads the three buffers, calls `crypto_core_salsa20_tweet` with the fixture's
ABI, and prints the output buffer. The proof composes the driver loops with
`salsa20_correct`. The emulator test runs the same image on standard input for every Salsa20
case.

## HSalsa20 binary proof

`lean/TweetNaCl/ForHumans/HSalsa20Spec.lean` models HSalsa20 (Bernstein, *Extending the
Salsa20 nonce*, §2): the Salsa20 state of `Salsa20Spec`, the twenty-round permutation without
feed-forward, and words 0, 5, 10, 15, 6, 7, 8, 9 of the result. It checks NaCl's `core1` and
`core2` test vectors by `decide`.

`ForHumans/HSalsa20Result.lean` states `hsalsa20_correct`, with the call assumptions of the
Salsa20 proof and return PC `0x11e0`. The linked `crypto_core_hsalsa20_tweet` writes exactly the
32 bytes of `hsalsa20` and returns zero after 11,514 model instructions. It restores `sp` and
`ra`, changes no memory outside the 32-byte output and 528-byte stack frame, and follows one
instruction, branch and data-address trace for all inputs.

The proof reuses the Salsa20 machinery: `HSalsa20Replay` checks the schedule from the wrapper,
in which `core` takes its `h = 1` branch, and `HSalsa20Correct` compares the circuit of that
schedule with `HSalsa20Reference.hcore`. That branch still adds the initial state, then
subtracts the constant and input words again, reloaded from memory; `hcore` does the same, and
`hcore_concrete_eq_hsalsa20` shows that the added and subtracted words cancel exactly.

`ForHumans/HSalsa20IOResult.lean` proves `IsCorrect` from `ForHumans/HSalsa20IOSpec.lean` for
the machine `load 64 prog 0x100000 []` of `HSalsa20IOProgram.lean`: given input, key and
constant on standard input, it prints the 32 bytes of `hsalsa20` and exits with code zero,
within 11,926 instructions. The driver is the Salsa20 driver, placed after the HSalsa20
wrapper at `0x1194` and printing 32 bytes.

## Comparison proof target

* `lean/TweetNaCl/ForHumans/Spec.lean` gives the functional result for two
  32-byte inputs, independently of the machine code.
* `lean/TweetNaCl/Verify32Program.lean` records the linked entry address and
  all 14 instruction words for `crypto_verify_32_tweet`. The test checks them
  against the ELF built with GCC 13.2.0. If a toolchain change moves or
  changes this code, inspect the new disassembly before updating the image.

A first theorem can start `TinyFive.Machine 64` at `entry`, with those words
in memory, `a0` and `a1` pointing to readable 32-byte inputs, and `ra` set to
a valid return address. Show that the routine reaches `ra` after 231 steps
with `a0 = verify32Result left right` and unchanged memory. A useful loop
invariant is that the accumulator is the bitwise OR of the XORs of the byte
pairs processed so far.

The comparison theorem is not yet implemented.
