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
and return PC `0x70000`. Argument registers point to those buffers, and the
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
at both the helper and wrapper entries. This does not verify HSalsa20
or the variable-length stream wrapper.

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
