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
comparison and SHA-512 routines directly.

## Starting a machine-code proof

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

No correctness or constant-time theorem is claimed here.
