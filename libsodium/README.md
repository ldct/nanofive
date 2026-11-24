# libsodium's Salsa20 and HSalsa20 cores on NanoFive

`vendor/` contains unmodified files from libsodium 1.0.22: `crypto_core/salsa/ref`, which
implements `crypto_core_salsa20`, `crypto_core_salsa2012` and `crypto_core_salsa208` with one
static function `crypto_core_salsa(out, in, k, c, rounds)`; `crypto_core/hsalsa20/ref2`,
which implements `crypto_core_hsalsa20`; and the headers they include. See
`vendor/SOURCES` for provenance and hashes.

```sh
./libsodium/build.sh          # needs riscv64-unknown-elf-gcc and picolibc's headers; or:
docker run --rm -v "$PWD":/w -w /w nanofive-rvgcc ./libsodium/build.sh
python3 libsodium/gen_lean.py # regenerate the Program files of lean/LibsodiumSalsa20
python3 libsodium/libsodium_test.py
lake build LibsodiumSalsa20
```

The build uses GCC 13.2.0, RV64IM, LP64, `-O2 -fno-strict-overflow`, as `tweetnacl/build.sh`
does, with what libsodium's `configure` defines on a little-endian target (`CONFIGURED`,
`NATIVE_LITTLE_ENDIAN`, so `LOAD32_LE` and `STORE32_LE` are `memcpy`s, which GCC expands to
byte loads and stores). libsodium is hosted code, so it is compiled against picolibc's headers
rather than with `-ffreestanding`; no library is linked. `--gc-sections` keeps only
`crypto_core_salsa` and `crypto_core_salsa20`, which GCC does not inline into each other. The
driver `start.S` is `nacl/start.S` calling `crypto_core_salsa20`: it reads 64 bytes from
standard input, calls `crypto_core_salsa20(out, in, k, c)`, prints the 64 output bytes and
exits 0. `core_hsalsa20_ref2.c` is built the same way and linked after `start_hsalsa20.S`,
which calls `crypto_core_hsalsa20` and prints 32 bytes.

## Result

`lean/LibsodiumSalsa20/ForHumans/Salsa20IOResult.lean` proves

```lean
example : IsCorrect LibsodiumSalsa20.initial := LibsodiumSalsa20.IO.isCorrect
```

with `IsCorrect` from `tweetnacl/lean/TweetNaCl/ForHumans/Salsa20IOSpec.lean`, the definition
used for TweetNaCl and NaCl. The run takes 2,704 instructions, 2,165 of them in the call.
`ForHumans/Salsa20Result.lean` states the call by itself, for any input, key and constant;
in particular the `c != NULL` branch is the one taken.

## Proof

The proof is that of `nacl/`, reusing its `Wire`, `Symbolic` and `Reference` modules and their
soundness proofs: `Call.lean` replays the call to fix its schedule, runs the symbolic pass over
it and checks that every output byte has the normal form `Reference.core` gives it. `IO.lean`
is `nacl/lean/NaClSalsa20/IO.lean` with this program's addresses and counts.

## HSalsa20

`ForHumans/HSalsa20IOResult.lean` proves `IsCorrect LibsodiumSalsa20.HSalsa20.initial`, with
`IsCorrect` from `tweetnacl/lean/TweetNaCl/ForHumans/HSalsa20IOSpec.lean` and HSalsa20 from
`TweetNaCl/ForHumans/HSalsa20Spec.lean`. The run takes 2,430 instructions, 2,019 of them in
the call. `ForHumans/HSalsa20Result.lean` states the call by itself, with `c` the constant's
address; the `c == NULL` branch, which uses the constant "expand 32-byte k", is not covered.
The proof uses `nacl/lean/NaClSalsa20/HSalsa20Reference.lean`, as the NaCl one does.
