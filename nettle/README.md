# Nettle's Salsa20 core on NanoFive

`vendor/` contains unmodified files from GNU Nettle 3.10.2: `salsa20-core-internal.c`, which
defines `_nettle_salsa20_core(uint32_t *dst, const uint32_t *src, unsigned rounds)`, and the
headers it includes. See `vendor/SOURCES` for provenance and hashes.

```sh
./nettle/build.sh             # needs riscv64-unknown-elf-gcc and picolibc; or:
docker run --rm -v "$PWD":/w -w /w nanofive-rvgcc ./nettle/build.sh
python3 nettle/gen_lean.py    # regenerate lean/NettleSalsa20/Program.lean from the ELF
python3 nettle/nettle_test.py
lake build NettleSalsa20
```

Nettle's core works on the 16-word Salsa20 state rather than on input, key and constant.
The driver `start.S` therefore reads the 64 bytes of standard input (input, key, constant, as
for TweetNaCl, NaCl and libsodium) in seven pieces to where `Salsa20Spec.initialState` holds
them, calls `_nettle_salsa20_core(dst, src, 20)`, prints the 64 output bytes and exits 0.

The build uses GCC 13.2.0, RV64IM, LP64, `-O2 -fno-strict-overflow`, as `tweetnacl/build.sh`
does, against picolibc's headers, with two differences:

* `-fno-tree-slp-vectorize`. Without it GCC packs pairs of state words into 64-bit registers
  before storing them, and the symbolic pass this proof shares with `nacl/` tracks only the
  low 32 bits of each register. The source is unchanged.
* The program links picolibc 1.8.6's `memcpy` (from the `rv64im/lp64` `libc.a` of Ubuntu's
  `picolibc-riscv64-unknown-elf`), which GCC calls to copy the state, and `assert.S`, an
  `__assert_func` that exits 1, for Nettle's `assert((rounds & 1) == 0)`. The proof covers both
  as linked code; the assert never fires.

`Program.lean` holds the whole loaded image: the code and the `.rodata` with the assert's
strings.

## Result

`lean/NettleSalsa20/ForHumans/Salsa20IOResult.lean` proves

```lean
example : IsCorrect NettleSalsa20.initial := NettleSalsa20.IO.isCorrect
```

with `IsCorrect` from `tweetnacl/lean/TweetNaCl/ForHumans/Salsa20IOSpec.lean`, the definition
used for TweetNaCl, NaCl and libsodium. The run takes 2,931 instructions, 2,373 of them in the
call. `ForHumans/Salsa20Result.lean` states the call by itself: for any 64-byte state, it
writes `Salsa20Spec.coreBytes` of the state.

## Proof

* `Call.lean` is `nacl/lean/NaClSalsa20/Call.lean` for this call: the replay fixes the
  schedule, including `memcpy` and the branch on `rounds`, and the symbolic pass of `nacl/`
  checks each output byte against `Reference.core`, with the input, key and constant atoms
  at their offsets in the state (`statePos`). `coreBytes_split` turns that into a statement
  about `coreBytes` of the whole state.
* `IO.lean` follows `nacl/lean/NaClSalsa20/IO.lean`, with seven reads in place of three.
