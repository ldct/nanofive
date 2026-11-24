#!/bin/sh
# Compile libsodium 1.0.22's crypto_core/salsa/ref and crypto_core/hsalsa20/ref2 for RV64IM,
# with the flags of tweetnacl/build.sh, and link crypto_core_salsa20 with the stand-alone
# driver start.S and crypto_core_hsalsa20 with start_hsalsa20.S.
# CONFIGURED and NATIVE_LITTLE_ENDIAN are what libsodium's configure defines on a
# little-endian target. libsodium is hosted code: it is compiled without -ffreestanding
# against picolibc's headers (no libc is linked), so GCC expands its 4-byte memcpy calls.
# --gc-sections drops the functions the driver does not reach.
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
build="$here/build"
src="$here/vendor/src/libsodium"
tool=${CROSS_COMPILE:-riscv64-unknown-elf-}
rm -rf "$build"
mkdir -p "$build"
set -- -march=rv64im -mabi=lp64 -mcmodel=medany -msmall-data-limit=0
"${tool}gcc" "$@" --specs=picolibc.specs -O2 -fno-strict-overflow -ffunction-sections \
  -DCONFIGURED=1 -DNATIVE_LITTLE_ENDIAN=1 -I"$src/include/sodium" -c \
  "$src/crypto_core/salsa/ref/core_salsa_ref.c" -o "$build/core.o"
"${tool}gcc" "$@" -nostdlib -T "$here/../asm/link.ld" \
  -Wl,--build-id=none,--no-relax,--no-warn-rwx-segments,--gc-sections \
  "$here/start.S" "$build/core.o" -o "$build/libsodium_salsa20.elf"
"${tool}objdump" -d "$build/libsodium_salsa20.elf" > "$build/libsodium_salsa20.dis"
"${tool}gcc" "$@" --specs=picolibc.specs -O2 -fno-strict-overflow -ffunction-sections \
  -DCONFIGURED=1 -DNATIVE_LITTLE_ENDIAN=1 -I"$src/include/sodium" -c \
  "$src/crypto_core/hsalsa20/ref2/core_hsalsa20_ref2.c" -o "$build/hcore.o"
"${tool}gcc" "$@" -nostdlib -T "$here/../asm/link.ld" \
  -Wl,--build-id=none,--no-relax,--no-warn-rwx-segments,--gc-sections \
  "$here/start_hsalsa20.S" "$build/hcore.o" -o "$build/libsodium_hsalsa20.elf"
"${tool}objdump" -d "$build/libsodium_hsalsa20.elf" > "$build/libsodium_hsalsa20.dis"
