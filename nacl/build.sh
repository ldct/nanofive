#!/bin/sh
# Compile NaCl 20110221's crypto_core/salsa20/ref and crypto_core/hsalsa20/ref for RV64IM,
# with the same flags as tweetnacl/build.sh, and link each with its stand-alone driver.
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
build="$here/build"
tool=${CROSS_COMPILE:-riscv64-unknown-elf-}
rm -rf "$build"
flags="-march=rv64im -mabi=lp64 -mcmodel=medany -msmall-data-limit=0"
# build PRIMITIVE DRIVER: compile crypto_core/PRIMITIVE/ref and link it after DRIVER.
build() {
  include="$build/$1/include"
  mkdir -p "$include"
  cp "$here/vendor/crypto_core/$1/ref/api.h" "$here/vendor/MACROS" \
    "$here/vendor/PROTOTYPES.c" "$here/vendor/PROTOTYPES.cpp" "$include/"
  (cd "$include" && sh "$here/headers.sh" "$1" "crypto_core/$1/ref")
  "${tool}gcc" $flags -O2 -ffreestanding -fno-strict-overflow -I"$include" -c \
    "$here/vendor/crypto_core/$1/ref/core.c" -o "$build/$1/core.o"
  "${tool}gcc" $flags -nostdlib -T "$here/../asm/link.ld" \
    -Wl,--build-id=none,--no-relax,--no-warn-rwx-segments \
    "$here/$2" "$build/$1/core.o" -o "$build/nacl_$1.elf"
  "${tool}objdump" -d "$build/nacl_$1.elf" > "$build/nacl_$1.dis"
}
build salsa20 start.S
build hsalsa20 start_hsalsa20.S
