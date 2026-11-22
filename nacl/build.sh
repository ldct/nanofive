#!/bin/sh
# Compile NaCl 20110221's crypto_core/salsa20/ref for RV64IM, with the same flags as
# tweetnacl/build.sh, and link it with the stand-alone driver start.S.
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
build="$here/build"
tool=${CROSS_COMPILE:-riscv64-unknown-elf-}
rm -rf "$build"
mkdir -p "$build/include"
cp "$here/vendor/crypto_core/salsa20/ref/api.h" "$here/vendor/MACROS" \
  "$here/vendor/PROTOTYPES.c" "$here/vendor/PROTOTYPES.cpp" "$build/include/"
(cd "$build/include" && sh "$here/headers.sh")
set -- -march=rv64im -mabi=lp64 -mcmodel=medany -msmall-data-limit=0
"${tool}gcc" "$@" -O2 -ffreestanding -fno-strict-overflow -I"$build/include" -c \
  "$here/vendor/crypto_core/salsa20/ref/core.c" -o "$build/core.o"
"${tool}gcc" "$@" -nostdlib -T "$here/../asm/link.ld" \
  -Wl,--build-id=none,--no-relax,--no-warn-rwx-segments \
  "$here/start.S" "$build/core.o" -o "$build/nacl_salsa20.elf"
"${tool}objdump" -d "$build/nacl_salsa20.elf" > "$build/nacl_salsa20.dis"
