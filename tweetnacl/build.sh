#!/bin/sh
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
build="$here/build"
tool=${CROSS_COMPILE:-riscv64-unknown-elf-}
mkdir -p "$build"
set -- -march=rv64im -mabi=lp64 -mcmodel=medany -msmall-data-limit=0
"${tool}gcc" "$@" -O2 -ffreestanding -fno-strict-overflow -c \
  "$here/vendor/tweetnacl.c" -o "$build/tweetnacl.o"
"${tool}ar" rcsD "$build/libtweetnacl.a" "$build/tweetnacl.o"
"${tool}gcc" "$@" -nostdlib -T "$here/../asm/link.ld" \
  -Wl,--build-id=none,--no-relax,--no-warn-rwx-segments \
  "$here/start.S" "$build/libtweetnacl.a" -o "$build/tweetnacl.elf"
