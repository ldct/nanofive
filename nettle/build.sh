#!/bin/sh
# Compile Nettle 3.10.2's salsa20-core-internal.c for RV64IM, with the flags of
# tweetnacl/build.sh, and link _nettle_salsa20_core with the stand-alone driver start.S.
# Nettle is hosted code: it is compiled without -ffreestanding against picolibc's headers.
# GCC calls memcpy for the 64-byte copy of the state; it comes from picolibc 1.8.6's
# rv64im/lp64 libc.a (the Ubuntu package picolibc-riscv64-unknown-elf), the only member
# the link takes from it. Nettle keeps its asserts (no NDEBUG); assert.S supplies the
# __assert_func they call.
# -fno-tree-slp-vectorize: at -O2, GCC 13 otherwise packs pairs of the 32-bit state words into
# 64-bit registers before storing them, and the symbolic pass of the proof
# (nacl/lean/NaClSalsa20/Symbolic.lean) tracks only the low 32 bits of a register.
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
build="$here/build"
tool=${CROSS_COMPILE:-riscv64-unknown-elf-}
rm -rf "$build"
mkdir -p "$build"
set -- -march=rv64im -mabi=lp64 -mcmodel=medany -msmall-data-limit=0
"${tool}gcc" "$@" --specs=picolibc.specs -O2 -fno-strict-overflow -fno-tree-slp-vectorize -I"$here/vendor" -c \
  "$here/vendor/salsa20-core-internal.c" -o "$build/core.o"
"${tool}gcc" "$@" --specs=picolibc.specs -nostartfiles -nodefaultlibs -T "$here/../asm/link.ld" \
  -Wl,--build-id=none,--no-relax,--no-warn-rwx-segments \
  "$here/start.S" "$build/core.o" "$here/assert.S" -lc -o "$build/nettle_salsa20.elf"
"${tool}objdump" -d "$build/nettle_salsa20.elf" > "$build/nettle_salsa20.dis"
