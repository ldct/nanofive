#!/bin/sh
# Compile src/lpha.cpp (lpha's pi, as ported in
# prime_benchmark/counting_primes_lpha.py) for RV64IM and link it with
# start.S. Then run gen_lean.py to refresh lean/LphaBinary/Program.lean and
# counting_primes_lpha_rv64.py.
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
build="$here/build"
tool=${CROSS_COMPILE:-riscv64-linux-gnu-}
rm -rf "$build"
mkdir -p "$build"
set -- -march=rv64im -mabi=lp64 -mcmodel=medany -msmall-data-limit=0
"${tool}g++" "$@" -Os -std=c++17 -ffreestanding -fno-exceptions -fno-rtti \
  -fno-tree-loop-distribute-patterns -fno-threadsafe-statics -fno-asynchronous-unwind-tables -fno-unwind-tables -c \
  "$here/src/lpha.cpp" -o "$build/lpha.o"
"${tool}gcc" "$@" -nostdlib -static -T "$here/../../asm/link.ld" -Wl,--defsym=MEM_SIZE=0x400000 \
  -Wl,--build-id=none,--no-relax,--no-warn-rwx-segments \
  "$here/start.S" "$build/lpha.o" -o "$build/lpha.elf"
"${tool}objdump" -d -r "$build/lpha.elf" > "$build/lpha.dis"
