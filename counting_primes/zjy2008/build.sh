#!/bin/sh
# Compile src/zjy2008.cpp (zjy2008's pi, as ported in
# prime_benchmark/counting_primes_zjy2008.py) for RV64IM and link it with
# start.S. Then run gen_lean.py to refresh lean/ZjyBinary/Program.lean and
# counting_primes_zjy2008_rv64.py.
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
build="$here/build"
tool=${CROSS_COMPILE:-riscv64-linux-gnu-}
rm -rf "$build"
mkdir -p "$build"
set -- -march=rv64im -mabi=lp64 -mcmodel=medany -msmall-data-limit=0
"${tool}g++" "$@" -Os -std=c++17 -ffreestanding -fno-exceptions -fno-rtti \
  -fno-tree-loop-distribute-patterns -fno-threadsafe-statics -fno-asynchronous-unwind-tables -fno-unwind-tables -c \
  "$here/src/zjy2008.cpp" -o "$build/zjy2008.o"
"${tool}gcc" "$@" -nostdlib -static -T "$here/../../asm/link.ld" -Wl,--defsym=MEM_SIZE=0x400000 \
  -Wl,--build-id=none,--no-relax,--no-warn-rwx-segments \
  "$here/start.S" "$build/zjy2008.o" -o "$build/zjy2008.elf"
"${tool}objdump" -d -r "$build/zjy2008.elf" > "$build/zjy2008.dis"
