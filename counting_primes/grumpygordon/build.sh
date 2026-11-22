#!/bin/sh
# Compile src/grumpygordon.cpp (grumpygordon's prime_pi, as ported in
# prime_benchmark/counting_primes_grumpygordon.py) for RV64IM and link it with
# start.S. Then run gen_lean.py to refresh lean/GrumpyProgram.lean and
# grumpy_rv64_words.py.
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
build="$here/build"
tool=${CROSS_COMPILE:-riscv64-linux-gnu-}
rm -rf "$build"
mkdir -p "$build"
set -- -march=rv64im -mabi=lp64 -mcmodel=medany -msmall-data-limit=0
"${tool}g++" "$@" -Os -std=c++17 -ffreestanding -fno-exceptions -fno-rtti \
  -fno-tree-loop-distribute-patterns -fno-threadsafe-statics -fno-asynchronous-unwind-tables -fno-unwind-tables -c \
  "$here/src/grumpygordon.cpp" -o "$build/grumpygordon.o"
"${tool}gcc" "$@" -nostdlib -static -T "$here/../../asm/link.ld" -Wl,--defsym=MEM_SIZE=0x400000 \
  -Wl,--build-id=none,--no-relax,--no-warn-rwx-segments \
  "$here/start.S" "$build/grumpygordon.o" -o "$build/grumpygordon.elf"
"${tool}objdump" -d -r "$build/grumpygordon.elf" > "$build/grumpygordon.dis"
