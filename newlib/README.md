# newlib + printf on nanofive

C programs linked against [newlib](https://sourceware.org/newlib/) run on
nanofive. newlib's system call stubs (`syscalls.c`) map onto nanofive's
RARS-style ecalls: `_write` -> a7=11 per byte, `_read` -> a7=12, `_exit` ->
a7=93. Floating-point printf, multithreading and files are left out.

- `crt0.S`     — sets gp/sp, clears .bss, runs constructors, `exit(main())`
- `syscalls.c` — `_write/_read/_sbrk/_exit` + trivial stubs
- `link.ld`    — flat 1 MiB memory at address 0, stack at the top
- `hello.c`    — printf/snprintf/malloc test program
- `hello.elf`  — prebuilt hello.c for rv32im/ilp32, used by the test when no
  RISC-V gcc is installed
- `hello64.elf` — the same for rv64im/lp64 (runs on `machine64`). The vendored
  sources and the configure-generated headers in `vendor/build/` (made for
  rv32im) also compile as-is for rv64im/lp64
- `vendor/`    — the subset of newlib 4.4.0.20231231 sources and headers that
  hello.c actually links (41 sources, listed in `vendor/SOURCES`; license in
  `vendor/COPYING.NEWLIB`). `vendor/build/` holds the configure-generated
  headers (`newlib.h`, `_newlib_version.h`, `targ-include/`).
- `../newlib_test.py` — compiles vendor/ + hello.c for RV32 and RV64, loads
  each ELF into the matching machine, runs it, checks output

## Run

    sudo apt-get install gcc-riscv64-unknown-elf   # optional
    python3 newlib_test.py

## How vendor/ was produced

A full newlib was built for rv32im/ilp32 as below; hello.c was linked against
its libc.a with `-Wl,-Map` to find the archive members used, and the sources
of those members plus their header dependencies (from the `.deps` files) were
copied over. To use more of libc (e.g. sscanf), build newlib like this and link
against `$NANOFIVE/newlib-rv32im/riscv64-unknown-elf/lib/libc.a`, or vendor
more files.


    sudo apt-get install gcc-riscv64-unknown-elf texinfo
    wget https://sourceware.org/pub/newlib/newlib-4.4.0.20231231.tar.gz
    tar xzf newlib-4.4.0.20231231.tar.gz && mkdir nl-build && cd nl-build
    ../newlib-4.4.0.20231231/configure --target=riscv64-unknown-elf \
      --prefix=$NANOFIVE/newlib-rv32im --disable-multilib \
      --disable-newlib-supplied-syscalls --disable-newlib-io-float \
      --enable-newlib-io-long-long --disable-newlib-multithread \
      --enable-newlib-reent-small \
      CC_FOR_TARGET="riscv64-unknown-elf-gcc -march=rv32im -mabi=ilp32" \
      AR_FOR_TARGET=riscv64-unknown-elf-ar RANLIB_FOR_TARGET=riscv64-unknown-elf-ranlib \
      AS_FOR_TARGET=riscv64-unknown-elf-as LD_FOR_TARGET=riscv64-unknown-elf-ld \
      CFLAGS_FOR_TARGET="-O2 -g -mcmodel=medany"
    make -j$(nproc) all-target-newlib && make install-target-newlib
