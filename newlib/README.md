# newlib + printf on nanofive

C programs linked against [newlib](https://sourceware.org/newlib/) run on
nanofive. newlib's system call stubs (`syscalls.c`) map onto nanofive's
RARS-style ecalls: `_write` -> a7=11 per byte, `_read` -> a7=12, `_exit` ->
a7=93. Floating-point printf, multithreading and files are left out.

- `crt0.S`     — sets gp/sp, clears .bss, runs constructors, `exit(main())`
- `syscalls.c` — `_write/_read/_sbrk/_exit` + trivial stubs
- `link.ld`    — flat 1 MiB memory at address 0, stack at the top
- `hello.c`    — printf/snprintf/malloc test program
- `../newlib_test.py` — compiles hello.c, loads the ELF, runs it, checks output

## Build newlib (rv32im / ilp32)

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

Then `python3 newlib_test.py`.
