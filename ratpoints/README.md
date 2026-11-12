# ratpoints on nanofive

[ratpoints](https://github.com/MichaelStollBayreuth/ratpoints) by Michael Stoll
searches for rational points of bounded height on hyperelliptic curves
y^2 = f(x). Here it is compiled for RV32IM (ilp32, soft float) against newlib
and GMP and run on nanofive; its output is byte-identical to a native x86-64
build of the same source.

- `build.sh`      — downloads and builds everything (below), writes `ratpoints.elf`
- `crt0.S`        — startup code that passes argc/argv to main
- `ratpoints.elf` — prebuilt, stripped (350 KB; 8 MiB memory, 256 KiB stack)
- `expected/`     — outputs of the native build for the test curves
- `../ratpoints_test.py` — runs the test curves on nanofive and compares
- `build/`        — sources and build trees (gitignored)

## Run

    python3 ratpoints_test.py                         # the test curves
    python3 ratpoints_test.py '1 0 -3 0 1 0 1' 50     # y^2 = x^6 + x^4 - 3x^2 + 1, height <= 50
    python3 ratpoints_test.py '-2 0 0 1' 1000 -q      # any ratpoints options

The instruction count and running time go to stderr. At ~400k instructions
per second, height bounds of a few hundred to a thousand are practical:

| test       | curve                         | arguments              | points | instructions | time  |
|------------|-------------------------------|------------------------|-------:|-------------:|------:|
| genus2     | y^2 = x^6 + x^4 - 3x^2 + 1    | 50                     | 10     | 1,905,237    | 4.1 s |
| quintic    | y^2 = x^5 - 3x^3 + 1          | 100                    | 8      | 748,663      | 1.6 s |
| quintic2   | y^2 = x^5 - x + 1             | 200 -q                 | 11     | 758,866      | 1.6 s |
| elliptic   | y^2 = x^3 - 2                 | 1000 -q                | 5      | 1,088,204    | 2.4 s |
| nopoints   | y^2 = 3x^6 + x^5 + x - 6      | 300                    | 0      | 2,523,473    | 5.4 s |
| interval   | y^2 = x^6 + x^4 - 3x^2 + 1    | 300 -l 0 -u 5 -q       | 7      | 4,494,395    | 9.8 s |
| verbose    | y^2 = 7x^6 + 6x^5 + ... + 1   | 10 -v                  | 6      | 438,072      | 1.0 s |
| (not in the test) | y^2 = x^6 + x^4 - 3x^2 + 1 | 1000 -q            | 10     | 10,112,458   | 22.8 s |

## Which version: 2.2.4, not 3.x

ratpoints 3.0.0 and later require a 64-bit `unsigned long` (`rp-private.h`
stops with `#error "ratpoints needs a 64-bit long since version 3.0.0; use
version 2.2.4 on this machine"`), and `long` is used throughout the code and
for the GMP interface (`mpz_set_si` etc.), so porting 3.x to ilp32 would be a
rewrite. The same repository's tag `v2.2.4` (a maintenance release from
September 2026) is the last version that supports a 32-bit long, and is what
is built here, unmodified. No source patches are needed.

## How it is built (`sh ratpoints/build.sh`)

Toolchain: `riscv64-unknown-elf-gcc` 13.2 (Ubuntu `gcc-riscv64-unknown-elf`)
with its rv32im/ilp32 multilib libgcc, all code compiled with
`-march=rv32im -mabi=ilp32 -mcmodel=medany`. Doubles are soft float (libgcc).
The native reference build needs `gcc`, `make` and `libgmp-dev`. The whole
build takes a couple of minutes.

1. **newlib 4.4.0.20231231**, configured exactly like `../newlib-rv32im`
   (see `../newlib/README.md`) except `--enable-newlib-io-float` instead of
   `--disable-newlib-io-float`: ratpoints prints its search intervals with
   `%f` and parses `-l`/`-u` with `sscanf("%lf")`. Installed into
   `build/newlib`, so the shared `newlib-rv32im` is not touched.

2. **Runtime**: `crt0.S` (here) and `../newlib/syscalls.c` (unchanged), put
   together in `build/libnanofive.a`. Linked with `../newlib/link.ld` and
   `--defsym=MEM_SIZE=0x800000 --defsym=STACK_SIZE=0x40000` (8 MiB flat
   memory; the heap of the runs above stays under 1 MiB).
   Link flags: `-nostdlib -nostartfiles -T link.ld -Wl,-u,_start ...
   -lm -Wl,--start-group -lc -lgcc -lnanofive -Wl,--end-group`.
   `crt0.o` sits in the archive and is pulled in by `-u _start` because
   libtool (in GMP's build) refuses plain `.o` files in `LDFLAGS`.

3. **GMP 6.3.0**, generic C:

       configure --host=riscv32-unknown-elf --disable-assembly \
         --disable-shared --enable-static \
         CC="riscv64-unknown-elf-gcc -march=rv32im -mabi=ilp32 -mcmodel=medany" \
         CFLAGS=-O2 CPPFLAGS="-isystem build/newlib/riscv64-unknown-elf/include" \
         LDFLAGS="<link flags above>" LIBS="<libraries above>" \
         AR=riscv64-unknown-elf-ar RANLIB=riscv64-unknown-elf-ranlib \
         NM=riscv64-unknown-elf-nm \
         gmp_cv_c_double_format="IEEE little endian"

   The last one presets a test that cross-compiling cannot run (GMP's
   configure links that test without `LDFLAGS`, which fails).

4. **ratpoints v2.2.4** (`git clone --branch v2.2.4`), with the flags of its
   Makefile for `CCFLAGS1 = ${CCFLAGS64}`, i.e. bit arrays of one
   `unsigned long` (32 bits on RV32; the SSE/AVX variants need x86 SIMD), and
   `RATPOINTS_CHUNK` left at its default for that case (1: a plain loop over
   words, left to the compiler):
   `-Wall -O2 -fomit-frame-pointer -DRATPOINTS_MAX_BITS_IN_PRIME=7`, plus
   `-funroll-loops` for sift.c and `-funroll-loops -O3` for init.c, as in the
   Makefile. The Makefile generates `init_sieve.h` and `find_points.h` by
   running `gen_init_sieve_h` and `gen_find_points_h`, whose output depends on
   the word size (they differ between 32 and 64 bits), so these two are
   compiled for RV32IM and run **on nanofive** (`ratpoints_test.py --run`;
   73k and 3.9M instructions). The ELF is stripped.

5. **Native reference**: the same source with `make ratpoints CCFLAGS1=`
   (64-bit unsigned long bit arrays) in `build/native/`. `ratpoints_test.py`
   compares against `expected/` and, if this binary exists, against its live
   output too.

## Command-line arguments

nanofive has no OS, so `ratpoints_test.py` passes arguments the way Linux
does: it writes argc, argv[0..argc-1], NULL and the strings at the top of
memory and sets sp to point at argc before starting at the ELF entry point.
`crt0.S` reads them from there, aligns sp down, and calls `main(argc, argv)`;
if sp is 0 it behaves like `../newlib/crt0.S` (argc = 0). The stack grows
down from below the argument block.

## Limitations

- Only the single-word (32-bit) bit-array configuration; no threads (2.2.4
  has none anyway).
- No changes to `machine.py` were needed.
