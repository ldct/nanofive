#!/bin/sh
# Build ratpoints 2.2.4 for nanofive (RV32IM, ilp32, soft float) -> ratpoints.elf,
# plus a native x86-64 build of the same source for reference output.
# See README.md. Everything is downloaded and built under ratpoints/build/
# (gitignored); only ratpoints.elf is written next to this script.
#
#   sh ratpoints/build.sh            # everything (newlib, GMP, ratpoints, native)
#   JOBS=4 sh ratpoints/build.sh
#
# Each stage leaves a stamp file and is skipped when re-run; rm -rf
# ratpoints/build to start over.
set -eu

HERE=$(cd "$(dirname "$0")" && pwd)
NANOFIVE=$(dirname "$HERE")
B=$HERE/build
JOBS=${JOBS:-$(nproc)}
mkdir -p "$B"

TARGET=riscv64-unknown-elf
ARCH="-march=rv32im -mabi=ilp32 -mcmodel=medany"
CC_RV="$TARGET-gcc $ARCH"

NEWLIB=newlib-4.4.0.20231231
NEWLIB_URL=https://sourceware.org/pub/newlib/$NEWLIB.tar.gz
NEWLIB_SHA256=0c166a39e1bf0951dfafcd68949fe0e4b6d3658081d6282f39aeefc6310f2f13
GMP=gmp-6.3.0
GMP_URL=https://gmplib.org/download/gmp/$GMP.tar.xz
GMP_SHA256=a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898
RATPOINTS_URL=https://github.com/MichaelStollBayreuth/ratpoints
RATPOINTS_TAG=v2.2.4   # 3.x needs a 64-bit long, see README.md

# memory layout of the ELF; must match MEM_SIZE in ratpoints_test.py
MEM_SIZE=0x800000      # 8 MiB
STACK_SIZE=0x40000     # 256 KiB

fetch() {  # fetch URL SHA256 -> $B/basename, checked
  f=$B/$(basename "$1")
  if [ ! -f "$f" ]; then curl -fL --retry 3 -o "$f.part" "$1"; mv "$f.part" "$f"; fi
  echo "$2  $f" | sha256sum -c -
}

#------------------------------------------------------------------------------
# 1. newlib, configured like ../newlib-rv32im (see newlib/README.md) but with
#    --enable-newlib-io-float: ratpoints prints its search intervals with %f
#    and parses -l/-u with sscanf("%lf").
if [ ! -f "$B/newlib.stamp" ]; then
  fetch $NEWLIB_URL $NEWLIB_SHA256
  rm -rf "$B/$NEWLIB" "$B/newlib-build" && tar xzf "$B/$NEWLIB.tar.gz" -C "$B"
  mkdir -p "$B/newlib-build" && cd "$B/newlib-build"
  "../$NEWLIB/configure" --target=$TARGET --prefix="$B/newlib" \
    --disable-multilib --disable-newlib-supplied-syscalls \
    --enable-newlib-io-float --enable-newlib-io-long-long \
    --disable-newlib-multithread --enable-newlib-reent-small \
    CC_FOR_TARGET="$TARGET-gcc -march=rv32im -mabi=ilp32" \
    AR_FOR_TARGET=$TARGET-ar RANLIB_FOR_TARGET=$TARGET-ranlib \
    AS_FOR_TARGET=$TARGET-as LD_FOR_TARGET=$TARGET-ld \
    CFLAGS_FOR_TARGET="-O2 -g -mcmodel=medany" > "$B/newlib-configure.log"
  make -j"$JOBS" all-target-newlib > "$B/newlib-make.log" 2>&1
  make install-target-newlib >> "$B/newlib-make.log" 2>&1
  touch "$B/newlib.stamp"
fi
NL=$B/newlib/$TARGET

# startup code + system calls, linked into everything below (also into GMP's
# configure tests, which link programs)
if [ ! -f "$B/rt.stamp" ]; then
  $CC_RV -O2 -c "$HERE/crt0.S" -o "$B/crt0.o"
  $CC_RV -O2 -isystem "$NL/include" -c "$NANOFIVE/newlib/syscalls.c" -o "$B/syscalls.o"
  rm -f "$B/libnanofive.a" && $TARGET-ar rcs "$B/libnanofive.a" "$B/crt0.o" "$B/syscalls.o"
  touch "$B/rt.stamp"
fi
LDFLAGS_RV="-nostdlib -nostartfiles -T $NANOFIVE/newlib/link.ld -Wl,--no-warn-rwx-segments"
LDFLAGS_RV="$LDFLAGS_RV -Wl,--defsym=MEM_SIZE=$MEM_SIZE -Wl,--defsym=STACK_SIZE=$STACK_SIZE"
# crt0.o and syscalls.o are put in an archive, libnanofive.a, and crt0.o is
# pulled in by -u _start (libtool refuses plain .o files in LDFLAGS)
LDFLAGS_RV="$LDFLAGS_RV -Wl,-u,_start -L$B -L$NL/lib"
LIBS_RV="-lm -Wl,--start-group -lc -lgcc -lnanofive -Wl,--end-group"

#------------------------------------------------------------------------------
# 2. GMP: generic C (no assembly), static, for riscv32
if [ ! -f "$B/gmp.stamp" ]; then
  fetch $GMP_URL $GMP_SHA256
  rm -rf "$B/$GMP" "$B/gmp-build" && tar xJf "$B/$GMP.tar.xz" -C "$B"
  mkdir -p "$B/gmp-build" && cd "$B/gmp-build"
  "../$GMP/configure" --host=riscv32-unknown-elf --prefix="$B/gmp" \
    --disable-assembly --disable-shared --enable-static \
    CC="$CC_RV" CFLAGS="-O2" CPPFLAGS="-isystem $NL/include" \
    LDFLAGS="$LDFLAGS_RV" LIBS="$LIBS_RV" \
    AR=$TARGET-ar RANLIB=$TARGET-ranlib NM=$TARGET-nm \
    gmp_cv_c_double_format="IEEE little endian" \
    > "$B/gmp-configure.log"
  make -j"$JOBS" > "$B/gmp-make.log" 2>&1
  make install >> "$B/gmp-make.log" 2>&1
  touch "$B/gmp.stamp"
fi

#------------------------------------------------------------------------------
# 3. ratpoints source
SRC=$B/ratpoints
if [ ! -f "$B/src.stamp" ]; then
  rm -rf "$SRC"
  git clone -q --branch $RATPOINTS_TAG --depth 1 $RATPOINTS_URL "$SRC"
  touch "$B/src.stamp"
fi

# The compiler flags of ratpoints' Makefile with CCFLAGS1 = ${CCFLAGS64}, i.e.
# bit arrays of one unsigned long (32 bits here; no SIMD on RV32IM).
RPFLAGS="-Wall -O2 -fomit-frame-pointer -DRATPOINTS_MAX_BITS_IN_PRIME=7"

# 4. ratpoints for nanofive. The Makefile generates init_sieve.h and
#    find_points.h by running two small programs, whose output depends on the
#    word size, so they are compiled for RV32IM and run on nanofive.
RV=$B/rv32
rm -rf "$RV" && mkdir -p "$RV" && cd "$RV"
INC_RV="-isystem $NL/include -I$B/gmp/include -I$SRC"
for g in gen_init_sieve_h gen_find_points_h; do
  $CC_RV $RPFLAGS $INC_RV "$SRC/$g.c" -o $g.elf $LDFLAGS_RV $LIBS_RV
done
python3 "$NANOFIVE/ratpoints_test.py" --run gen_init_sieve_h.elf > init_sieve.h
python3 "$NANOFIVE/ratpoints_test.py" --run gen_find_points_h.elf > find_points.h
INC_RV="-I$RV $INC_RV"  # generated headers first
$CC_RV $RPFLAGS $INC_RV -funroll-loops -c "$SRC/sift.c"
$CC_RV $RPFLAGS $INC_RV -funroll-loops -O3 -c "$SRC/init.c"
$CC_RV $RPFLAGS $INC_RV -c "$SRC/sturm.c"
$CC_RV $RPFLAGS $INC_RV -c "$SRC/find_points.c"
$CC_RV $RPFLAGS $INC_RV -c "$SRC/main.c"
$CC_RV main.o sift.o init.o sturm.o find_points.o -o "$HERE/ratpoints.elf" \
  $LDFLAGS_RV -L"$B/gmp/lib" -lgmp $LIBS_RV
$TARGET-strip "$HERE/ratpoints.elf"
ls -l "$HERE/ratpoints.elf"

#------------------------------------------------------------------------------
# 5. native x86-64 reference build of the same source, same flags (needs
#    libgmp-dev); 64-bit unsigned long bit arrays
NAT=$B/native
rm -rf "$NAT" && cp -r "$SRC" "$NAT" && cd "$NAT"
make -s ratpoints CCFLAGS1= > /dev/null
ls -l "$NAT/ratpoints"
