#!/bin/sh
# Build jwerle/url.h for nanofive (RV32IM, ilp32) against newlib:
#   url_test.elf    -- url.h's own test.c, unmodified
#   url_inspect.elf -- inspect.c: parse one URL per input line and print it
# plus native builds of the same two programs, for reference output. See
# README.md. url.h's source is vendored in urlh/vendor/; newlib is downloaded
# and everything is built under urlh/build/ (gitignored). Only the two ELFs
# are written next to this script.
#
#   sh urlh/build.sh     # needs riscv64-unknown-elf-gcc, gcc, curl
#
# Each stage leaves a stamp file and is skipped when re-run; rm -rf urlh/build
# to start over.
set -eu

HERE=$(cd "$(dirname "$0")" && pwd)
NANOFIVE=$(dirname "$HERE")
B=$HERE/build
JOBS=${JOBS:-$(nproc)}
mkdir -p "$B"

TARGET=riscv64-unknown-elf
CC_RV="$TARGET-gcc -march=rv32im -mabi=ilp32 -mcmodel=medany"

NEWLIB=newlib-4.4.0.20231231
NEWLIB_URL=https://sourceware.org/pub/newlib/$NEWLIB.tar.gz
NEWLIB_SHA256=0c166a39e1bf0951dfafcd68949fe0e4b6d3658081d6282f39aeefc6310f2f13

# memory layout of the ELFs; must match MEM_SIZE in urlh_test.py
MEM_SIZE=0x100000      # 1 MiB
STACK_SIZE=0x10000     # 64 KiB

fetch() {  # fetch URL SHA256 -> $B/basename, checked
  f=$B/$(basename "$1")
  if [ ! -f "$f" ]; then curl -fL --retry 3 -o "$f.part" "$1"; mv "$f.part" "$f"; fi
  echo "$2  $f" | sha256sum -c -
}

#------------------------------------------------------------------------------
# 1. newlib, configured as in ../newlib/README.md (url.c needs sscanf, which
#    the vendored subset in ../newlib/vendor leaves out)
if [ ! -f "$B/newlib.stamp" ]; then
  fetch $NEWLIB_URL $NEWLIB_SHA256
  rm -rf "$B/$NEWLIB" "$B/newlib-build" && tar xzf "$B/$NEWLIB.tar.gz" -C "$B"
  mkdir -p "$B/newlib-build" && cd "$B/newlib-build"
  "../$NEWLIB/configure" --target=$TARGET --prefix="$B/newlib" \
    --disable-multilib --disable-newlib-supplied-syscalls \
    --disable-newlib-io-float --enable-newlib-io-long-long \
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

#------------------------------------------------------------------------------
# 2. url.h source, vendored (see vendor/SOURCES). url.c includes
#    url_char_category_table.h, which upstream's Makefile generates with
#    gen_char_category_table; check that the vendored copy is what it makes.
SRC=$HERE/vendor
cc -std=c99 -o "$B/gen_char_category_table" "$SRC/gen_char_category_table.c"
"$B/gen_char_category_table" | cmp - "$SRC/url_char_category_table.h"

# The flags of url.h's Makefile, plus -O2. Compiling from inside $SRC keeps
# __FILE__ (printed in url_parse's error messages) equal to "url.c" in both
# builds.
CFLAGS="-std=c99 -Wall -O2"

# 3. RV32IM
RV=$B/rv32
rm -rf "$RV" && mkdir -p "$RV"
LDFLAGS_RV="-nostdlib -nostartfiles -T $NANOFIVE/asm/link.ld -Wl,--no-warn-rwx-segments"
LDFLAGS_RV="$LDFLAGS_RV -Wl,--defsym=MEM_SIZE=$MEM_SIZE -Wl,--defsym=STACK_SIZE=$STACK_SIZE"
LIBS_RV="-L$NL/lib -Wl,--start-group -lc -lgcc -Wl,--end-group"
cd "$SRC"
$CC_RV $CFLAGS -isystem "$NL/include" -c url.c -o "$RV/url.o"
$CC_RV $CFLAGS -isystem "$NL/include" -c test.c -o "$RV/test.o"
$CC_RV $CFLAGS -isystem "$NL/include" -I. -c "$HERE/inspect.c" -o "$RV/inspect.o"
$CC_RV -O2 -c "$NANOFIVE/asm/crt0.S" -o "$RV/crt0.o"
$CC_RV -O2 -isystem "$NL/include" -c "$NANOFIVE/asm/syscalls.c" -o "$RV/syscalls.o"
for p in test inspect; do
  $CC_RV "$RV/crt0.o" "$RV/$p.o" "$RV/url.o" "$RV/syscalls.o" \
    -o "$HERE/url_$p.elf" $LDFLAGS_RV $LIBS_RV
done
$TARGET-objdump -d "$HERE/url_inspect.elf" > "$RV/url_inspect.dis"
$TARGET-strip "$HERE/url_test.elf" "$HERE/url_inspect.elf"
ls -l "$HERE"/url_*.elf

#------------------------------------------------------------------------------
# 4. native reference build, same flags
NAT=$B/native
rm -rf "$NAT" && mkdir -p "$NAT"
cc $CFLAGS -o "$NAT/url_test" test.c url.c
cc $CFLAGS -I. -o "$NAT/url_inspect" "$HERE/inspect.c" url.c
ls -l "$NAT"/url_*
