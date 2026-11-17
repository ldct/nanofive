# jwerle/url.h on nanofive

[url.h](https://github.com/jwerle/url.h) is a small C URL parser. This directory
holds it compiled for RV32IM against newlib, with tests that run it on the
Python emulator and a Lean proof about part of its machine code.

## Build

url.h's source is vendored, unmodified, in `vendor/` (see `vendor/SOURCES`
for the commit and license). `build.sh` builds newlib (as in
`../newlib/README.md`, without float I/O) and links two programs with
`../asm/crt0.S`, `../asm/syscalls.c` and `../asm/link.ld`:

* `url_test.elf`: url.h's own `test.c`, which asserts facts about two URLs and
  exits 0 only if they all hold.
* `url_inspect.elf`: `inspect.c`, which parses each line on stdin and prints
  every part of it.

It also builds both natively, and the native `url_inspect` writes
`expected/*.out` from `urls.txt`. It needs `riscv64-unknown-elf-gcc` and a host
gcc. On macOS, use the Docker image from `../newlib/README.md`
(run from the repository root):

    docker run --rm -v "$PWD":/w -w /w nanofive-rvgcc sh -c \
      'apt-get install -y -qq python3 >/dev/null 2>&1; sh urlh/build.sh'

The ELFs are checked in; intermediate files go to `urlh/build/`.

## Test

    python3 urlh/urlh_test.py
    echo 'https://user@a.b:8080/p%20q?q=1#f' | python3 urlh/urlh_test.py --inspect

The first command runs both ELFs and compares their output with `expected/`
(and with the native build when it can run here). It also checks that the
code of `decode_percent` at `0x374` in `url_inspect.elf` is the code proved in
`lean/UrlDecode.lean`, and runs that code on its own against a Python
copy of the Lean spec.

## Proof

`lean/UrlDecode.lean` proves `decode_percent`, the function that
decodes `%XX` escapes in place, correct on `TinyFive.Machine`, for strings of
any length. It also proves facts about the spec: the output is never longer
than the input, strings without `%` are unchanged, decoding inverts
percent-encoding, and `%00` cuts the C string short. See the module docstring.
Build with `lake build` from the repository root.

## Findings

* `url_get_scheme` copies the scheme with `sscanf(url, "%[^://]", protocol)`
  into a heap buffer of `URL_PROTOCOL_MAX_LENGTH` (32) bytes with no width
  limit, so a URL with more than 31 bytes before its first `:` or `/`
  overflows it.
* `://no-scheme.com` parses with an empty scheme instead of failing.
* `%00` decodes to a NUL byte, which truncates the decoded path, fragment or
  query value as a C string (`decodePercent_nul`).
