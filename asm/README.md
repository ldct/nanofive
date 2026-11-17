# Shared runtime

Startup code, system calls and linker script for C programs compiled with
`riscv64-unknown-elf-gcc` to run on nanofive. Used by `../newlib`,
`../ratpoints` and `../urlh`.

- `crt0.S`      — sets gp/sp, clears .bss, runs constructors, `exit(main())`
- `crt0_args.S` — the same, but takes argc/argv from the top of memory, where
  the loader writes them the way Linux does (see `../ratpoints/README.md`)
- `syscalls.c`  — newlib's system calls on nanofive's RARS-style ecalls:
  `_write` -> a7=11 per byte, `_read` -> a7=12, `_exit` -> a7=93, plus `_sbrk`
  and trivial stubs
- `link.ld`     — flat memory at address 0 with the stack at the top;
  `MEM_SIZE` (default 1 MiB) and `STACK_SIZE` (default 64 KiB) can be set with
  `--defsym`
