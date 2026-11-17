# startup code: set up gp/sp, clear .bss, run main(), exit with its result
  .section .text.init
  .globl _start
_start:
  .option push
  .option norelax
  la   gp, __global_pointer$
  .option pop
  la   sp, __stack_top
  la   t0, __bss_start          # clear .bss (the loader already zeroes memory,
  la   t1, _end                 # but do it anyway, like real hardware would)
1:bgeu t0, t1, 2f
  sw   zero, 0(t0)
  addi t0, t0, 4
  j    1b
2:call __libc_init_array        # run C/C++ constructors
  li   a0, 0                    # argc = 0
  li   a1, 0                    # argv = NULL
  call main
  tail exit                     # flushes stdio, then calls _exit
