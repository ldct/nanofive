# startup code with command-line arguments, for programs that want argc/argv.
# Like newlib/crt0.S, but the loader may pass arguments the way Linux does: it
# writes argc, argv[0..argc-1], NULL and the strings at the top of memory and
# sets sp to point at argc. If sp is 0 (nothing passed), argc = 0, argv = NULL
# and the stack starts at __stack_top, exactly as in newlib/crt0.S.
  .section .text.init
  .globl _start
_start:
  .option push
  .option norelax
  la   gp, __global_pointer$
  .option pop
  li   s0, 0                    # s0 = argc
  li   s1, 0                    # s1 = argv
  bnez sp, 1f
  la   sp, __stack_top          # no arguments
  j    2f
1:lw   s0, 0(sp)                # argc
  addi s1, sp, 4                # argv
  andi sp, sp, -16              # the stack grows down from below the block
2:la   t0, __bss_start          # clear .bss
  la   t1, _end
3:bgeu t0, t1, 4f
  sw   zero, 0(t0)
  addi t0, t0, 4
  j    3b
4:call __libc_init_array        # run C/C++ constructors
  mv   a0, s0
  mv   a1, s1
  call main
  tail exit                     # flushes stdio, then calls _exit
