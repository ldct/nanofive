  # __assert_func, which Nettle's assert calls when its condition fails: exit with
  # status 1 (TinyFive ecall 93). It is linked after Nettle's code.
  .text
  .option norvc
  .globl __assert_func
__assert_func:
  addi a0, zero, 1
  addi a7, zero, 93
  ecall
