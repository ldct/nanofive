  .section .text.init
  .globl _start
_start:
  la   sp, __stack_top
  la   a0, zeros
  mv   a1, a0
  call crypto_verify_32_tweet
  j    exit

  # This proof fixture has no entropy source. Never return fake key material.
  .globl randombytes
randombytes:
  li   a0, 125
exit:
  li   a7, 93
  ecall
1:j    1b

  .section .rodata
zeros:
  .zero 32
