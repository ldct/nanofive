"""A 200-byte RV64I odds-only Sieve of Eratosthenes with a word-summing count.

The host only reads N, allocates zeroed memory, and preloads a0. Marking and
counting run as RISC-V instructions, using only RV32I-style base instructions
(no M extension, no ld/sd/lwu, no *W instructions).

Flag byte i lives at address BASE + i and stands for the odd number 2*i + 1:
0 means unmarked, 1 means composite. With K = (N + [N > 1]) >> 1 flags in
use, index 0 (the number 1) is never marked and stands in for the prime 2,
so pi(N) = K - (number of marked flags below K). The N > 1 term makes K = 0
for N = 1.

Marking: for odd p = 3, 5, ... while p*p <= N, if flags[(p-1)/2] is clear,
mark indices (p*p-1)/2, +p, +2p, ... below K. The address of the flag of p*p
is tracked incrementally: (p+2)^2 = p^2 + 4p + 4 moves it by p + (p+2).

Counting: the flags are summed sixteen at a time with four lw. Each byte is
0 or 1, so a word sum keeps four byte lanes apart as long as no lane exceeds
255. A chunk is at most 496 bytes (31 iterations, 124 words), so every lane
is at most 124 and the two-step fold (lanes 0+2 and 1+3, each at most 248)
cannot carry. The top flag byte is at most 1, so lw never sign-extends a
negative word. The last iteration may read up to 15 bytes past the flags;
those bytes are never written, so they are zero (the host pads the memory).
"""

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))  # machine.py, elf.py
from machine import machine64, a0

BASE = 256
PAD = 16            # The count loop reads whole 16-byte blocks.
MAX_N = 10**11 - 1  # Same input range as the other prime counters.

prog = [
    0x00100f13,  #   0: li   t5,1          # composite marker
    0x00af32b3,  #   4: sltu t0,t5,a0      # N > 1
    0x00a282b3,  #   8: add  t0,t0,a0
    0x0012d513,  #  12: srli a0,t0,1       # K = (N + [N > 1]) >> 1, the count so far
    0x10050613,  #  16: addi a2,a0,256     # end = BASE + K
    0x10100e13,  #  20: li   t3,257        # address of flag of p = 3
    0x10400e93,  #  24: li   t4,260        # address of flag of p*p = 9
    0x00300f93,  #  28: li   t6,3          # p
    0x02cef863,  #  32: bgeu t4,a2,80      # nothing to mark if p*p > N
    0x000e4283,  #  36: lbu  t0,0(t3)      # flag of p
    0x00029a63,  #  40: bnez t0,60         # skip composite p
    0x000e8313,  #  44: mv   t1,t4         # j = flag address of p*p
    0x01e30023,  #  48: sb   t5,0(t1)      # mark j
    0x01f30333,  #  52: add  t1,t1,t6      # j += p (2p in number space)
    0xfec36ce3,  #  56: bltu t1,a2,48
    0x001e0e13,  #  60: addi t3,t3,1       # flag address of p + 2
    0x01fe8eb3,  #  64: add  t4,t4,t6      # square address += p ...
    0x002f8f93,  #  68: addi t6,t6,2       # p += 2
    0x01fe8eb3,  #  72: add  t4,t4,t6      # ... += p + 2
    0xfcceece3,  #  76: bltu t4,a2,36      # continue while p*p <= N
    0x10000593,  #  80: li   a1,256        # ptr = BASE
    0x00000313,  #  84: li   t1,0          # chunk: lane sums
    0x1f058393,  #  88: addi t2,a1,496     # chunk end = min(ptr + 496, end)
    0x00767463,  #  92: bgeu a2,t2,100
    0x00060393,  #  96: mv   t2,a2
    0x0005a283,  # 100: lw   t0,0(a1)
    0x00530333,  # 104: add  t1,t1,t0
    0x0045a283,  # 108: lw   t0,4(a1)
    0x00530333,  # 112: add  t1,t1,t0
    0x0085a283,  # 116: lw   t0,8(a1)
    0x00530333,  # 120: add  t1,t1,t0
    0x00c5a283,  # 124: lw   t0,12(a1)
    0x00530333,  # 128: add  t1,t1,t0
    0x01058593,  # 132: addi a1,a1,16
    0xfc75eee3,  # 136: bltu a1,t2,100
    0x01035293,  # 140: srli t0,t1,16
    0x00530333,  # 144: add  t1,t1,t0      # lanes 0+2 and 1+3
    0x0ff37293,  # 148: andi t0,t1,255
    0x40550533,  # 152: sub  a0,a0,t0      # count -= lanes 0+2
    0x00835313,  # 156: srli t1,t1,8
    0x0ff37313,  # 160: andi t1,t1,255
    0x40650533,  # 164: sub  a0,a0,t1      # count -= lanes 1+3
    0xfac5e6e3,  # 168: bltu a1,a2,84      # next chunk
    0x00100893,  # 172: li   a7,1          # print_int
    0x00000073,  # 176: ecall
    0x00a00513,  # 180: li   a0,10
    0x00b00893,  # 184: li   a7,11         # print_char
    0x00000073,  # 188: ecall
    0x00a00893,  # 192: li   a7,10         # exit
    0x00000073,  # 196: ecall
]


def initial(n):
    if not 0 <= n <= MAX_N:
        raise ValueError(f"N must be in [0, {MAX_N}]")
    m = machine64(mem_size=BASE + (n + 1) // 2 + PAD)
    m.write_i32_vec(prog, 0)
    m.x[a0] = n
    return m


if __name__ == "__main__":
    initial(int(input())).run(start=0)
