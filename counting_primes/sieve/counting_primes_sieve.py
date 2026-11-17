"""A 100-byte RV64I Sieve of Eratosthenes.

The host only reads N, allocates zeroed memory, and preloads a0. All prime
counting and composite marking run as RISC-V instructions. Byte flags
start at address 128: 0 means unmarked, 1 means composite.
See lean/CountingPrimesSieve.lean for the machine-code proof.
"""

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))  # machine.py, elf.py
from machine import machine64, a0

BASE = 128
MAX_N = 10**11 - 1  # The proved range; marking advances j to at most 2*N.

prog = [
    0x00200293,  #  0: li   t0,2          # candidate p
    0x00000313,  #  4: li   t1,0          # count
    0x00100f13,  #  8: li   t5,1          # composite marker
    0x08000f93,  # 12: li   t6,128        # flag base
    0x02556a63,  # 16: bltu a0,t0,68     # done if N < p
    0x005f8e33,  # 20: add  t3,t6,t0
    0x000e4e83,  # 24: lbu  t4,0(t3)     # flags[p]
    0x020e9063,  # 28: bnez t4,60        # skip composite
    0x00130313,  # 32: addi t1,t1,1      # p is prime
    0x005283b3,  # 36: add  t2,t0,t0     # j = 2*p
    0x00756a63,  # 40: bltu a0,t2,60     # done marking if N < j
    0x007f8e33,  # 44: add  t3,t6,t2
    0x01ee0023,  # 48: sb   t5,0(t3)     # flags[j] = 1
    0x005383b3,  # 52: add  t2,t2,t0     # j += p
    0xff1ff06f,  # 56: j    40
    0x00128293,  # 60: addi t0,t0,1
    0xfd1ff06f,  # 64: j    16
    0x00030513,  # 68: mv   a0,t1
    0x00100893,  # 72: li   a7,1         # print_int
    0x00000073,  # 76: ecall
    0x00a00513,  # 80: li   a0,10
    0x00b00893,  # 84: li   a7,11        # print_char
    0x00000073,  # 88: ecall
    0x00a00893,  # 92: li   a7,10        # exit
    0x00000073,  # 96: ecall
]


def initial(n):
    if not 0 <= n <= MAX_N:
        raise ValueError(f"N must be in [0, {MAX_N}]")
    m = machine64(mem_size=BASE + n + 1)
    m.write_i32_vec(prog, 0)
    m.x[a0] = n
    return m


if __name__ == "__main__":
    initial(int(input())).run(start=0)
