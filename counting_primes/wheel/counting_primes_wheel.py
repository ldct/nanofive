"""RV32I mod-30 candidate-wheel byte sieve.

The machine handles candidates 2, 3, 5, then 7, 11, 13, 17, 19, 23,
29, 31, ... using an immutable cyclic gap table. All prime counting and
marking execute on RV32I; the host only allocates memory and preloads N.
Marking deliberately uses every multiple (j=2*p, j+=p), not a compressed
wheel representation. See lean/CountingPrimesWheel.lean for the proof.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))  # machine.py, elf.py
from machine import machine, a0

BASE = 256
MAX_N = 2**30 - 1
GAPS = (1, 2, 2, 4, 2, 4, 2, 4, 6, 2, 6)

prog = [
    0x00200293,  #   0: li t0,2
    0x00000313,  #   4: li t1,0
    0x00100f13,  #   8: li t5,1
    0x10000f93,  #  12: li t6,256
    0x00000593,  #  16: li a1,0
    0x00b00613,  #  20: li a2,11
    0x04556463,  #  24: bltu a0,t0,96
    0x005f8e33,  #  28: add t3,t6,t0
    0x000e4e83,  #  32: lbu t4,0(t3)
    0x020e9063,  #  36: bnez t4,68
    0x00130313,  #  40: addi t1,t1,1
    0x005283b3,  #  44: add t2,t0,t0
    0x00756a63,  #  48: bltu a0,t2,68
    0x007f8e33,  #  52: add t3,t6,t2
    0x01ee0023,  #  56: sb t5,0(t3)
    0x005383b3,  #  60: add t2,t2,t0
    0xff1ff06f,  #  64: j 48
    0x08058e13,  #  68: addi t3,a1,128
    0x000e4e83,  #  72: lbu t4,0(t3)
    0x01d282b3,  #  76: add t0,t0,t4
    0x00158593,  #  80: addi a1,a1,1
    0xfcc5e2e3,  #  84: bltu a1,a2,24
    0x00300593,  #  88: li a1,3
    0xfbdff06f,  #  92: j 24
    0x00030513,  #  96: mv a0,t1
    0x00100893,  # 100: li a7,1
    0x00000073,  # 104: ecall
    0x00a00513,  # 108: li a0,10
    0x00b00893,  # 112: li a7,11
    0x00000073,  # 116: ecall
    0x00a00893,  # 120: li a7,10
    0x00000073,  # 124: ecall
    0x04020201,  # 128: gap bytes 1,2,2,4
    0x04020402,  # 132: gap bytes 2,4,2,4
    0x00060206,  # 136: gap bytes 6,2,6,0
]


def initial(n):
    if not 0 <= n <= MAX_N:
        raise ValueError(f"N must be in [0, {MAX_N}]")
    m = machine(mem_size=BASE + n + 1)
    m.write_i32_vec(prog, 0)
    m.x[a0] = n
    return m


if __name__ == "__main__":
    initial(int(input())).run(start=0)
