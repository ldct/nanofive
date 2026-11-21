"""Count primes <= N using 23 RV64I instructions and constant memory.

Deliberately slow trial division: test every d in [2, k), computing k % d
by repeated subtraction. No sieve, multiplication, division, or stack.
The host reads N into a0; the RISC-V code counts, prints, and exits.
See lean/CountingPrimesTrialDivision.lean for the correctness proof.
"""

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))  # machine.py, elf.py
from machine import machine64, a0

MAX_N = 10**11 - 1  # The proved range; k reaches N+1, far below 2^63.

prog = [
    # registers: a0 = N (input), t0 = k (candidate), t1 = count, t2 = d (trial divisor), t3 = r (k mod d)
    0x00200293,  #  0: li   t0,2                     # t0 = 2                     k = 2
    0x00000313,  #  4: li   t1,0                     # t1 = 0                     count = 0
    0x02556a63,  #  8: bltu a0,t0,60 <───────────┬─┐ # if a0 < t0, jump to 60     while k <= N:
    0x00200393,  # 12: li   t2,2                 │ │ # t2 = 2                         d = 2
    0x02538063,  # 16: beq  t2,t0,48 <─────┬─┐   │ │ # if t2 == t0, jump to 48        while d != k:
    0x00028e13,  # 20: mv   t3,t0          │ │   │ │ # t3 = t0                            r = k
    0x007e6663,  # 24: bltu t3,t2,36 <─┬─┐ │ │   │ │ # if t3 < t2, jump to 36             while r >= d:
    0x407e0e33,  # 28: sub  t3,t3,t2   │ │ │ │   │ │ # t3 -= t2                               r -= d
    0xff9ff06f,  # 32: j    24       ──┘ │ │ │   │ │ # loop back to 24
    0x000e0863,  # 36: beqz t3,52    <───┴─┼─┼─┐ │ │ # if t3 == 0, jump to 52             if r == 0: break   # divisor found: composite
    0x00138393,  # 40: addi t2,t2,1        │ │ │ │ │ # t2 += 1                            d += 1
    0xfe5ff06f,  # 44: j    16       ──────┘ │ │ │ │ # loop back to 16
    0x00130313,  # 48: addi t1,t1,1  <───────┘ │ │ │ # t1 += 1                        else: count += 1       # d reached k: prime
    0x00128293,  # 52: addi t0,t0,1  <─────────┘ │ │ # t0 += 1                        k += 1
    0xfd1ff06f,  # 56: j    8        ────────────┘ │ # loop back to 8
    0x00030513,  # 60: mv   a0,t1    <─────────────┘ # a0 = t1                    
    0x00100893,  # 64: li   a7,1                     # a7 = 1 (PRINT_INT)
    0x00000073,  # 68: ecall                         # ECALL(a7=PRINT_INT, a0)    print(count)
    0x00a00513,  # 72: li   a0,10                    # a0 = 10 ('\n')             
    0x00b00893,  # 76: li   a7,11                    # a7 = 11 (PRINT_CHAR)
    0x00000073,  # 80: ecall                         # ECALL(a7=PRINT_CHAR, a0)   print('\n')
    0x00a00893,  # 84: li   a7,10                    # a7 = 10 (EXIT)             
    0x00000073,  # 88: ecall                         # ECALL(a7=EXIT)             exit()
]

def initial(n):
    if not 0 <= n <= MAX_N:
        raise ValueError(f"N must be in [0, {MAX_N}]")
    m = machine64(mem_size=128)
    m.write_i32_vec(prog, 0)
    m.x[a0] = n
    return m


if __name__ == "__main__":
    initial(int(input())).run(start=0)
