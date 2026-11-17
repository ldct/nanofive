"""A 380-byte RV64IM prime counter using O(sqrt N) memory (Lucy_Hedgehog DP).

The host only reads N, allocates zeroed memory, and preloads a0. All
arithmetic and printing run as RISC-V instructions. Beyond the base integer
instructions the program uses mul, divu, ld and sd.

Let r be the largest odd number with r*r <= N, and for a stage prime p let
S(v) be the number of n in [5, v] that are prime or have no prime factor
below p. Two tables of 64-bit slots are interleaved from address BASE = 512:

  small[i] at BASE + 16*i      holds S(2*i + 1)   for 2*i + 1 <= r
  large[k] at BASE + 8*k       holds S(N // k)    for odd k <= r

S(v) = S(v - 1) for even v >= 2, so S(v) is read as small[(v - 1) >> 1].
Both tables start at stage 5 (numbers coprime to 6), which is
((v - 1) & ~1) // 3. Stage p then applies S(v) -= S(v // p) - S(p - 1) to
every v >= p*p, large v first. Two shortcuts keep the work down:

  - large[k] with 1 < k <= p is left stale at stage p: later stages read
    large[k*p'] only for k = 1 or k > p', so such a slot is never read again.
    large[1] itself lives in register a3.
  - Once N // (p*p) < p + 2 only large[1] changes, so a short tail loop
    subtracts large[p] - S(p - 1) for each remaining prime p <= r.

Loop variables are kept pre-scaled by 8 so they double as slot offsets:
a1 = 8*r, a4 = 8*p, a7 = 16*p, s0 = 8*d with d = k*p, s1 = 8*kmax*p,
s5 = 8*p*p, s3 = 8*((N - d) >> 1), s4 = 8*v. Unscaled: a5 = p, a6 = p*p,
t6 = c = S(p - 1), s2 = &large[k], and in the first loop t0 = v, t5 = x = N // v.
The answer is large[1] + 2 for N >= 3 and N >> 1 below that.
"""

import os, sys
from math import isqrt
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))  # machine.py, elf.py
from machine import machine64, a0

BASE = 512
MAX_N = 10**11 - 1  # Scaled intermediates stay below 2**63 far beyond this.

prog = [
    0x00300393,  #   0: li t2,3
    0x16756863,  #   4: bltu a0,t2,372        # N < 3: pi(N) = N >> 1
    0x01800b13,  #   8: li s6,24
    0x00100293,  #  12: li t0,1
    0x00000313,  #  16: li t1,0
    0x00050f13,  #  20: mv t5,a0              # x = N / v
    0x03635e33,  #  24: divu t3,t1,s6
    0x21c33023,  #  28: sd t3,512(t1)         # small[i] = 2*i/3, i = (v-1)/2
    0xffff0e13,  #  32: addi t3,t5,-1
    0xffee7e13,  #  36: andi t3,t3,-2
    0x027e5e33,  #  40: divu t3,t3,t2
    0x21c33423,  #  44: sd t3,520(t1)         # large[v] = ((x-1) & ~1)/3
    0x01030313,  #  48: addi t1,t1,16
    0x00228293,  #  52: addi t0,t0,2
    0x02555f33,  #  56: divu t5,a0,t0
    0xfc5f7ee3,  #  60: bgeu t5,t0,24         # while v*v <= N
    0xff830593,  #  64: addi a1,t1,-8         # 8*r, r = largest odd number with r*r <= N
    0x00251613,  #  68: slli a2,a0,2
    0x20803683,  #  72: ld a3,520(zero)       # large[1] lives in a register from here on
    0x02800713,  #  76: li a4,40              # 8*p, p = 5
    0x00000f93,  #  80: li t6,0               # c = small[(p-3)/2]
    0x10e5e063,  #  84: bltu a1,a4,340
    0x1f873f03,  #  88: ld t5,504(a4)         # small[(p-1)/2]
    0x0dff0663,  #  92: beq t5,t6,296         # p is not prime
    0x20073e03,  #  96: ld t3,512(a4)         # large[p]
    0x41fe0e33,  # 100: sub t3,t3,t6
    0x41c686b3,  # 104: sub a3,a3,t3          # large[1] -= large[p] - c
    0x00375793,  # 108: srli a5,a4,3
    0x02f78833,  # 112: mul a6,a5,a5
    0x00e708b3,  # 116: add a7,a4,a4
    0x00381a93,  # 120: slli s5,a6,3          # 8*p*p
    0x02f584b3,  # 124: mul s1,a1,a5          # p*p <= r: kmax = r
    0x0155f663,  # 128: bgeu a1,s5,140
    0x03055e33,  # 132: divu t3,a0,a6         # p*p > r: kmax = N/(p*p)
    0x02ee04b3,  # 136: mul s1,t3,a4          # 8*kmax*p
    0x011a8433,  # 140: add s0,s5,a7          # 8*d, d = k*p, k = p+2
    0x0a84ec63,  # 144: bltu s1,s0,328        # kmax < p+2, now and for every later prime
    0x21070913,  # 148: addi s2,a4,528        # &large[k]
    0x0285e263,  # 152: bltu a1,s0,188
    0x20043e03,  # 156: ld t3,512(s0)         # large[d]
    0x00093e83,  # 160: ld t4,0(s2)
    0x41fe0e33,  # 164: sub t3,t3,t6
    0x41ce8eb3,  # 168: sub t4,t4,t3
    0x01d93023,  # 172: sd t4,0(s2)           # large[k] -= large[k*p] - c
    0x01090913,  # 176: addi s2,s2,16
    0x01140433,  # 180: add s0,s0,a7
    0xfe85f2e3,  # 184: bgeu a1,s0,156        # while k*p <= r
    0x00145e13,  # 188: srli t3,s0,1
    0x41c60e33,  # 192: sub t3,a2,t3
    0xff8e7993,  # 196: andi s3,t3,-8         # 8*((N-d) >> 1)
    0x0289de33,  # 200: divu t3,s3,s0         # (N/d - 1) >> 1
    0x004e1e13,  # 204: slli t3,t3,4
    0x200e3e03,  # 208: ld t3,512(t3)         # small[(N/d - 1) >> 1]
    0x00093e83,  # 212: ld t4,0(s2)
    0x41fe0e33,  # 216: sub t3,t3,t6
    0x41ce8eb3,  # 220: sub t4,t4,t3
    0x01d93023,  # 224: sd t4,0(s2)           # large[k] -= small[...] - c
    0x01090913,  # 228: addi s2,s2,16
    0x01140433,  # 232: add s0,s0,a7
    0x40e989b3,  # 236: sub s3,s3,a4
    0xfc84fce3,  # 240: bgeu s1,s0,200        # while k <= kmax
    0x0355e863,  # 244: bltu a1,s5,292        # p*p > r: small is unchanged
    0x00058a13,  # 248: mv s4,a1              # 8*v, v = r
    0x40ea0e33,  # 252: sub t3,s4,a4
    0x031e5e33,  # 256: divu t3,t3,a7         # (v/p - 1) >> 1
    0x004e1e13,  # 260: slli t3,t3,4
    0x200e3e03,  # 264: ld t3,512(t3)
    0x1f8a3e83,  # 268: ld t4,504(s4)
    0x41fe0e33,  # 272: sub t3,t3,t6
    0x41ce8eb3,  # 276: sub t4,t4,t3
    0x1fda3c23,  # 280: sd t4,504(s4)         # small[(v-1)/2] -= small[(v/p - 1) >> 1] - c
    0xff0a0a13,  # 284: addi s4,s4,-16
    0xfd5a7ee3,  # 288: bgeu s4,s5,252        # while v >= p*p
    0x001f8f93,  # 292: addi t6,t6,1
    0x01070713,  # 296: addi a4,a4,16
    0xf2e5f6e3,  # 300: bgeu a1,a4,88
    0x0240006f,  # 304: j 340
    0x1f873f03,  # 308: ld t5,504(a4)         # small[(p-1)/2]
    0x01ff0a63,  # 312: beq t5,t6,332         # p is not prime
    0x20073e03,  # 316: ld t3,512(a4)         # large[p]
    0x41fe0e33,  # 320: sub t3,t3,t6
    0x41c686b3,  # 324: sub a3,a3,t3          # large[1] -= large[p] - c
    0x001f8f93,  # 328: addi t6,t6,1
    0x01070713,  # 332: addi a4,a4,16
    0xfee5f2e3,  # 336: bgeu a1,a4,308
    0x00268513,  # 340: addi a0,a3,2          # count the primes 2 and 3
    0x00100893,  # 344: li a7,1               # print_int
    0x00000073,  # 348: ecall
    0x00a00513,  # 352: li a0,10
    0x00b00893,  # 356: li a7,11              # print_char
    0x00000073,  # 360: ecall
    0x00a00893,  # 364: li a7,10              # exit
    0x00000073,  # 368: ecall
    0x00155513,  # 372: srli a0,a0,1
    0xfe1ff06f,  # 376: j 344
]


def initial(n):
    if not 0 <= n <= MAX_N:
        raise ValueError(f"N must be in [0, {MAX_N}]")
    m = machine64(mem_size=BASE + 8 * (isqrt(n) + 1))  # last slot is large[r]
    m.write_i32_vec(prog, 0)
    m.x[a0] = n
    return m


if __name__ == "__main__":
    initial(int(input())).run(start=0)
