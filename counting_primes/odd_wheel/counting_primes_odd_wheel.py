"""RV64I mod-6 wheel sieve: flags only for numbers coprime to 6.

The host only reads N, allocates zeroed memory, and preloads a0. Everything
else runs as RISC-V base instructions (no M extension, no ld/sd, no *W).

Layout. Flag i is the byte at BASE + i and stands for n = (3i+1)|1, that is
1, 5, 7, 11, 13, ...; so i = n // 3. A flag is 0 (unmarked) or 1 (composite).
E = #{n <= N : gcd(n, 6) = 1} is the number of flags that matter.

Marking. For a prime p >= 5 the multiples p*m with gcd(m, 6) = 1 and m >= p
form two progressions with index stride 2p, starting at p^2 and at p*(p+2)
(p = 6k-1) or p*(p+4) (p = 6k+1); one loop marks both, five instructions per
two marks. p = 5 is unrolled instead: its progressions are 3 flags apart, so
one sw of 0x01000001 marks both (it also writes two zero bytes, which is why
it must run first). Candidates are taken in pairs (6k+1, 6k+5) with all
indices tracked by additions:
  idx((6k-1)^2) = 12k^2 - 4k,  idx((6k+1)^2) = 12k^2 + 4k.
Mark loops are bottom-tested without an entry check and only the first
progression is compared with E, so marks can land at indices >= E. Those are
still genuine composites ("marked implies composite" holds for every index),
they are never counted, and the host allocates room for them.

Counting. pi(N) = E + 1 - (marks in flags [0, E)) for N >= 3. The marks are
summed from index E downward, 16 flags (four lw) per round, so the pass ends
exactly at E and over-reads only the zero bytes below BASE (at most 15).
Words are added as four byte-wide lanes; a block is at most 31 rounds, which
keeps every lane <= 124 before it is folded into the count.
"""

import os, sys
from math import isqrt
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))  # machine.py, elf.py
from machine import machine64, a0

BASE = 512
MAX_N = 10**11 - 1  # The division by 3 is exact well beyond this; see the test.

prog = [
    0x00350293,  #   0:          addi t0,a0,3
    0x0012d293,  #   4:          srli t0,t0,1       # m = (N+3) >> 1
    0x00200813,  #   8:          li a6,2            # f = 2k, k = 1
    0x12587a63,  #  12:          bgeu a6,t0,320     # N < 3 (m <= 2): pi = N >> 1
    0x00229313,  #  16:          slli t1,t0,2
    0x006282b3,  #  20:          add t0,t0,t1       # 5m
    0x00429313,  #  24:          slli t1,t0,4
    0x006282b3,  #  28:          add t0,t0,t1       # 0x55 m
    0x00829313,  #  32:          slli t1,t0,8
    0x006282b3,  #  36:          add t0,t0,t1       # Y = 0x5555 m
    0x0102d313,  #  40:          srli t1,t0,16
    0x00530333,  #  44:          add t1,t1,t0
    0x01035313,  #  48:          srli t1,t1,16
    0x006282b3,  #  52:          add t0,t0,t1       # T = Y + (Y>>16) + (Y>>32) < m * 2^16 / 3
    0x00f2d293,  #  56:          srli t0,t0,15      # E = ceil(2m/3) - 1 = #{n <= N : gcd(n,6) = 1}
    0x010003b7,  #  60:          lui t2,0x1000
    0x00138393,  #  64:          addi t2,t2,1       # 0x01000001: byte marker; as a word it marks i and i+3
    0x00800593,  #  68:          li a1,8            # i = index of 25
    0x2075a023,  #  72: l5:      sw t2,512(a1)      # 25 + 60j and 35 + 60j
    0x2075a523,  #  76:          sw t2,522(a1)      # 55 + 60j and 65 + 60j
    0x01458593,  #  80:          addi a1,a1,20
    0xfe55eae3,  #  84:          bltu a1,t0,72      # while i < E
    0x01000613,  #  88:          li a2,16           # a2 = index of 7^2
    0x00800713,  #  92:          li a4,8            # D = 8k
    0x00a00793,  #  96:          li a5,10           # s = 12k - 2
    0x00e605b3,  # 100: top:     add a1,a2,a4       # p = 6k+1; a2 = index of p^2
    0x00870713,  # 104:          addi a4,a4,8       # D = 8(k+1)
    0x00e585b3,  # 108:          add a1,a1,a4       # a1 = index of (6k+5)^2
    0x20084303,  # 112:          lbu t1,512(a6)     # flag of 6k+1
    0x02031063,  # 116:          bne t1,zero,148    # composite: skip
    0x00e606b3,  # 120:          add a3,a2,a4       # index of p(p+4), plus 7
    0x00478893,  # 124:          addi a7,a5,4       # stride 2p = 12k+2
    0x20760023,  # 128: l2:      sb t2,512(a2)      # p^2 + 6pj
    0x1e768ca3,  # 132:          sb t2,505(a3)      # p(p+4) + 6pj
    0x01160633,  # 136:          add a2,a2,a7
    0x011686b3,  # 140:          add a3,a3,a7
    0xfe5668e3,  # 144:          bltu a2,t0,128     # while a2 < E
    0x00c78793,  # 148: q:       addi a5,a5,12      # k += 1; p = 6k-1; a1 = index of p^2
    0x00280813,  # 152:          addi a6,a6,2       # f = 2k
    0x00e58633,  # 156:          add a2,a1,a4       # a2 = index of (6k+1)^2
    0x1ff84303,  # 160:          lbu t1,511(a6)     # flag of 6k-1
    0x02031063,  # 164:          bne t1,zero,196    # composite: skip
    0x010586b3,  # 168:          add a3,a1,a6
    0x010686b3,  # 172:          add a3,a3,a6       # index of p(p+2), plus 1
    0x20758023,  # 176: l1:      sb t2,512(a1)      # p^2 + 6pj
    0x1e768fa3,  # 180:          sb t2,511(a3)      # p(p+2) + 6pj
    0x00f585b3,  # 184:          add a1,a1,a5
    0x00f686b3,  # 188:          add a3,a3,a5
    0xfe55e8e3,  # 192:          bltu a1,t0,176     # while a1 < E
    0xfa5660e3,  # 196: nx:      bltu a2,t0,100     # next pair while (6k+1)^2 <= N
    0x00128513,  # 200:          addi a0,t0,1       # E + 1 = E - 1 (for 1) + 2 (for 2, 3); t0 = e = E
    0xe1028313,  # 204: blk:     addi t1,t0,-496    # block of at most 31 rounds, so byte sums <= 124
    0x00035463,  # 208:          bge t1,zero,216
    0x00000313,  # 212:          li t1,0            # t1 = max(e - 496, 0)
    0x00000e13,  # 216: clamped: li t3,0            # acc = 0
    0x1fc2ae83,  # 220: cnt:     lw t4,508(t0)      # flags e-4 .. e-1
    0x1f82af03,  # 224:          lw t5,504(t0)      # flags e-8 .. e-5
    0x1f42af83,  # 228:          lw t6,500(t0)      # flags e-12 .. e-9
    0x1f02a883,  # 232:          lw a7,496(t0)      # flags e-16 .. e-13
    0x01de0e33,  # 236:          add t3,t3,t4
    0x01ee0e33,  # 240:          add t3,t3,t5
    0x01fe0e33,  # 244:          add t3,t3,t6
    0x011e0e33,  # 248:          add t3,t3,a7
    0xff028293,  # 252:          addi t0,t0,-16     # e -= 16
    0xfc534ee3,  # 256:          blt t1,t0,220      # while t1 < e
    0x010e5e93,  # 260:          srli t4,t3,16
    0x01de0e33,  # 264:          add t3,t3,t4       # byte 0 = S0+S2, byte 1 = S1+S3
    0x0ffe7e93,  # 268:          andi t4,t3,255
    0x41d50533,  # 272:          sub a0,a0,t4       # count -= S0+S2
    0x008e5e13,  # 276:          srli t3,t3,8
    0x0ffe7e13,  # 280:          andi t3,t3,255
    0x41c50533,  # 284:          sub a0,a0,t3       # count -= S1+S3
    0xfa5046e3,  # 288:          blt zero,t0,204    # more blocks while e > 0
    0x00100893,  # 292: print:   li a7,1            # print_int
    0x00000073,  # 296:          ecall
    0x00a00513,  # 300:          li a0,10
    0x00b00893,  # 304:          li a7,11           # print_char '\n'
    0x00000073,  # 308:          ecall
    0x00a00893,  # 312:          li a7,10           # exit
    0x00000073,  # 316:          ecall
    0x00155513,  # 320: small:   srli a0,a0,1       # N < 3
    0xfe1ff06f,  # 324:          j 292
]


def mem_size(n):
    """Flags [0, E) plus room for marks past E (below E + 6*sqrt(E) + 16, and below 48 for tiny N)."""
    return BASE + n // 3 + 4 * isqrt(n) + 64


def initial(n):
    if not 0 <= n <= MAX_N:
        raise ValueError(f"N must be in [0, {MAX_N}]")
    m = machine64(mem_size=mem_size(n))
    m.write_i32_vec(prog, 0)
    m.x[a0] = n
    return m


if __name__ == "__main__":
    initial(int(input())).run(start=0)
