"""Count primes <= N using 23 RV32I instructions and constant memory.

Deliberately slow trial division: test every d in [2, k), computing k % d
by repeated subtraction. No sieve, multiplication, division, or stack.
The host reads N into a0; the RISC-V code counts, prints, and exits.
See lean/TinyFive/CountingPrimes.lean for the correctness proof.
"""

from machine import machine, a0

MAX_N = 2**31 - 2  # k reaches N+1; the count must print as signed RV32.

prog = [
    0x00200293,  #  0: li   t0,2          # candidate k
    0x00000313,  #  4: li   t1,0          # count
    0x02556a63,  #  8: bltu a0,t0,60     # done if N < k
    0x00200393,  # 12: li   t2,2          # divisor d
    0x02538063,  # 16: beq  t2,t0,48     # no proper divisor: prime
    0x00028e13,  # 20: mv   t3,t0        # remainder r = k
    0x007e6663,  # 24: bltu t3,t2,36     # r < d: remainder ready
    0x407e0e33,  # 28: sub  t3,t3,t2
    0xff9ff06f,  # 32: j    24
    0x000e0863,  # 36: beqz t3,52        # composite
    0x00138393,  # 40: addi t2,t2,1
    0xfe5ff06f,  # 44: j    16
    0x00130313,  # 48: addi t1,t1,1      # prime
    0x00128293,  # 52: addi t0,t0,1
    0xfd1ff06f,  # 56: j    8
    0x00030513,  # 60: mv   a0,t1
    0x00100893,  # 64: li   a7,1         # print_int
    0x00000073,  # 68: ecall
    0x00a00513,  # 72: li   a0,10
    0x00b00893,  # 76: li   a7,11        # print_char
    0x00000073,  # 80: ecall
    0x00a00893,  # 84: li   a7,10        # exit
    0x00000073,  # 88: ecall
]


def initial(n):
    if not 0 <= n <= MAX_N:
        raise ValueError(f"N must be in [0, {MAX_N}]")
    m = machine(mem_size=128)
    m.write_i32_vec(prog, 0)
    m.x[a0] = n
    return m


if __name__ == "__main__":
    initial(int(input())).run(start=0)
