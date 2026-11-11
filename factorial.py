from machine import *

# Recursive factorial, run from machine code in memory. The assembly source is
# in the comments; pseudo-instructions are expanded the standard way:
#   li rd, imm -> addi rd, x0, imm      j label -> jal x0, label
#   jr ra      -> jalr x0, ra, 0        jal label -> jal ra, label
#   mv rd, rs  -> addi rd, rs, 0
# System calls follow the RARS simulator convention (see machine.ECALL).

prog = [
  # fact:  arg: n in a0, returns n! in a1
  0xff810113,  #  0: addi sp, sp, -8      reserve our stack area
  0x00112023,  #  4: sw   ra, 0(sp)       save the return address
  0x00200293,  #  8: li   t0, 2
  0x00554e63,  # 12: blt  a0, t0, ret_one 0! and 1! == 1
  0x00a12223,  # 16: sw   a0, 4(sp)       save our n
  0xfff50513,  # 20: addi a0, a0, -1
  0xfe9ff0ef,  # 24: jal  fact            call fact(n-1), a1 <- fact(n-1)
  0x00412283,  # 28: lw   t0, 4(sp)       t0 <- n
  0x02b285b3,  # 32: mul  a1, t0, a1      a1 <- n * fact(n-1)
  0x0080006f,  # 36: j    done
  # ret_one:
  0x00100593,  # 40: li   a1, 1
  # done:
  0x00012083,  # 44: lw   ra, 0(sp)       restore return address from stack
  0x00810113,  # 48: addi sp, sp, 8       free our stack frame
  0x00008067,  # 52: jr   ra              and return
  # __start:
  0x00500513,  # 56: li   a0, 5           compute 5!
  0xfc5ff0ef,  # 60: jal  fact
  0x00058513,  # 64: mv   a0, a1          print it
  0x00100893,  # 68: li   a7, 1           (print_int)
  0x00000073,  # 72: ecall
  0x00a00893,  # 76: li   a7, 10          (exit)
  0x00000073]  # 80: ecall                and exit

m = machine(mem_size=1024)
m.write_i32_vec(prog, 0)
m.x[sp] = len(m.mem)  # stack grows down from the top of memory
m.run(start=56)       # __start
print()
print('exit code: ' + str(m.exit_code))
