import TinyFive.Machine
import TweetNaCl.Salsa20Program

/-!
# A stand-alone Salsa20 program

The linked `core` and `crypto_core_salsa20_tweet` words at their linked addresses, plus a
hand-assembled driver. The driver reads the 16 input, 32 key and 16 constant bytes from
standard input, calls `crypto_core_salsa20_tweet`, prints the 64 output bytes, and exits.
-/
namespace TweetNaCl.Salsa20IOProgram
open TinyFive

def driverEntry : Nat := 0x1170

/-- The driver, at `driverEntry`. `readn` reads bytes into `[t0, t1)` and returns to `t2`. -/
def driverWords : List (BitVec 32) := [
  0x00100137,  -- 0x1170  lui  sp, 0x100
  0x00c00893,  -- 0x1174  li   a7, 12             read a byte
  0x000802b7,  -- 0x1178  lui  t0, 0x80
  0x10028293,  -- 0x117c  addi t0, t0, 0x100      input, 16 bytes
  0x01028313,  -- 0x1180  addi t1, t0, 16
  0x05c003ef,  -- 0x1184  jal  t2, readn
  0x000802b7,  -- 0x1188  lui  t0, 0x80
  0x20028293,  -- 0x118c  addi t0, t0, 0x200      key, 32 bytes
  0x02028313,  -- 0x1190  addi t1, t0, 32
  0x04c003ef,  -- 0x1194  jal  t2, readn
  0x000802b7,  -- 0x1198  lui  t0, 0x80
  0x30028293,  -- 0x119c  addi t0, t0, 0x300      constant, 16 bytes
  0x01028313,  -- 0x11a0  addi t1, t0, 16
  0x03c003ef,  -- 0x11a4  jal  t2, readn
  0x00080537,  -- 0x11a8  lui  a0, 0x80           output
  0x10050593,  -- 0x11ac  addi a1, a0, 0x100
  0x20050613,  -- 0x11b0  addi a2, a0, 0x200
  0x30050693,  -- 0x11b4  addi a3, a0, 0x300
  0xf95ff0ef,  -- 0x11b8  jal  ra, crypto_core_salsa20_tweet
  0x000802b7,  -- 0x11bc  lui  t0, 0x80
  0x04028313,  -- 0x11c0  addi t1, t0, 64
  0x00b00893,  -- 0x11c4  li   a7, 11             print a byte
  0x0002c503,  -- 0x11c8  print: lbu a0, 0(t0)
  0x00000073,  -- 0x11cc  ecall
  0x00128293,  -- 0x11d0  addi t0, t0, 1
  0xfe629ae3,  -- 0x11d4  bne  t0, t1, print
  0x00a00893,  -- 0x11d8  li   a7, 10             exit 0
  0x00000073,  -- 0x11dc  ecall
  0x00000073,  -- 0x11e0  readn: ecall
  0x00a28023,  -- 0x11e4  sb   a0, 0(t0)
  0x00128293,  -- 0x11e8  addi t0, t0, 1
  0xfe629ae3,  -- 0x11ec  bne  t0, t1, readn
  0x00038067]  -- 0x11f0  jr   t2

/-- The image from address 0: a jump to the driver, the helper at `coreEntry`, the wrapper
at `entry`, then the driver. -/
def prog : List (BitVec 32) :=
  [0x1700106f] ++  -- 0x0  j driver
  List.replicate 11 0 ++ Salsa20Program.coreWords ++
  List.replicate 840 0 ++ Salsa20Program.wrapperWords ++ driverWords

/-- One mebibyte of memory, as for the linked fixture. -/
def memSize : Nat := 0x100000

def initial : Machine 64 := load 64 prog memSize []

end TweetNaCl.Salsa20IOProgram
