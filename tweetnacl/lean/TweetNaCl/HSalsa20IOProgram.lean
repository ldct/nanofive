import TinyFive.Machine
import TweetNaCl.HSalsa20Program

/-!
# A stand-alone HSalsa20 program

The linked `core` and `crypto_core_hsalsa20_tweet` words at their linked addresses, plus the
driver of `Salsa20IOProgram`, moved to follow the wrapper and printing 32 bytes. The driver
reads the 16 input, 32 key and 16 constant bytes from standard input, calls
`crypto_core_hsalsa20_tweet`, prints the 32 output bytes, and exits.
-/
namespace TweetNaCl.HSalsa20IOProgram
open TinyFive

def driverEntry : Nat := 0x1194

/-- The driver, at `driverEntry`. `readn` reads bytes into `[t0, t1)` and returns to `t2`. -/
def driverWords : List (BitVec 32) := [
  0x00100137,  -- 0x1194  lui  sp, 0x100
  0x00c00893,  -- 0x1198  li   a7, 12             read a byte
  0x000802b7,  -- 0x119c  lui  t0, 0x80
  0x10028293,  -- 0x11a0  addi t0, t0, 0x100      input, 16 bytes
  0x01028313,  -- 0x11a4  addi t1, t0, 16
  0x05c003ef,  -- 0x11a8  jal  t2, readn
  0x000802b7,  -- 0x11ac  lui  t0, 0x80
  0x20028293,  -- 0x11b0  addi t0, t0, 0x200      key, 32 bytes
  0x02028313,  -- 0x11b4  addi t1, t0, 32
  0x04c003ef,  -- 0x11b8  jal  t2, readn
  0x000802b7,  -- 0x11bc  lui  t0, 0x80
  0x30028293,  -- 0x11c0  addi t0, t0, 0x300      constant, 16 bytes
  0x01028313,  -- 0x11c4  addi t1, t0, 16
  0x03c003ef,  -- 0x11c8  jal  t2, readn
  0x00080537,  -- 0x11cc  lui  a0, 0x80           output
  0x10050593,  -- 0x11d0  addi a1, a0, 0x100
  0x20050613,  -- 0x11d4  addi a2, a0, 0x200
  0x30050693,  -- 0x11d8  addi a3, a0, 0x300
  0xf95ff0ef,  -- 0x11dc  jal  ra, crypto_core_hsalsa20_tweet
  0x000802b7,  -- 0x11e0  lui  t0, 0x80
  0x02028313,  -- 0x11e4  addi t1, t0, 32
  0x00b00893,  -- 0x11e8  li   a7, 11             print a byte
  0x0002c503,  -- 0x11ec  print: lbu a0, 0(t0)
  0x00000073,  -- 0x11f0  ecall
  0x00128293,  -- 0x11f4  addi t0, t0, 1
  0xfe629ae3,  -- 0x11f8  bne  t0, t1, print
  0x00a00893,  -- 0x11fc  li   a7, 10             exit 0
  0x00000073,  -- 0x1200  ecall
  0x00000073,  -- 0x1204  readn: ecall
  0x00a28023,  -- 0x1208  sb   a0, 0(t0)
  0x00128293,  -- 0x120c  addi t0, t0, 1
  0xfe629ae3,  -- 0x1210  bne  t0, t1, readn
  0x00038067]  -- 0x1214  jr   t2

/-- The image from address 0: a jump to the driver, the helper at `coreEntry`, the wrapper
at `HSalsa20Program.entry`, then the driver. -/
def prog : List (BitVec 32) :=
  [0x1940106f] ++  -- 0x0  j driver
  List.replicate 11 0 ++ Salsa20Program.coreWords ++
  List.replicate 849 0 ++ HSalsa20Program.wrapperWords ++ driverWords

/-- One mebibyte of memory, as for the linked fixture. -/
def memSize : Nat := 0x100000

def initial : Machine 64 := load 64 prog memSize []

end TweetNaCl.HSalsa20IOProgram
