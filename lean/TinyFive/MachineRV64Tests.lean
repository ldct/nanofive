import TinyFive.Machine

/-! Kernel-checked tests of the RV64 word and M-extension encodings. The operands
with dirty high halves detect using XLEN arithmetic in place of word arithmetic. -/
namespace TinyFive.MachineRV64Tests
set_option maxRecDepth 1024

private def r (opcode f3 f7 : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (opcode + 3 * 2^7 + f3 * 2^12 + 1 * 2^15 + 2 * 2^20 + f7 * 2^25)

private def i (opcode f3 imm : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (opcode + 3 * 2^7 + f3 * 2^12 + 1 * 2^15 + imm * 2^20)

private def check (word : BitVec 32) (a b expected : BitVec 64) : Bool :=
  let m := load 64 [word, 0x87654321] 8 []
  let m' := step ((m.setReg 1 a).setReg 2 b)
  m'.status == .running && m'.pc == 4 && m'.x.get 3 == expected

example : check (i 0x03 6 4) 0 0 0x87654321 := by decide
example : check (i 0x03 2 4) 0 0 0xffffffff87654321 := by decide
example : check (i 0x1b 0 4095) 0xdeadbeef80000000 0 0x7fffffff := by decide
example : check (i 0x1b 1 31) 1 0 0xffffffff80000000 := by decide
example : check (i 0x1b 5 31) 0xdeadbeef80000000 0 1 := by decide
example : check (i 0x1b 5 (1024 + 31)) 0xdeadbeef80000000 0 (-1) := by decide
example : check (r 0x3b 0 0) 0xdeadbeef7fffffff 1 0xffffffff80000000 := by decide
example : check (r 0x3b 0 0x20) 0xdeadbeef80000000 1 0x7fffffff := by decide
example : check (r 0x3b 1 0) 1 63 0xffffffff80000000 := by decide
example : check (r 0x3b 5 0) 0xdeadbeef80000000 33 0x40000000 := by decide
example : check (r 0x3b 5 0x20) 0xdeadbeef80000000 33 0xffffffffc0000000 := by decide
example : check (r 0x3b 0 1) 0xdeadbeef7fffffff 2 (-2) := by decide
example : check (r 0x3b 4 1) 0xfeedfacefffffff9 3 (-2) := by decide
example : check (r 0x3b 6 1) 0xfeedfacefffffff9 3 (-1) := by decide
example : check (r 0x3b 4 1) 0x80000000 0xffffffff 0xffffffff80000000 := by decide
example : check (r 0x3b 6 1) 0x80000000 0xffffffff 0 := by decide
example : check (r 0x3b 5 1) 0xdeadbeef80000001 1 0xffffffff80000001 := by decide
example : check (r 0x3b 7 1) 0xdeadbeef80000001 0xffffffff 0xffffffff80000001 := by decide
example : check (r 0x3b 4 1) 0x87654321 0x100000000 (-1) := by decide
example : check (r 0x3b 5 1) 0x87654321 0x100000000 (-1) := by decide
example : check (r 0x3b 6 1) 0x87654321 0x100000000 0xffffffff87654321 := by decide
example : check (r 0x3b 7 1) 0x87654321 0x100000000 0xffffffff87654321 := by decide
example : check (r 0x33 1 1) (-2) 3 (-1) := by decide
example : check (r 0x33 2 1) (-2) (-1) (-2) := by decide
example : check (r 0x33 3 1) (-1) (-1) (-2) := by decide
example : check (r 0x33 4 1) (-7) 3 (-2) := by decide
example : check (r 0x33 6 1) 7 (-3) 1 := by decide
example : check (r 0x33 4 1) (2^63) (-1) (2^63) := by decide
example : check (r 0x33 6 1) (2^63) (-1) 0 := by decide
example : check (r 0x33 4 1) (-7) 0 (-1) := by decide
example : check (r 0x33 6 1) (-7) 0 (-7) := by decide
example : check (r 0x33 7 1) (-7) 0 (-7) := by decide
example : check (r 0x33 7 1) (-1) 3 0 := by decide

-- RV32 excludes RV64-only instructions, not the XLEN-wide M operations.
example : decode 32 (i 0x03 6 4) = none := by decide
example : decode 32 (i 0x1b 0 4095) = none := by decide
example : decode 32 (r 0x3b 0 1) = none := by decide
example : decode 32 (r 0x33 2 1) = some (.op .mulhsu 3 1 2) := by decide
example : alu .div (0x80000000 : BitVec 32) (-1) = 0x80000000 := by decide

-- imm[5] is reserved on word shifts, but is part of shamt on XLEN-wide RV64 shifts.
example : decode 64 (i 0x1b 1 32) = none := by decide
example : decode 64 (i 0x1b 5 32) = none := by decide
example : decode 64 (i 0x1b 5 (1024 + 32)) = none := by decide
example : decode 64 (i 0x1b 2 1) = none := by decide
example : decode 64 (r 0x3b 1 0x20) = none := by decide
example : check (i 0x13 1 32) 1 0 0x100000000 := by decide

end TinyFive.MachineRV64Tests
