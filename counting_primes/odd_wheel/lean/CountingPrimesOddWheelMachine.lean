import TinyFive.Machine
import TinyFive.SieveMemory

namespace TinyFive.CountingPrimesOddWheel
open SieveMemory

def prog : List (BitVec 32) := [
  0x00350293, 0x0012d293, 0x00200813, 0x12587a63, 0x00229313,
  0x006282b3, 0x00429313, 0x006282b3, 0x00829313, 0x006282b3,
  0x0102d313, 0x00530333, 0x01035313, 0x006282b3, 0x00f2d293,
  0x010003b7, 0x00138393, 0x00800593, 0x2075a023, 0x2075a523,
  0x01458593, 0xfe55eae3, 0x01000613, 0x00800713, 0x00a00793,
  0x00e605b3, 0x00870713, 0x00e585b3, 0x20084303, 0x02031063,
  0x00e606b3, 0x00478893, 0x20760023, 0x1e768ca3, 0x01160633,
  0x011686b3, 0xfe5668e3, 0x00c78793, 0x00280813, 0x00e58633,
  0x1ff84303, 0x02031063, 0x010586b3, 0x010686b3, 0x20758023,
  0x1e768fa3, 0x00f585b3, 0x00f686b3, 0xfe55e8e3, 0xfa5660e3,
  0x00128513, 0xe1028313, 0x00035463, 0x00000313, 0x00000e13,
  0x1fc2ae83, 0x1f82af03, 0x1f42af83, 0x1f02a883, 0x01de0e33,
  0x01ee0e33, 0x01fe0e33, 0x011e0e33, 0xff028293, 0xfc534ee3,
  0x010e5e93, 0x01de0e33, 0x0ffe7e93, 0x41d50533, 0x008e5e13,
  0x0ffe7e13, 0x41c50533, 0xfa5046e3, 0x00100893, 0x00000073,
  0x00a00513, 0x00b00893, 0x00000073, 0x00a00893, 0x00000073,
  0x00155513, 0xfe1ff06f]

def memSize (n : Nat) : Nat := 512 + n / 3 + 4 * Nat.sqrt n + 64
def initial (n : Nat) : Machine 64 :=
  (load 64 prog (memSize n) []).setReg 10 (BitVec.ofNat 64 n)
def image : Array (BitVec 8) := (load 64 prog 512 []).mem
def code : List Instr := prog.map (fun w => (decode 64 w).getD .ecall)

theorem fetch : ∀ pc, pc < 328 → pc % 4 = 0 →
    (readBytes image pc 4).bind (decode 64) = some (code.getD (pc/4) .ecall) := by
  decide +kernel

theorem step_image (x : Regs 64) (pc : BitVec 64) (mem : Array (BitVec 8))
    (out : String) (st : Status) (hmem : Prefix image mem 328)
    (h : pc.toNat < 328) (h4 : pc.toNat % 4 = 0) :
    step ⟨x, pc, mem, [], out, st⟩ =
      exec (code.getD (pc.toNat/4) .ecall) ⟨x, pc, mem, [], out, st⟩ := by
  apply step_of_prefix _ image 328 hmem (by change pc.toNat + 4 ≤ 328; omega)
  exact fetch _ h h4

theorem initial_layout (n : Nat) : Layout image 328 (memSize n) (initial n).mem := by
  exact load_layout_boundary 64 prog 328 512 (memSize n) [] []
    (by decide) (by decide) (by unfold memSize; omega)

end TinyFive.CountingPrimesOddWheel
