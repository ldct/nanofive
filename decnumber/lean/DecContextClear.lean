import TinyFive.SieveMemory
import Std.Tactic.BVDecide

/-! A proof about `decContextClearStatus` from the jq RV64IM test ELF.
The Python runner checks these exact instruction words against the ELF symbol. -/

namespace DecContextClear
open TinyFive

private theorem fetch {m : Machine 64} {word : BitVec 32} {i : Instr}
    (h : readBytes m.mem m.pc.toNat 4 = some word) (d : decode 64 word = some i) :
    step m = exec i m := by simp [step, h, d]

private theorem write_disjoint {k n a b len : Nat} {mem mem' : Array (BitVec 8)}
    {v : BitVec k} (hw : writeBytes mem a v n = some mem')
    (h : a + n ≤ b ∨ b + len ≤ a) : readBytes mem' b len = readBytes mem b len := by
  induction n generalizing mem a v with
  | zero => simp [writeBytes] at hw; subst mem'; rfl
  | succ n ih =>
    simp only [writeBytes] at hw
    split at hw
    next =>
      rw [ih hw (by omega), SieveMemory.readBytes_update_disjoint]
      omega
    next => contradiction

private theorem write32_low (mem : Array (BitVec 8)) (a : Nat) (v : BitVec 64) :
    writeBytes mem a v 4 = writeBytes mem a (v.setWidth 32) 4 := by
  have h0 : v.setWidth 8 = (v.setWidth 32).setWidth 8 := by bv_decide
  have h1 : (v >>> 8).setWidth 8 = (v.setWidth 32 >>> 8).setWidth 8 := by bv_decide
  have h2 : (v >>> 8 >>> 8).setWidth 8 = (v.setWidth 32 >>> 8 >>> 8).setWidth 8 := by bv_decide
  have h3 : (v >>> 8 >>> 8 >>> 8).setWidth 8 =
      (v.setWidth 32 >>> 8 >>> 8 >>> 8).setWidth 8 := by bv_decide
  simp only [writeBytes, h0, h1, h2, h3]

private theorem status_bits (old : BitVec 32) (mask : BitVec 64) :
    (old.signExtend 64 &&& (mask ^^^ (-1 : BitVec 64))).setWidth 32 =
      old &&& ~~~(mask.setWidth 32) := by bv_decide

/-- For any initial register file and memory satisfying the fetch/load and writable,
nonaliasing status-slot assumptions below, the five instructions clear exactly the
requested status bits, return to `ra` (with bit 0 cleared as required by JALR), and
leave all other memory unchanged. The resulting `a0` is the original pointer. -/
theorem clear_status (x : Regs 64) (pc : BitVec 64) (mem mem' : Array (BitVec 8))
    (inp : List Char) (out : String) (old : BitVec 32)
    (h0 : readBytes mem pc.toNat 4 = some 0x01452703)
    (h1 : readBytes mem (pc + 4).toNat 4 = some 0xfff5c593)
    (h2 : readBytes mem ((pc + 4) + 4).toNat 4 = some 0x00b77733)
    (h3 : readBytes mem (((pc + 4) + 4) + 4).toNat 4 = some 0x00e52a23)
    (h4 : readBytes mem ((((pc + 4) + 4) + 4) + 4).toNat 4 = some 0x00008067)
    (hr : readBytes mem (x.get 10 + 20).toNat 4 = some old)
    (hw : writeBytes mem (x.get 10 + 20).toNat (old &&& ~~~((x.get 11).setWidth 32)) 4 = some mem')
    (hd : (x.get 10 + 20).toNat + 4 ≤ ((((pc + 4) + 4) + 4) + 4).toNat ∨
      ((((pc + 4) + 4) + 4) + 4).toNat + 4 ≤ (x.get 10 + 20).toNat) :
    let result := run 5 (⟨x, pc, mem, inp, out, .running⟩ : Machine 64)
    result.mem = mem' ∧ result.pc = (x.get 1 &&& ~~~1) ∧ result.x.get 10 = x.get 10 ∧
      result.status = .running ∧ result.input = inp ∧ result.output = out := by
  dsimp only
  simp only [run]
  rw [fetch (m := ⟨x, pc, mem, inp, out, .running⟩) h0
    (show decode 64 0x01452703 = some (.load .word true 14 10 20) by decide)]
  simp only [exec, Width.bytes, Machine.advance, Machine.setReg,
    show BitVec.signExtend 64 (20 : BitVec 12) = 20 by decide, hr]
  rw [fetch (m := ⟨_, pc + 4, mem, inp, out, .running⟩) h1
    (show decode 64 0xfff5c593 = some (.opImm .xor 11 11 (-1)) by decide)]
  simp only [exec, Machine.advance, Machine.setReg, alu, Regs.get_set,
    show (14 : Reg) ≠ 11 by decide, show (11 : Reg) ≠ 0 by decide, ite_false,
    show BitVec.signExtend 64 (-1 : BitVec 12) = -1 by decide]
  rw [fetch (m := ⟨_, (pc + 4) + 4, mem, inp, out, .running⟩) h2
    (show decode 64 0x00b77733 = some (.op .and 14 14 11) by decide)]
  simp only [exec, Machine.advance, Machine.setReg, alu, Regs.get_set,
    show (11 : Reg) ≠ 14 by decide, show (14 : Reg) ≠ 0 by decide, ite_false, ite_true]
  rw [fetch (m := ⟨_, ((pc + 4) + 4) + 4, mem, inp, out, .running⟩) h3
    (show decode 64 0x00e52a23 = some (.store .word 14 10 20) by decide)]
  simp only [exec, Width.bytes, Machine.advance, Regs.get_set,
    show (14 : Reg) ≠ 10 by decide, show (11 : Reg) ≠ 10 by decide,
    show (10 : Reg) ≠ 0 by decide, show (14 : Reg) ≠ 0 by decide,
    show (11 : Reg) ≠ 0 by decide, ite_false, ite_true,
    show BitVec.signExtend 64 (20 : BitVec 12) = 20 by decide]
  have hw64 : writeBytes mem (x.get 10 + 20).toNat
      (old.signExtend 64 &&& (x.get 11 ^^^ (-1 : BitVec 64))) 4 = some mem' := by
    rw [write32_low, status_bits]
    exact hw
  rw [hw64]
  have hret := (write_disjoint hw hd).trans h4
  rw [fetch (m := ⟨_, (((pc + 4) + 4) + 4) + 4, mem', inp, out, .running⟩) hret
    (show decode 64 0x00008067 = some (.jalr 0 1 0) by decide)]
  simp [exec, Machine.setReg, Regs.get_set]

end DecContextClear
