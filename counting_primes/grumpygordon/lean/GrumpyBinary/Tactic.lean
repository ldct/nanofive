import GrumpyBinary.Arith

/-! Stores as a total function `wr`, and the symbolic-execution tactic `gexec`.

`gexec` unfolds `run` from a concrete `pc`, fetches each instruction from `instrAt`, and evaluates
it on registers given as `x.get r = bv n` hypotheses. Each store becomes a `wr` layer on the
memory, and a load reads through those layers to a hypothesis about the original memory. Side
conditions (no wrap-around, branch outcomes, disjointness, the code prefix) are discharged by
`omega` from the hypotheses in context. -/
namespace TinyFive.GrumpyBinary
open SieveMemory

local notation "bv" => BitVec.ofNat 64

/-- The memory after storing the low `n` bytes of `v` at `a`; unchanged if out of bounds. -/
def wr (mem : Array (BitVec 8)) (a : Nat) {k : Nat} (v : BitVec k) (n : Nat) : Array (BitVec 8) :=
  (writeBytes mem a v n).getD mem

theorem writeBytes_wr (mem : Array (BitVec 8)) (a : Nat) {k : Nat} (v : BitVec k) (n : Nat)
    (h : a + n ≤ mem.size) : writeBytes mem a v n = some (wr mem a v n) := by
  obtain ⟨mem', hw, _⟩ := LucyMemory.writeBytes_spec n mem a v h
  simp [wr, hw]

theorem writeBytes_size {k : Nat} (n : Nat) (mem mem' : Array (BitVec 8)) (a : Nat) (v : BitVec k)
    (h : writeBytes mem a v n = some mem') : mem'.size = mem.size := by
  induction n generalizing mem a v with
  | zero => simp only [writeBytes, Option.some.injEq] at h; rw [h]
  | succ n ih =>
    simp only [writeBytes] at h
    split at h
    · rw [ih _ _ _ h, Array.size_setIfInBounds]
    · cases h

@[simp] theorem wr_size (mem : Array (BitVec 8)) (a : Nat) {k : Nat} (v : BitVec k) (n : Nat) :
    (wr mem a v n).size = mem.size := by
  unfold wr
  cases hw : writeBytes mem a v n with
  | none => rfl
  | some mem' => exact writeBytes_size n mem mem' a v hw

theorem wr_get (mem : Array (BitVec 8)) (a : Nat) {k : Nat} (v : BitVec k) (n : Nat)
    (h : a + n ≤ mem.size) (i : Nat) (hi : i < a ∨ a + n ≤ i) :
    (wr mem a v n)[i]? = mem[i]? := by
  obtain ⟨mem', hw, _, hf, _⟩ := LucyMemory.writeBytes_spec n mem a v h
  simp only [wr, hw, Option.getD_some]
  exact hf i hi

theorem read_wr_other (mem : Array (BitVec 8)) (a : Nat) {k : Nat} (v : BitVec k) (n b m : Nat)
    (h : a + n ≤ mem.size) (hd : b + m ≤ a ∨ a + n ≤ b) :
    readBytes (wr mem a v n) b m = readBytes mem b m := by
  apply readBytes_congr
  intro i h1 h2
  exact wr_get mem a v n h i (by omega)

theorem read_wr_same (mem : Array (BitVec 8)) (a : Nat) {k : Nat} (v : BitVec k) (n : Nat)
    (h : a + n ≤ mem.size) : readBytes (wr mem a v n) a n = some (v.setWidth (8 * n)) := by
  obtain ⟨mem', hw, _, _, hr⟩ := LucyMemory.writeBytes_spec n mem a v h
  simp only [wr, hw, Option.getD_some]
  exact hr

theorem prefix_wr {mem : Array (BitVec 8)} (a : Nat) {k : Nat} (v : BitVec k) (n : Nat)
    (hp : Prefix image mem 1236) (h : a + n ≤ mem.size) (ha : 1236 ≤ a) :
    Prefix image (wr mem a v n) 1236 := by
  intro i hi
  rw [wr_get mem a v n h i (by omega)]
  exact hp i hi

/-- `jalr x0, 0(ra)` to an even return address. -/
theorem ret_target (R : Nat) (hR : R % 2 = 0) :
    bv R &&& 18446744073709551614#64 = bv R := by
  rw [show 18446744073709551614#64 = ~~~1#64 by decide]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases h0 : i = 0
  · subst h0
    rw [BitVec.getLsbD_ofNat, Nat.testBit_zero]; simp [hR]
  · simp [hi, h0]

theorem mod_neg (a k : Nat) (hk : k < 18446744073709551616) (h : 18446744073709551616 - k ≤ a)
    (ha : a < 18446744073709551616) :
    (a + k) % 18446744073709551616 = a - (18446744073709551616 - k) := by omega

theorem get_set_ne (x : Regs 64) (r i : Reg) (v : BitVec 64) (h : i ≠ r) :
    (x.set r v).get i = x.get i := by
  rw [Regs.get_set]
  by_cases h0 : i = 0
  · simp [h0]
  · simp [h0, Ne.symm h]

theorem get_set_zero (x : Regs 64) (i : Reg) (v : BitVec 64) :
    (x.set 0 v).get i = x.get i := by
  rw [Regs.get_set]
  by_cases h0 : i = 0
  · simp [h0]
  · simp [h0, Ne.symm h0]

/-- Registers outside the listed ones are unchanged. -/
macro "frame_tac" : tactic =>
  `(tactic| (intro i hi
             simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
             simp [get_set_ne, get_set_zero, hi]))

/-! `exec` one instruction kind at a time. Unfolding `exec` by definition inside `simp` would
leave the kernel to re-check a `match` whose discriminant is symbolic address arithmetic, which
it evaluates in unary; these equations avoid that. -/

section ExecEq
variable {w : Nat} (m : Machine w)
theorem exec_lui (rd : Reg) (imm : BitVec 20) :
    exec (.lui rd imm) m = (m.setReg rd ((imm ++ 0#12).signExtend w)).advance := rfl
theorem exec_auipc (rd : Reg) (imm : BitVec 20) :
    exec (.auipc rd imm) m = (m.setReg rd (m.pc + (imm ++ 0#12).signExtend w)).advance := rfl
theorem exec_jal (rd : Reg) (imm : BitVec 21) :
    exec (.jal rd imm) m = { m.setReg rd (m.pc + 4) with pc := m.pc + imm.signExtend w } := rfl
theorem exec_jalr (rd rs1 : Reg) (imm : BitVec 12) :
    exec (.jalr rd rs1 imm) m =
      { m.setReg rd (m.pc + 4) with pc := (m.x.get rs1 + imm.signExtend w) &&& ~~~1 } := rfl
theorem exec_branch (op : BranchOp) (rs1 rs2 : Reg) (imm : BitVec 13) :
    exec (.branch op rs1 rs2 imm) m =
      if op.taken (m.x.get rs1) (m.x.get rs2) then { m with pc := m.pc + imm.signExtend w }
      else m.advance := rfl
theorem exec_load (width : Width) (signed : Bool) (rd rs1 : Reg) (imm : BitVec 12) :
    exec (.load width signed rd rs1 imm) m =
      match readBytes m.mem (m.x.get rs1 + imm.signExtend w).toNat width.bytes with
      | some v => (m.setReg rd (if signed then v.signExtend w else v.setWidth w)).advance
      | none => m.fail := rfl
theorem exec_store (width : Width) (rs2 rs1 : Reg) (imm : BitVec 12) :
    exec (.store width rs2 rs1 imm) m =
      match writeBytes m.mem (m.x.get rs1 + imm.signExtend w).toNat (m.x.get rs2) width.bytes with
      | some mem => { m with mem := mem }.advance
      | none => m.fail := rfl
theorem exec_opImm (op : AluOp) (rd rs1 : Reg) (imm : BitVec 12) :
    exec (.opImm op rd rs1 imm) m = (m.setReg rd (alu op (m.x.get rs1) (imm.signExtend w))).advance :=
  rfl
theorem exec_op (op : AluOp) (rd rs1 rs2 : Reg) :
    exec (.op op rd rs1 rs2) m = (m.setReg rd (alu op (m.x.get rs1) (m.x.get rs2))).advance := rfl
theorem exec_opImmWord (op : AluOp) (rd rs1 : Reg) (imm : BitVec 12) :
    exec (.opImmWord op rd rs1 imm) m =
      (m.setReg rd ((alu op ((m.x.get rs1).setWidth 32) (imm.signExtend 32)).signExtend w)).advance :=
  rfl
theorem exec_opWord (op : AluOp) (rd rs1 rs2 : Reg) :
    exec (.opWord op rd rs1 rs2) m =
      (m.setReg rd ((alu op ((m.x.get rs1).setWidth 32)
        ((m.x.get rs2).setWidth 32)).signExtend w)).advance := rfl
theorem exec_ecall : exec .ecall m = ecall m := rfl
end ExecEq

/-- A store is in bounds when it ends inside memory (through any number of `wr` layers). -/
macro "gsize" : tactic => `(tactic| (simp only [wr_size] at *; omega))

/-- Discharge the side conditions of symbolic execution. -/
syntax "gdisch" : tactic
macro_rules
  | `(tactic| gdisch) => `(tactic| first
      | omega
      | assumption
      | gsize
      | (apply prefix_wr <;> first | gdisch | gsize))

/-- Symbolic execution of the recompiled image. -/
macro "gexec" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := gdisch) [-BitVec.toNat_add, -BitVec.reduceSignExtend, run, step_at, gfetch, exec_lui, exec_auipc,
      exec_jal, exec_jalr, exec_branch, exec_load, exec_store, exec_opImm, exec_op, exec_opImmWord,
      exec_opWord, exec_ecall,
      Machine.setReg, Machine.advance, Machine.fail, ecall, Width.bytes, Regs.get_set,
      BranchOp.taken, CountingPrimesLucy.alu_add, CountingPrimesLucy.alu_sub,
      CountingPrimesLucy.alu_mul, CountingPrimesLucy.alu_divu, CountingPrimesLucy.alu_sll,
      CountingPrimesLucy.alu_srl, CountingPrimesLucy.alu_and_m8,
      CountingPrimesLucy.ult_true, CountingPrimesLucy.ult_false, CountingPrimesLucy.addr,
      CountingPrimesLucy.addr', CountingPrimesLucy.addr0,
      alu_div, alu_sra, alu_or_one, slt_true, slt_false, bne_true, bne_false, beq_true',
      beq_false', bne_zero_true, bne_zero_false, addr_neg1, setWidth32, sext32, alu32_add, alu32_sub, alu32_mul, alu32_sll,
      alu32_sra, alu32_div, bv32_add_neg, bv_add_neg, sext_dword, writeBytes_wr, read_wr_same,
      read_wr_other, wr_size, ret_target, mod_neg, Nat.mod_eq_of_lt, *] $[$loc]?)

end TinyFive.GrumpyBinary
