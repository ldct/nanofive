import GrumpyBinary.Tactic
import LphaBinary.Exec

/-! The symbolic-execution tactic `lexec` for the lpha image. It is `gexec` of the
grumpygordon proof (same rewrite rules for stores, loads and arithmetic), with this image's
instruction fetch and code prefix. -/
namespace TinyFive.LphaBinary
open SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

theorem prefix_wr {mem : Array (BitVec 8)} (a : Nat) {k : Nat} (v : BitVec k) (n : Nat)
    (hp : Prefix image mem 1536) (h : a + n ≤ mem.size) (ha : 1536 ≤ a) :
    Prefix image (wr mem a v n) 1536 := by
  intro i hi
  rw [wr_get mem a v n h i (by omega)]
  exact hp i hi

/-- Discharge the side conditions of symbolic execution. -/
syntax "ldisch" : tactic
macro_rules
  | `(tactic| ldisch) => `(tactic| first
      | omega
      | assumption
      | gsize
      | (apply prefix_wr <;> first | ldisch | gsize))

/-- Symbolic execution of the recompiled lpha image. -/
macro "lexec" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := ldisch) [-BitVec.toNat_add, -BitVec.reduceSignExtend, run, step_at, gfetch, exec_lui, exec_auipc,
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

end TinyFive.LphaBinary
