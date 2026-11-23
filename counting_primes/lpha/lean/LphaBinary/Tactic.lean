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

theorem addr_neg4 (a : Nat) (h : 4 ≤ a) (ha : a < 18446744073709551616) :
    (BitVec.ofNat 64 a + 18446744073709551612#64).toNat = a - 4 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem addr_neg8 (a : Nat) (h : 8 ≤ a) (ha : a < 18446744073709551616) :
    (BitVec.ofNat 64 a + 18446744073709551608#64).toNat = a - 8 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem addr_neg168 (a : Nat) (h : 168 ≤ a) (ha : a < 18446744073709551616) :
    (BitVec.ofNat 64 a + 18446744073709551448#64).toNat = a - 168 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem addr_neg920 (a : Nat) (h : 920 ≤ a) (ha : a < 18446744073709551616) :
    (BitVec.ofNat 64 a + 18446744073709550696#64).toNat = a - 920 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem addr_neg1008 (a : Nat) (h : 1008 ≤ a) (ha : a < 18446744073709551616) :
    (BitVec.ofNat 64 a + 18446744073709550608#64).toNat = a - 1008 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- `sp` moves past `prime_count`'s 3.3 MiB of tables, and back. -/
@[gfetch] theorem sp_down : alu AluOp.add 4193152#64 18446744073706074112#64 = 715648#64 := by decide
@[gfetch] theorem sp_up : alu AluOp.add 715648#64 3477504#64 = 4193152#64 := by decide

/-! Loads and stores through a plain function of the `Option` result, so that `simp` rewrites
the address (and the read or write) before reducing anything: a `match` on `readBytes` would be
reduced by whnf first, and an address `a + (2^64 - k)` is then evaluated in unary. -/
def loadK (m : Machine 64) (signed : Bool) (rd : Reg) {n : Nat} (o : Option (BitVec n)) :
    Machine 64 :=
  match o with
  | some v => (m.setReg rd (if signed then v.signExtend 64 else v.setWidth 64)).advance
  | none => m.fail

def storeK (m : Machine 64) (o : Option (Array (BitVec 8))) : Machine 64 :=
  match o with
  | some mem => { m with mem := mem }.advance
  | none => m.fail

theorem exec_load_k (m : Machine 64) (width : Width) (signed : Bool) (rd rs1 : Reg)
    (imm : BitVec 12) : exec (.load width signed rd rs1 imm) m =
      loadK m signed rd (readBytes m.mem (m.x.get rs1 + imm.signExtend 64).toNat width.bytes) := by
  rw [exec_load]; generalize readBytes _ _ _ = o; cases o <;> rfl

theorem exec_store_k (m : Machine 64) (width : Width) (rs2 rs1 : Reg) (imm : BitVec 12) :
    exec (.store width rs2 rs1 imm) m =
      storeK m (writeBytes m.mem (m.x.get rs1 + imm.signExtend 64).toNat (m.x.get rs2)
        width.bytes) := by
  rw [exec_store]; generalize writeBytes _ _ _ _ = o; cases o <;> rfl

theorem loadK_some (m : Machine 64) (signed : Bool) (rd : Reg) {n : Nat} (v : BitVec n) :
    loadK m signed rd (some v) =
      (m.setReg rd (if signed then v.signExtend 64 else v.setWidth 64)).advance := rfl

theorem storeK_some (m : Machine 64) (mem : Array (BitVec 8)) :
    storeK m (some mem) = { m with mem := mem }.advance := rfl

theorem writeBytes_low (n : Nat) : ∀ (mem : Array (BitVec 8)) (a : Nat) (v w : BitVec 64),
    v.toNat % 2 ^ (8 * n) = w.toNat % 2 ^ (8 * n) → writeBytes mem a v n = writeBytes mem a w n := by
  induction n with
  | zero => intro mem a v w _; rfl
  | succ n ih =>
    intro mem a v w h
    have h8 : v.setWidth 8 = w.setWidth 8 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      have e : 2 ^ (8 * (n + 1)) = 2 ^ 8 * 2 ^ (8 * n) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [e] at h
      have := congrArg (· % 2 ^ 8) h
      simp only [Nat.mod_mul_right_mod] at this
      exact this
    have hs : (v >>> 8).toNat % 2 ^ (8 * n) = (w >>> 8).toNat % 2 ^ (8 * n) := by
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have e : 2 ^ (8 * (n + 1)) = 2 ^ 8 * 2 ^ (8 * n) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [e] at h
      rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, h]
    simp only [writeBytes, h8]
    split
    · exact ih _ _ _ _ hs
    · rfl

theorem sext_low32 (z : BitVec 32) : (z.signExtend 64).setWidth 32 = z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_signExtend, hi]
  omega

/-- `sw` stores the low word: a sign-extended word stores as the word. -/
theorem wr_sext32 (mem : Array (BitVec 8)) (a z : Nat) :
    wr mem a ((BitVec.ofNat 32 z).signExtend 64) 4 = wr mem a (bv z) 4 := by
  unfold wr
  rw [writeBytes_low 4 mem a _ (bv z)]
  have h := sext_low32 (BitVec.ofNat 32 z)
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  simp only [BitVec.toNat_ofNat, show 8 * 4 = 32 from rfl]
  omega

/-- `slli 32; srli 30`: a zero-extended word index times 4. -/
theorem mul_sll32_srl30 (a : Nat) : a * 4294967296 / 1073741824 = a * 4 := by omega

/-! Address arithmetic with constant offsets: `(a + b) + c` and `(a + b) - c` for numerals `a`, `c`
become `n + b`, so that addresses reached through different base registers agree. -/
theorem lit_add_add (a b c n : Nat) (h : a + c = n) : a + b + c = n + b := by omega
theorem lit_add_sub (a b c n : Nat) (h : a - c = n) (hc : Nat.ble c a = true) :
    a + b - c = n + b := by
  have := Nat.le_of_ble_eq_true hc; omega

open Lean Meta Simp in
simproc litAddAdd ((_ + _ : Nat) + _) := fun e => do
  let_expr HAdd.hAdd _ _ _ _ ab c ← e | return .continue
  let_expr HAdd.hAdd _ _ _ _ a b ← ab | return .continue
  let some na ← Nat.fromExpr? a | return .continue
  let some nc ← Nat.fromExpr? c | return .continue
  unless na + nc < 2 ^ 63 do return .continue
  let n := mkNatLit (na + nc)
  let pf := mkApp5 (mkConst ``lit_add_add) a b c n (← mkEqRefl n)
  return .done { expr := mkNatAdd n b, proof? := some pf }

open Lean Meta Simp in
simproc litAddSub ((_ + _ : Nat) - _) := fun e => do
  let_expr HSub.hSub _ _ _ _ ab c ← e | return .continue
  let_expr HAdd.hAdd _ _ _ _ a b ← ab | return .continue
  let some na ← Nat.fromExpr? a | return .continue
  let some nc ← Nat.fromExpr? c | return .continue
  unless nc ≤ na do return .continue
  let n := mkNatLit (na - nc)
  let pf := mkApp6 (mkConst ``lit_add_sub) a b c n (← mkEqRefl n) (← mkEqRefl (toExpr true))
  return .done { expr := mkNatAdd n b, proof? := some pf }

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
      exec_jal, exec_jalr, exec_branch, exec_load_k, exec_store_k, loadK_some, storeK_some, exec_opImm, exec_op, exec_opImmWord,
      exec_opWord, exec_ecall,
      Machine.setReg, Machine.advance, Machine.fail, ecall, Width.bytes, Regs.get_set,
      BranchOp.taken, CountingPrimesLucy.alu_add, CountingPrimesLucy.alu_sub,
      CountingPrimesLucy.alu_mul, CountingPrimesLucy.alu_divu, CountingPrimesLucy.alu_sll,
      CountingPrimesLucy.alu_srl, CountingPrimesLucy.alu_and_m8,
      CountingPrimesLucy.ult_true, CountingPrimesLucy.ult_false, CountingPrimesLucy.addr,
      CountingPrimesLucy.addr', CountingPrimesLucy.addr0,
      alu_div, alu_sra, alu_or_one, slt_true, slt_false, bne_true, bne_false, beq_true',
      beq_false', bne_zero_true, bne_zero_false, addr_neg1, addr_neg4, addr_neg8, addr_neg168, addr_neg920, addr_neg1008, setWidth32, sext32, alu32_add, alu32_sub, alu32_mul, alu32_sll,
      alu32_sra, alu32_div, bv32_add_neg, bv_add_neg, sext_dword, writeBytes_wr, read_wr_same,
      read_wr_other, wr_size, ret_target, mod_neg, Nat.mod_eq_of_lt, litAddAdd, litAddSub, mul_sll32_srl30, wr_sext32, sext_low32, *] $[$loc]?)

end TinyFive.LphaBinary
