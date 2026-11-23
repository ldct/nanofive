import TinyFive.Machine
import TinyFive.SieveMemory
import LucyMemory
import CountingPrimesLucy
import GrumpyBinary.Exec

/-! Machine arithmetic on registers holding natural numbers, for the recompiled grumpygordon
image, and the symbolic-execution tactic `gexec`.

A register holding the natural number `n` is `bv n`. Compiled C `int` code computes in the
low 32 bits (`addiw`, `subw`, `mulw`, `divw`, `sraiw`, `slliw`, `sext.w`) and sign-extends;
each rule below says when that agrees with natural-number arithmetic. -/
namespace TinyFive.GrumpyBinary
open SieveMemory

local notation "bv" => BitVec.ofNat 64

/-! ## 64-bit operations -/

theorem msb_bv (a : Nat) (ha : a < 9223372036854775808) : (bv a).msb = false := by
  rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [decide_eq_false_iff_not]; omega

theorem msb_bv32 (a : Nat) (ha : a < 2147483648) : (BitVec.ofNat 32 a).msb = false := by
  rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [decide_eq_false_iff_not]; omega

theorem bv_eq_iff (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    bv a = bv b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  · rintro rfl; rfl

/-- `addi rd, rs, -k`. -/
theorem bv_add_neg (a k : Nat) (hk : 9223372036854775808 ≤ k) (hk' : k < 18446744073709551616)
    (h : 18446744073709551616 - k ≤ a) :
    BitVec.ofNat 64 (a + k) = BitVec.ofNat 64 (a - (18446744073709551616 - k)) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem alu_div (a b : Nat) (ha : a < 9223372036854775808) (hb : b < 9223372036854775808)
    (hb0 : 0 < b) :
    alu .div (bv a) (bv b) = bv (a / b) := by
  have hne : bv b ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    simp at this
    omega
  simp only [alu, hne, ite_false]
  have hab : a / b ≤ a := Nat.div_le_self a b
  rw [BitVec.sdiv_eq, msb_bv a ha, msb_bv b hb, BitVec.udiv_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a < 2^64 by omega), Nat.mod_eq_of_lt (show b < 2^64 by omega),
    Nat.mod_eq_of_lt (show a / b < 2^64 by omega)]

theorem alu_sra (a b : Nat) (ha : a < 9223372036854775808) (hb : b < 64) :
    alu .sra (bv a) (bv b) = bv (a / 2 ^ b) := by
  have hb' : b % 18446744073709551616 % 64 = b := by omega
  have h2 : a / 2 ^ b ≤ a := Nat.div_le_self a _
  simp only [alu, BitVec.toNat_ofNat, hb']
  rw [BitVec.sshiftRight_eq_of_msb_false (msb_bv a ha)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show a < 2^64 by omega),
    Nat.mod_eq_of_lt (show a / 2 ^ b < 2^64 by omega)]

theorem or_one_eq (a : Nat) : a ||| 1 = a / 2 * 2 + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero =>
    simp only [Nat.testBit_zero]
    have : (a / 2 * 2 + 1) % 2 = 1 := by omega
    simp [this]
  | succ i =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have h1 : (1 : Nat) / 2 = 0 := rfl
    have h2 : (a / 2 * 2 + 1) / 2 = a / 2 := by omega
    rw [h1, h2, Nat.zero_testBit, Bool.or_false]

theorem alu_or_one (a : Nat) (ha : a < 18446744073709551616) :
    alu .or (bv a) (bv 1) = bv (a / 2 * 2 + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [alu]
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show a / 2 * 2 + 1 < 2^64 by omega),
    show (1 : Nat) % 2 ^ 64 = 1 from rfl, or_one_eq]

theorem slt_ofNat (a b : Nat) (ha : a < 9223372036854775808) (hb : b < 9223372036854775808) :
    (bv a).slt (bv b) = decide (a < b) := by
  rw [BitVec.slt_eq_ult_of_msb_eq (by rw [msb_bv a ha, msb_bv b hb])]
  rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show a < 2^64 by omega), Nat.mod_eq_of_lt (show b < 2^64 by omega)]

theorem bne_ofNat (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (bv a != bv b) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · have : bv a ≠ bv b := fun e => h ((bv_eq_iff a b ha hb).mp e)
    simp [this, h]

theorem beq_ofNat (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (bv a == bv b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : bv a ≠ bv b := fun e => h ((bv_eq_iff a b ha hb).mp e)
    simp [this, h]

theorem slt_true (a b : Nat) (h : a < b) (hb : b < 9223372036854775808) :
    (bv a).slt (bv b) = true := by
  rw [slt_ofNat a b (by omega) hb]; simp [h]

theorem slt_false (a b : Nat) (h : b ≤ a) (ha : a < 9223372036854775808) :
    (bv a).slt (bv b) = false := by
  rw [slt_ofNat a b ha (by omega)]; simp; omega

theorem bne_true (a b : Nat) (h : a ≠ b) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) : (bv a != bv b) = true := by
  rw [bne_ofNat a b ha hb]; simp [h]

theorem bne_false (a b : Nat) (h : a = b) : (bv a != bv b) = false := by
  subst h; simp

theorem beq_true' (a b : Nat) (h : a = b) : (bv a == bv b) = true := by
  subst h; simp

theorem beq_false' (a b : Nat) (h : a ≠ b) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) : (bv a == bv b) = false := by
  rw [beq_ofNat a b ha hb]; simp [h]

theorem bne_zero_true (a : Nat) (h : a ≠ 0) (ha : a < 18446744073709551616) :
    (bv a != (0 : BitVec 64)) = true := bne_true a 0 h ha (by decide)

theorem bne_zero_false (a : Nat) (h : a = 0) : (bv a != (0 : BitVec 64)) = false := by
  subst h; decide

theorem addr_neg1 (a : Nat) (h : 1 ≤ a) (ha : a < 18446744073709551616) :
    (BitVec.ofNat 64 a + 18446744073709551615#64).toNat = a - 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-! ## 32-bit (`int`) operations -/

theorem setWidth32 (a : Nat) : (bv a).setWidth 32 = BitVec.ofNat 32 a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem sext32 (a : Nat) (ha : a < 2147483648) :
    (BitVec.ofNat 32 a).signExtend 64 = bv a := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (msb_bv32 a ha)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem alu32_add (a b : Nat) :
    alu .add (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = BitVec.ofNat 32 (a + b) := by
  simp only [alu, BitVec.ofNat_add]

theorem alu32_sub (a b : Nat) (h : b ≤ a) :
    alu .sub (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = BitVec.ofNat 32 (a - b) := by
  have : BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  simp only [alu]
  rw [this, BitVec.add_sub_cancel]

theorem alu32_mul (a b : Nat) :
    alu .mul (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = BitVec.ofNat 32 (a * b) := by
  simp only [alu, BitVec.ofNat_mul]

theorem alu32_sll (a b : Nat) (hb : b < 32) :
    alu .sll (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = BitVec.ofNat 32 (a * 2 ^ b) := by
  apply BitVec.eq_of_toNat_eq
  have : b % 4294967296 % 32 = b := by omega
  simp only [alu, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, this, Nat.shiftLeft_eq,
    Nat.mod_mul_mod]

theorem alu32_sra (a b : Nat) (ha : a < 2147483648) (hb : b < 32) :
    alu .sra (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = BitVec.ofNat 32 (a / 2 ^ b) := by
  have hb' : b % 4294967296 % 32 = b := by omega
  have h2 : a / 2 ^ b ≤ a := Nat.div_le_self a _
  simp only [alu, BitVec.toNat_ofNat, hb']
  rw [BitVec.sshiftRight_eq_of_msb_false (msb_bv32 a ha)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show a < 2^32 by omega),
    Nat.mod_eq_of_lt (show a / 2 ^ b < 2^32 by omega)]

theorem alu32_div (a b : Nat) (ha : a < 2147483648) (hb : b < 2147483648) (hb0 : 0 < b) :
    alu .div (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = BitVec.ofNat 32 (a / b) := by
  have hne : BitVec.ofNat 32 b ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    simp at this
    omega
  simp only [alu, hne, ite_false]
  have hab : a / b ≤ a := Nat.div_le_self a b
  rw [BitVec.sdiv_eq, msb_bv32 a ha, msb_bv32 b hb, BitVec.udiv_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a < 2^32 by omega), Nat.mod_eq_of_lt (show b < 2^32 by omega),
    Nat.mod_eq_of_lt (show a / b < 2^32 by omega)]

/-- `addiw rd, rs, -k`. -/
theorem bv32_add_neg (a k : Nat) (hk : 2147483648 ≤ k) (hk' : k < 4294967296)
    (h : 4294967296 - k ≤ a) :
    BitVec.ofNat 32 (a + k) = BitVec.ofNat 32 (a - (4294967296 - k)) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-! ## Loads -/

theorem sext_dword (v : BitVec 64) : v.signExtend 64 = v := BitVec.signExtend_eq v

end TinyFive.GrumpyBinary
