import Std.Tactic.BVDecide
import TinyFive.Machine
import TinyFive.Primes
import TinyFive.SieveMemory
import LucyMath
import LucyMemory

/-! The Lucy_Hedgehog prime counter on the RV64 machine with `mul`, `divu`, `ld` and `sd`. -/
namespace TinyFive.CountingPrimesLucy
open CountingPrimes SieveMemory LucyMath LucyMemory

def prog : List (BitVec 32) := [
  0x00300393, 0x16756863, 0x01800b13, 0x00100293, 0x00000313, 0x00050f13,
  0x03635e33, 0x21c33023, 0xffff0e13, 0xffee7e13, 0x027e5e33, 0x21c33423,
  0x01030313, 0x00228293, 0x02555f33, 0xfc5f7ee3, 0xff830593, 0x00251613,
  0x20803683, 0x02800713, 0x00000f93, 0x10e5e063, 0x1f873f03, 0x0dff0663,
  0x20073e03, 0x41fe0e33, 0x41c686b3, 0x00375793, 0x02f78833, 0x00e708b3,
  0x00381a93, 0x02f584b3, 0x0155f663, 0x03055e33, 0x02ee04b3, 0x011a8433,
  0x0a84ec63, 0x21070913, 0x0285e263, 0x20043e03, 0x00093e83, 0x41fe0e33,
  0x41ce8eb3, 0x01d93023, 0x01090913, 0x01140433, 0xfe85f2e3, 0x00145e13,
  0x41c60e33, 0xff8e7993, 0x0289de33, 0x004e1e13, 0x200e3e03, 0x00093e83,
  0x41fe0e33, 0x41ce8eb3, 0x01d93023, 0x01090913, 0x01140433, 0x40e989b3,
  0xfc84fce3, 0x0355e863, 0x00058a13, 0x40ea0e33, 0x031e5e33, 0x004e1e13,
  0x200e3e03, 0x1f8a3e83, 0x41fe0e33, 0x41ce8eb3, 0x1fda3c23, 0xff0a0a13,
  0xfd5a7ee3, 0x001f8f93, 0x01070713, 0xf2e5f6e3, 0x0240006f, 0x1f873f03,
  0x01ff0a63, 0x20073e03, 0x41fe0e33, 0x41c686b3, 0x001f8f93, 0x01070713,
  0xfee5f2e3, 0x00268513, 0x00100893, 0x00000073, 0x00a00513, 0x00b00893,
  0x00000073, 0x00a00893, 0x00000073, 0x00155513, 0xfe1ff06f]

/-- The machine as `counting_primes_lucy.initial(n)` builds it: the program at address 0 of a
zeroed memory of `BASE + 8 * (isqrt(n) + 1)` bytes, and `n` in `a0`. -/
def initial (n : Nat) : Machine 64 :=
  (load 64 prog (512 + 8 * (isqrt n + 1)) []).setReg 10 (BitVec.ofNat 64 n)

def image : Array (BitVec 8) := (load 64 prog 512 []).mem

/-- The instruction at each code address, as `fetch` checks against the loaded words. -/
def instrAt : Nat → Instr
  | 0 => .opImm .add 7 0 3
  | 4 => .branch .bltu 10 7 368
  | 8 => .opImm .add 22 0 24
  | 12 => .opImm .add 5 0 1
  | 16 => .opImm .add 6 0 0
  | 20 => .opImm .add 30 10 0
  | 24 => .op .divu 28 6 22
  | 28 => .store .dword 28 6 512
  | 32 => .opImm .add 28 30 (-1)
  | 36 => .opImm .and 28 28 (-2)
  | 40 => .op .divu 28 28 7
  | 44 => .store .dword 28 6 520
  | 48 => .opImm .add 6 6 16
  | 52 => .opImm .add 5 5 2
  | 56 => .op .divu 30 10 5
  | 60 => .branch .bgeu 30 5 (-36)
  | 64 => .opImm .add 11 6 (-8)
  | 68 => .opImm .sll 12 10 2
  | 72 => .load .dword true 13 0 520
  | 76 => .opImm .add 14 0 40
  | 80 => .opImm .add 31 0 0
  | 84 => .branch .bltu 11 14 256
  | 88 => .load .dword true 30 14 504
  | 92 => .branch .beq 30 31 204
  | 96 => .load .dword true 28 14 512
  | 100 => .op .sub 28 28 31
  | 104 => .op .sub 13 13 28
  | 108 => .opImm .srl 15 14 3
  | 112 => .op .mul 16 15 15
  | 116 => .op .add 17 14 14
  | 120 => .opImm .sll 21 16 3
  | 124 => .op .mul 9 11 15
  | 128 => .branch .bgeu 11 21 12
  | 132 => .op .divu 28 10 16
  | 136 => .op .mul 9 28 14
  | 140 => .op .add 8 21 17
  | 144 => .branch .bltu 9 8 184
  | 148 => .opImm .add 18 14 528
  | 152 => .branch .bltu 11 8 36
  | 156 => .load .dword true 28 8 512
  | 160 => .load .dword true 29 18 0
  | 164 => .op .sub 28 28 31
  | 168 => .op .sub 29 29 28
  | 172 => .store .dword 29 18 0
  | 176 => .opImm .add 18 18 16
  | 180 => .op .add 8 8 17
  | 184 => .branch .bgeu 11 8 (-28)
  | 188 => .opImm .srl 28 8 1
  | 192 => .op .sub 28 12 28
  | 196 => .opImm .and 19 28 (-8)
  | 200 => .op .divu 28 19 8
  | 204 => .opImm .sll 28 28 4
  | 208 => .load .dword true 28 28 512
  | 212 => .load .dword true 29 18 0
  | 216 => .op .sub 28 28 31
  | 220 => .op .sub 29 29 28
  | 224 => .store .dword 29 18 0
  | 228 => .opImm .add 18 18 16
  | 232 => .op .add 8 8 17
  | 236 => .op .sub 19 19 14
  | 240 => .branch .bgeu 9 8 (-40)
  | 244 => .branch .bltu 11 21 48
  | 248 => .opImm .add 20 11 0
  | 252 => .op .sub 28 20 14
  | 256 => .op .divu 28 28 17
  | 260 => .opImm .sll 28 28 4
  | 264 => .load .dword true 28 28 512
  | 268 => .load .dword true 29 20 504
  | 272 => .op .sub 28 28 31
  | 276 => .op .sub 29 29 28
  | 280 => .store .dword 29 20 504
  | 284 => .opImm .add 20 20 (-16)
  | 288 => .branch .bgeu 20 21 (-36)
  | 292 => .opImm .add 31 31 1
  | 296 => .opImm .add 14 14 16
  | 300 => .branch .bgeu 11 14 (-212)
  | 304 => .jal 0 36
  | 308 => .load .dword true 30 14 504
  | 312 => .branch .beq 30 31 20
  | 316 => .load .dword true 28 14 512
  | 320 => .op .sub 28 28 31
  | 324 => .op .sub 13 13 28
  | 328 => .opImm .add 31 31 1
  | 332 => .opImm .add 14 14 16
  | 336 => .branch .bgeu 11 14 (-28)
  | 340 => .opImm .add 10 13 2
  | 344 => .opImm .add 17 0 1
  | 348 => .ecall
  | 352 => .opImm .add 10 0 10
  | 356 => .opImm .add 17 0 11
  | 360 => .ecall
  | 364 => .opImm .add 17 0 10
  | 368 => .ecall
  | 372 => .opImm .srl 10 10 1
  | 376 => .jal 0 (-32)
  | _ => .ecall

theorem fetch : ∀ pc, pc < 380 → pc % 4 = 0 →
    (readBytes image pc 4).bind (decode 64) = some (instrAt pc) := by
  decide +kernel

theorem step_at (x : Regs 64) (pc : Nat) (mem : Array (BitVec 8))
    (out : String) (st : Status) (hmem : Prefix image mem 380)
    (h : pc < 380) (h4 : pc % 4 = 0) :
    step ⟨x, BitVec.ofNat 64 pc, mem, [], out, st⟩ =
      exec (instrAt pc) ⟨x, BitVec.ofNat 64 pc, mem, [], out, st⟩ := by
  have hpc : (BitVec.ofNat 64 pc).toNat = pc := by
    rw [BitVec.toNat_ofNat]; omega
  apply step_of_prefix _ image 380 hmem (by change (BitVec.ofNat 64 pc).toNat + 4 ≤ 380; omega)
  change (readBytes image (BitVec.ofNat 64 pc).toNat 4).bind (decode 64) = _
  rw [hpc]
  exact fetch _ h h4

/-! ## Machine arithmetic on values that are natural numbers below `2^64` -/

theorem alu_add (a b : Nat) :
    alu .add (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a + b) := by
  simp [alu, BitVec.ofNat_add]

theorem alu_sub (a b : Nat) (h : b ≤ a) :
    alu .sub (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a - b) := by
  have : BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  rw [this]
  simp [alu, BitVec.add_sub_cancel]

theorem alu_mul (a b : Nat) :
    alu .mul (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a * b) := by
  simp [alu, BitVec.ofNat_mul]

theorem alu_divu (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616)
    (hb0 : 0 < b) :
    alu .divu (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a / b) := by
  have hne : BitVec.ofNat 64 b ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    simp at this
    omega
  simp only [alu, hne, ite_false]
  apply BitVec.eq_of_toNat_eq
  have : a / b ≤ a := Nat.div_le_self a b
  simp only [BitVec.toNat_udiv, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a < 2^64 by omega), Nat.mod_eq_of_lt (show b < 2^64 by omega),
    Nat.mod_eq_of_lt (show a / b < 2^64 by omega)]

theorem alu_sll (a b : Nat) (hb : b < 64) :
    alu .sll (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a * 2 ^ b) := by
  apply BitVec.eq_of_toNat_eq
  have : b % 18446744073709551616 % 64 = b := by omega
  simp [alu, this, Nat.shiftLeft_eq, Nat.mod_mul_mod]

theorem alu_srl (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 64) :
    alu .srl (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a / 2 ^ b) := by
  apply BitVec.eq_of_toNat_eq
  have : b % 18446744073709551616 % 64 = b := by omega
  have h2 : a / 2 ^ b ≤ a := Nat.div_le_self a _
  simp [alu, this, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show a / 2 ^ b < 18446744073709551616 by omega)]

theorem alu_and_m2 (a : Nat) (ha : a < 18446744073709551616) :
    alu .and (BitVec.ofNat 64 a) (BitVec.ofNat 64 18446744073709551614) =
      BitVec.ofNat 64 (a / 2 * 2) := by
  have h : ∀ x : BitVec 64, x &&& 18446744073709551614#64 = (x >>> 1) <<< 1 := by
    intro x; bv_decide
  apply BitVec.eq_of_toNat_eq
  simp only [alu, h]
  simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt ha]

theorem alu_and_m8 (a : Nat) (ha : a < 18446744073709551616) :
    alu .and (BitVec.ofNat 64 a) (BitVec.ofNat 64 18446744073709551608) =
      BitVec.ofNat 64 (a / 8 * 8) := by
  have h : ∀ x : BitVec 64, x &&& 18446744073709551608#64 = (x >>> 3) <<< 3 := by
    intro x; bv_decide
  apply BitVec.eq_of_toNat_eq
  simp only [alu, h]
  simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt ha]

theorem ofNat_m1 (a : Nat) (h : 1 ≤ a) :
    BitVec.ofNat 64 (a + 18446744073709551615) = BitVec.ofNat 64 (a - 1) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem ofNat_m8 (a : Nat) (h : 8 ≤ a) :
    BitVec.ofNat 64 (a + 18446744073709551608) = BitVec.ofNat 64 (a - 8) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem ofNat_m16 (a : Nat) (h : 16 ≤ a) :
    BitVec.ofNat 64 (a + 18446744073709551600) = BitVec.ofNat 64 (a - 16) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem ult_true (a b : Nat) (h : a < b) (hb : b < 18446744073709551616) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = true := by
  simp [BitVec.ult, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (show a < 18446744073709551616 by omega), h]

theorem ult_false (a b : Nat) (h : b ≤ a) (ha : a < 18446744073709551616) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = false := by
  simp [BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show b < 18446744073709551616 by omega), h]

theorem beq_true (a b : Nat) (h : a = b) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = true := by
  simp [h]

theorem beq_false (a b : Nat) (h : a ≠ b) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false := by
  apply Bool.eq_false_iff.mpr
  intro he
  have := congrArg BitVec.toNat (eq_of_beq he)
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem addr (a b : Nat) (h : a + b < 18446744073709551616) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).toNat = a + b := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem addr' (a b : Nat) (h : a + b < 18446744073709551616) :
    (a % 18446744073709551616 + b) % 18446744073709551616 = a + b := by
  omega

theorem addr0 (a : Nat) (h : a < 18446744073709551616) :
    (BitVec.ofNat 64 a).toNat = a := by
  simp only [BitVec.toNat_ofNat]; omega

/-- Symbolic execution: fetch from the protected image, then evaluate each instruction on natural
numbers, discharging the no-wrap side conditions with `omega`. -/
macro "lucy_exec" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := first | omega | (show Prefix _ _ _; assumption)) [run, step_at, instrAt, exec,
      Machine.setReg, Machine.advance, Machine.fail, ecall, Width.bytes, Regs.get_set,
      BranchOp.taken, alu_add, alu_sub, alu_mul, alu_divu, alu_sll, alu_srl, alu_and_m2,
      alu_and_m8, ofNat_m1, ofNat_m8, ofNat_m16, ult_true, ult_false, beq_true, beq_false,
      addr, addr', addr0, Nat.mod_eq_of_lt, *] $[$loc]?)

local notation "bv" => BitVec.ofNat 64

theorem get_set_zero (x : Regs 64) (i : Reg) (v : BitVec 64) :
    (x.set 0 v).get i = x.get i := by
  rw [Regs.get_set]
  by_cases h0 : i = 0
  · simp [h0]
  · simp [h0, Ne.symm h0]

theorem get_set_ne (x : Regs 64) (r i : Reg) (v : BitVec 64) (h : i ≠ r) :
    (x.set r v).get i = x.get i := by
  rw [Regs.get_set]
  by_cases h0 : i = 0
  · simp [h0]
  · simp [h0, Ne.symm h]

/-- Registers outside the listed ones are unchanged. -/
macro "frame_tac" : tactic =>
  `(tactic| (intro i hi
             simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
             simp [get_set_ne, get_set_zero, hi]))

/-! ## Straight-line blocks -/

section Blocks

-- Hypotheses are used through `simp [*]` and the `omega` discharger.
set_option linter.unusedVariables false

variable (x : Regs 64) (mem : Array (BitVec 8)) (out : String)

/-- `N < 3`: print `N >> 1`. -/
theorem blk_small (N : Nat) (hmem : Prefix image mem 380) (h10 : x.get 10 = bv N) (hN : N < 3) :
    (run 11 ⟨x, 0, mem, [], out, .running⟩).status = .exited 0 ∧
    (run 11 ⟨x, 0, mem, [], out, .running⟩).output =
      out ++ toString (bv (N / 2)).toInt ++ "\n" := by
  generalize hm : run 11 ⟨x, 0, mem, [], out, .running⟩ = m'
  lucy_exec at hm
  subst hm
  exact ⟨rfl, rfl⟩

/-- Addresses 0 to 20: set up the initialization loop. -/
theorem blk_init (N : Nat) (hmem : Prefix image mem 380) (h10 : x.get 10 = bv N)
    (hN : 3 ≤ N) (hN' : N < 1099511627776) :
    ∃ x', run 6 ⟨x, 0, mem, [], out, .running⟩ = ⟨x', 24, mem, [], out, .running⟩ ∧
      x'.get 10 = bv N ∧ x'.get 7 = bv 3 ∧ x'.get 22 = bv 24 ∧ x'.get 5 = bv 1 ∧
      x'.get 6 = bv 0 ∧ x'.get 30 = bv N := by
  generalize hm : run 6 ⟨x, 0, mem, [], out, .running⟩ = m'
  lucy_exec at hm
  subst hm
  exact ⟨_, rfl, by simp [Regs.get_set, *], by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set]⟩

/-- Addresses 24 to 60: one round of the initialization loop, which stores `small[(v-1)/2]` and
`large[v]`. -/
theorem blk_init_body (N v t q : Nat) (mem1 mem2 : Array (BitVec 8))
    (hmem : Prefix image mem 380) (hmem1 : Prefix image mem1 380) (hmem2 : Prefix image mem2 380)
    (h10 : x.get 10 = bv N) (h5 : x.get 5 = bv v) (h6 : x.get 6 = bv t) (h30 : x.get 30 = bv q)
    (h7 : x.get 7 = bv 3) (h22 : x.get 22 = bv 24)
    (hN : N < 1099511627776) (hv : v < 1099511627776) (ht : t < 1099511627776)
    (hq : q < 1099511627776) (hq1 : 1 ≤ q)
    (hw1 : writeBytes mem (t + 512) (bv (t / 24)) 8 = some mem1)
    (hw2 : writeBytes mem1 (t + 520) (bv ((q - 1) / 2 * 2 / 3)) 8 = some mem2)
    (pc' : Nat) (hpc : (v + 2 ≤ N / (v + 2) ∧ pc' = 24) ∨ (N / (v + 2) < v + 2 ∧ pc' = 64)) :
    ∃ x', run 10 ⟨x, 24, mem, [], out, .running⟩ = ⟨x', bv pc', mem2, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([28, 6, 5, 30] : List Reg) → x'.get i = x.get i) ∧
      x'.get 6 = bv (t + 16) ∧ x'.get 5 = bv (v + 2) ∧ x'.get 30 = bv (N / (v + 2)) := by
  have := Nat.div_le_self N (v + 2)
  generalize hm : run 10 ⟨x, 24, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set], by simp [Regs.get_set],
      by simp [Regs.get_set]⟩

/-- Addresses 64 to 84: `a1 = 8r`, `a2 = 4N`, `a3 = large[1]`, `p = 5`, `c = 0`. -/
theorem blk_post_init (N t a : Nat) (hmem : Prefix image mem 380)
    (h10 : x.get 10 = bv N) (h6 : x.get 6 = bv t)
    (hN : N < 1099511627776) (ht : t < 1099511627776) (ht8 : 8 ≤ t)
    (hr : readBytes mem 520 8 = some (bv a))
    (pc' : Nat) (hpc : (t - 8 < 40 ∧ pc' = 340) ∨ (40 ≤ t - 8 ∧ pc' = 88)) :
    ∃ x', run 6 ⟨x, 64, mem, [], out, .running⟩ = ⟨x', bv pc', mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([11, 12, 13, 14, 31] : List Reg) → x'.get i = x.get i) ∧
      x'.get 11 = bv (t - 8) ∧ x'.get 12 = bv (N * 4) ∧ x'.get 13 = bv a ∧
      x'.get 14 = bv 40 ∧ x'.get 31 = bv 0 := by
  generalize hm : run 6 ⟨x, 64, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set], by simp [Regs.get_set],
      by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set]⟩

/-- Addresses 88 and 92: `p` is prime exactly when `small[(p-1)/2]` differs from `c`. -/
theorem blk_test (e4 c t : Nat) (hmem : Prefix image mem 380)
    (h14 : x.get 14 = bv e4) (h31 : x.get 31 = bv c)
    (he4 : e4 < 1099511627776) (hc : c < 1099511627776) (ht : t < 1099511627776)
    (hr : readBytes mem (e4 + 504) 8 = some (bv t))
    (pc' : Nat) (hpc : (t = c ∧ pc' = 296) ∨ (t ≠ c ∧ pc' = 96)) :
    ∃ x', run 2 ⟨x, 88, mem, [], out, .running⟩ = ⟨x', bv pc', mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([30] : List Reg) → x'.get i = x.get i) := by
  generalize hm : run 2 ⟨x, 88, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac⟩

/-- Addresses 308 and 312: the same test in the tail loop. -/
theorem blk_tail_test (e4 c t : Nat) (hmem : Prefix image mem 380)
    (h14 : x.get 14 = bv e4) (h31 : x.get 31 = bv c)
    (he4 : e4 < 1099511627776) (hc : c < 1099511627776) (ht : t < 1099511627776)
    (hr : readBytes mem (e4 + 504) 8 = some (bv t))
    (pc' : Nat) (hpc : (t = c ∧ pc' = 332) ∨ (t ≠ c ∧ pc' = 316)) :
    ∃ x', run 2 ⟨x, 308, mem, [], out, .running⟩ = ⟨x', bv pc', mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([30] : List Reg) → x'.get i = x.get i) := by
  generalize hm : run 2 ⟨x, 308, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac⟩

/-- Addresses 296 and 300, and 304 on the way out: the next odd `p`. -/
theorem blk_next (e4 e1 : Nat) (hmem : Prefix image mem 380)
    (h14 : x.get 14 = bv e4) (h11 : x.get 11 = bv e1)
    (he4 : e4 < 1099511627776) (he1 : e1 < 1099511627776)
    (n pc' : Nat) (hpc : (e4 + 16 ≤ e1 ∧ n = 2 ∧ pc' = 88) ∨ (e1 < e4 + 16 ∧ n = 3 ∧ pc' = 340)) :
    ∃ x', run n ⟨x, 296, mem, [], out, .running⟩ = ⟨x', bv pc', mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([14] : List Reg) → x'.get i = x.get i) ∧ x'.get 14 = bv (e4 + 16) := by
  generalize hm : run n ⟨x, 296, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl, rfl⟩ | ⟨hc, rfl, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set]⟩

/-- Addresses 292 to 300 (and 304): count the prime `p`, then the next odd `p`. -/
theorem blk_inc (e4 e1 c : Nat) (hmem : Prefix image mem 380)
    (h14 : x.get 14 = bv e4) (h11 : x.get 11 = bv e1) (h31 : x.get 31 = bv c)
    (he4 : e4 < 1099511627776) (he1 : e1 < 1099511627776)
    (n pc' : Nat) (hpc : (e4 + 16 ≤ e1 ∧ n = 3 ∧ pc' = 88) ∨ (e1 < e4 + 16 ∧ n = 4 ∧ pc' = 340)) :
    ∃ x', run n ⟨x, 292, mem, [], out, .running⟩ = ⟨x', bv pc', mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([31, 14] : List Reg) → x'.get i = x.get i) ∧
      x'.get 14 = bv (e4 + 16) ∧ x'.get 31 = bv (c + 1) := by
  generalize hm : run n ⟨x, 292, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl, rfl⟩ | ⟨hc, rfl, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set], by simp [Regs.get_set]⟩

/-- Addresses 328 to 336: count the prime `p`, then the next odd `p` of the tail loop. -/
theorem blk_tail_inc (e4 e1 c : Nat) (hmem : Prefix image mem 380)
    (h14 : x.get 14 = bv e4) (h11 : x.get 11 = bv e1) (h31 : x.get 31 = bv c)
    (he4 : e4 < 1099511627776) (he1 : e1 < 1099511627776)
    (pc' : Nat) (hpc : (e4 + 16 ≤ e1 ∧ pc' = 308) ∨ (e1 < e4 + 16 ∧ pc' = 340)) :
    ∃ x', run 3 ⟨x, 328, mem, [], out, .running⟩ = ⟨x', bv pc', mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([31, 14] : List Reg) → x'.get i = x.get i) ∧
      x'.get 14 = bv (e4 + 16) ∧ x'.get 31 = bv (c + 1) := by
  generalize hm : run 3 ⟨x, 328, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set], by simp [Regs.get_set]⟩

/-- Addresses 332 and 336: the next odd `p` of the tail loop. -/
theorem blk_tail_next (e4 e1 : Nat) (hmem : Prefix image mem 380)
    (h14 : x.get 14 = bv e4) (h11 : x.get 11 = bv e1)
    (he4 : e4 < 1099511627776) (he1 : e1 < 1099511627776)
    (pc' : Nat) (hpc : (e4 + 16 ≤ e1 ∧ pc' = 308) ∨ (e1 < e4 + 16 ∧ pc' = 340)) :
    ∃ x', run 2 ⟨x, 332, mem, [], out, .running⟩ = ⟨x', bv pc', mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([14] : List Reg) → x'.get i = x.get i) ∧ x'.get 14 = bv (e4 + 16) := by
  generalize hm : run 2 ⟨x, 332, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set]⟩

/-- Addresses 316 to 324: `large[1] -= large[p] - c` in the tail loop. -/
theorem blk_tail_prime (e4 c a L : Nat) (hmem : Prefix image mem 380)
    (h14 : x.get 14 = bv e4) (h31 : x.get 31 = bv c) (h13 : x.get 13 = bv a)
    (he4 : e4 < 1099511627776)
    (hr : readBytes mem (e4 + 512) 8 = some (bv L)) (hcL : c ≤ L) (hLa : L - c ≤ a) :
    ∃ x', run 3 ⟨x, 316, mem, [], out, .running⟩ = ⟨x', 328, mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([28, 13] : List Reg) → x'.get i = x.get i) ∧
      x'.get 13 = bv (a - (L - c)) := by
  generalize hm : run 3 ⟨x, 316, mem, [], out, .running⟩ = m'
  lucy_exec at hm
  subst hm
  exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set]⟩

/-- Addresses 96 to 128 when `p*p ≤ r`: `large[1] -= large[p] - c`, then `p`, `p*p`, `16p`,
`8p*p` and `8*kmax*p` with `kmax = r`. -/
theorem blk_prime_a (e4 e1 p c a L : Nat) (hmem : Prefix image mem 380)
    (h14 : x.get 14 = bv e4) (h31 : x.get 31 = bv c) (h13 : x.get 13 = bv a)
    (h11 : x.get 11 = bv e1)
    (he4 : e4 < 1099511627776) (he1 : e1 < 1099511627776) (hp : e4 / 8 = p)
    (hpp : p * p < 1099511627776)
    (hr : readBytes mem (e4 + 512) 8 = some (bv L)) (hcL : c ≤ L) (hLa : L - c ≤ a)
    (hbr : p * p * 8 ≤ e1) :
    ∃ x', run 9 ⟨x, 96, mem, [], out, .running⟩ = ⟨x', 140, mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([28, 13, 15, 16, 17, 21, 9] : List Reg) → x'.get i = x.get i) ∧
      x'.get 13 = bv (a - (L - c)) ∧ x'.get 17 = bv (e4 + e4) ∧ x'.get 21 = bv (p * p * 8) ∧
      x'.get 9 = bv (e1 * p) := by
  generalize hm : run 9 ⟨x, 96, mem, [], out, .running⟩ = m'
  lucy_exec at hm
  subst hm
  exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set]⟩

/-- Addresses 96 to 136 when `p*p > r`: the same with `kmax = N / (p*p)`. -/
theorem blk_prime_b (N e4 e1 p c a L : Nat) (hmem : Prefix image mem 380)
    (h10 : x.get 10 = bv N)
    (h14 : x.get 14 = bv e4) (h31 : x.get 31 = bv c) (h13 : x.get 13 = bv a)
    (h11 : x.get 11 = bv e1)
    (hN : N < 1099511627776)
    (he4 : e4 < 1099511627776) (he1 : e1 < 1099511627776) (hp : e4 / 8 = p)
    (hpp : p * p < 1099511627776) (hpp0 : 0 < p * p)
    (hr : readBytes mem (e4 + 512) 8 = some (bv L)) (hcL : c ≤ L) (hLa : L - c ≤ a)
    (hbr : e1 < p * p * 8) :
    ∃ x', run 11 ⟨x, 96, mem, [], out, .running⟩ = ⟨x', 140, mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([28, 13, 15, 16, 17, 21, 9] : List Reg) → x'.get i = x.get i) ∧
      x'.get 13 = bv (a - (L - c)) ∧ x'.get 17 = bv (e4 + e4) ∧ x'.get 21 = bv (p * p * 8) ∧
      x'.get 9 = bv (N / (p * p) * e4) := by
  generalize hm : run 11 ⟨x, 96, mem, [], out, .running⟩ = m'
  lucy_exec at hm
  subst hm
  exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set], by simp [Regs.get_set],
    by simp [Regs.get_set], by simp [Regs.get_set]⟩

/-- Addresses 140 and 144: `d = (p+2)*p`, and the test `kmax < p + 2` that enters the tail. -/
theorem blk_140 (e5 e7 s1 : Nat) (hmem : Prefix image mem 380)
    (h21 : x.get 21 = bv e5) (h17 : x.get 17 = bv e7) (h9 : x.get 9 = bv s1)
    (he5 : e5 < 1099511627776) (he7 : e7 < 1099511627776) (hs1 : s1 < 1099511627776)
    (pc' : Nat) (hpc : (s1 < e5 + e7 ∧ pc' = 328) ∨ (e5 + e7 ≤ s1 ∧ pc' = 148)) :
    ∃ x', run 2 ⟨x, 140, mem, [], out, .running⟩ = ⟨x', bv pc', mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([8] : List Reg) → x'.get i = x.get i) ∧ x'.get 8 = bv (e5 + e7) := by
  generalize hm : run 2 ⟨x, 140, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set]⟩

/-- Addresses 148 and 152: `s2 = &large[p+2]`, and whether the first loop runs at all. -/
theorem blk_148 (e4 e1 e8 : Nat) (hmem : Prefix image mem 380)
    (h14 : x.get 14 = bv e4) (h11 : x.get 11 = bv e1) (h8 : x.get 8 = bv e8)
    (he1 : e1 < 1099511627776) (he8 : e8 < 1099511627776)
    (pc' : Nat) (hpc : (e1 < e8 ∧ pc' = 188) ∨ (e8 ≤ e1 ∧ pc' = 156)) :
    ∃ x', run 2 ⟨x, 148, mem, [], out, .running⟩ = ⟨x', bv pc', mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([18] : List Reg) → x'.get i = x.get i) ∧ x'.get 18 = bv (e4 + 528) := by
  generalize hm : run 2 ⟨x, 148, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set]⟩

/-- Addresses 156 to 184: `large[k] -= large[k*p] - c`. -/
theorem blk_first (e8 a18 c e7 e1 A Bv : Nat) (mem' : Array (BitVec 8))
    (hmem : Prefix image mem 380) (hmem' : Prefix image mem' 380)
    (h8 : x.get 8 = bv e8) (h18 : x.get 18 = bv a18) (h31 : x.get 31 = bv c)
    (h17 : x.get 17 = bv e7) (h11 : x.get 11 = bv e1)
    (he8 : e8 < 1099511627776) (ha18 : a18 < 1099511627776) (he7 : e7 < 1099511627776)
    (he1 : e1 < 1099511627776)
    (hr1 : readBytes mem (e8 + 512) 8 = some (bv A))
    (hr2 : readBytes mem a18 8 = some (bv Bv)) (hcA : c ≤ A) (hAB : A - c ≤ Bv)
    (hw : writeBytes mem a18 (bv (Bv - (A - c))) 8 = some mem')
    (pc' : Nat) (hpc : (e8 + e7 ≤ e1 ∧ pc' = 156) ∨ (e1 < e8 + e7 ∧ pc' = 188)) :
    ∃ x', run 8 ⟨x, 156, mem, [], out, .running⟩ = ⟨x', bv pc', mem', [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([28, 29, 18, 8] : List Reg) → x'.get i = x.get i) ∧
      x'.get 18 = bv (a18 + 16) ∧ x'.get 8 = bv (e8 + e7) := by
  generalize hm : run 8 ⟨x, 156, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set], by simp [Regs.get_set]⟩

/-- Addresses 188 to 196: `s3 = 8 * ((N - d) >> 1)`. -/
theorem blk_188 (e8 e2 : Nat) (hmem : Prefix image mem 380)
    (h8 : x.get 8 = bv e8) (h12 : x.get 12 = bv e2)
    (he8 : e8 < 1099511627776) (he2 : e2 < 1099511627776) (he : e8 / 2 ≤ e2) :
    ∃ x', run 3 ⟨x, 188, mem, [], out, .running⟩ = ⟨x', 200, mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([28, 19] : List Reg) → x'.get i = x.get i) ∧
      x'.get 19 = bv ((e2 - e8 / 2) / 8 * 8) := by
  generalize hm : run 3 ⟨x, 188, mem, [], out, .running⟩ = m'
  lucy_exec at hm
  subst hm
  exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set]⟩

/-- Addresses 200 to 240: `large[k] -= small[(N/(k*p) - 1) >> 1] - c`. -/
theorem blk_second (e8 a18 e9 c e7 e4 s1 j A Bv : Nat) (mem' : Array (BitVec 8))
    (hmem : Prefix image mem 380) (hmem' : Prefix image mem' 380)
    (h8 : x.get 8 = bv e8) (h18 : x.get 18 = bv a18) (h19 : x.get 19 = bv e9)
    (h31 : x.get 31 = bv c) (h17 : x.get 17 = bv e7) (h14 : x.get 14 = bv e4)
    (h9 : x.get 9 = bv s1)
    (he8 : e8 < 1099511627776) (he80 : 0 < e8) (ha18 : a18 < 1099511627776)
    (he9 : e9 < 1099511627776) (he7 : e7 < 1099511627776) (hs1 : s1 < 1099511627776)
    (hj : e9 / e8 = j) (hj' : j < 1099511627776)
    (hr1 : readBytes mem (j * 16 + 512) 8 = some (bv A))
    (hr2 : readBytes mem a18 8 = some (bv Bv)) (hcA : c ≤ A) (hAB : A - c ≤ Bv)
    (hw : writeBytes mem a18 (bv (Bv - (A - c))) 8 = some mem')
    (pc' : Nat) (hpc : (e8 + e7 ≤ s1 ∧ pc' = 200) ∨ (s1 < e8 + e7 ∧ pc' = 244)) :
    ∃ x', run 11 ⟨x, 200, mem, [], out, .running⟩ = ⟨x', bv pc', mem', [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([28, 29, 18, 8, 19] : List Reg) → x'.get i = x.get i) ∧
      x'.get 18 = bv (a18 + 16) ∧ x'.get 8 = bv (e8 + e7) ∧
      (e4 ≤ e9 → x'.get 19 = bv (e9 - e4)) := by
  generalize hm : run 11 ⟨x, 200, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set], by simp [Regs.get_set],
      fun h => by simp [Regs.get_set, alu_sub, h]⟩

/-- Address 244 when `p*p > r`: the small table is unchanged. -/
theorem blk_244_skip (e1 e5 : Nat) (hmem : Prefix image mem 380)
    (h11 : x.get 11 = bv e1) (h21 : x.get 21 = bv e5)
    (he5 : e5 < 1099511627776) (hc : e1 < e5) :
    run 1 ⟨x, 244, mem, [], out, .running⟩ = ⟨x, 292, mem, [], out, .running⟩ := by
  lucy_exec

/-- Addresses 244 and 248 when `p*p ≤ r`: start the third loop at `v = r`. -/
theorem blk_244_enter (e1 e5 : Nat) (hmem : Prefix image mem 380)
    (h11 : x.get 11 = bv e1) (h21 : x.get 21 = bv e5)
    (he1 : e1 < 1099511627776) (hc : e5 ≤ e1) :
    ∃ x', run 2 ⟨x, 244, mem, [], out, .running⟩ = ⟨x', 252, mem, [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([20] : List Reg) → x'.get i = x.get i) ∧ x'.get 20 = bv e1 := by
  generalize hm : run 2 ⟨x, 244, mem, [], out, .running⟩ = m'
  lucy_exec at hm
  subst hm
  exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set]⟩

/-- Addresses 252 to 288: `small[(v-1)/2] -= small[(v/p - 1) >> 1] - c`. -/
theorem blk_third (e0 e4 e7 e5 c j A Bv : Nat) (mem' : Array (BitVec 8))
    (hmem : Prefix image mem 380) (hmem' : Prefix image mem' 380)
    (h20 : x.get 20 = bv e0) (h14 : x.get 14 = bv e4) (h17 : x.get 17 = bv e7)
    (h31 : x.get 31 = bv c) (h21 : x.get 21 = bv e5)
    (he0 : e0 < 1099511627776) (he40 : e4 ≤ e0) (he7 : e7 < 1099511627776) (he70 : 0 < e7)
    (he016 : 16 ≤ e0) (he5 : e5 < 1099511627776)
    (hj : (e0 - e4) / e7 = j) (hj' : j < 1099511627776)
    (hr1 : readBytes mem (j * 16 + 512) 8 = some (bv A))
    (hr2 : readBytes mem (e0 + 504) 8 = some (bv Bv)) (hcA : c ≤ A) (hAB : A - c ≤ Bv)
    (hw : writeBytes mem (e0 + 504) (bv (Bv - (A - c))) 8 = some mem')
    (pc' : Nat) (hpc : (e5 ≤ e0 - 16 ∧ pc' = 252) ∨ (e0 - 16 < e5 ∧ pc' = 292)) :
    ∃ x', run 10 ⟨x, 252, mem, [], out, .running⟩ = ⟨x', bv pc', mem', [], out, .running⟩ ∧
      (∀ i : Reg, i ∉ ([28, 29, 20] : List Reg) → x'.get i = x.get i) ∧
      x'.get 20 = bv (e0 - 16) := by
  generalize hm : run 10 ⟨x, 252, mem, [], out, .running⟩ = m'
  rcases hpc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  all_goals
    lucy_exec at hm
    subst hm
    exact ⟨_, rfl, by frame_tac, by simp [Regs.get_set]⟩

/-- Addresses 340 to 368: print `large[1] + 2` and a newline, and exit. -/
theorem blk_final (a : Nat) (hmem : Prefix image mem 380) (h13 : x.get 13 = bv a) :
    (run 8 ⟨x, 340, mem, [], out, .running⟩).status = .exited 0 ∧
    (run 8 ⟨x, 340, mem, [], out, .running⟩).output =
      out ++ toString (bv (a + 2)).toInt ++ "\n" := by
  generalize hm : run 8 ⟨x, 340, mem, [], out, .running⟩ = m'
  lucy_exec at hm
  subst hm
  exact ⟨rfl, rfl⟩

end Blocks

end TinyFive.CountingPrimesLucy
