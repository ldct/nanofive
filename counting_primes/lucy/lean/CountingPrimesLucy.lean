import TinyFive.Machine
import TinyFive.Primes
import CountingPrimesLoad
import LucyProgram
import TinyFive.SieveMemory
import LucyMath
import LucyMemory

/-! A Lucy_Hedgehog prime counter in O(√N) memory on the RV64 machine, using `mul`, `divu`,
`ld` and `sd` beyond the base instructions.

`correct` gives exit code zero and output `π(n)` within `26 + 41 * n` instructions for every
`n < 10^11`. The arithmetic of the algorithm is in `LucyMath`: `S P v` counts the `n` in `[5, v]`
that are prime or have no prime factor below `P`, and the tables hold `S p` at stage `p`:
`small[i] = S p (2i+1)` and `large[k] = S p (N / k)`. This file shows that the machine code
maintains them:

* each straight-line block is executed symbolically on natural numbers (`blk_*`), with `omega`
  discharging every no-wrap side condition;
* `first_loop`, `second_loop` and `third_loop` are the table updates of one stage, `tail_loop`
  the stages that only change `large[1]`, and `outer_loop` the loop over odd `p ≤ r`;
* `init_loop` fills the tables with the stage-5 values and determines `r`.

The budget is crude: a stage costs at most `11 * r + 60` instructions and there are at most
`r / 2` stages, with `r * r ≤ n`. -/
namespace TinyFive.CountingPrimesLucy
open CountingPrimes SieveMemory LucyMath LucyMemory

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

/-- Clearing the low `n` bits is a shift right and back. -/
theorem and_mask (x : BitVec 64) (n : Nat) :
    x &&& (BitVec.allOnes 64 <<< n) = (x >>> n) <<< n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes]
  by_cases h : i < n
  · simp [h]
  · simp [h, hi, show n + (i - n) = i by omega]
    intro _
    omega

theorem alu_and_m2 (a : Nat) (ha : a < 18446744073709551616) :
    alu .and (BitVec.ofNat 64 a) (BitVec.ofNat 64 18446744073709551614) =
      BitVec.ofNat 64 (a / 2 * 2) := by
  have h : ∀ x : BitVec 64, x &&& 18446744073709551614#64 = (x >>> 1) <<< 1 := by
    intro x
    rw [show 18446744073709551614#64 = BitVec.allOnes 64 <<< 1 by decide, and_mask]
  apply BitVec.eq_of_toNat_eq
  simp only [alu, h]
  simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt ha]

theorem alu_and_m8 (a : Nat) (ha : a < 18446744073709551616) :
    alu .and (BitVec.ofNat 64 a) (BitVec.ofNat 64 18446744073709551608) =
      BitVec.ofNat 64 (a / 8 * 8) := by
  have h : ∀ x : BitVec 64, x &&& 18446744073709551608#64 = (x >>> 3) <<< 3 := by
    intro x
    rw [show 18446744073709551608#64 = BitVec.allOnes 64 <<< 3 by decide, and_mask]
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

/-! ## The two tables in memory -/

/-- A 64-bit slot holding a natural number. -/
def Cell (mem : Array (BitVec 8)) (a v : Nat) : Prop :=
  readBytes mem a 8 = some (bv v)

/-- `small[(v-1)/2]`, at `BASE - 8 + 8v`, holds `f v` for every odd `v ≤ r`. -/
def Small (mem : Array (BitVec 8)) (r : Nat) (f : Nat → Nat) : Prop :=
  ∀ v, v % 2 = 1 → v ≤ r → Cell mem (8 * v + 504) (f v)

/-- `large[k]`, at `BASE + 8k`, holds `g k` for every odd `k` with `lo ≤ k ≤ r`. -/
def Large (mem : Array (BitVec 8)) (lo r : Nat) (g : Nat → Nat) : Prop :=
  ∀ k, k % 2 = 1 → lo ≤ k → k ≤ r → Cell mem (8 * k + 512) (g k)

theorem store_cell {mem : Array (BitVec 8)} {cap : Nat} (hl : Layout image 380 cap mem)
    (a w : Nat) (hlo : 380 ≤ a) (hhi : a + 8 ≤ cap) :
    ∃ mem', writeBytes mem a (bv w) 8 = some mem' ∧ Layout image 380 cap mem' ∧
      Cell mem' a w ∧ ∀ b u, b + 8 ≤ a ∨ a + 8 ≤ b → Cell mem b u → Cell mem' b u := by
  obtain ⟨mem', hw, hl', hr, hf⟩ := store64 hl a (bv w) hlo hhi
  exact ⟨mem', hw, hl', hr, fun b u hb hc => by unfold Cell; rw [hf b hb]; exact hc⟩

/-- What holds of the input `N`, of `r` and of the memory size once the tables are set up: `r` is
the largest odd number with `r * r ≤ N`, and `large[r]` is inside memory. -/
structure Ctx (N r cap : Nat) : Prop where
  hN : N < 100000000000
  h3 : 3 ≤ N
  hodd : r % 2 = 1
  hlo : r * r ≤ N
  hhi : N < (r + 2) * (r + 2)
  hcap : 8 * r + 520 ≤ cap

theorem Ctx.r_lt {N r cap : Nat} (ctx : Ctx N r cap) : r < 316228 := r_lt_of_sq ctx.hlo ctx.hN

theorem Ctx.r_le {N r cap : Nat} (ctx : Ctx N r cap) : r ≤ N :=
  Nat.le_trans (Nat.le_mul_self r) ctx.hlo

/-- The registers of the outer loop: `a0 = N`, `a1 = 8r`, `a2 = 4N`, `a3 = large[1]`, `a4 = 8p`
and `t6 = c`. -/
structure OReg (x : Regs 64) (N r a p c : Nat) : Prop where
  h10 : x.get 10 = bv N
  h11 : x.get 11 = bv (8 * r)
  h12 : x.get 12 = bv (4 * N)
  h13 : x.get 13 = bv a
  h14 : x.get 14 = bv (8 * p)
  h31 : x.get 31 = bv c

/-- The registers of one stage: those of the outer loop with `a7 = 16p`, `s5 = 8p*p` and
`s1 = 8*kmax*p`. -/
structure SReg (x : Regs 64) (N r a p c K : Nat) : Prop where
  h10 : x.get 10 = bv N
  h11 : x.get 11 = bv (8 * r)
  h12 : x.get 12 = bv (4 * N)
  h13 : x.get 13 = bv a
  h14 : x.get 14 = bv (8 * p)
  h31 : x.get 31 = bv c
  h17 : x.get 17 = bv (16 * p)
  h21 : x.get 21 = bv (8 * (p * p))
  h9 : x.get 9 = bv (8 * (K * p))

theorem OReg.frame {x x' : Regs 64} {N r a p c : Nat} {W : List Reg} (h : OReg x N r a p c)
    (hfr : ∀ i : Reg, i ∉ W → x'.get i = x.get i)
    (hW : ∀ i ∈ ([10, 11, 12, 13, 14, 31] : List Reg), i ∉ W) : OReg x' N r a p c :=
  ⟨by rw [hfr 10 (hW 10 (by decide))]; exact h.h10,
   by rw [hfr 11 (hW 11 (by decide))]; exact h.h11,
   by rw [hfr 12 (hW 12 (by decide))]; exact h.h12,
   by rw [hfr 13 (hW 13 (by decide))]; exact h.h13,
   by rw [hfr 14 (hW 14 (by decide))]; exact h.h14,
   by rw [hfr 31 (hW 31 (by decide))]; exact h.h31⟩

theorem SReg.frame {x x' : Regs 64} {N r a p c K : Nat} {W : List Reg} (h : SReg x N r a p c K)
    (hfr : ∀ i : Reg, i ∉ W → x'.get i = x.get i)
    (hW : ∀ i ∈ ([10, 11, 12, 13, 14, 31, 17, 21, 9] : List Reg), i ∉ W) :
    SReg x' N r a p c K :=
  ⟨by rw [hfr 10 (hW 10 (by decide))]; exact h.h10,
   by rw [hfr 11 (hW 11 (by decide))]; exact h.h11,
   by rw [hfr 12 (hW 12 (by decide))]; exact h.h12,
   by rw [hfr 13 (hW 13 (by decide))]; exact h.h13,
   by rw [hfr 14 (hW 14 (by decide))]; exact h.h14,
   by rw [hfr 31 (hW 31 (by decide))]; exact h.h31,
   by rw [hfr 17 (hW 17 (by decide))]; exact h.h17,
   by rw [hfr 21 (hW 21 (by decide))]; exact h.h21,
   by rw [hfr 9 (hW 9 (by decide))]; exact h.h9⟩

theorem SReg.toOReg {x : Regs 64} {N r a p c K : Nat} (h : SReg x N r a p c K) :
    OReg x N r a p c :=
  ⟨h.h10, h.h11, h.h12, h.h13, h.h14, h.h31⟩

/-- Restate a register's value as an equal natural number. -/
theorem bv_of {x : Regs 64} {i : Reg} {a b : Nat} (h : x.get i = bv a) (hab : a = b) :
    x.get i = bv b := hab ▸ h

/-! ## The three inner loops of a stage -/

/-- The first loop, addresses 156 to 184: `large[k] -= large[k*p] - c` while `k * p ≤ r`. -/
theorem first_loop (N r cap p a : Nat) (ctx : Ctx N r cap) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1)
    (hpr : p ≤ r) (hprime : Prime p) (hpp : (p + 2) * p ≤ r)
    (k d : Nat) (hkodd : k % 2 = 1) (hk : p + 2 ≤ k) (hd : d = k * p) (hdr : d ≤ r)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hreg : SReg x N r a p (S p (p - 1)) (kmax N r p))
    (h8 : x.get 8 = bv (8 * d)) (h18 : x.get 18 = bv (8 * k + 512))
    (hlay : Layout image 380 cap mem) (hs : Small mem r (S p))
    (hl : Large mem (p + 2) r (fun j => if j < k then S (p + 1) (N / j) else S p (N / j))) :
    ∃ fuel k' x' mem', fuel + 4 * k ≤ 4 * k' ∧ k' ≤ r ∧ k' % 2 = 1 ∧ p + 2 ≤ k' ∧
      r < k' * p ∧ k' * (p * p) ≤ N ∧
      run fuel ⟨x, 156, mem, [], out, .running⟩ = ⟨x', 188, mem', [], out, .running⟩ ∧
      SReg x' N r a p (S p (p - 1)) (kmax N r p) ∧
      x'.get 8 = bv (8 * (k' * p)) ∧ x'.get 18 = bv (8 * k' + 512) ∧
      Layout image 380 cap mem' ∧ Small mem' r (S p) ∧
      Large mem' (p + 2) r (fun j => if j < k' then S (p + 1) (N / j) else S p (N / j)) := by
  have hr := ctx.r_lt
  have hrN := ctx.r_le
  have hNb := ctx.hN
  have hcap := ctx.hcap
  have hp0 : 0 < p := by omega
  have hkd : k ≤ d := by rw [hd]; exact Nat.le_mul_of_pos_right k hp0
  have hk5 : k * 5 ≤ k * p := Nat.mul_le_mul_left k hp5
  have hdodd : d % 2 = 1 := by rw [hd]; exact odd_mul hkodd hpodd
  have hpd : p * d ≤ N := Nat.le_trans (Nat.mul_le_mul hpr hdr) ctx.hlo
  have hpNd : p ≤ N / d := (Nat.le_div_iff_mul_le (by omega)).mpr hpd
  have hdiv : N / k / p = N / d := by rw [Nat.div_div_eq_div_mul, hd]
  have hA : Cell mem (8 * d + 512) (S p (N / d)) := by
    have := hl d hdodd (by omega) hdr
    simpa [show ¬ d < k by omega] using this
  have hB : Cell mem (8 * k + 512) (S p (N / k)) := by
    have := hl k hkodd hk (by omega)
    simpa using this
  have hstep := S_prime_step p hprime hp5 (N / k) (by rw [hdiv]; exact hpNd)
  rw [hdiv] at hstep
  have hcA : S p (p - 1) ≤ S p (N / d) := S_mono p (by omega)
  have hAle : S p (N / d) ≤ N := Nat.le_trans (S_le _ _) (Nat.div_le_self _ _)
  have hBle : S p (N / k) ≤ N := Nat.le_trans (S_le _ _) (Nat.div_le_self _ _)
  obtain ⟨mem', hw, hlay', hcell, hframe⟩ :=
    store_cell hlay (8 * k + 512) (S (p + 1) (N / k)) (by omega) (by omega)
  have hval : S p (N / k) - (S p (N / d) - S p (p - 1)) = S (p + 1) (N / k) := by omega
  have hs' : Small mem' r (S p) := fun v hv hvr => hframe _ _ (by omega) (hs v hv hvr)
  have hl' : Large mem' (p + 2) r
      (fun j => if j < k + 2 then S (p + 1) (N / j) else S p (N / j)) := by
    intro j hj hjlo hjr
    by_cases hjk : j = k
    · subst hjk
      simpa using hcell
    · have := hframe _ _ (by omega) (hl j hj hjlo hjr)
      by_cases hlt : j < k
      · simpa [hlt, show j < k + 2 by omega] using this
      · simpa [hlt, show ¬ j < k + 2 by omega] using this
  have hd' : d + 2 * p = (k + 2) * p := by rw [hd, Nat.add_mul]
  by_cases hcont : d + 2 * p ≤ r
  · obtain ⟨y, hrun, hfr, hy18, hy8⟩ := blk_first x mem out (8 * d) (8 * k + 512) (S p (p - 1))
      (16 * p) (8 * r) (S p (N / d)) (S p (N / k)) mem' hlay.code_eq hlay'.code_eq h8 h18
      hreg.h31 hreg.h17 hreg.h11 (by omega) (by omega) (by omega) (by omega) hA hB hcA
      (by omega) (by rw [hval]; exact hw) 156 (Or.inl ⟨by omega, rfl⟩)
    obtain ⟨fuel, k', x', mem'', hfuel, hk'r, hk'odd, hk', hrk', hk'N, hrun', hreg', h8', h18',
        hlay'', hs'', hl''⟩ :=
      first_loop N r cap p a ctx hp5 hpodd hpr hprime hpp (k + 2) (d + 2 * p) (by omega)
        (by omega) hd' hcont y mem' out (hreg.frame hfr (by decide))
        (bv_of hy8 (by omega)) (bv_of hy18 (by omega)) hlay' hs' hl'
    refine ⟨8 + fuel, k', x', mem'', by omega, hk'r, hk'odd, by omega, hrk', hk'N, ?_, hreg',
      h8', h18', hlay'', hs'', hl''⟩
    rw [run_add, hrun]
    exact hrun'
  · obtain ⟨y, hrun, hfr, hy18, hy8⟩ := blk_first x mem out (8 * d) (8 * k + 512) (S p (p - 1))
      (16 * p) (8 * r) (S p (N / d)) (S p (N / k)) mem' hlay.code_eq hlay'.code_eq h8 h18
      hreg.h31 hreg.h17 hreg.h11 (by omega) (by omega) (by omega) (by omega) hA hB hcA
      (by omega) (by rw [hval]; exact hw) 188 (Or.inr ⟨by omega, rfl⟩)
    refine ⟨8, k + 2, y, mem', by omega, by omega, by omega, by omega, by rw [← hd']; omega,
      first_exit hp0 (hd ▸ hdr) hpp ctx.hlo, hrun, hreg.frame hfr (by decide), ?_, ?_, hlay',
      hs', hl'⟩
    · exact bv_of hy8 (by omega)
    · exact bv_of hy18 (by omega)
termination_by r + 2 - k
decreasing_by omega

/-- The second loop, addresses 200 to 240: `large[k] -= small[(N/(k*p) - 1) >> 1] - c` while
`k ≤ kmax`. -/
theorem second_loop (N r cap p a : Nat) (ctx : Ctx N r cap) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1)
    (hpr : p ≤ r) (hprime : Prime p)
    (k d : Nat) (hkodd : k % 2 = 1) (hk : p + 2 ≤ k) (hkK : k ≤ kmax N r p) (hd : d = k * p)
    (hrd : r < d)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hreg : SReg x N r a p (S p (p - 1)) (kmax N r p))
    (h8 : x.get 8 = bv (8 * d)) (h18 : x.get 18 = bv (8 * k + 512))
    (h19 : x.get 19 = bv (8 * ((N - d) / 2)))
    (hlay : Layout image 380 cap mem) (hs : Small mem r (S p))
    (hl : Large mem (p + 2) r (fun j => if j < k then S (p + 1) (N / j) else S p (N / j))) :
    ∃ fuel x' mem', fuel + 6 * k ≤ 6 * (r + 2) ∧
      run fuel ⟨x, 200, mem, [], out, .running⟩ = ⟨x', 244, mem', [], out, .running⟩ ∧
      SReg x' N r a p (S p (p - 1)) (kmax N r p) ∧
      Layout image 380 cap mem' ∧ Small mem' r (S p) ∧
      Large mem' (p + 2) r (fun j => S (p + 1) (N / j)) := by
  have hr := ctx.r_lt
  have hrN := ctx.r_le
  have hNb := ctx.hN
  have hcap := ctx.hcap
  have hrodd := ctx.hodd
  have hp0 : 0 < p := by omega
  have hkr : k ≤ r := kmax_le hp0 hpodd ctx.hodd ctx.hhi hkodd hkK
  have hkN : k * (p * p) ≤ N := (kmax_iff hp0 ctx.hlo hkr).mp hkK
  have hpd : p * d ≤ N := by rw [hd, Nat.mul_left_comm]; exact hkN
  have hdN : d ≤ N := Nat.le_trans (Nat.le_mul_of_pos_left d hp0) hpd
  have hd0 : 0 < d := by omega
  have hpNd : p ≤ N / d := (Nat.le_div_iff_mul_le hd0).mpr hpd
  have hdodd : d % 2 = 1 := by rw [hd]; exact odd_mul hkodd hpodd
  have hNd : N / d < r + 2 := by
    rw [Nat.div_lt_iff_lt_mul hd0]
    exact Nat.lt_of_lt_of_le ctx.hhi (Nat.mul_le_mul_left _ (by omega))
  have hKp := kmax_mul_le (N := N) hp0 hpr ctx.hlo
  have hdiv : N / k / p = N / d := by rw [Nat.div_div_eq_div_mul, hd]
  have hj := scaled_half_div N d hdN
  have hA : Cell mem ((N / d - 1) / 2 * 16 + 512) (S p (N / d)) := by
    have := hs (2 * ((N / d - 1) / 2) + 1) (by omega) (by omega)
    rw [S_odd_index p (by omega) (N / d) (by omega)] at this
    rw [show (N / d - 1) / 2 * 16 + 512 = 8 * (2 * ((N / d - 1) / 2) + 1) + 504 by omega]
    exact this
  have hB : Cell mem (8 * k + 512) (S p (N / k)) := by
    have := hl k hkodd hk (by omega)
    simpa using this
  have hstep := S_prime_step p hprime hp5 (N / k) (by rw [hdiv]; exact hpNd)
  rw [hdiv] at hstep
  have hcA : S p (p - 1) ≤ S p (N / d) := S_mono p (by omega)
  have hAle : S p (N / d) ≤ N := Nat.le_trans (S_le _ _) (Nat.div_le_self _ _)
  have hBle : S p (N / k) ≤ N := Nat.le_trans (S_le _ _) (Nat.div_le_self _ _)
  obtain ⟨mem', hw, hlay', hcell, hframe⟩ :=
    store_cell hlay (8 * k + 512) (S (p + 1) (N / k)) (by omega) (by omega)
  have hval : S p (N / k) - (S p (N / d) - S p (p - 1)) = S (p + 1) (N / k) := by omega
  have hs' : Small mem' r (S p) := fun v hv hvr => hframe _ _ (by omega) (hs v hv hvr)
  have hl' : Large mem' (p + 2) r
      (fun j => if j < k + 2 then S (p + 1) (N / j) else S p (N / j)) := by
    intro j hj hjlo hjr
    by_cases hjk : j = k
    · subst hjk
      simpa using hcell
    · have := hframe _ _ (by omega) (hl j hj hjlo hjr)
      by_cases hlt : j < k
      · simpa [hlt, show j < k + 2 by omega] using this
      · simpa [hlt, show ¬ j < k + 2 by omega] using this
  have hd' : d + 2 * p = (k + 2) * p := by rw [hd, Nat.add_mul]
  by_cases hcont : k + 2 ≤ kmax N r p
  · have hk2r : k + 2 ≤ r := kmax_le hp0 hpodd ctx.hodd ctx.hhi (by omega) hcont
    have hk2N : (k + 2) * (p * p) ≤ N := (kmax_iff hp0 ctx.hlo hk2r).mp hcont
    have hk2p : (k + 2) * p ≤ (k + 2) * (p * p) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left p hp0)
    have hmul : (k + 2) * p ≤ kmax N r p * p := Nat.mul_le_mul_right p hcont
    obtain ⟨y, hrun, hfr, hy18, hy8, hy19⟩ := blk_second x mem out (8 * d) (8 * k + 512)
      (8 * ((N - d) / 2)) (S p (p - 1)) (16 * p) (8 * p) (8 * (kmax N r p * p))
      ((N / d - 1) / 2) (S p (N / d)) (S p (N / k)) mem' hlay.code_eq hlay'.code_eq h8 h18 h19
      hreg.h31 hreg.h17 hreg.h14 hreg.h9 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hj (by omega) hA hB hcA (by omega) (by rw [hval]; exact hw) 200
      (Or.inl ⟨by omega, rfl⟩)
    obtain ⟨fuel, x', mem'', hfuel, hrun', hreg', hlay'', hs'', hl''⟩ :=
      second_loop N r cap p a ctx hp5 hpodd hpr hprime (k + 2) (d + 2 * p) (by omega)
        (by omega) hcont hd' (by omega) y mem' out (hreg.frame hfr (by decide))
        (bv_of hy8 (by omega)) (bv_of hy18 (by omega)) (bv_of (hy19 (by omega)) (by omega))
        hlay' hs' hl'
    refine ⟨11 + fuel, x', mem'', by omega, ?_, hreg', hlay'', hs'', hl''⟩
    rw [run_add, hrun]
    exact hrun'
  · have hmul : kmax N r p * p < (k + 2) * p := (Nat.mul_lt_mul_right hp0).mpr (by omega)
    obtain ⟨y, hrun, hfr, hy18, hy8, hy19⟩ := blk_second x mem out (8 * d) (8 * k + 512)
      (8 * ((N - d) / 2)) (S p (p - 1)) (16 * p) (8 * p) (8 * (kmax N r p * p))
      ((N / d - 1) / 2) (S p (N / d)) (S p (N / k)) mem' hlay.code_eq hlay'.code_eq h8 h18 h19
      hreg.h31 hreg.h17 hreg.h14 hreg.h9 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hj (by omega) hA hB hcA (by omega) (by rw [hval]; exact hw) 244
      (Or.inr ⟨by omega, rfl⟩)
    refine ⟨11, y, mem', by omega, hrun, hreg.frame hfr (by decide), hlay', hs', ?_⟩
    intro j hj hjlo hjr
    have := hl' j hj hjlo hjr
    by_cases hlt : j < k + 2
    · simpa [hlt] using this
    · have hnot : ¬ j * (p * p) ≤ N := fun h => by
        have := (kmax_iff hp0 ctx.hlo hjr).mpr h
        omega
      have hsm := S_small p (by omega) (N / j) (div_lt_sq_of_not (by omega) hnot)
      simp only [hlt, ite_false] at this
      show Cell mem' (8 * j + 512) (S (p + 1) (N / j))
      rw [hsm]
      exact this
termination_by r + 2 - k
decreasing_by
  have := kmax_le (by omega : 0 < p) hpodd ctx.hodd ctx.hhi hkodd hkK
  omega

/-- The third loop, addresses 252 to 288: `small[(v-1)/2] -= small[(v/p - 1) >> 1] - c` for `v`
from `r` down to `p * p`. -/
theorem third_loop (N r cap p a : Nat) (ctx : Ctx N r cap) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1)
    (hpr : p ≤ r) (hprime : Prime p)
    (v : Nat) (hvodd : v % 2 = 1) (hpv : p * p ≤ v) (hvr : v ≤ r)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hreg : SReg x N r a p (S p (p - 1)) (kmax N r p))
    (h20 : x.get 20 = bv (8 * v))
    (hlay : Layout image 380 cap mem)
    (hs : Small mem r (fun u => if v < u then S (p + 1) u else S p u))
    (g : Nat → Nat) (hl : Large mem (p + 2) r g) :
    ∃ fuel x' mem', fuel ≤ 5 * v ∧
      run fuel ⟨x, 252, mem, [], out, .running⟩ = ⟨x', 292, mem', [], out, .running⟩ ∧
      SReg x' N r a p (S p (p - 1)) (kmax N r p) ∧
      Layout image 380 cap mem' ∧ Small mem' r (S (p + 1)) ∧ Large mem' (p + 2) r g := by
  have hr := ctx.r_lt
  have hrN := ctx.r_le
  have hNb := ctx.hN
  have hcap := ctx.hcap
  have hp0 : 0 < p := by omega
  have hppp : p ≤ p * p := Nat.le_mul_of_pos_left p hp0
  have hpvp : p ≤ v / p := (Nat.le_div_iff_mul_le hp0).mpr hpv
  have hvp : v / p ≤ v := Nat.div_le_self v p
  have hj := scaled_half_div' v p (by omega)
  have hA : Cell mem ((v / p - 1) / 2 * 16 + 512) (S p (v / p)) := by
    have := hs (2 * ((v / p - 1) / 2) + 1) (by omega) (by omega)
    simp only [show ¬ v < 2 * ((v / p - 1) / 2) + 1 by omega, ite_false] at this
    rw [S_odd_index p (by omega) (v / p) (by omega)] at this
    rw [show (v / p - 1) / 2 * 16 + 512 = 8 * (2 * ((v / p - 1) / 2) + 1) + 504 by omega]
    exact this
  have hB : Cell mem (8 * v + 504) (S p v) := by
    have := hs v hvodd hvr
    simpa using this
  have hstep := S_prime_step p hprime hp5 v hpvp
  have hcA : S p (p - 1) ≤ S p (v / p) := S_mono p (by omega)
  have hAle : S p (v / p) ≤ v := Nat.le_trans (S_le _ _) hvp
  have hBle : S p v ≤ v := S_le _ _
  obtain ⟨mem', hw, hlay', hcell, hframe⟩ :=
    store_cell hlay (8 * v + 504) (S (p + 1) v) (by omega) (by omega)
  have hval : S p v - (S p (v / p) - S p (p - 1)) = S (p + 1) v := by omega
  have hs' : Small mem' r (fun u => if v - 2 < u then S (p + 1) u else S p u) := by
    intro u hu hur
    by_cases huv : u = v
    · subst huv
      simpa [show u - 2 < u by omega] using hcell
    · have := hframe _ _ (by omega) (hs u hu hur)
      by_cases hlt : v < u
      · simpa [hlt, show v - 2 < u by omega] using this
      · simpa [hlt, show ¬ v - 2 < u by omega] using this
  have hl' : Large mem' (p + 2) r g := fun k hk hklo hkr =>
    hframe _ _ (by omega) (hl k hk hklo hkr)
  by_cases hcont : p * p ≤ v - 2
  · obtain ⟨y, hrun, hfr, hy20⟩ := blk_third x mem out (8 * v) (8 * p) (16 * p) (8 * (p * p))
      (S p (p - 1)) ((v / p - 1) / 2) (S p (v / p)) (S p v) mem' hlay.code_eq hlay'.code_eq
      h20 hreg.h14 hreg.h17 hreg.h31 hreg.h21 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hj (by omega) hA hB hcA (by omega) (by rw [hval]; exact hw) 252
      (Or.inl ⟨by omega, rfl⟩)
    obtain ⟨fuel, x', mem'', hfuel, hrun', hreg', hlay'', hs'', hl''⟩ :=
      third_loop N r cap p a ctx hp5 hpodd hpr hprime (v - 2) (by omega) hcont (by omega)
        y mem' out (hreg.frame hfr (by decide)) (bv_of hy20 (by omega)) hlay' hs' g hl'
    refine ⟨10 + fuel, x', mem'', by omega, ?_, hreg', hlay'', hs'', hl''⟩
    rw [run_add, hrun]
    exact hrun'
  · obtain ⟨y, hrun, hfr, hy20⟩ := blk_third x mem out (8 * v) (8 * p) (16 * p) (8 * (p * p))
      (S p (p - 1)) ((v / p - 1) / 2) (S p (v / p)) (S p v) mem' hlay.code_eq hlay'.code_eq
      h20 hreg.h14 hreg.h17 hreg.h31 hreg.h21 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hj (by omega) hA hB hcA (by omega) (by rw [hval]; exact hw) 292
      (Or.inr ⟨by omega, rfl⟩)
    refine ⟨10, y, mem', by omega, hrun, hreg.frame hfr (by decide), hlay', ?_, hl'⟩
    intro u hu hur
    have := hs' u hu hur
    by_cases hlt : v - 2 < u
    · simpa [hlt] using this
    · simp only [hlt, ite_false] at this
      rw [S_small p (by omega) u (by omega)]
      exact this
termination_by v
decreasing_by omega

/-! ## One stage -/

theorem run_chain {a b : Nat} {m m1 m2 : Machine 64} (h1 : run a m = m1) (h2 : run b m1 = m2) :
    run (a + b) m = m2 := by
  rw [run_add, h1, h2]

theorem exits_chain {a b : Nat} {m m1 : Machine 64} {o : String} (h1 : run a m = m1)
    (h2 : is_exited_with_output (run b m1) o) : is_exited_with_output (run (a + b) m) o := by
  rw [run_add, h1]
  exact h2

/-- From address 188 to the end of the stage's table updates: the second and third loops. -/
theorem stage_rest (N r cap p a : Nat) (ctx : Ctx N r cap) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1)
    (hpr : p ≤ r) (hprime : Prime p)
    (k : Nat) (hkodd : k % 2 = 1) (hk : p + 2 ≤ k) (hkK : k ≤ kmax N r p) (hrk : r < k * p)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hreg : SReg x N r a p (S p (p - 1)) (kmax N r p))
    (h8 : x.get 8 = bv (8 * (k * p))) (h18 : x.get 18 = bv (8 * k + 512))
    (hlay : Layout image 380 cap mem) (hs : Small mem r (S p))
    (hl : Large mem (p + 2) r (fun j => if j < k then S (p + 1) (N / j) else S p (N / j))) :
    ∃ fuel x' mem', fuel + 6 * k ≤ 11 * r + 20 ∧
      run fuel ⟨x, 188, mem, [], out, .running⟩ = ⟨x', 292, mem', [], out, .running⟩ ∧
      SReg x' N r a p (S p (p - 1)) (kmax N r p) ∧
      Layout image 380 cap mem' ∧ Small mem' r (S (p + 1)) ∧
      Large mem' (p + 2) r (fun j => S (p + 1) (N / j)) := by
  have hr := ctx.r_lt
  have hrN := ctx.r_le
  have hNb := ctx.hN
  have hp0 : 0 < p := by omega
  have hkr : k ≤ r := kmax_le hp0 hpodd ctx.hodd ctx.hhi hkodd hkK
  have hkN : k * (p * p) ≤ N := (kmax_iff hp0 ctx.hlo hkr).mp hkK
  have hpd : p * (k * p) ≤ N := by rw [Nat.mul_left_comm]; exact hkN
  have hdN : k * p ≤ N := Nat.le_trans (Nat.le_mul_of_pos_left (k * p) hp0) hpd
  have hppN : p * p ≤ N := Nat.le_trans (Nat.mul_le_mul hpr hpr) ctx.hlo
  obtain ⟨y, hrun1, hfr1, hy19⟩ := blk_188 x mem out (8 * (k * p)) (4 * N) hlay.code_eq h8
    hreg.h12 (by omega) (by omega) (by omega)
  obtain ⟨fuel2, z, mem2, hfuel2, hrun2, hreg2, hlay2, hs2, hl2⟩ :=
    second_loop N r cap p a ctx hp5 hpodd hpr hprime k (k * p) hkodd hk hkK rfl hrk y mem out
      (hreg.frame hfr1 (by decide)) (by rw [hfr1 8 (by decide)]; exact h8)
      (by rw [hfr1 18 (by decide)]; exact h18) (bv_of hy19 (by omega)) hlay hs hl
  by_cases hsq : p * p ≤ r
  · obtain ⟨w, hrun3, hfr3, hw20⟩ := blk_244_enter z mem2 out (8 * r) (8 * (p * p))
      hlay2.code_eq hreg2.h11 hreg2.h21 (by omega) (by omega)
    have hs2' : Small mem2 r (fun u => if r < u then S (p + 1) u else S p u) := by
      intro u hu hur
      have := hs2 u hu hur
      simpa [show ¬ r < u by omega] using this
    obtain ⟨fuel3, x', mem3, hfuel3, hrun4, hreg3, hlay3, hs3, hl3⟩ :=
      third_loop N r cap p a ctx hp5 hpodd hpr hprime r ctx.hodd hsq (Nat.le_refl r) w mem2 out
        (hreg2.frame hfr3 (by decide)) hw20 hlay2 hs2' _ hl2
    exact ⟨3 + (fuel2 + (2 + fuel3)), x', mem3, by omega,
      run_chain hrun1 (run_chain hrun2 (run_chain hrun3 hrun4)), hreg3, hlay3, hs3, hl3⟩
  · have hrun3 := blk_244_skip z mem2 out (8 * r) (8 * (p * p)) hlay2.code_eq hreg2.h11
      hreg2.h21 (by omega) (by omega)
    refine ⟨3 + (fuel2 + 1), z, mem2, by omega, run_chain hrun1 (run_chain hrun2 hrun3), hreg2,
      hlay2, ?_, hl2⟩
    intro u hu hur
    rw [S_small p (by omega) u (by omega)]
    exact hs2 u hu hur

/-- From address 148 to address 292: all the table updates of the stage of a prime `p`. -/
theorem stage_body (N r cap p a : Nat) (ctx : Ctx N r cap) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1)
    (hpr : p ≤ r) (hprime : Prime p) (hK : p + 2 ≤ kmax N r p)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hreg : SReg x N r a p (S p (p - 1)) (kmax N r p))
    (h8 : x.get 8 = bv (8 * ((p + 2) * p)))
    (hlay : Layout image 380 cap mem) (hs : Small mem r (S p))
    (hl : Large mem (p + 2) r (fun j => S p (N / j))) :
    ∃ fuel x' mem', fuel ≤ 11 * r + 22 ∧
      run fuel ⟨x, 148, mem, [], out, .running⟩ = ⟨x', 292, mem', [], out, .running⟩ ∧
      SReg x' N r a p (S p (p - 1)) (kmax N r p) ∧
      Layout image 380 cap mem' ∧ Small mem' r (S (p + 1)) ∧
      Large mem' (p + 2) r (fun j => S (p + 1) (N / j)) := by
  have hr := ctx.r_lt
  have hNb := ctx.hN
  have hp0 : 0 < p := by omega
  have hKp := kmax_mul_le (N := N) hp0 hpr ctx.hlo
  have hmul := Nat.mul_le_mul_right p hK
  have hl0 : Large mem (p + 2) r
      (fun j => if j < p + 2 then S (p + 1) (N / j) else S p (N / j)) := by
    intro j hj hjlo hjr
    have := hl j hj hjlo hjr
    simpa [show ¬ j < p + 2 by omega] using this
  by_cases hfirst : (p + 2) * p ≤ r
  · obtain ⟨y, hrun1, hfr1, hy18⟩ := blk_148 x mem out (8 * p) (8 * r) (8 * ((p + 2) * p))
      hlay.code_eq hreg.h14 hreg.h11 h8 (by omega) (by omega) 156 (Or.inr ⟨by omega, rfl⟩)
    obtain ⟨fuel1, k', z, mem1, hfuel1, hk'r, hk'odd, hk', hrk', hk'N, hrun2, hreg1, h8', h18',
        hlay1, hs1, hl1⟩ :=
      first_loop N r cap p a ctx hp5 hpodd hpr hprime hfirst (p + 2) ((p + 2) * p) (by omega)
        (Nat.le_refl _) rfl hfirst y mem out (hreg.frame hfr1 (by decide))
        (by rw [hfr1 8 (by decide)]; exact h8) (bv_of hy18 (by omega)) hlay hs hl0
    obtain ⟨fuel2, x', mem2, hfuel2, hrun3, hreg2, hlay2, hs2, hl2⟩ :=
      stage_rest N r cap p a ctx hp5 hpodd hpr hprime k' hk'odd hk'
        ((kmax_iff hp0 ctx.hlo hk'r).mpr hk'N) hrk' z mem1 out hreg1 h8' h18' hlay1 hs1 hl1
    exact ⟨2 + (fuel1 + fuel2), x', mem2, by omega, run_chain hrun1 (run_chain hrun2 hrun3),
      hreg2, hlay2, hs2, hl2⟩
  · obtain ⟨y, hrun1, hfr1, hy18⟩ := blk_148 x mem out (8 * p) (8 * r) (8 * ((p + 2) * p))
      hlay.code_eq hreg.h14 hreg.h11 h8 (by omega) (by omega) 188 (Or.inl ⟨by omega, rfl⟩)
    obtain ⟨fuel2, x', mem2, hfuel2, hrun3, hreg2, hlay2, hs2, hl2⟩ :=
      stage_rest N r cap p a ctx hp5 hpodd hpr hprime (p + 2) (by omega) (Nat.le_refl _) hK
        (by omega) y mem out (hreg.frame hfr1 (by decide))
        (by rw [hfr1 8 (by decide)]; exact h8) (bv_of hy18 (by omega)) hlay hs hl0
    exact ⟨2 + fuel2, x', mem2, by omega, run_chain hrun1 hrun3, hreg2, hlay2, hs2, hl2⟩

/-- Addresses 96 to 144 for a prime `p`: `large[1]` is updated, the stage's registers are set up,
and control goes to the tail (328) when `kmax < p + 2` and to the table updates (148)
otherwise. -/
theorem prime_head (N r cap p : Nat) (ctx : Ctx N r cap) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1)
    (hpr : p ≤ r) (hprime : Prime p)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hreg : OReg x N r (S p N) p (S p (p - 1)))
    (hlay : Layout image 380 cap mem) (hl : Large mem p r (fun j => S p (N / j))) :
    ∃ fuel x' pc', fuel ≤ 13 ∧
      run fuel ⟨x, 96, mem, [], out, .running⟩ = ⟨x', bv pc', mem, [], out, .running⟩ ∧
      SReg x' N r (S (p + 1) N) p (S p (p - 1)) (kmax N r p) ∧
      x'.get 8 = bv (8 * ((p + 2) * p)) ∧
      ((kmax N r p < p + 2 ∧ pc' = 328) ∨ (p + 2 ≤ kmax N r p ∧ pc' = 148)) := by
  have hr := ctx.r_lt
  have hrN := ctx.r_le
  have hNb := ctx.hN
  have hp0 : 0 < p := by omega
  have hppN : p * p ≤ N := Nat.le_trans (Nat.mul_le_mul hpr hpr) ctx.hlo
  have hpNp : p ≤ N / p := (Nat.le_div_iff_mul_le hp0).mpr hppN
  have hL : Cell mem (8 * p + 512) (S p (N / p)) := hl p hpodd (Nat.le_refl p) hpr
  have hstep := S_prime_step p hprime hp5 N hpNp
  have hcL : S p (p - 1) ≤ S p (N / p) := S_mono p (by omega)
  have hval : S p N - (S p (N / p) - S p (p - 1)) = S (p + 1) N := by omega
  have hKp := kmax_mul_le (N := N) hp0 hpr ctx.hlo
  have e : (p + 2) * p = p * p + 2 * p := Nat.add_mul p 2 p
  have stage1 : ∃ n y, n ≤ 11 ∧
      run n ⟨x, 96, mem, [], out, .running⟩ = ⟨y, 140, mem, [], out, .running⟩ ∧
      SReg y N r (S (p + 1) N) p (S p (p - 1)) (kmax N r p) := by
    by_cases hsq : p * p ≤ r
    · obtain ⟨y, hrun, hfr, hy13, hy17, hy21, hy9⟩ := blk_prime_a x mem out (8 * p) (8 * r) p
        (S p (p - 1)) (S p N) (S p (N / p)) hlay.code_eq hreg.h14 hreg.h31 hreg.h13 hreg.h11
        (by omega) (by omega) (by omega) (by omega) hL hcL (by omega) (by omega)
      have hkm : kmax N r p = r := by simp [kmax, hsq]
      exact ⟨9, y, by omega, hrun,
        ⟨by rw [hfr 10 (by decide)]; exact hreg.h10, by rw [hfr 11 (by decide)]; exact hreg.h11,
         by rw [hfr 12 (by decide)]; exact hreg.h12, bv_of hy13 hval,
         by rw [hfr 14 (by decide)]; exact hreg.h14, by rw [hfr 31 (by decide)]; exact hreg.h31,
         bv_of hy17 (by omega), bv_of hy21 (by omega),
         bv_of hy9 (by rw [hkm, Nat.mul_assoc])⟩⟩
    · obtain ⟨y, hrun, hfr, hy13, hy17, hy21, hy9⟩ := blk_prime_b x mem out N (8 * p) (8 * r) p
        (S p (p - 1)) (S p N) (S p (N / p)) hlay.code_eq hreg.h10 hreg.h14 hreg.h31 hreg.h13
        hreg.h11 (by omega) (by omega) (by omega) (by omega) (by omega) (Nat.mul_pos hp0 hp0)
        hL hcL (by omega) (by omega)
      have hkm : kmax N r p = N / (p * p) := by simp [kmax, hsq]
      exact ⟨11, y, by omega, hrun,
        ⟨by rw [hfr 10 (by decide)]; exact hreg.h10, by rw [hfr 11 (by decide)]; exact hreg.h11,
         by rw [hfr 12 (by decide)]; exact hreg.h12, bv_of hy13 hval,
         by rw [hfr 14 (by decide)]; exact hreg.h14, by rw [hfr 31 (by decide)]; exact hreg.h31,
         bv_of hy17 (by omega), bv_of hy21 (by omega),
         bv_of hy9 (by rw [hkm, Nat.mul_left_comm])⟩⟩
  obtain ⟨n, y, hn, hrun1, hy⟩ := stage1
  by_cases hK : kmax N r p < p + 2
  · have hmul := (Nat.mul_lt_mul_right hp0).mpr hK
    obtain ⟨z, hrun2, hfr2, hz8⟩ := blk_140 y mem out (8 * (p * p)) (16 * p)
      (8 * (kmax N r p * p)) hlay.code_eq hy.h21 hy.h17 hy.h9 (by omega) (by omega) (by omega)
      328 (Or.inl ⟨by omega, rfl⟩)
    exact ⟨n + 2, z, 328, by omega, run_chain hrun1 hrun2, hy.frame hfr2 (by decide),
      bv_of hz8 (by omega), Or.inl ⟨hK, rfl⟩⟩
  · have hmul := Nat.mul_le_mul_right p (show p + 2 ≤ kmax N r p by omega)
    obtain ⟨z, hrun2, hfr2, hz8⟩ := blk_140 y mem out (8 * (p * p)) (16 * p)
      (8 * (kmax N r p * p)) hlay.code_eq hy.h21 hy.h17 hy.h9 (by omega) (by omega) (by omega)
      148 (Or.inr ⟨by omega, rfl⟩)
    exact ⟨n + 2, z, 148, by omega, run_chain hrun1 hrun2, hy.frame hfr2 (by decide),
      bv_of hz8 (by omega), Or.inr ⟨by omega, rfl⟩⟩

/-! ## The end of the program -/

private theorem toInt_nat (c : Nat) (hc : c < 2^63) :
    (BitVec.ofNat 64 c).toInt = (c : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have h64 : c < 2^64 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, show 2*c < 2^64 by omega]

private theorem nat_int_string (c : Nat) : toString (c : Int) = toString c := rfl

/-- Addresses 340 to 368: once the stage has passed `√N`, `large[1] + 2` is `π(N)`. -/
theorem finish (N P : Nat) (h3 : 3 ≤ N) (hN : N < 100000000000) (hP : N < P * P)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (hmem : Prefix image mem 380)
    (h13 : x.get 13 = bv (S P N)) :
    is_exited_with_output (run 8 ⟨x, 340, mem, [], out, .running⟩)
      (out ++ toString (countPrimes N) ++ "\n") := by
  obtain ⟨hst, hout⟩ := blk_final x mem out (S P N) hmem h13
  have hc := countPrimes_eq N P h3 hP
  have hle := countPrimes_le N
  refine ⟨hst, ?_⟩
  rw [hout, ← hc, toInt_nat _ (by omega), nat_int_string]

theorem OReg.next {x x' : Regs 64} {N r a p c p' c' : Nat} {W : List Reg}
    (h : OReg x N r a p c) (hfr : ∀ i : Reg, i ∉ W → x'.get i = x.get i)
    (hW : ∀ i ∈ ([10, 11, 12, 13] : List Reg), i ∉ W)
    (h14 : x'.get 14 = bv (8 * p')) (h31 : x'.get 31 = bv c') : OReg x' N r a p' c' :=
  ⟨by rw [hfr 10 (hW 10 (by decide))]; exact h.h10,
   by rw [hfr 11 (hW 11 (by decide))]; exact h.h11,
   by rw [hfr 12 (hW 12 (by decide))]; exact h.h12,
   by rw [hfr 13 (hW 13 (by decide))]; exact h.h13, h14, h31⟩

/-- The tail loop, addresses 308 to 336: once `N / (p*p) < p + 2`, a stage only changes
`large[1]`. -/
theorem tail_loop (N r cap : Nat) (ctx : Ctx N r cap) (p : Nat) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1)
    (hpr : p ≤ r) (ht1 : r < p * p) (ht2 : N / (p * p) < p + 2) (m : Nat) (hm : r + 2 - p ≤ 2 * m)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hreg : OReg x N r (S p N) p (S p (p - 1)))
    (hlay : Layout image 380 cap mem) (hs : Small mem r (S p))
    (hl : Large mem p r (fun j => S p (N / j))) :
    ∃ fuel, fuel ≤ 8 * m + 8 ∧
      is_exited_with_output (run fuel ⟨x, 308, mem, [], out, .running⟩)
        (out ++ toString (countPrimes N) ++ "\n") := by
  have hr := ctx.r_lt
  have hrN := ctx.r_le
  have hNb := ctx.hN
  have hrodd := ctx.hodd
  have hp0 : 0 < p := by omega
  have hppN : p * p ≤ N := Nat.le_trans (Nat.mul_le_mul hpr hpr) ctx.hlo
  have hpNp : p ≤ N / p := (Nat.le_div_iff_mul_le hp0).mpr hppN
  have ht : Cell mem (8 * p + 504) (S p p) := hs p hpodd hpr
  have hself := S_self p hp5
  have hc2 := S_next_c p hp5 hpodd
  have hSp : S p p ≤ p := S_le _ _
  have hSc : S p (p - 1) ≤ p - 1 := S_le _ _
  have hs2 : Small mem r (S (p + 2)) := by
    intro v hv hvr
    rw [S_add_two p (by omega) hpodd, S_small p (by omega) v (by omega)]
    exact hs v hv hvr
  have hl2 : Large mem (p + 2) r (fun j => S (p + 2) (N / j)) := by
    intro j hj hjlo hjr
    show Cell mem (8 * j + 512) (S (p + 2) (N / j))
    rw [S_add_two p (by omega) hpodd, S_small p (by omega) (N / j) (div_lt_sq hp0 (by omega))]
    exact hl j hj (by omega) hjr
  have ht1' : r < (p + 2) * (p + 2) :=
    Nat.lt_of_lt_of_le ht1 (Nat.mul_le_mul (by omega) (by omega))
  have ht2' := tail_next (N := N) hp0 ht2
  have hfinal : r < p + 2 → N < (p + 2) * (p + 2) := fun h =>
    Nat.lt_of_lt_of_le ctx.hhi (Nat.mul_le_mul (by omega) (by omega))
  by_cases hprime : Prime p
  · have hne : S p p ≠ S p (p - 1) := by rw [hself]; simp [hprime]
    obtain ⟨y1, hrun1, hfr1⟩ := blk_tail_test x mem out (8 * p) (S p (p - 1)) (S p p)
      hlay.code_eq hreg.h14 hreg.h31 (by omega) (by omega) (by omega) ht 316
      (Or.inr ⟨hne, rfl⟩)
    have hreg1 := hreg.frame hfr1 (by decide)
    have hL : Cell mem (8 * p + 512) (S p (N / p)) := hl p hpodd (Nat.le_refl p) hpr
    have hstep := S_prime_step p hprime hp5 N hpNp
    have hcL : S p (p - 1) ≤ S p (N / p) := S_mono p (by omega)
    obtain ⟨y2, hrun2, hfr2, hy13⟩ := blk_tail_prime y1 mem out (8 * p) (S p (p - 1)) (S p N)
      (S p (N / p)) hlay.code_eq hreg1.h14 hreg1.h31 hreg1.h13 (by omega) hL hcL (by omega)
    have hy13' : y2.get 13 = bv (S (p + 2) N) :=
      bv_of hy13 (by rw [S_add_two p (by omega) hpodd]; omega)
    have hc2' : S p (p - 1) + 1 = S (p + 2) (p + 2 - 1) := by
      rw [show p + 2 - 1 = p + 1 by omega, hc2]; simp [hprime]
    by_cases hnext : p + 2 ≤ r
    · obtain ⟨y3, hrun3, hfr3, hy14, hy31⟩ := blk_tail_inc y2 mem out (8 * p) (8 * r)
        (S p (p - 1)) hlay.code_eq (by rw [hfr2 14 (by decide)]; exact hreg1.h14)
        (by rw [hfr2 11 (by decide)]; exact hreg1.h11)
        (by rw [hfr2 31 (by decide)]; exact hreg1.h31) (by omega) (by omega) 308
        (Or.inl ⟨by omega, rfl⟩)
      have hreg3 : OReg y3 N r (S (p + 2) N) (p + 2) (S (p + 2) (p + 2 - 1)) :=
        ⟨by rw [hfr3 10 (by decide), hfr2 10 (by decide)]; exact hreg1.h10,
         by rw [hfr3 11 (by decide), hfr2 11 (by decide)]; exact hreg1.h11,
         by rw [hfr3 12 (by decide), hfr2 12 (by decide)]; exact hreg1.h12,
         by rw [hfr3 13 (by decide)]; exact hy13',
         bv_of hy14 (by omega), bv_of hy31 hc2'⟩
      obtain ⟨fuel, hfuel, hex⟩ := tail_loop N r cap ctx (p + 2) (by omega) (by omega) hnext
        ht1' ht2' (m - 1) (by omega) y3 mem out hreg3 hlay hs2 hl2
      exact ⟨2 + (3 + (3 + fuel)), by omega,
        exits_chain hrun1 (exits_chain hrun2 (exits_chain hrun3 hex))⟩
    · obtain ⟨y3, hrun3, hfr3, hy14, hy31⟩ := blk_tail_inc y2 mem out (8 * p) (8 * r)
        (S p (p - 1)) hlay.code_eq (by rw [hfr2 14 (by decide)]; exact hreg1.h14)
        (by rw [hfr2 11 (by decide)]; exact hreg1.h11)
        (by rw [hfr2 31 (by decide)]; exact hreg1.h31) (by omega) (by omega) 340
        (Or.inr ⟨by omega, rfl⟩)
      have hex := finish N (p + 2) ctx.h3 ctx.hN (hfinal (by omega)) y3 mem out hlay.code_eq
        (by rw [hfr3 13 (by decide)]; exact hy13')
      exact ⟨2 + (3 + (3 + 8)), by omega,
        exits_chain hrun1 (exits_chain hrun2 (exits_chain hrun3 hex))⟩
  · have heq : S p p = S p (p - 1) := by rw [hself]; simp [hprime]
    have hSN : S (p + 2) N = S p N := by
      rw [S_add_two p (by omega) hpodd, S_composite p (by omega) hprime]
    have hc2' : S p (p - 1) = S (p + 2) (p + 2 - 1) := by
      rw [show p + 2 - 1 = p + 1 by omega, hc2]; simp [hprime]
    by_cases hnext : p + 2 ≤ r
    · obtain ⟨y1, hrun1, hfr1⟩ := blk_tail_test x mem out (8 * p) (S p (p - 1)) (S p p)
        hlay.code_eq hreg.h14 hreg.h31 (by omega) (by omega) (by omega) ht 332
        (Or.inl ⟨heq, rfl⟩)
      have hreg1 := hreg.frame hfr1 (by decide)
      obtain ⟨y2, hrun2, hfr2, hy14⟩ := blk_tail_next y1 mem out (8 * p) (8 * r) hlay.code_eq
        hreg1.h14 hreg1.h11 (by omega) (by omega) 308 (Or.inl ⟨by omega, rfl⟩)
      have hreg2 : OReg y2 N r (S (p + 2) N) (p + 2) (S (p + 2) (p + 2 - 1)) := by
        rw [hSN, ← hc2']
        exact hreg1.next hfr2 (by decide) (bv_of hy14 (by omega))
          (by rw [hfr2 31 (by decide)]; exact hreg1.h31)
      obtain ⟨fuel, hfuel, hex⟩ := tail_loop N r cap ctx (p + 2) (by omega) (by omega) hnext
        ht1' ht2' (m - 1) (by omega) y2 mem out hreg2 hlay hs2 hl2
      exact ⟨2 + (2 + fuel), by omega, exits_chain hrun1 (exits_chain hrun2 hex)⟩
    · obtain ⟨y1, hrun1, hfr1⟩ := blk_tail_test x mem out (8 * p) (S p (p - 1)) (S p p)
        hlay.code_eq hreg.h14 hreg.h31 (by omega) (by omega) (by omega) ht 332
        (Or.inl ⟨heq, rfl⟩)
      have hreg1 := hreg.frame hfr1 (by decide)
      obtain ⟨y2, hrun2, hfr2, hy14⟩ := blk_tail_next y1 mem out (8 * p) (8 * r) hlay.code_eq
        hreg1.h14 hreg1.h11 (by omega) (by omega) 340 (Or.inr ⟨by omega, rfl⟩)
      have hex := finish N (p + 2) ctx.h3 ctx.hN (hfinal (by omega)) y2 mem out hlay.code_eq
        (by rw [hfr2 13 (by decide), hSN]; exact hreg1.h13)
      exact ⟨2 + (2 + 8), by omega, exits_chain hrun1 (exits_chain hrun2 hex)⟩
termination_by r + 2 - p
decreasing_by all_goals omega

/-! ## The outer loop -/

/-- The outer loop, from address 88: one stage for each odd `p` from 5 to `r`, with at most `W`
instructions a stage. -/
theorem outer_loop (N r cap : Nat) (ctx : Ctx N r cap) (W : Nat) (hW : 11 * r + 60 ≤ W)
    (p : Nat) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1) (hpr : p ≤ r) (m : Nat) (hm : r + 2 - p ≤ 2 * m)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hreg : OReg x N r (S p N) p (S p (p - 1)))
    (hlay : Layout image 380 cap mem) (hs : Small mem r (S p))
    (hl : Large mem p r (fun j => S p (N / j))) :
    ∃ fuel, fuel ≤ W * m + 9 ∧
      is_exited_with_output (run fuel ⟨x, 88, mem, [], out, .running⟩)
        (out ++ toString (countPrimes N) ++ "\n") := by
  have hr := ctx.r_lt
  have hrN := ctx.r_le
  have hNb := ctx.hN
  have hrodd := ctx.hodd
  have hp0 : 0 < p := by omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hWm : W * (m' + 1) = W * m' + W := Nat.mul_succ W m'
  have ht : Cell mem (8 * p + 504) (S p p) := hs p hpodd hpr
  have hself := S_self p hp5
  have hc2 := S_next_c p hp5 hpodd
  have hSp : S p p ≤ p := S_le _ _
  have hSc : S p (p - 1) ≤ p - 1 := S_le _ _
  have hfinal : r < p + 2 → N < (p + 2) * (p + 2) := fun h =>
    Nat.lt_of_lt_of_le ctx.hhi (Nat.mul_le_mul (by omega) (by omega))
  by_cases hprime : Prime p
  · have hne : S p p ≠ S p (p - 1) := by rw [hself]; simp [hprime]
    obtain ⟨y1, hrun1, hfr1⟩ := blk_test x mem out (8 * p) (S p (p - 1)) (S p p)
      hlay.code_eq hreg.h14 hreg.h31 (by omega) (by omega) (by omega) ht 96
      (Or.inr ⟨hne, rfl⟩)
    have hreg1 := hreg.frame hfr1 (by decide)
    obtain ⟨f2, y2, pc', hf2, hrun2, hreg2, h8, hcase⟩ :=
      prime_head N r cap p ctx hp5 hpodd hpr hprime y1 mem out hreg1 hlay hl
    have hc2' : S p (p - 1) + 1 = S (p + 2) (p + 2 - 1) := by
      rw [show p + 2 - 1 = p + 1 by omega, hc2]; simp [hprime]
    have hSN : S (p + 1) N = S (p + 2) N := (S_add_two p (by omega) hpodd N).symm
    rcases hcase with ⟨hK, rfl⟩ | ⟨hK, rfl⟩
    · -- the tail starts here
      obtain ⟨ht1, ht2⟩ := kmax_tail hp5 hK
      have hs2 : Small mem r (S (p + 2)) := by
        intro v hv hvr
        rw [S_add_two p (by omega) hpodd, S_small p (by omega) v (by omega)]
        exact hs v hv hvr
      have hl2 : Large mem (p + 2) r (fun j => S (p + 2) (N / j)) := by
        intro j hj hjlo hjr
        show Cell mem (8 * j + 512) (S (p + 2) (N / j))
        rw [S_add_two p (by omega) hpodd,
          S_small p (by omega) (N / j) (div_lt_sq hp0 (by omega))]
        exact hl j hj (by omega) hjr
      have ht1' : r < (p + 2) * (p + 2) :=
        Nat.lt_of_lt_of_le ht1 (Nat.mul_le_mul (by omega) (by omega))
      have ht2' := tail_next (N := N) hp0 ht2
      by_cases hnext : p + 2 ≤ r
      · obtain ⟨y3, hrun3, hfr3, hy14, hy31⟩ := blk_tail_inc y2 mem out (8 * p) (8 * r)
          (S p (p - 1)) hlay.code_eq hreg2.h14 hreg2.h11 hreg2.h31 (by omega) (by omega) 308
          (Or.inl ⟨by omega, rfl⟩)
        have hreg3 : OReg y3 N r (S (p + 2) N) (p + 2) (S (p + 2) (p + 2 - 1)) := by
          rw [← hSN]
          exact hreg2.toOReg.next hfr3 (by decide) (bv_of hy14 (by omega)) (bv_of hy31 hc2')
        obtain ⟨fuel, hfuel, hex⟩ := tail_loop N r cap ctx (p + 2) (by omega) (by omega) hnext
          ht1' ht2' m' (by omega) y3 mem out hreg3 hlay hs2 hl2
        have h8m : 8 * m' ≤ W * m' := Nat.mul_le_mul_right m' (by omega)
        exact ⟨2 + (f2 + (3 + fuel)), by omega,
          exits_chain hrun1 (exits_chain hrun2 (exits_chain hrun3 hex))⟩
      · obtain ⟨y3, hrun3, hfr3, hy14, hy31⟩ := blk_tail_inc y2 mem out (8 * p) (8 * r)
          (S p (p - 1)) hlay.code_eq hreg2.h14 hreg2.h11 hreg2.h31 (by omega) (by omega) 340
          (Or.inr ⟨by omega, rfl⟩)
        have hex := finish N (p + 2) ctx.h3 ctx.hN (hfinal (by omega)) y3 mem out hlay.code_eq
          (by rw [hfr3 13 (by decide), ← hSN]; exact hreg2.h13)
        exact ⟨2 + (f2 + (3 + 8)), by omega,
          exits_chain hrun1 (exits_chain hrun2 (exits_chain hrun3 hex))⟩
    · -- the table updates
      obtain ⟨f3, y3, mem3, hf3, hrun3, hreg3, hlay3, hs3, hl3⟩ :=
        stage_body N r cap p (S (p + 1) N) ctx hp5 hpodd hpr hprime hK y2 mem out hreg2 h8 hlay
          hs (fun j hj hjlo hjr => hl j hj (by omega) hjr)
      have hfun : S (p + 2) = S (p + 1) := funext (S_add_two p (by omega) hpodd)
      have hs4 : Small mem3 r (S (p + 2)) := by rw [hfun]; exact hs3
      have hl4 : Large mem3 (p + 2) r (fun j => S (p + 2) (N / j)) := by rw [hfun]; exact hl3
      by_cases hnext : p + 2 ≤ r
      · obtain ⟨y4, hrun4, hfr4, hy14, hy31⟩ := blk_inc y3 mem3 out (8 * p) (8 * r)
          (S p (p - 1)) hlay3.code_eq hreg3.h14 hreg3.h11 hreg3.h31 (by omega) (by omega) 3 88
          (Or.inl ⟨by omega, rfl, rfl⟩)
        have hreg4 : OReg y4 N r (S (p + 2) N) (p + 2) (S (p + 2) (p + 2 - 1)) := by
          rw [← hSN]
          exact hreg3.toOReg.next hfr4 (by decide) (bv_of hy14 (by omega)) (bv_of hy31 hc2')
        obtain ⟨fuel, hfuel, hex⟩ := outer_loop N r cap ctx W hW (p + 2) (by omega) (by omega)
          hnext m' (by omega) y4 mem3 out hreg4 hlay3 hs4 hl4
        exact ⟨2 + (f2 + (f3 + (3 + fuel))), by omega,
          exits_chain hrun1 (exits_chain hrun2 (exits_chain hrun3 (exits_chain hrun4 hex)))⟩
      · obtain ⟨y4, hrun4, hfr4, hy14, hy31⟩ := blk_inc y3 mem3 out (8 * p) (8 * r)
          (S p (p - 1)) hlay3.code_eq hreg3.h14 hreg3.h11 hreg3.h31 (by omega) (by omega) 4 340
          (Or.inr ⟨by omega, rfl, rfl⟩)
        have hex := finish N (p + 2) ctx.h3 ctx.hN (hfinal (by omega)) y4 mem3 out
          hlay3.code_eq (by rw [hfr4 13 (by decide), ← hSN]; exact hreg3.h13)
        exact ⟨2 + (f2 + (f3 + (4 + 8))), by omega,
          exits_chain hrun1 (exits_chain hrun2 (exits_chain hrun3 (exits_chain hrun4 hex)))⟩
  · have heq : S p p = S p (p - 1) := by rw [hself]; simp [hprime]
    have hfun : S (p + 2) = S p := funext fun v => by
      rw [S_add_two p (by omega) hpodd, S_composite p (by omega) hprime]
    have hc2' : S p (p - 1) = S (p + 2) (p + 2 - 1) := by
      rw [show p + 2 - 1 = p + 1 by omega, hc2]; simp [hprime]
    obtain ⟨y1, hrun1, hfr1⟩ := blk_test x mem out (8 * p) (S p (p - 1)) (S p p)
      hlay.code_eq hreg.h14 hreg.h31 (by omega) (by omega) (by omega) ht 296
      (Or.inl ⟨heq, rfl⟩)
    have hreg1 := hreg.frame hfr1 (by decide)
    by_cases hnext : p + 2 ≤ r
    · obtain ⟨y2, hrun2, hfr2, hy14⟩ := blk_next y1 mem out (8 * p) (8 * r) hlay.code_eq
        hreg1.h14 hreg1.h11 (by omega) (by omega) 2 88 (Or.inl ⟨by omega, rfl, rfl⟩)
      have hreg2 : OReg y2 N r (S (p + 2) N) (p + 2) (S (p + 2) (p + 2 - 1)) := by
        rw [← hc2', hfun]
        exact hreg1.next hfr2 (by decide) (bv_of hy14 (by omega))
          (by rw [hfr2 31 (by decide)]; exact hreg1.h31)
      have hs2 : Small mem r (S (p + 2)) := by rw [hfun]; exact hs
      have hl2 : Large mem (p + 2) r (fun j => S (p + 2) (N / j)) := by
        rw [hfun]
        exact fun j hj hjlo hjr => hl j hj (by omega) hjr
      obtain ⟨fuel, hfuel, hex⟩ := outer_loop N r cap ctx W hW (p + 2) (by omega) (by omega)
        hnext m' (by omega) y2 mem out hreg2 hlay hs2 hl2
      exact ⟨2 + (2 + fuel), by omega, exits_chain hrun1 (exits_chain hrun2 hex)⟩
    · obtain ⟨y2, hrun2, hfr2, hy14⟩ := blk_next y1 mem out (8 * p) (8 * r) hlay.code_eq
        hreg1.h14 hreg1.h11 (by omega) (by omega) 3 340 (Or.inr ⟨by omega, rfl, rfl⟩)
      have hex := finish N (p + 2) ctx.h3 ctx.hN (hfinal (by omega)) y2 mem out hlay.code_eq
        (by rw [hfr2 13 (by decide), hfun]; exact hreg1.h13)
      exact ⟨2 + (3 + 8), by omega, exits_chain hrun1 (exits_chain hrun2 hex)⟩
termination_by r + 2 - p
decreasing_by all_goals omega

/-! ## Initialization -/

/-- The initialization loop, addresses 24 to 60: for each odd `v` with `v * v ≤ N`, store the
stage-5 values of `small[(v-1)/2]` and `large[v]`. It ends with `r`, the largest such `v`. -/
theorem init_loop (N cap : Nat) (hN : N < 100000000000) (h3 : 3 ≤ N)
    (hcap : cap = 512 + 8 * (isqrt N + 1))
    (v : Nat) (hvodd : v % 2 = 1) (hv : v * v ≤ N)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (h10 : x.get 10 = bv N) (h5 : x.get 5 = bv v) (h6 : x.get 6 = bv (8 * (v - 1)))
    (h30 : x.get 30 = bv (N / v)) (h7 : x.get 7 = bv 3) (h22 : x.get 22 = bv 24)
    (hlay : Layout image 380 cap mem) (hs : Small mem (v - 2) (S 5))
    (hl : Large mem 1 (v - 2) (fun k => S 5 (N / k))) :
    ∃ fuel r x' mem', fuel + 5 * v ≤ 5 * (r + 2) ∧ Ctx N r cap ∧
      run fuel ⟨x, 24, mem, [], out, .running⟩ = ⟨x', 64, mem', [], out, .running⟩ ∧
      x'.get 10 = bv N ∧ x'.get 6 = bv (8 * (r + 1)) ∧
      Layout image 380 cap mem' ∧ Small mem' r (S 5) ∧
      Large mem' 1 r (fun k => S 5 (N / k)) := by
  have hvi := le_isqrt hv
  have hvN : v ≤ N := Nat.le_trans (Nat.le_mul_self v) hv
  have hq1 : v ≤ N / v := (Nat.le_div_iff_mul_le (by omega)).mpr hv
  have hqN := Nat.div_le_self N v
  have e1 : 8 * (v - 1) / 24 = S 5 v := by rw [S_init]; omega
  have e2 : (N / v - 1) / 2 * 2 / 3 = S 5 (N / v) := (S_init _).symm
  obtain ⟨mem1, hw1, hlay1, hcell1, hframe1⟩ :=
    store_cell hlay (8 * (v - 1) + 512) (8 * (v - 1) / 24) (by omega) (by omega)
  obtain ⟨mem2, hw2, hlay2, hcell2, hframe2⟩ :=
    store_cell hlay1 (8 * (v - 1) + 520) ((N / v - 1) / 2 * 2 / 3) (by omega) (by omega)
  have hs' : Small mem2 v (S 5) := by
    intro u hu huv
    by_cases he : u = v
    · subst he
      have := hframe2 _ _ (by omega) hcell1
      rw [e1] at this
      rw [show 8 * u + 504 = 8 * (u - 1) + 512 by omega]
      exact this
    · exact hframe2 _ _ (by omega) (hframe1 _ _ (by omega) (hs u hu (by omega)))
  have hl' : Large mem2 1 v (fun k => S 5 (N / k)) := by
    intro k hk hk1 hkv
    by_cases he : k = v
    · subst he
      show Cell mem2 (8 * k + 512) (S 5 (N / k))
      rw [← e2, show 8 * k + 512 = 8 * (k - 1) + 520 by omega]
      exact hcell2
    · exact hframe2 _ _ (by omega) (hframe1 _ _ (by omega) (hl k hk hk1 (by omega)))
  have hdiv := Nat.div_le_self N (v + 2)
  by_cases hcont : v + 2 ≤ N / (v + 2)
  · obtain ⟨y, hrun, hfr, hy6, hy5, hy30⟩ := blk_init_body x mem out N v (8 * (v - 1)) (N / v)
      mem1 mem2 hlay.code_eq hlay1.code_eq hlay2.code_eq h10 h5 h6 h30 h7 h22 (by omega)
      (by omega) (by omega) (by omega) (by omega) hw1 hw2 24 (Or.inl ⟨hcont, rfl⟩)
    have hv2 : (v + 2) * (v + 2) ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hcont
    obtain ⟨fuel, r, x', mem', hfuel, ctx, hrun', h10', h6', hlay', hs'', hl''⟩ :=
      init_loop N cap hN h3 hcap (v + 2) (by omega) hv2 y mem2 out
        (by rw [hfr 10 (by decide)]; exact h10) hy5 (bv_of hy6 (by omega)) hy30
        (by rw [hfr 7 (by decide)]; exact h7) (by rw [hfr 22 (by decide)]; exact h22) hlay2
        (by rw [show v + 2 - 2 = v by omega]; exact hs')
        (by rw [show v + 2 - 2 = v by omega]; exact hl')
    exact ⟨10 + fuel, r, x', mem', by omega, ctx, run_chain hrun hrun', h10', h6', hlay', hs'',
      hl''⟩
  · obtain ⟨y, hrun, hfr, hy6, hy5, hy30⟩ := blk_init_body x mem out N v (8 * (v - 1)) (N / v)
      mem1 mem2 hlay.code_eq hlay1.code_eq hlay2.code_eq h10 h5 h6 h30 h7 h22 (by omega)
      (by omega) (by omega) (by omega) (by omega) hw1 hw2 64 (Or.inr ⟨by omega, rfl⟩)
    have hhi : N < (v + 2) * (v + 2) := (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
    exact ⟨10, v, y, mem2, by omega, ⟨hN, h3, hvodd, hv, hhi, by omega⟩, hrun,
      by rw [hfr 10 (by decide)]; exact h10, bv_of hy6 (by omega), hlay2, hs', hl'⟩
termination_by N - v
decreasing_by omega

/-! ## The program -/

theorem initial_layout (n : Nat) :
    Layout image 380 (512 + 8 * (isqrt n + 1)) (initial n).mem :=
  load_layout_boundary 64 prog 380 512 (512 + 8 * (isqrt n + 1)) [] []
    (by decide) (by decide) (by omega)

/-- **Correctness with an instruction budget.** For every input below `10^11`, the loaded RV64
program exits with code zero after printing `π(n)` and a newline, within `26 + 41 * n` modeled
instructions. -/
theorem correct (n : Nat) (hn : n < 10^11) :
    ∃ fuel, fuel ≤ 26 + 41 * n ∧
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n") := by
  have hlay := initial_layout n
  generalize hcapdef : 512 + 8 * (isqrt n + 1) = cap at hlay
  let x0 : Regs 64 := (⟨Vector.replicate 32 0⟩ : Regs 64).set 10 (bv n)
  have hi : initial n = ⟨x0, 0, (initial n).mem, [], "", .running⟩ := rfl
  have h10 : x0.get 10 = bv n := by simp [x0, Regs.get_set]
  rw [hi]
  generalize (initial n).mem = mem0 at hlay
  by_cases h3 : n < 3
  · obtain ⟨hst, hout⟩ := blk_small x0 mem0 "" n hlay.code_eq h10 h3
    have hc : countPrimes n = n / 2 := by
      have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases this with rfl | rfl | rfl <;> decide
    refine ⟨11, by omega, hst, ?_⟩
    rw [hout, toInt_nat _ (by omega), nat_int_string, hc, String.empty_append]
  · obtain ⟨x1, hrun1, h10', h7, h22, h5, h6, h30⟩ := blk_init x0 mem0 "" n hlay.code_eq h10
      (by omega) (by omega)
    obtain ⟨f2, r, x2, mem2, hf2, ctx, hrun2, h10'', h6'', hlay2, hs2, hl2⟩ :=
      init_loop n cap (by omega) (by omega) hcapdef.symm 1 (by decide) (by omega) x1 mem0 ""
        h10' h5 h6 (by rw [Nat.div_one]; exact h30) h7 h22 hlay
        (fun v hv hvr => by omega) (fun k hk hk1 hkr => by omega)
    have hr := ctx.r_lt
    have hrN := ctx.r_le
    have hrodd := ctx.hodd
    have ha : Cell mem2 520 (S 5 n) := by
      have := hl2 1 (by decide) (Nat.le_refl 1) (by omega)
      simpa using this
    by_cases hr5 : r < 5
    · obtain ⟨x3, hrun3, hfr3, _, _, h13, _, _⟩ := blk_post_init x2 mem2 "" n (8 * (r + 1))
        (S 5 n) hlay2.code_eq h10'' h6'' (by omega) (by omega) (by omega) ha 340
        (Or.inl ⟨by omega, rfl⟩)
      have hP : n < 5 * 5 :=
        Nat.lt_of_lt_of_le ctx.hhi (Nat.mul_le_mul (by omega) (by omega))
      have hex := finish n 5 ctx.h3 ctx.hN hP x3 mem2 "" hlay2.code_eq h13
      refine ⟨6 + (f2 + (6 + 8)), by omega, ?_⟩
      have := exits_chain hrun1 (exits_chain hrun2 (exits_chain hrun3 hex))
      simpa using this
    · obtain ⟨x3, hrun3, hfr3, h11, h12, h13, h14, h31⟩ := blk_post_init x2 mem2 "" n
        (8 * (r + 1)) (S 5 n) hlay2.code_eq h10'' h6'' (by omega) (by omega) (by omega) ha 88
        (Or.inr ⟨by omega, rfl⟩)
      have hreg : OReg x3 n r (S 5 n) 5 (S 5 (5 - 1)) :=
        ⟨by rw [hfr3 10 (by decide)]; exact h10'', bv_of h11 (by omega), bv_of h12 (by omega),
         h13, h14, bv_of h31 (by rw [S_init])⟩
      obtain ⟨f4, hf4, hex⟩ := outer_loop n r cap ctx (11 * r + 60) (Nat.le_refl _) 5
        (by omega) (by decide) (by omega) (r / 2) (by omega) x3 mem2 "" hreg hlay2 hs2
        (fun j hj hjlo hjr => hl2 j hj (by omega) hjr)
      have hX : (11 * r + 60) * (r / 2) * 2 ≤ 11 * (r * r) + 60 * r := by
        have h1 : (11 * r + 60) * r = 11 * (r * r) + 60 * r := by
          rw [Nat.add_mul, Nat.mul_assoc]
        have h2 := Nat.mul_le_mul_left (11 * r + 60) (Nat.div_mul_le_self r 2)
        rw [Nat.mul_assoc]
        omega
      have hrr := ctx.hlo
      refine ⟨6 + (f2 + (6 + f4)), by omega, ?_⟩
      have := exits_chain hrun1 (exits_chain hrun2 (exits_chain hrun3 hex))
      simpa using this

/-- One fuel value works for every input below `10^11`. -/
theorem correct_uniform_fuel :
    ∃ fuel, ∀ n < 10^11,
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n") := by
  refine ⟨26 + 41 * 10^11, fun n hn => ?_⟩
  obtain ⟨fuel, hb, h⟩ := correct n hn
  exact is_exited_with_output_mono (by omega) h

/-- `initial'` meets the specification. -/
theorem isCorrect : IsCorrect initial' :=
  isCorrect_of_load prog (fun n => 512 + 8 * (isqrt n + 1)) (512 + 8*316228)
    (fun _ _ => by have : 4 * prog.length ≤ 512 := (by decide); omega)
    (fun n hn => by have := r_lt_of_sq (isqrt_spec n).1 hn; omega)
    correct_uniform_fuel

/-- `initial'` holds 344 nonzero bytes. Zero padding is free, so the size bound rules out
lookup tables. -/
theorem programSize_eq : programSize initial' = 344 := by
  rw [initial', programSize_load prog 512 (512 + 8*316228) (by decide) (by omega)]
  decide +kernel

end TinyFive.CountingPrimesLucy
