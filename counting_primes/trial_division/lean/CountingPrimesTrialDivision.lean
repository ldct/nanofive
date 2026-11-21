import TinyFive.Machine
import TinyFive.Primes
import TinyFive.TrialDivisionCost
import CountingPrimesLoad
import TrialDivisionProgram

/-!
# Correctness proof of `TrialDivisionProgram`

The exact RV64I instruction words implement trial division by repeated subtraction. The proof
composes symbolic execution blocks using `TinyFive.run_add` from `Machine`, then uses decreasing
natural-number measures for subtraction, divisor search, and candidate search.

`correct_bounded` gives the budget `11 + (n-1)*(6 + scanCost n 2 (n-2))`, where the scan sums
`6 + 3*(n/d)` over the possible divisors. Thirty-six dyadic blocks bound the quotient sum by
`36*n` below `10^11 < 2^37`, which gives `correct`'s `11 + 114*n*n`.
-/
namespace TinyFive.CountingPrimesTrialDivision

open CountingPrimes TrialDivisionCost

/-- Machine state with `prog` loaded. -/
def initial (n : Nat) : Machine 64 :=
  (load 64 prog 128 []).setReg 10 (BitVec.ofNat 64 n)

def image : Array (BitVec 8) := (load 64 prog 128 []).mem

def code : List Instr := [
  .opImm .add 5 0 2, .opImm .add 6 0 0,
  .branch .bltu 10 5 52, .opImm .add 7 0 2,
  .branch .beq 7 5 32, .opImm .add 28 5 0,
  .branch .bltu 28 7 12, .op .sub 28 28 7, .jal 0 (-8),
  .branch .beq 28 0 16, .opImm .add 7 7 1, .jal 0 (-28),
  .opImm .add 6 6 1, .opImm .add 5 5 1, .jal 0 (-48),
  .opImm .add 10 6 0, .opImm .add 17 0 1, .ecall,
  .opImm .add 10 0 10, .opImm .add 17 0 11, .ecall,
  .opImm .add 17 0 10, .ecall]

/-- Decoding is checked by kernel evaluation at every instruction address. -/
theorem fetch : ∀ pc, pc < 92 → pc % 4 = 0 →
    (readBytes image pc 4).bind (decode 64) = some (code.getD (pc / 4) .ecall) := by
  decide +kernel

theorem step_image (x : Regs 64) (pc : BitVec 64) (out : String) (st : Status)
    (h : pc.toNat < 92) (h4 : pc.toNat % 4 = 0) :
    step ⟨x, pc, image, [], out, st⟩ =
      exec (code.getD (pc.toNat / 4) .ecall) ⟨x, pc, image, [], out, st⟩ := by
  simp only [step, fetch _ h h4]

macro "prime_exec" : tactic =>
  `(tactic| simp [run, step_image, code, exec, Machine.setReg, Machine.advance,
      Machine.fail, alu, ecall, Regs.get_set, BranchOp.taken, *])

/-- The three registers live throughout the nested loops. -/
def Inv (x : Regs 64) (n k c : Nat) : Prop :=
  x.get 10 = BitVec.ofNat 64 n ∧
  x.get 5 = BitVec.ofNat 64 k ∧
  x.get 6 = BitVec.ofNat 64 c

private theorem rem_less (x : Regs 64) (out : String)
    (h : (x.get 28).ult (x.get 7) = true) :
    run 1 ⟨x, 24, image, [], out, .running⟩ =
      ⟨x, 36, image, [], out, .running⟩ := by
  prime_exec

private theorem rem_sub (x : Regs 64) (out : String)
    (h : (x.get 28).ult (x.get 7) = false) :
    ∃ x' : Regs 64, x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 ∧
      x'.get 6 = x.get 6 ∧ x'.get 7 = x.get 7 ∧
      x'.get 28 = x.get 28 - x.get 7 ∧
      run 3 ⟨x, 24, image, [], out, .running⟩ =
        ⟨x', 24, image, [], out, .running⟩ := by
  refine ⟨(x.set 28 (x.get 28 - x.get 7)).set 0 36, ?_⟩
  prime_exec

private theorem trial_start (x : Regs 64) (out : String)
    (h : x.get 7 ≠ x.get 5) :
    ∃ x' : Regs 64, x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 ∧
      x'.get 6 = x.get 6 ∧ x'.get 7 = x.get 7 ∧ x'.get 28 = x.get 5 ∧
      run 2 ⟨x, 16, image, [], out, .running⟩ =
        ⟨x', 24, image, [], out, .running⟩ := by
  refine ⟨x.set 28 (x.get 5), ?_⟩
  prime_exec

private theorem trial_zero (x : Regs 64) (out : String) (h : x.get 28 = 0) :
    run 1 ⟨x, 36, image, [], out, .running⟩ =
      ⟨x, 52, image, [], out, .running⟩ := by
  prime_exec

private theorem trial_nonzero (x : Regs 64) (out : String) (h : x.get 28 ≠ 0#64) :
    ∃ x' : Regs 64, x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 ∧
      x'.get 6 = x.get 6 ∧ x'.get 7 = x.get 7 + 1 ∧
      run 3 ⟨x, 36, image, [], out, .running⟩ =
        ⟨x', 16, image, [], out, .running⟩ := by
  refine ⟨(x.set 7 (x.get 7 + 1)).set 0 48, ?_⟩
  prime_exec

private theorem trial_prime (x : Regs 64) (out : String) (h : x.get 7 = x.get 5) :
    ∃ x' : Regs 64, x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 ∧
      x'.get 6 = x.get 6 + 1 ∧
      run 2 ⟨x, 16, image, [], out, .running⟩ =
        ⟨x', 52, image, [], out, .running⟩ := by
  refine ⟨x.set 6 (x.get 6 + 1), ?_⟩
  prime_exec

private theorem outer_start (x : Regs 64) (out : String)
    (h : (x.get 10).ult (x.get 5) = false) :
    ∃ x' : Regs 64, x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 ∧
      x'.get 6 = x.get 6 ∧ x'.get 7 = 2 ∧
      run 2 ⟨x, 8, image, [], out, .running⟩ =
        ⟨x', 16, image, [], out, .running⟩ := by
  refine ⟨x.set 7 2, ?_⟩
  prime_exec

private theorem outer_next (x : Regs 64) (out : String) :
    ∃ x' : Regs 64, x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 + 1 ∧
      x'.get 6 = x.get 6 ∧
      run 2 ⟨x, 52, image, [], out, .running⟩ =
        ⟨x', 8, image, [], out, .running⟩ := by
  refine ⟨(x.set 5 (x.get 5 + 1)).set 0 60, ?_⟩
  prime_exec

private theorem outer_done (x : Regs 64) (out : String)
    (h : (x.get 10).ult (x.get 5) = true) :
    (run 9 ⟨x, 8, image, [], out, .running⟩).status = .exited 0 ∧
    (run 9 ⟨x, 8, image, [], out, .running⟩).output =
      out ++ toString (x.get 6).toInt ++ "\n" := by
  prime_exec
  rfl

/-- Unsigned arithmetic agrees with natural subtraction when there is no underflow. -/
private theorem nat_sub (r d : Nat) (hr : r < 2^64) (hd : d ≤ r) :
    BitVec.ofNat 64 r - BitVec.ofNat 64 d = BitVec.ofNat 64 (r - d) := by
  apply BitVec.eq_of_toNat_eq
  grind [BitVec.toNat_ofNat]

private theorem nat_ult (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  grind [BitVec.ult]

private theorem nat_ne (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) (hne : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  grind [BitVec.toNat_ofNat]

/-- The subtraction loop terminates with the mathematical remainder in `t3`.
The live input, candidate, count, and divisor registers are preserved. -/
private theorem rem_correct (r d : Nat) (hd : 0 < d) (hd64 : d < 2^64)
    (x : Regs 64) (out : String) (hr : r < 2^64)
    (hxr : x.get 28 = BitVec.ofNat 64 r) (hxd : x.get 7 = BitVec.ofNat 64 d) :
    ∃ fuel x', fuel = 1+3*(r/d) ∧
      x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 ∧
      x'.get 6 = x.get 6 ∧ x'.get 7 = x.get 7 ∧
      x'.get 28 = BitVec.ofNat 64 (r % d) ∧
      run fuel ⟨x, 24, image, [], out, .running⟩ =
        ⟨x', 36, image, [], out, .running⟩ := by
  induction r using Nat.strongRecOn generalizing x with
  | ind r ih =>
    by_cases hlt : r < d
    · refine ⟨1, x, by simp [Nat.div_eq_of_lt hlt], rfl, rfl, rfl, rfl, ?_, ?_⟩
      · simpa [Nat.mod_eq_of_lt hlt] using hxr
      · apply rem_less
        rw [hxr, hxd, nat_ult r d hr hd64]
        simp [hlt]
    · have hge : d ≤ r := by grind
      have hbranch : (x.get 28).ult (x.get 7) = false := by
        rw [hxr, hxd, nat_ult r d hr hd64]
        simp [hlt]
      obtain ⟨x', h10, h5, h6, h7, h28, hs⟩ := rem_sub x out hbranch
      have hxr' : x'.get 28 = BitVec.ofNat 64 (r-d) := by
        rw [h28, hxr, hxd, nat_sub r d hr hge]
      obtain ⟨fuel, x'', hfuel, g10, g5, g6, g7, g28, ht⟩ :=
        ih (r-d) (by omega) x' (by omega) hxr' (h7.trans hxd)
      refine ⟨3 + fuel, x'', ?_, g10.trans h10, g5.trans h5, g6.trans h6,
        g7.trans h7, ?_, ?_⟩
      · grind [Nat.div_eq_sub_div hd hge]
      · grind [Nat.mod_eq_sub_mod]
      · rw [run_add, hs, ht]

/-- Divisors below `d` have already been rejected. -/
private def NoDivisor (k d : Nat) : Prop :=
  ∀ e, 2 ≤ e → e < d → k % e ≠ 0

/-- The complete divisor scan terminates at the candidate-update block. It increments
`t1` exactly when the mathematical candidate is prime. -/
private theorem trial_correct (k d : Nat) (hk : 2 ≤ k) (hk64 : k < 2^64)
    (hd : 2 ≤ d) (hdk : d ≤ k) (hnodiv : NoDivisor k d)
    (n c : Nat) (x : Regs 64) (out : String) (hinv : Inv x n k c)
    (hxd : x.get 7 = BitVec.ofNat 64 d) :
    ∃ fuel x', fuel ≤ 2+scanCost k d (k-d) ∧
      Inv x' n k (c + if Prime k then 1 else 0) ∧
      run fuel ⟨x, 16, image, [], out, .running⟩ =
        ⟨x', 52, image, [], out, .running⟩ := by
  by_cases heq : d = k
  · have hp : Prime k := (prime_iff k).mpr ⟨hk, by simpa [heq, NoDivisor] using hnodiv⟩
    have hreg : x.get 7 = x.get 5 := by rw [hxd, hinv.2.1, heq]
    obtain ⟨x', h10, h5, h6, hs⟩ := trial_prime x out hreg
    refine ⟨2, x', by simp [heq], ?_, hs⟩
    refine ⟨h10.trans hinv.1, h5.trans hinv.2.1, ?_⟩
    rw [h6, hinv.2.2]
    simp [hp, BitVec.ofNat_add]
  · have hlt : d < k := by omega
    have hreg : x.get 7 ≠ x.get 5 := by
      rw [hxd, hinv.2.1]
      exact nat_ne d k (by omega) hk64 heq
    obtain ⟨x', h10, h5, h6, h7, h28, hs⟩ := trial_start x out hreg
    obtain ⟨fuel, x'', hfuel, g10, g5, g6, g7, g28, ht⟩ :=
      rem_correct k d (by omega) (by omega) x' out hk64
        (h28.trans hinv.2.1) (h7.trans hxd)
    have hi : Inv x'' n k c :=
      ⟨g10.trans (h10.trans hinv.1), g5.trans (h5.trans hinv.2.1),
        g6.trans (h6.trans hinv.2.2)⟩
    have hdreg : x''.get 7 = BitVec.ofNat 64 d := g7.trans (h7.trans hxd)
    by_cases hz : k % d = 0
    · have hnp : ¬ Prime k := by
        intro hp
        exact (prime_iff k).mp hp |>.2 d hd hlt hz
      have hzreg : x''.get 28 = 0 := by simpa [hz] using g28
      have hscan : scanCost k d (k-d) = 6+3*(k/d)+scanCost k (d+1) (k-(d+1)) := by
        rw [show k-d = (k-(d+1))+1 by omega, scanCost_succ]
      refine ⟨2 + fuel + 1, x'', ?_, ?_, ?_⟩
      · rw [hscan]
        omega
      · simpa [hnp] using hi
      · rw [run_add, run_add, hs, ht, trial_zero x'' out hzreg]
    · have hnzreg : x''.get 28 ≠ 0#64 := by
        rw [g28]
        exact nat_ne (k%d) 0 (by have := Nat.mod_lt k (show 0 < d by omega); omega)
          (by decide) hz
      obtain ⟨y, j10, j5, j6, j7, hu⟩ := trial_nonzero x'' out hnzreg
      have hj : Inv y n k c := ⟨j10.trans hi.1, j5.trans hi.2.1, j6.trans hi.2.2⟩
      have hjd : y.get 7 = BitVec.ofNat 64 (d+1) := by
        rw [j7, hdreg, BitVec.ofNat_add]
        rfl
      have hnodiv' : NoDivisor k (d+1) := by
        intro e he hed
        by_cases hed' : e < d
        · exact hnodiv e he hed'
        · have : e = d := by omega
          simpa [this] using hz
      obtain ⟨more, z, hmore, hz, hv⟩ :=
        trial_correct k (d+1) hk hk64 (by omega) (by omega) hnodiv' n c y out hj hjd
      have hscan : scanCost k d (k-d) = 6+3*(k/d)+scanCost k (d+1) (k-(d+1)) := by
        rw [show k-d = (k-(d+1))+1 by omega, scanCost_succ]
      refine ⟨2 + fuel + 3 + more, z, ?_, hz, ?_⟩
      · rw [hscan]
        omega
      · rw [run_add, run_add, run_add, hs, ht, hu, hv]
termination_by k-d

private theorem toInt_nat (c : Nat) (hc : c < 2^63) :
    (BitVec.ofNat 64 c).toInt = (c : Int) := by
  grind [BitVec.toInt_eq_toNat_cond]

private theorem nat_int_string (c : Nat) : toString (c : Int) = toString c := rfl

private theorem countPrimes_step (k : Nat) (hk : 0 < k) :
    countPrimes k = countPrimes (k-1) + if Prime k then 1 else 0 := by
  cases k with
  | zero => omega
  | succ k => rfl

/-- From the outer loop, `t1` counts exactly the primes below `t0`. The variant
`n+1-k` decreases on each candidate, and every nested scan terminates. -/
private theorem outer_correct (n k : Nat) (hn : n < 10^11) (hk : 2 ≤ k)
    (hkn : k ≤ n+1) (x : Regs 64) (out : String)
    (hinv : Inv x n k (countPrimes (k-1))) :
    ∃ fuel, fuel ≤ 9+(n+1-k)*(6+scanCost n 2 (n-2)) ∧
      (run fuel ⟨x, 8, image, [], out, .running⟩).status = .exited 0 ∧
      (run fuel ⟨x, 8, image, [], out, .running⟩).output =
        out ++ toString (countPrimes n) ++ "\n" := by
  have hn64 : n < 2^64 := by omega
  have hk64 : k < 2^64 := by omega
  by_cases hdone : n < k
  · have he : k-1 = n := by omega
    have hbranch : (x.get 10).ult (x.get 5) = true := by
      grind [hinv.1, hinv.2, nat_ult]
    have hc : countPrimes n < 2^63 := by have := countPrimes_le n; omega
    refine ⟨9, by omega, ?_⟩
    grind only [hinv.2, toInt_nat, nat_int_string, outer_done x out hbranch]
  · have hnk : k ≤ n := by omega
    have hbranch : (x.get 10).ult (x.get 5) = false := by
      grind [hinv.1, hinv.2.1, nat_ult n k hn64 hk64]
    obtain ⟨x', h10, h5, h6, h7, hs⟩ := outer_start x out hbranch
    have hi : Inv x' n k (countPrimes (k-1)) :=
      ⟨h10.trans hinv.1, h5.trans hinv.2.1, h6.trans hinv.2.2⟩
    have hnodiv : NoDivisor k 2 := by intro e he he2; omega
    obtain ⟨fuel, y, hfuel, hy, ht⟩ :=
      trial_correct k 2 hk hk64 (by decide) (by omega) hnodiv n
        (countPrimes (k-1)) x' out hi h7
    have hcount := countPrimes_step k (by omega)
    have hy' : Inv y n k (countPrimes k) := by simpa [← hcount] using hy
    obtain ⟨z, j10, j5, j6, hu⟩ := outer_next y out
    have hj : Inv z n (k+1) (countPrimes ((k+1)-1)) := by
      refine ⟨j10.trans hy'.1, ?_, ?_⟩ <;> grind [hy'.2, BitVec.ofNat_add]
    obtain ⟨more, hmore, hm⟩ := outer_correct n (k+1) hn (by omega) (by omega) z out hj
    have hscan : scanCost k 2 (k-2) ≤ scanCost n 2 (n-2) := by
      refine Nat.le_trans (scanCost_mono_n k n 2 (k-2) hnk) ?_
      exact (scanCost_mono_len n 2 (k-2) (n-2) (by grind))
    refine ⟨2 + fuel + 2 + more, ?_, ?_⟩
    · have he : n+1-k = (n+1-(k+1))+1 := by grind
      grind [ Nat.add_mul]
    · rwa [run_add, run_add, run_add, hs, ht, hu]
termination_by n+1-k

/-- Initialize the candidate and count without changing the preloaded input. -/
private theorem initialize_regs (n : Nat) :
    ∃ x, Inv x n 2 0 ∧ run 2 (initial n) =
      ⟨x, 8, image, [], "", .running⟩ := by
  let x : Regs 64 := (⟨Vector.replicate 32 0⟩ : Regs 64).set 10 (BitVec.ofNat 64 n)
  have hi : initial n = ⟨x, 0, image, [], "", .running⟩ := rfl
  rw [hi]
  refine ⟨(x.set 5 2).set 6 0, ?_, ?_⟩
  · simp [Inv, x, Regs.get_set]
  · prime_exec


/-- The loaded instruction words exit with code zero after printing `π(n)` and a newline,
within the input-dependent budget `instructionBound n`. No fuel or termination hypothesis is
assumed. -/
theorem correct_bounded (n : Nat) (hn : n < 10^11) :
    ∃ fuel, fuel ≤ instructionBound n ∧
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n") := by
  obtain ⟨x, hx, hs⟩ := initialize_regs n
  by_cases hsmall : n < 2
  · have hc : countPrimes n = 0 := by
      have : n = 0 ∨ n = 1 := by omega
      obtain rfl | rfl := this <;> simp
    have hbranch : (x.get 10).ult (x.get 5) = true := by
      rw [hx.1, hx.2.1, nat_ult n 2 (by omega) (by decide)]
      simp [hsmall]
    refine ⟨2 + 9, by unfold instructionBound; omega, ?_⟩
    rw [run_add, hs]
    simpa only [hx.2.2, hc, toInt_nat 0 (by decide), nat_int_string, String.empty_append]
      using outer_done x "" hbranch
  · have hi : Inv x n 2 (countPrimes (2-1)) := by simpa using hx
    obtain ⟨fuel, hbound, hf⟩ := outer_correct n 2 hn (by decide) (by omega) x "" hi
    refine ⟨2 + fuel, ?_, ?_⟩
    · unfold instructionBound
      have he : n+1-2 = n-1 := by omega
      rw [he] at hbound
      omega
    · rw [run_add, hs]
      simpa using hf

/-- **Correctness with an instruction budget.** For every input below `10^11`, the loaded
RV64I program exits with code zero after printing `π(n)` and a newline, within
`11 + 114*n*n` modeled instructions. -/
theorem correct (n : Nat) (hn : n < 10^11) :
    ∃ fuel, fuel ≤ 11+114*n*n ∧
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n") := by
  obtain ⟨fuel, hb, h⟩ := correct_bounded n hn
  exact ⟨fuel, Nat.le_trans hb (instructionBound_le n hn), h⟩

/-- A logarithmic-block bound, tighter than `correct`'s for small inputs. -/
theorem correct_dyadic_bound (n k : Nat) (hn : n < 10^11) (hk : n < 2^(k+1)) :
    ∃ fuel, fuel ≤ 11+(n-1)*(6+6*(n-2)+3*k*n) ∧
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n") := by
  obtain ⟨fuel, hb, h⟩ := correct_bounded n hn
  exact ⟨fuel, Nat.le_trans hb (instructionBound_dyadic n k hk), h⟩

/-- One fuel value works for every input below `10^11`. -/
theorem correct_uniform_fuel :
    ∃ fuel, ∀ n < 10^11,
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n") := by
  refine ⟨11+114*10^11*10^11, fun n hn => ?_⟩
  obtain ⟨fuel, hb, h⟩ := correct n hn
  have := Nat.mul_le_mul (Nat.mul_le_mul_left 114 (Nat.le_of_lt hn)) (Nat.le_of_lt hn)
  exact is_exited_with_output_mono (by omega) h

/-- `initial'` meets the specification. -/
theorem isCorrect : IsCorrect initial' :=
  isCorrect_of_load prog (fun _ => 128) 128
    (fun _ _ => by decide)
    (fun _ _ => Nat.le_refl _)
    correct_uniform_fuel

/-- `initial'` holds 68 nonzero bytes. Zero padding is free, so the size bound rules out
lookup tables. -/
theorem programSize_eq : programSize initial' = 68 := by
  rw [initial', programSize_load prog 128 128 (by decide) (by omega)]
  decide +kernel

end TinyFive.CountingPrimesTrialDivision
