import TinyFive.Machine
import TinyFive.Primes
import TinyFive.TrialDivisionCost

/-!
# Correctness of `counting_primes_simple.py`

The exact RV32I instruction words below implement trial division by repeated subtraction.
`correct` connects the loaded machine, not a separate interpreter, to the prime-counting
specification. Inputs are preloaded in `a0`, as by the Python wrapper.

## Statement and boundary

`correct` proves termination, exit code zero, and exact decimal output followed by a newline,
for every natural input `n ≤ 2^31-2` (including zero and one). `prime_iff_no_proper_divisor`
identifies the prime predicate with conventional natural-number divisibility. This proof is
RV32 only; the bound keeps the incremented candidate and signed printed count in range.

The instruction bytes, decoding, arithmetic, branches, and modeled system calls are all covered
by the proof. The boundary is the semantics of `TinyFive.Machine`: equivalence of that model
with the Python emulator, equality of this `prog` with the Python program's instruction list,
and the wrapper's input parsing/preloading are checked separately, not proved here.

The proof composes symbolic execution blocks using `TinyFive.run_add` from `Machine`, then
uses decreasing natural-number measures for subtraction, divisor search, and candidate search.
No execution-fuel assumption is required.

## Instruction bound

`correct_bounded` strengthens the same machine execution with budget
`11 + (n-1)*(6 + scanCost n 2 (n-2))`, where the scan sums
`6 + 3*(n/d)` over the possible divisors. Thirty dyadic blocks bound the
quotient sum by `30*n` on the full input domain. Consequently
`correct_quadratic_bound` gives `11 + (n-1)*(6 + 96*n)`, and
`correct_numeric_bound` gives a uniform cap of `442721856751121990201 < 2^69`.
Natural subtraction is truncated, so the formulas also cover zero and one.

The unit is one modeled RV32 instruction, including each `ecall` as one
instruction. Host input parsing, allocation/loading, emulator overhead, and
the host work performed by printing are not included. The budgets are upper
bounds, not claims of exact or minimal running time.
-/
namespace TinyFive.CountingPrimes

open TrialDivisionCost

/-- Exact instruction words used by the Python program. -/
def prog : List (BitVec 32) := [
  0x00200293, 0x00000313, 0x02556a63, 0x00200393, 0x02538063,
  0x00028e13, 0x007e6663, 0x407e0e33, 0xff9ff06f, 0x000e0863,
  0x00138393, 0xfe5ff06f, 0x00130313, 0x00128293, 0xfd1ff06f,
  0x00030513, 0x00100893, 0x00000073, 0x00a00513, 0x00b00893,
  0x00000073, 0x00a00893, 0x00000073]

/-- State after the wrapper has preloaded the nonnegative input. -/
def initial (n : Nat) : Machine 32 :=
  (load 32 prog 128 []).setReg 10 (BitVec.ofNat 32 n)

def image : Array (BitVec 8) := (load 32 prog 128 []).mem

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
    (readBytes image pc 4).bind (decode 32) = some (code.getD (pc / 4) .ecall) := by
  decide +kernel

theorem step_image (x : Regs 32) (pc : BitVec 32) (out : String) (st : Status)
    (h : pc.toNat < 92) (h4 : pc.toNat % 4 = 0) :
    step ⟨x, pc, image, [], out, st⟩ =
      exec (code.getD (pc.toNat / 4) .ecall) ⟨x, pc, image, [], out, st⟩ := by
  simp only [step, fetch _ h h4]

macro "prime_exec" : tactic =>
  `(tactic| simp [run, step_image, code, exec, Machine.setReg, Machine.advance,
      Machine.fail, alu, ecall, Regs.get_set, BranchOp.taken, *])

/-- The three registers live throughout the nested loops. -/
def Inv (x : Regs 32) (n k c : Nat) : Prop :=
  x.get 10 = BitVec.ofNat 32 n ∧ x.get 5 = BitVec.ofNat 32 k ∧
    x.get 6 = BitVec.ofNat 32 c

private theorem rem_less (x : Regs 32) (out : String)
    (h : (x.get 28).ult (x.get 7) = true) :
    run 1 ⟨x, 24, image, [], out, .running⟩ =
      ⟨x, 36, image, [], out, .running⟩ := by
  prime_exec

private theorem rem_sub (x : Regs 32) (out : String)
    (h : (x.get 28).ult (x.get 7) = false) :
    ∃ x' : Regs 32, x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 ∧
      x'.get 6 = x.get 6 ∧ x'.get 7 = x.get 7 ∧
      x'.get 28 = x.get 28 - x.get 7 ∧
      run 3 ⟨x, 24, image, [], out, .running⟩ =
        ⟨x', 24, image, [], out, .running⟩ := by
  refine ⟨(x.set 28 (x.get 28 - x.get 7)).set 0 36, ?_⟩
  prime_exec

private theorem trial_start (x : Regs 32) (out : String)
    (h : x.get 7 ≠ x.get 5) :
    ∃ x' : Regs 32, x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 ∧
      x'.get 6 = x.get 6 ∧ x'.get 7 = x.get 7 ∧ x'.get 28 = x.get 5 ∧
      run 2 ⟨x, 16, image, [], out, .running⟩ =
        ⟨x', 24, image, [], out, .running⟩ := by
  refine ⟨x.set 28 (x.get 5), ?_⟩
  prime_exec

private theorem trial_zero (x : Regs 32) (out : String) (h : x.get 28 = 0) :
    run 1 ⟨x, 36, image, [], out, .running⟩ =
      ⟨x, 52, image, [], out, .running⟩ := by
  prime_exec

private theorem trial_nonzero (x : Regs 32) (out : String) (h : x.get 28 ≠ 0#32) :
    ∃ x' : Regs 32, x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 ∧
      x'.get 6 = x.get 6 ∧ x'.get 7 = x.get 7 + 1 ∧
      run 3 ⟨x, 36, image, [], out, .running⟩ =
        ⟨x', 16, image, [], out, .running⟩ := by
  refine ⟨(x.set 7 (x.get 7 + 1)).set 0 48, ?_⟩
  prime_exec

private theorem trial_prime (x : Regs 32) (out : String) (h : x.get 7 = x.get 5) :
    ∃ x' : Regs 32, x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 ∧
      x'.get 6 = x.get 6 + 1 ∧
      run 2 ⟨x, 16, image, [], out, .running⟩ =
        ⟨x', 52, image, [], out, .running⟩ := by
  refine ⟨x.set 6 (x.get 6 + 1), ?_⟩
  prime_exec

private theorem outer_start (x : Regs 32) (out : String)
    (h : (x.get 10).ult (x.get 5) = false) :
    ∃ x' : Regs 32, x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 ∧
      x'.get 6 = x.get 6 ∧ x'.get 7 = 2 ∧
      run 2 ⟨x, 8, image, [], out, .running⟩ =
        ⟨x', 16, image, [], out, .running⟩ := by
  refine ⟨x.set 7 2, ?_⟩
  prime_exec

private theorem outer_next (x : Regs 32) (out : String) :
    ∃ x' : Regs 32, x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 + 1 ∧
      x'.get 6 = x.get 6 ∧
      run 2 ⟨x, 52, image, [], out, .running⟩ =
        ⟨x', 8, image, [], out, .running⟩ := by
  refine ⟨(x.set 5 (x.get 5 + 1)).set 0 60, ?_⟩
  prime_exec

private theorem outer_done (x : Regs 32) (out : String)
    (h : (x.get 10).ult (x.get 5) = true) :
    (run 9 ⟨x, 8, image, [], out, .running⟩).status = .exited 0 ∧
    (run 9 ⟨x, 8, image, [], out, .running⟩).output =
      out ++ toString (x.get 6).toInt ++ "\n" := by
  prime_exec
  rfl

/-- Unsigned arithmetic agrees with natural subtraction when there is no underflow. -/
private theorem nat_sub (r d : Nat) (hr : r < 2^32) (hd : d ≤ r) :
    BitVec.ofNat 32 r - BitVec.ofNat 32 d = BitVec.ofNat 32 (r - d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

private theorem nat_ult (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    (BitVec.ofNat 32 a).ult (BitVec.ofNat 32 b) = decide (a < b) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem nat_ne (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) (hne : a ≠ b) :
    BitVec.ofNat 32 a ≠ BitVec.ofNat 32 b := by
  intro he
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact hne this

/-- The subtraction loop terminates with the mathematical remainder in `t3`.
The live input, candidate, count, and divisor registers are preserved. -/
private theorem rem_correct (r d : Nat) (hd : 0 < d) (hd32 : d < 2^32)
    (x : Regs 32) (out : String) (hr : r < 2^32)
    (hxr : x.get 28 = BitVec.ofNat 32 r) (hxd : x.get 7 = BitVec.ofNat 32 d) :
    ∃ fuel x', fuel = 1+3*(r/d) ∧
      x'.get 10 = x.get 10 ∧ x'.get 5 = x.get 5 ∧
      x'.get 6 = x.get 6 ∧ x'.get 7 = x.get 7 ∧
      x'.get 28 = BitVec.ofNat 32 (r % d) ∧
      run fuel ⟨x, 24, image, [], out, .running⟩ =
        ⟨x', 36, image, [], out, .running⟩ := by
  induction r using Nat.strongRecOn generalizing x with
  | ind r ih =>
    by_cases hlt : r < d
    · refine ⟨1, x, by simp [Nat.div_eq_of_lt hlt], rfl, rfl, rfl, rfl, ?_, ?_⟩
      · simpa [Nat.mod_eq_of_lt hlt] using hxr
      · apply rem_less
        rw [hxr, hxd, nat_ult r d hr hd32]
        simp [hlt]
    · have hge : d ≤ r := by omega
      have hbranch : (x.get 28).ult (x.get 7) = false := by
        rw [hxr, hxd, nat_ult r d hr hd32]
        simp [hlt]
      obtain ⟨x', h10, h5, h6, h7, h28, hs⟩ := rem_sub x out hbranch
      have hxr' : x'.get 28 = BitVec.ofNat 32 (r-d) := by
        rw [h28, hxr, hxd, nat_sub r d hr hge]
      obtain ⟨fuel, x'', hfuel, g10, g5, g6, g7, g28, ht⟩ :=
        ih (r-d) (by omega) x' (by omega) hxr' (h7.trans hxd)
      refine ⟨3 + fuel, x'', ?_, g10.trans h10, g5.trans h5, g6.trans h6,
        g7.trans h7, ?_, ?_⟩
      · rw [Nat.div_eq_sub_div hd hge, hfuel]
        omega
      · simpa [Nat.mod_eq_sub_mod hge] using g28
      · rw [run_add, hs, ht]

/-- Divisors below `d` have already been rejected. -/
private def NoDivisor (k d : Nat) : Prop :=
  ∀ e, 2 ≤ e → e < d → k % e ≠ 0

/-- The complete divisor scan terminates at the candidate-update block. It increments
`t1` exactly when the mathematical candidate is prime. -/
private theorem trial_correct (k d : Nat) (hk : 2 ≤ k) (hk32 : k < 2^32)
    (hd : 2 ≤ d) (hdk : d ≤ k) (hnodiv : NoDivisor k d)
    (n c : Nat) (x : Regs 32) (out : String) (hinv : Inv x n k c)
    (hxd : x.get 7 = BitVec.ofNat 32 d) :
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
      exact nat_ne d k (by omega) hk32 heq
    obtain ⟨x', h10, h5, h6, h7, h28, hs⟩ := trial_start x out hreg
    obtain ⟨fuel, x'', hfuel, g10, g5, g6, g7, g28, ht⟩ :=
      rem_correct k d (by omega) (by omega) x' out hk32
        (h28.trans hinv.2.1) (h7.trans hxd)
    have hi : Inv x'' n k c :=
      ⟨g10.trans (h10.trans hinv.1), g5.trans (h5.trans hinv.2.1),
        g6.trans (h6.trans hinv.2.2)⟩
    have hdreg : x''.get 7 = BitVec.ofNat 32 d := g7.trans (h7.trans hxd)
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
    · have hnzreg : x''.get 28 ≠ 0#32 := by
        rw [g28]
        exact nat_ne (k%d) 0 (by have := Nat.mod_lt k (show 0 < d by omega); omega)
          (by decide) hz
      obtain ⟨y, j10, j5, j6, j7, hu⟩ := trial_nonzero x'' out hnzreg
      have hj : Inv y n k c := ⟨j10.trans hi.1, j5.trans hi.2.1, j6.trans hi.2.2⟩
      have hjd : y.get 7 = BitVec.ofNat 32 (d+1) := by
        rw [j7, hdreg, BitVec.ofNat_add]
        rfl
      have hnodiv' : NoDivisor k (d+1) := by
        intro e he hed
        by_cases hed' : e < d
        · exact hnodiv e he hed'
        · have : e = d := by omega
          simpa [this] using hz
      obtain ⟨more, z, hmore, hz, hv⟩ :=
        trial_correct k (d+1) hk hk32 (by omega) (by omega) hnodiv' n c y out hj hjd
      have hscan : scanCost k d (k-d) = 6+3*(k/d)+scanCost k (d+1) (k-(d+1)) := by
        rw [show k-d = (k-(d+1))+1 by omega, scanCost_succ]
      refine ⟨2 + fuel + 3 + more, z, ?_, hz, ?_⟩
      · rw [hscan]
        omega
      · rw [run_add, run_add, run_add, hs, ht, hu, hv]
termination_by k-d

private theorem toInt_nat (c : Nat) (hc : c < 2^31) :
    (BitVec.ofNat 32 c).toInt = (c : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have h32 : c < 2^32 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32, show 2*c < 2^32 by omega]

private theorem nat_int_string (c : Nat) : toString (c : Int) = toString c := rfl

private theorem countPrimes_step (k : Nat) (hk : 0 < k) :
    countPrimes k = countPrimes (k-1) + if Prime k then 1 else 0 := by
  cases k with
  | zero => omega
  | succ k => rfl

/-- From the outer loop, `t1` counts exactly the primes below `t0`. The variant
`n+1-k` decreases on each candidate, and every nested scan terminates. -/
private theorem outer_correct (n k : Nat) (hn : n ≤ 2^31-2) (hk : 2 ≤ k)
    (hkn : k ≤ n+1) (x : Regs 32) (out : String)
    (hinv : Inv x n k (countPrimes (k-1))) :
    ∃ fuel, fuel ≤ 9+(n+1-k)*(6+scanCost n 2 (n-2)) ∧
      (run fuel ⟨x, 8, image, [], out, .running⟩).status = .exited 0 ∧
      (run fuel ⟨x, 8, image, [], out, .running⟩).output =
        out ++ toString (countPrimes n) ++ "\n" := by
  have hn32 : n < 2^32 := by omega
  have hk32 : k < 2^32 := by omega
  by_cases hdone : n < k
  · have he : k-1 = n := by omega
    have hbranch : (x.get 10).ult (x.get 5) = true := by
      rw [hinv.1, hinv.2.1, nat_ult n k hn32 hk32]
      simp [hdone]
    have hc : countPrimes n < 2^31 := by have := countPrimes_le n; omega
    refine ⟨9, by omega, ?_⟩
    simpa only [hinv.2.2, he, toInt_nat _ hc, nat_int_string] using outer_done x out hbranch
  · have hnk : k ≤ n := by omega
    have hbranch : (x.get 10).ult (x.get 5) = false := by
      rw [hinv.1, hinv.2.1, nat_ult n k hn32 hk32]
      simp [hdone]
    obtain ⟨x', h10, h5, h6, h7, hs⟩ := outer_start x out hbranch
    have hi : Inv x' n k (countPrimes (k-1)) :=
      ⟨h10.trans hinv.1, h5.trans hinv.2.1, h6.trans hinv.2.2⟩
    have hnodiv : NoDivisor k 2 := by intro e he he2; omega
    obtain ⟨fuel, y, hfuel, hy, ht⟩ :=
      trial_correct k 2 hk hk32 (by decide) (by omega) hnodiv n
        (countPrimes (k-1)) x' out hi h7
    have hcount := countPrimes_step k (by omega)
    have hy' : Inv y n k (countPrimes k) := by simpa [← hcount] using hy
    obtain ⟨z, j10, j5, j6, hu⟩ := outer_next y out
    have hj : Inv z n (k+1) (countPrimes ((k+1)-1)) := by
      refine ⟨j10.trans hy'.1, ?_, ?_⟩
      · rw [j5, hy'.2.1, BitVec.ofNat_add]
        rfl
      · simpa using j6.trans hy'.2.2
    obtain ⟨more, hmore, hm⟩ := outer_correct n (k+1) hn (by omega) (by omega) z out hj
    have hscan : scanCost k 2 (k-2) ≤ scanCost n 2 (n-2) :=
      Nat.le_trans (scanCost_mono_n k n 2 (k-2) hnk)
        (scanCost_mono_len n 2 (k-2) (n-2) (by omega))
    refine ⟨2 + fuel + 2 + more, ?_, ?_⟩
    · have he : n+1-k = (n+1-(k+1))+1 := by omega
      rw [he, Nat.add_mul, Nat.one_mul]
      omega
    · rwa [run_add, run_add, run_add, hs, ht, hu]
termination_by n+1-k

/-- Initialize the candidate and count without changing the preloaded input. -/
private theorem initialize_regs (n : Nat) :
    ∃ x, Inv x n 2 0 ∧ run 2 (initial n) =
      ⟨x, 8, image, [], "", .running⟩ := by
  let x : Regs 32 := (⟨Vector.replicate 32 0⟩ : Regs 32).set 10 (BitVec.ofNat 32 n)
  have hi : initial n = ⟨x, 0, image, [], "", .running⟩ := rfl
  rw [hi]
  refine ⟨(x.set 5 2).set 6 0, ?_, ?_⟩
  · simp [Inv, x, Regs.get_set]
  · prime_exec

/-- **RV32 machine correctness.** For every input up to `2^31-2`, the actual loaded
instruction words terminate with exit code zero and print the number of primes at most
`n`, followed by a newline, within `instructionBound n` modeled instructions.
No fuel or termination hypothesis is assumed. -/
theorem correct_bounded (n : Nat) (hn : n ≤ 2^31-2) :
    ∃ fuel, fuel ≤ instructionBound n ∧
      (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" := by
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

/-- Original correctness API, now obtained from the instruction-bounded proof. -/
theorem correct (n : Nat) (hn : n ≤ 2^31-2) :
    ∃ fuel, (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" := by
  obtain ⟨fuel, _, h⟩ := correct_bounded n hn
  exact ⟨fuel, h⟩

/-- Actual loaded-machine execution, with an input-dependent RV32 instruction bound. -/
theorem correct_quadratic_bound (n : Nat) (hn : n ≤ 2^31-2) :
    ∃ fuel, fuel ≤ 11+(n-1)*(6+96*n) ∧
      (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" := by
  obtain ⟨fuel, hb, h⟩ := correct_bounded n hn
  exact ⟨fuel, Nat.le_trans hb (instructionBound_rv32_quadratic n hn), h⟩

/-- A logarithmic-block bound for the actual loaded machine. -/
theorem correct_dyadic_bound (n k : Nat) (hn : n ≤ 2^31-2) (hk : n < 2^(k+1)) :
    ∃ fuel, fuel ≤ 11+(n-1)*(6+6*(n-2)+3*k*n) ∧
      (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" := by
  obtain ⟨fuel, hb, h⟩ := correct_bounded n hn
  exact ⟨fuel, Nat.le_trans hb (instructionBound_dyadic n k hk), h⟩

/-- Explicit numerical instruction cap for the entire supported domain. -/
theorem correct_numeric_bound (n : Nat) (hn : n ≤ 2^31-2) :
    ∃ fuel, fuel ≤ 442721856751121990201 ∧
      (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" := by
  obtain ⟨fuel, hb, h⟩ := correct_bounded n hn
  exact ⟨fuel, Nat.le_trans hb (instructionBound_rv32_bound n hn), h⟩

/-- Uniform instruction cap for the full unchanged input domain. -/
theorem correct_uniform_bound (n : Nat) (hn : n ≤ 2^31-2) :
    ∃ fuel, fuel < 2^69 ∧
      (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" := by
  obtain ⟨fuel, hb, h⟩ := correct_bounded n hn
  exact ⟨fuel, Nat.lt_of_le_of_lt hb (instructionBound_rv32_cap n hn), h⟩

end TinyFive.CountingPrimes
