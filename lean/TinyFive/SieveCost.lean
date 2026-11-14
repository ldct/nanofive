import TinyFive.CountingPrimes

/-!
# An executable instruction budget for the RV32 sieve

These arithmetic functions count the blocks traversed by the machine proof.
Bounds below are bounds on this budget; minimality of execution time is not
asserted here.
-/
namespace TinyFive.SieveCost

open CountingPrimes

/-- Number of stride-`p` iterations from cursor `j` through `n`, for positive `p`. -/
def innerIterations (n p j : Nat) : Nat := (n+p-j)/p

/-- The exit test costs one instruction, and each mark costs five. -/
def markCost (n p j : Nat) : Nat := 1+5*innerIterations n p j

theorem innerIterations_done (n p j : Nat) (hnj : n < j) (_hjp : j ≤ n+p) :
    innerIterations n p j = 0 := by
  unfold innerIterations
  apply Nat.div_eq_of_lt
  omega

theorem innerIterations_step (n p j : Nat) (hp : 0 < p) (hjn : j ≤ n) :
    innerIterations n p j = innerIterations n p (j+p)+1 := by
  unfold innerIterations
  have h1 : n+p-j = (n-j)+p := by omega
  have h2 : n+p-(j+p) = n-j := by omega
  rw [h1, h2, Nat.add_div_right _ hp]

theorem innerIterations_start (n p : Nat) (hp : 0 < p) (hpn : p ≤ n) :
    innerIterations n p (p+p) = n/p-1 := by
  unfold innerIterations
  have h : n+p-(p+p) = n-p := by omega
  rw [h]
  rw [Nat.div_eq_sub_div hp hpn]
  exact (Nat.add_sub_cancel _ 1).symm

theorem markCost_done (n p j : Nat) (hnj : n < j) (hjp : j ≤ n+p) :
    markCost n p j = 1 := by
  simp [markCost, innerIterations_done n p j hnj hjp]

theorem markCost_step (n p j : Nat) (hp : 0 < p) (hjn : j ≤ n) :
    markCost n p j = 5+markCost n p (j+p) := by
  simp only [markCost, innerIterations_step n p j hp hjn, Nat.mul_add, Nat.mul_one]
  omega

theorem markCost_start (n p : Nat) (hp : 0 < p) (hpn : p ≤ n) :
    markCost n p (p+p) = 1+5*(n/p-1) := by
  rw [markCost, innerIterations_start n p hp hpn]

/-- A prime candidate traverses the marking loop; a composite skips it. -/
def candidateCost (n p : Nat) : Nat :=
  if Prime p then 9+5*(n/p-1) else 6

/-- The budget for `len` consecutive candidates beginning at `p`. -/
def scanCost (n p : Nat) : Nat → Nat
  | 0 => 0
  | len+1 => candidateCost n p + scanCost n (p+1) len

@[simp] theorem scanCost_zero (n p : Nat) : scanCost n p 0 = 0 := rfl

@[simp] theorem scanCost_succ (n p len : Nat) :
    scanCost n p (len+1) = candidateCost n p + scanCost n (p+1) len := rfl

/-- Four initialization instructions and nine output/exit instructions. -/
def instructionCount (n : Nat) : Nat := 13+scanCost n 2 (n-1)

theorem instructionCount_small (n : Nat) (hn : n < 2) :
    instructionCount n = 13 := by
  have : n-1 = 0 := by omega
  simp [instructionCount, this]

theorem candidateCost_lower (n p : Nat) : 6 ≤ candidateCost n p := by
  unfold candidateCost
  split <;> omega

theorem candidateCost_upper (n p : Nat) : candidateCost n p ≤ 9+5*n := by
  have h := Nat.div_le_self n p
  unfold candidateCost
  split <;> omega

theorem candidateCost_mono (n m p : Nat) (hnm : n ≤ m) :
    candidateCost n p ≤ candidateCost m p := by
  have h := Nat.div_le_div_right (c := p) hnm
  unfold candidateCost
  split <;> omega

theorem scanCost_mono_n (n m p len : Nat) (hnm : n ≤ m) :
    scanCost n p len ≤ scanCost m p len := by
  induction len generalizing p with
  | zero => simp
  | succ len ih =>
    simp only [scanCost_succ]
    exact Nat.add_le_add (candidateCost_mono n m p hnm) (ih (p+1))

theorem scanCost_mono_len (n p a b : Nat) (hab : a ≤ b) :
    scanCost n p a ≤ scanCost n p b := by
  induction b generalizing p a with
  | zero =>
    have : a = 0 := by omega
    simp [this]
  | succ b ih =>
    cases a with
    | zero => simp
    | succ a =>
      simp only [scanCost_succ]
      exact Nat.add_le_add_left (ih (p+1) a (by omega)) _

theorem instructionCount_mono (n m : Nat) (hnm : n ≤ m) :
    instructionCount n ≤ instructionCount m := by
  unfold instructionCount
  apply Nat.add_le_add_left
  exact Nat.le_trans (scanCost_mono_n n m 2 (n-1) hnm)
    (scanCost_mono_len m 2 (n-1) (m-1) (by omega))

theorem scanCost_lower (n p len : Nat) : 6*len ≤ scanCost n p len := by
  induction len generalizing p with
  | zero => simp
  | succ len ih =>
    have hc := candidateCost_lower n p
    have hi := ih (p+1)
    simp only [scanCost_succ, Nat.mul_add, Nat.mul_one]
    omega

theorem scanCost_upper (n p len : Nat) :
    scanCost n p len ≤ len*(9+5*n) := by
  induction len generalizing p with
  | zero => simp
  | succ len ih =>
    have hc := candidateCost_upper n p
    have hi := ih (p+1)
    simp only [scanCost_succ, Nat.add_mul, Nat.one_mul]
    omega

theorem instructionCount_lower (n : Nat) :
    13+6*(n-1) ≤ instructionCount n := by
  exact Nat.add_le_add_left (scanCost_lower n 2 (n-1)) 13

theorem instructionCount_upper (n : Nat) :
    instructionCount n ≤ 13+(n-1)*(9+5*n) := by
  exact Nat.add_le_add_left (scanCost_upper n 2 (n-1)) 13

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
/-- Kernel evaluation of the executable budget, not an external timing test. -/
theorem instructionCount_600 : instructionCount 600 = 9529 := by
  decide +kernel

theorem instructionCount_le_600 (n : Nat) (hn : n ≤ 600) :
    instructionCount n ≤ 9529 := by
  have := instructionCount_mono n 600 hn
  rwa [instructionCount_600] at this

/-- Every input at most 600 fits strictly within a ten-thousand-instruction budget. -/
theorem instructionCount_lt_10000 (n : Nat) (hn : n ≤ 600) :
    instructionCount n < 10000 := by
  have := instructionCount_le_600 n hn
  omega

/-- A loose uniform budget for the complete memory-safe RV32 input range. -/
theorem instructionCount_rv32_cap (n : Nat) (hn : n ≤ 2^30-1) :
    instructionCount n < 2^63 := by
  have h1 : n-1 ≤ 2^30-2 := by omega
  have h2 : 9+5*n ≤ 9+5*(2^30-1) := by omega
  have hmul := Nat.mul_le_mul h1 h2
  have hbound := instructionCount_upper n
  omega

end TinyFive.SieveCost
