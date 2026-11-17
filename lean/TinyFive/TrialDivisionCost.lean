/-!
# Instruction budgets for repeated-subtraction trial division

A divisor costs at most `6 + 3*(n/d)` instructions. The quotient sum is
bounded by dyadic blocks, without any hypothesis about the density of primes.
These budgets are connected to the loaded machine by `CountingPrimes.correct_bounded`.
`quotientSum_le_dyadic` is shared with the sieve and wheel budgets.
-/
namespace TinyFive.TrialDivisionCost

/-- Sum of mathematical quotients over consecutive possible divisors.
For positive divisors these count subtractions; a full scan overcounts early
composite exits. -/
def quotientSum (n d : Nat) : Nat → Nat
  | 0 => 0
  | len+1 => n/d + quotientSum n (d+1) len

@[simp] theorem quotientSum_zero (n d : Nat) : quotientSum n d 0 = 0 := rfl
@[simp] theorem quotientSum_succ (n d len : Nat) :
    quotientSum n d (len+1) = n/d + quotientSum n (d+1) len := rfl

/-- All possible divisor tests, including their loop overhead. -/
def scanCost (n d len : Nat) : Nat := 6*len + 3*quotientSum n d len

@[simp] theorem scanCost_zero (n d : Nat) : scanCost n d 0 = 0 := by
  simp [scanCost]

@[simp] theorem scanCost_succ (n d len : Nat) :
    scanCost n d (len+1) = 6+3*(n/d)+scanCost n (d+1) len := by
  simp only [scanCost, quotientSum_succ, Nat.mul_add, Nat.mul_one]
  omega

/-- Initialization and output cost eleven instructions; each candidate also
costs six instructions outside its possible-divisor tests. -/
def instructionBound (n : Nat) : Nat := 11+(n-1)*(6+scanCost n 2 (n-2))

theorem quotientSum_mono_n (n m d len : Nat) (hnm : n ≤ m) :
    quotientSum n d len ≤ quotientSum m d len := by
  induction len generalizing d with
  | zero => simp
  | succ len ih =>
    exact Nat.add_le_add (Nat.div_le_div_right hnm) (ih (d+1))

theorem quotientSum_mono_len (n d a b : Nat) (hab : a ≤ b) :
    quotientSum n d a ≤ quotientSum n d b := by
  induction b generalizing d a with
  | zero =>
    have : a = 0 := by omega
    simp [this]
  | succ b ih =>
    cases a with
    | zero => simp
    | succ a => exact Nat.add_le_add_left (ih (d+1) a (by omega)) _

theorem scanCost_mono_n (n m d len : Nat) (hnm : n ≤ m) :
    scanCost n d len ≤ scanCost m d len := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 3 (quotientSum_mono_n n m d len hnm)) _

theorem scanCost_mono_len (n d a b : Nat) (hab : a ≤ b) :
    scanCost n d a ≤ scanCost n d b := by
  exact Nat.add_le_add (Nat.mul_le_mul_left 6 hab)
    (Nat.mul_le_mul_left 3 (quotientSum_mono_len n d a b hab))

theorem quotientSum_append (n d a b : Nat) :
    quotientSum n d (a+b) = quotientSum n d a + quotientSum n (d+a) b := by
  induction a generalizing d with
  | zero => simp
  | succ a ih =>
    rw [show a+1+b = (a+b)+1 by omega, quotientSum_succ, ih, quotientSum_succ]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem quotientSum_upper (n a d len : Nat) (ha : 0 < a) (had : a ≤ d) :
    quotientSum n d len ≤ len*(n/a) := by
  induction len generalizing d with
  | zero => simp
  | succ len ih =>
    have hq : n/d ≤ n/a := Nat.div_le_div_left had ha
    have hi := ih (d+1) (by omega)
    simp only [quotientSum_succ, Nat.add_mul, Nat.one_mul]
    omega

/-- Each dyadic block contributes at most `n` subtractions. -/
theorem quotientSum_dyadic_block (n a : Nat) (ha : 0 < a) :
    quotientSum n a a ≤ n := by
  exact Nat.le_trans (quotientSum_upper n a a a ha (by omega)) (Nat.mul_div_le n a)

theorem quotientSum_dyadic_upper (n k : Nat) :
    quotientSum n 2 (2^(k+1)-2) ≤ k*n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ha : 0 < 2^(k+1) := Nat.pow_pos (by decide)
    have ha2 : 2 ≤ 2^(k+1) := by
      rw [Nat.pow_succ]
      have : 0 < 2^k := Nat.pow_pos (by decide)
      omega
    have he : 2^(k+1+1) = 2^(k+1)*2 := Nat.pow_succ _ _
    have hlen : 2^(k+1+1)-2 = (2^(k+1)-2)+2^(k+1) := by omega
    rw [hlen, quotientSum_append, show 2+(2^(k+1)-2) = 2^(k+1) by omega]
    have hb := quotientSum_dyadic_block n (2^(k+1)) ha
    have hs := Nat.add_le_add ih hb
    simpa [Nat.add_mul] using hs

/-- An input-dependent logarithmic-block bound (including inputs zero and one). -/
theorem instructionBound_dyadic (n k : Nat) (hn : n < 2^(k+1)) :
    instructionBound n ≤ 11+(n-1)*(6+6*(n-2)+3*k*n) := by
  have hlen : n-2 ≤ 2^(k+1)-2 := by omega
  have hq := Nat.le_trans (quotientSum_mono_len n 2 (n-2) (2^(k+1)-2) hlen)
    (quotientSum_dyadic_upper n k)
  have hs : 6+scanCost n 2 (n-2) ≤ 6+6*(n-2)+3*k*n := by
    unfold scanCost
    have := Nat.mul_le_mul_left 3 hq
    simp only [Nat.mul_assoc] at *
    omega
  exact Nat.add_le_add_left (Nat.mul_le_mul_left (n-1) hs) _

/-- Any prefix of the divisors `2, 3, ...` below `2^(k+1)` has quotient sum at most `k*n`.
The sieve and wheel budgets use this too. -/
theorem quotientSum_le_dyadic (n k len : Nat) (hlen : len ≤ 2^(k+1)-2) :
    quotientSum n 2 len ≤ k*n :=
  Nat.le_trans (quotientSum_mono_len n 2 len (2^(k+1)-2) hlen) (quotientSum_dyadic_upper n k)

/-- Thirty-six dyadic blocks cover every input below `10^11 < 2^37`. -/
theorem instructionBound_le (n : Nat) (hn : n < 10^11) :
    instructionBound n ≤ 11+114*n*n := by
  have h := instructionBound_dyadic n 36 (by omega)
  have hs : (n-1)*(6+6*(n-2)+3*36*n) ≤ 114*n*n := by
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl <;> decide
    · have := Nat.mul_le_mul (show n-1 ≤ n by omega) (show 6+6*(n-2)+3*36*n ≤ 114*n by omega)
      rwa [Nat.mul_left_comm, ← Nat.mul_assoc] at this
  omega

end TinyFive.TrialDivisionCost
