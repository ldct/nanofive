import SieveCost

/-!
# Dyadic instruction bounds for the sieve

We overcount prime marking by allowing every candidate to mark. On a block
`[a, 2*a)`, every quotient `n/p` is at most `n/a`, so the block's marking
contribution is at most `5*a*(n/a) ≤ 5*n`. There are 36 such blocks
between 2 and `2^37 > 10^11`. No prime-density estimate or evaluation at the
largest supported input is needed.
-/
namespace TinyFive.SieveCost

theorem scanCost_append (n p a b : Nat) :
    scanCost n p (a+b) = scanCost n p a + scanCost n (p+a) b := by
  induction a generalizing p with
  | zero => simp
  | succ a ih =>
    rw [show a+1+b = (a+b)+1 by omega, scanCost_succ, ih, scanCost_succ]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem scanCost_quotient_upper (n a p len : Nat) (ha : 0 < a) (hp : a ≤ p) :
    scanCost n p len ≤ len*(9+5*(n/a)) := by
  induction len generalizing p with
  | zero => simp
  | succ len ih =>
    have hq : n/p ≤ n/a := Nat.div_le_div_left hp ha
    have hc : candidateCost n p ≤ 9+5*(n/a) := by
      unfold candidateCost
      split <;> omega
    have hi := ih (p+1) (by omega)
    simp only [scanCost_succ, Nat.add_mul, Nat.one_mul]
    omega

/-- Even if every candidate marked, one dyadic block costs at most `9*a+5*n`. -/
theorem scanCost_dyadic_block (n a : Nat) (ha : 0 < a) :
    scanCost n a a ≤ 9*a+5*n := by
  have h := scanCost_quotient_upper n a a a ha (by omega)
  have hq := Nat.mul_div_le n a
  calc
    scanCost n a a ≤ a*(9+5*(n/a)) := h
    _ = 9*a+5*(a*(n/a)) := by simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
    _ ≤ 9*a+5*n := Nat.add_le_add_left (Nat.mul_le_mul_left 5 hq) _

/-- The candidates `[2, 2^(k+1))` occupy `k` dyadic blocks. -/
theorem scanCost_dyadic_upper (n k : Nat) :
    scanCost n 2 (2^(k+1)-2) ≤ 9*(2^(k+1)-2)+5*k*n := by
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
    rw [hlen, scanCost_append, show 2+(2^(k+1)-2) = 2^(k+1) by omega]
    have hb := scanCost_dyadic_block n (2^(k+1)) ha
    have hs := Nat.add_le_add ih hb
    simp only [Nat.mul_add, Nat.add_mul] at *
    omega

/-- A logarithmic-block bound, allowing padding up to the next dyadic endpoint. -/
theorem instructionCount_dyadic_upper (n k : Nat) (hn : n < 2^(k+1)) :
    instructionCount n ≤ 13+9*(2^(k+1)-2)+5*k*n := by
  have hlen : n-1 ≤ 2^(k+1)-2 := by omega
  have hmono := scanCost_mono_len n 2 (n-1) (2^(k+1)-2) hlen
  have h := Nat.le_trans hmono (scanCost_dyadic_upper n k)
  unfold instructionCount
  omega

/-- A candidate costs at most `9 + 5*(n/p)`, whether or not it marks. -/
theorem scanCost_le_quotientSum (n p len : Nat) :
    scanCost n p len ≤ 9*len + 5*TrialDivisionCost.quotientSum n p len := by
  induction len generalizing p with
  | zero => simp
  | succ len ih =>
    have hc : candidateCost n p ≤ 9+5*(n/p) := by
      unfold candidateCost
      split <;> omega
    have hi := ih (p+1)
    simp only [scanCost_succ, TrialDivisionCost.quotientSum_succ]
    omega

/-- Thirty-six dyadic blocks cover every input below `10^11 < 2^37`. -/
theorem instructionCount_le (n : Nat) (hn : n < 10^11) :
    instructionCount n ≤ 13+189*n := by
  have h1 := scanCost_le_quotientSum n 2 (n-1)
  have h2 := TrialDivisionCost.quotientSum_le_dyadic n 36 (n-1) (by omega)
  unfold instructionCount
  omega

end TinyFive.SieveCost
