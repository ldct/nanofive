/-!
# Prime-counting functions

Definition of the prime-counting function independent of Mathlib
-/
namespace TinyFive.CountingPrimes

/-- Primality by the absence of a proper divisor. The bounded quantifier makes this
specification executable without adding a primality oracle. -/
def Prime (k : Nat) : Prop :=
  2 ≤ k ∧ ∀ d ∈ List.range k, 2 ≤ d → k % d ≠ 0

instance (k : Nat) : Decidable (Prime k) := by
  unfold Prime
  infer_instance

/-- The finite specification is equivalent to the usual trial-division predicate. -/
theorem prime_iff (k : Nat) :
    Prime k ↔ 2 ≤ k ∧ ∀ d, 2 ≤ d → d < k → k % d ≠ 0 := by
  grind [Prime]

/-- Equivalently, no natural number strictly between 1 and `k` divides `k`. -/
theorem prime_iff_no_proper_divisor (k : Nat) :
    Prime k ↔ 2 ≤ k ∧ ∀ d, 2 ≤ d → d < k → ¬ d ∣ k := by
  grind [prime_iff, Nat.dvd_iff_mod_eq_zero]

/-- The prime-counting function (https://en.wikipedia.org/wiki/Prime-counting_function). -/
def countPrimes : Nat → Nat
  | 0 => 0
  | n + 1 => countPrimes n + if Prime (n+1) then 1 else 0

@[simp] theorem countPrimes_zero : countPrimes 0 = 0 := rfl

@[simp] theorem countPrimes_one : countPrimes 1 = 0 := by
  simp [countPrimes, Prime]

theorem countPrimes_le (n : Nat) : countPrimes n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [countPrimes]
    split <;> omega

/-- The recursive specification really counts a finite set of mathematical primes. -/
theorem countPrimes_eq_filter (n : Nat) :
    countPrimes n = ((List.range (n+1)).filter (fun k => decide (Prime k))).length := by
  induction n with
  | zero => simp [Prime]
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hp : Prime (n+1)
    · simp [countPrimes, hp, ih]
    · simp [countPrimes, hp, ih]

end TinyFive.CountingPrimes
