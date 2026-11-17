/-!
# Prime-counting specification

`Prime` and `countPrimes`, the specification that the prime-counting programs
(`counting_primes_simple`, `counting_primes_sieve`, `counting_primes_wheel`) are proved to meet.
They stay in the `TinyFive.CountingPrimes` namespace, where the proofs refer to them.
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
  simp only [Prime, List.mem_range]
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun d hd hdk => h d hdk hd⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun d hdk hd => h d hd hdk⟩

/-- Equivalently, no natural number strictly between 1 and `k` divides `k`. -/
theorem prime_iff_no_proper_divisor (k : Nat) :
    Prime k ↔ 2 ≤ k ∧ ∀ d, 2 ≤ d → d < k → ¬ d ∣ k := by
  simp only [prime_iff, Nat.dvd_iff_mod_eq_zero]

/-- Number of primes at most `n`, independently of the machine's loop state. -/
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
