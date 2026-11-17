import TinyFive.Primes

/-!
# Arithmetic invariant for the sieve

`Marked p k` says that a proper divisor below the current candidate `p` has
already marked `k`. These are elementary divisor facts used by the machine
proof, not an alternative implementation of the sieve.
-/
namespace TinyFive.SieveMath

open CountingPrimes

/-- A previous candidate is a nontrivial proper divisor of `k`. -/
def Marked (p k : Nat) : Prop :=
  ∃ d, 2 ≤ d ∧ d < p ∧ d < k ∧ d ∣ k

instance (p k : Nat) : Decidable (Marked p k) := by
  apply decidable_of_iff (∃ d ∈ List.range p, 2 ≤ d ∧ d < k ∧ d ∣ k)
  constructor
  · rintro ⟨d, hd, hd2, hdk, hdvd⟩
    exact ⟨d, hd2, List.mem_range.mp hd, hdk, hdvd⟩
  · rintro ⟨d, hd2, hdp, hdk, hdvd⟩
    exact ⟨d, List.mem_range.mpr hdp, hd2, hdk, hdvd⟩

@[simp] theorem marked_two (k : Nat) : ¬ Marked 2 k := by
  rintro ⟨d, hd2, hd, _⟩
  omega

theorem marked_self_iff_not_prime (p : Nat) (hp : 2 ≤ p) :
    Marked p p ↔ ¬ Prime p := by
  constructor
  · rintro ⟨d, hd2, hdp, _, hdvd⟩ hprime
    exact (prime_iff_no_proper_divisor p).mp hprime |>.2 d hd2 hdp hdvd
  · intro hnp
    by_cases hm : Marked p p
    · exact hm
    · apply False.elim
      apply hnp
      apply (prime_iff_no_proper_divisor p).mpr
      refine ⟨hp, ?_⟩
      intro d hd2 hdp hdvd
      exact hm ⟨d, hd2, hdp, hdp, hdvd⟩

theorem marked_step (p k : Nat) (hp : 2 ≤ p) :
    Marked (p+1) k ↔ Marked p k ∨ (p < k ∧ p ∣ k) := by
  constructor
  · rintro ⟨d, hd2, hdp, hdk, hdvd⟩
    by_cases he : d = p
    · exact Or.inr (by simpa [he] using And.intro hdk hdvd)
    · exact Or.inl ⟨d, hd2, by omega, hdk, hdvd⟩
  · rintro (⟨d, hd2, hdp, hdk, hdvd⟩ | ⟨hpk, hdvd⟩)
    · exact ⟨d, hd2, by omega, hdk, hdvd⟩
    · exact ⟨p, hp, by omega, hpk, hdvd⟩

/-- Skipping a marked candidate cannot omit any new composite. -/
theorem composite_skip (p k : Nat) (hm : Marked p p) :
    Marked (p+1) k ↔ Marked p k := by
  obtain ⟨d, hd2, hdp, _, hdvd⟩ := hm
  have hp : 2 ≤ p := by omega
  rw [marked_step p k hp]
  constructor
  · rintro (hk | ⟨hpk, hpkdvd⟩)
    · exact hk
    · exact ⟨d, hd2, hdp, by omega, Nat.dvd_trans hdvd hpkdvd⟩
  · exact Or.inl

/-- A proper positive multiple is at least the doubled divisor. -/
theorem proper_multiple_ge_double (p k : Nat) (hpk : p < k) (hdvd : p ∣ k) :
    p+p ≤ k := by
  have hdiff : p ∣ k-p := Nat.dvd_sub hdvd (Nat.dvd_refl p)
  have hle := Nat.le_of_dvd (show 0 < k-p by omega) hdiff
  omega

/-- There is no other multiple in the half-open interval `[j,j+p)`. -/
theorem next_multiple_gap (p j k : Nat) (hp : 0 < p)
    (hj : p ∣ j) (hk : p ∣ k) :
    k < j+p ↔ k < j ∨ k = j := by
  constructor
  · intro h
    by_cases hkj : k < j
    · exact Or.inl hkj
    · have hz := Nat.eq_zero_of_dvd_of_lt (Nat.dvd_sub hk hj)
        (show k-j < p by omega)
      exact Or.inr (by omega)
  · intro h
    rcases h with h | h <;> omega

/-- Inner-loop marks: earlier divisors and multiples below the cursor `j`. -/
def InProgress (p j k : Nat) : Prop :=
  Marked p k ∨ (p < k ∧ p ∣ k ∧ k < j)

instance (p j k : Nat) : Decidable (InProgress p j k) := by
  unfold InProgress
  infer_instance

theorem progress_start (p k : Nat) :
    InProgress p (p+p) k ↔ Marked p k := by
  constructor
  · rintro (hm | ⟨hpk, hdvd, hlt⟩)
    · exact hm
    · have := proper_multiple_ge_double p k hpk hdvd
      omega
  · exact Or.inl

/-- Storing a mark at exactly `j` advances the processed-multiple interval. -/
theorem progress_step (p j k : Nat) (hp : 0 < p)
    (hpj : p < j) (hj : p ∣ j) :
    InProgress p (j+p) k ↔ InProgress p j k ∨ k = j := by
  constructor
  · rintro (hm | ⟨hpk, hk, hlt⟩)
    · exact Or.inl (Or.inl hm)
    · rcases (next_multiple_gap p j k hp hj hk).mp hlt with h | h
      · exact Or.inl (Or.inr ⟨hpk, hk, h⟩)
      · exact Or.inr h
  · rintro (hm | rfl)
    · rcases hm with hm | ⟨hpk, hk, hlt⟩
      · exact Or.inl hm
      · exact Or.inr ⟨hpk, hk, by omega⟩
    · exact Or.inr ⟨hpj, hj, by omega⟩

/-- At loop exit, all candidates at or below the input have been processed. -/
theorem progress_done (p j k : Nat) (hp : 2 ≤ p) (hkj : k < j) :
    InProgress p j k ↔ Marked (p+1) k := by
  rw [marked_step p k hp]
  simp only [InProgress]
  constructor
  · rintro (hm | ⟨hpk, hk, _⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨hpk, hk⟩
  · rintro (hm | ⟨hpk, hk⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨hpk, hk, hkj⟩

end TinyFive.SieveMath
