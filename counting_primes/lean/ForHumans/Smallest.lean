import CountingPrimesTrialDivision

/-!
# The smallest correct prime-counting program

A program is machine code `words` loaded at address 0 of `size` zeroed bytes, with every register
and `pc` zero and no input, as `load` builds it. The minimum is over programs, not arbitrary
machines: a machine could otherwise keep a table in its registers or its input, which
`programSize` does not count.

`smallestCorrectSize` is the fewest nonzero memory bytes of any program that satisfies
`IsCorrect`. `smallestCorrectSize_le` bounds it by the trial division program's 68 bytes.
-/
namespace TinyFive.CountingPrimes

/-- Some correct program has exactly `k` nonzero bytes. -/
def CorrectSize (k : Nat) : Prop :=
  ∃ words size, IsCorrect (load 64 words size []) ∧ programSize (load 64 words size []) = k

/-- `k` is the size of a smallest correct program. -/
def IsSmallestCorrectSize (k : Nat) : Prop :=
  CorrectSize k ∧ ∀ j, CorrectSize j → k ≤ j

/-- The size of a smallest correct program. -/
noncomputable def smallestCorrectSize : Nat :=
  Classical.epsilon IsSmallestCorrectSize

/-- A property of natural numbers that holds somewhere holds at a least number. -/
private theorem exists_least (P : Nat → Prop) :
    ∀ n, P n → ∃ k, P k ∧ ∀ j, P j → k ≤ j := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h : ∃ j, j < n ∧ P j
    · obtain ⟨j, hj, hpj⟩ := h
      exact ih j hj hpj
    · exact ⟨n, hn, fun j hj => Nat.le_of_not_lt fun hlt => h ⟨j, hlt, hj⟩⟩

theorem smallestCorrectSize_spec : IsSmallestCorrectSize smallestCorrectSize := by
  obtain ⟨k, hk⟩ := exists_least CorrectSize 68
    ⟨CountingPrimesTrialDivision.prog, 128,
      CountingPrimesTrialDivision.isCorrect, CountingPrimesTrialDivision.programSize_eq⟩
  exact Classical.epsilon_spec (p := IsSmallestCorrectSize) ⟨k, hk⟩

/-- **The smallest correct program has at most 68 nonzero bytes.** -/
theorem smallestCorrectSize_le : smallestCorrectSize ≤ 68 :=
  smallestCorrectSize_spec.2 68
    ⟨CountingPrimesTrialDivision.prog, 128,
      CountingPrimesTrialDivision.isCorrect, CountingPrimesTrialDivision.programSize_eq⟩

end TinyFive.CountingPrimes
