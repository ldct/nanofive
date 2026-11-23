import GrumpyBinary.SkipMath

/-! Bertrand's postulate below `159389`, from a chain of primes each less than twice the one
before. The compaction's first loop has no bound check: it stops at the first kept rough `j` with
`j * p > v`, and a prime in `(v / 2, v]` is one. -/
namespace TinyFive.LphaBinary
open CountingPrimes SieveMath GrumpyBinary

/-- Primality from trial division up to the square root. -/
theorem prime_of_sq (n : Nat) (h2 : 2 ≤ n) (hn : n < 360000)
    (hc : ∀ d ∈ List.range 600, 2 ≤ d → d * d ≤ n → n % d ≠ 0) : Prime n := by
  apply Decidable.byContradiction; intro hnp
  obtain ⟨q, hq, hdvd, hsq⟩ := prime_factor_sq n h2 hnp
  have hq2 := prime_ge_two hq
  have hq600 : q < 600 := by
    apply Decidable.byContradiction; intro h
    have := Nat.mul_le_mul (show 600 ≤ q by omega) (show 600 ≤ q by omega); omega
  exact hc q (List.mem_range.mpr hq600) hq2 hsq (Nat.mod_eq_zero_of_dvd hdvd)

macro "prime_tac" : tactic => `(tactic| (apply prime_of_sq _ (by decide) (by decide); decide +kernel))

theorem bertrand (n : Nat) (h3 : 3 ≤ n) (hn : n < 159389) : ∃ q, Prime q ∧ n < q ∧ q ≤ 2 * n := by
  by_cases h : n < 5
  · exact ⟨5, by prime_tac, by omega, by omega⟩
  by_cases h : n < 7
  · exact ⟨7, by prime_tac, by omega, by omega⟩
  by_cases h : n < 13
  · exact ⟨13, by prime_tac, by omega, by omega⟩
  by_cases h : n < 23
  · exact ⟨23, by prime_tac, by omega, by omega⟩
  by_cases h : n < 43
  · exact ⟨43, by prime_tac, by omega, by omega⟩
  by_cases h : n < 83
  · exact ⟨83, by prime_tac, by omega, by omega⟩
  by_cases h : n < 163
  · exact ⟨163, by prime_tac, by omega, by omega⟩
  by_cases h : n < 317
  · exact ⟨317, by prime_tac, by omega, by omega⟩
  by_cases h : n < 631
  · exact ⟨631, by prime_tac, by omega, by omega⟩
  by_cases h : n < 1259
  · exact ⟨1259, by prime_tac, by omega, by omega⟩
  by_cases h : n < 2503
  · exact ⟨2503, by prime_tac, by omega, by omega⟩
  by_cases h : n < 5003
  · exact ⟨5003, by prime_tac, by omega, by omega⟩
  by_cases h : n < 9973
  · exact ⟨9973, by prime_tac, by omega, by omega⟩
  by_cases h : n < 19937
  · exact ⟨19937, by prime_tac, by omega, by omega⟩
  by_cases h : n < 39869
  · exact ⟨39869, by prime_tac, by omega, by omega⟩
  by_cases h : n < 79699
  · exact ⟨79699, by prime_tac, by omega, by omega⟩
  · exact ⟨159389, by prime_tac, by omega, by omega⟩

end TinyFive.LphaBinary
