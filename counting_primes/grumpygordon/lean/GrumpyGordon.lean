import GrumpyTables

/-! Executable algorithm-level model of the grumpygordon rough-number counter. -/
namespace TinyFive.GrumpyGordon
open CountingPrimes LucyMath

/-- At the cutoff, the live rough denominators other than 1 are precisely
all the as-yet-unprocessed primes up to the square root. -/
theorem cutoff_roughs {N p : Nat} (hp : 3 ≤ p) (hcut : N < (p*p)*(p*p)) :
    roughList p (isqrt N) = primesFrom p (isqrt N+1-p) := by
  apply List.filter_congr
  intro q hq
  obtain ⟨hpq,hqv⟩ := List.mem_range'_1.mp hq
  have hv := (isqrt_spec N).1
  have hlt : isqrt N < p*p := by
    apply Decidable.byContradiction
    intro hn
    have := Nat.mul_le_mul (show p*p ≤ isqrt N by omega) (show p*p ≤ isqrt N by omega)
    omega
  simp [Alive, show 3 ≤ q by omega, unmarked_iff_prime p q (by omega) (by omega)]

def run (N v : Nat) (p : Nat) (t : Tables) : Nat :=
  if p*p ≤ v then
    let next := if small t (p-1) < small t p then step N v p t else t
    run N v (p+2) next
  else finish N v (small t) (large t) t.roughs
termination_by v+1-p
decreasing_by
  have : p ≤ p*p := Nat.le_mul_self p
  omega

theorem run_correct (N p : Nat) (t : Tables) (hN : 3 ≤ N) (hp : 3 ≤ p)
    (hodd : p % 2 = 1) (h : Valid N p t) : run N (isqrt N) p t = countPrimes N := by
  rw [run]
  split
  · rename_i hs
    have hpv := Nat.le_trans (Nat.le_mul_self p) hs
    have := Nat.mul_le_mul_right p hp
    apply run_correct N (p+2) _ hN (by omega) (by omega)
    apply skip_valid (by omega : 3 ≤ p+1) (by omega) (not_prime_even p hp hodd)
    rw [h.lo _ (by omega), h.lo _ hpv, C_self p hp]
    by_cases hprime : Prime p
    · simpa [hprime] using step_valid hp hpv hprime h
    · simpa [hprime] using skip_valid hp hpv hprime h
  · rename_i hs
    have hcut : N < (p*p)*(p*p) := by
      apply Decidable.byContradiction
      intro hn
      exact hs (le_isqrt (by omega))
    rw [h.keys, cutoff_roughs hp hcut]
    apply finish_correct N p hN hp hcut _ _ h.lo
    · simpa using h.hi 1 (by simp)
    · intro q hpq hqv hprime
      apply h.hi; apply List.mem_cons_of_mem
      rw [h.keys, cutoff_roughs hp hcut]
      simp [primesFrom, hpq, hprime]; omega
termination_by isqrt N+1-p

def primePi (N : Nat) :=
  if N < 3 then N/2 else
    let v := isqrt N
    run N v 3 (init N v)

/-- Correct on *all* naturals, including the Library Checker endpoint `10^11`.
This is about the executable Lean algorithm, not compiled machine code. -/
theorem correct (N : Nat) : primePi N = TinyFive.CountingPrimes.countPrimes N := by
  unfold primePi
  split
  · have : N = 0 ∨ N = 1 ∨ N = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  · apply run_correct N 3 _ (by omega) (by decide) (by decide)
    exact init_valid _ (le_isqrt (by omega))

end TinyFive.GrumpyGordon
