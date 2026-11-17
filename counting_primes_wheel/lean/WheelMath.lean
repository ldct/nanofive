import TinyFive.Primes
import TinyFive.SieveMath

/-! Elementary arithmetic for the mod-30 candidate wheel. Marking itself still
uses the ordinary sieve's divisor stride. -/
namespace TinyFive.WheelMath

open CountingPrimes SieveMath

/-- The eleven immutable gap bytes, including the three startup candidates. -/
def gap : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 4
  | 4 => 2
  | 5 => 4
  | 6 => 2
  | 7 => 4
  | 8 => 6
  | 9 => 2
  | 10 => 6
  | _ => 0

/-- Startup phases are visited once; the eight coprime residues then cycle. -/
def nextPhase (s : Nat) : Nat := if s+1 < 11 then s+1 else 3

/-- Current candidate and its position in the gap table. -/
def Phase (p s : Nat) : Prop :=
  (s = 0 ∧ p = 2) ∨ (s = 1 ∧ p = 3) ∨ (s = 2 ∧ p = 5) ∨
  (s = 3 ∧ 7 ≤ p ∧ p % 30 = 7) ∨
  (s = 4 ∧ 7 ≤ p ∧ p % 30 = 11) ∨
  (s = 5 ∧ 7 ≤ p ∧ p % 30 = 13) ∨
  (s = 6 ∧ 7 ≤ p ∧ p % 30 = 17) ∨
  (s = 7 ∧ 7 ≤ p ∧ p % 30 = 19) ∨
  (s = 8 ∧ 7 ≤ p ∧ p % 30 = 23) ∨
  (s = 9 ∧ 7 ≤ p ∧ p % 30 = 29) ∨
  (s = 10 ∧ 7 ≤ p ∧ p % 30 = 1)

instance (p s : Nat) : Decidable (Phase p s) := by
  unfold Phase
  infer_instance

theorem phase_initial : Phase 2 0 := by decide

theorem phase_bounds (p s : Nat) (h : Phase p s) : s < 11 ∧ 2 ≤ p := by
  unfold Phase at h
  omega

theorem gap_bounds (p s : Nat) (h : Phase p s) : 1 ≤ gap s ∧ gap s ≤ 6 := by
  rcases h with h|h|h|h|h|h|h|h|h|h|h <;>
    rcases h with ⟨rfl, h⟩ <;> simp [gap]

theorem phase_step (p s : Nat) (h : Phase p s) :
    Phase (p + gap s) (nextPhase s) := by
  rcases h with h|h|h|h|h|h|h|h|h|h|h <;>
    rcases h with ⟨rfl, h⟩ <;>
    simp_all [gap, nextPhase, Phase] <;> omega

/-- Every integer strictly between consecutive wheel candidates has a small
proper divisor already processed by the sieve. -/
theorem skipped_divisor (p s q : Nat) (h : Phase p s)
    (hpq : p < q) (hqp : q < p + gap s) :
    ∃ d, 2 ≤ d ∧ d < p+1 ∧ d < q ∧ d ∣ q := by
  have hp := (phase_bounds p s h).2
  have hg := (gap_bounds p s h).2
  have hoff : q = p+1 ∨ q = p+2 ∨ q = p+3 ∨ q = p+4 ∨ q = p+5 := by omega
  have hdiv : q % 2 = 0 ∨ q % 3 = 0 ∨ q % 5 = 0 := by
    rcases h with h|h|h|h|h|h|h|h|h|h|h <;>
      rcases h with ⟨rfl, h⟩ <;> simp only [gap] at hqp <;>
      rcases hoff with hoff|hoff|hoff|hoff|hoff <;> omega
  have hp3 : 3 ≤ p := by
    rcases h with h|h|h|h|h|h|h|h|h|h|h <;>
      rcases h with ⟨rfl, h⟩ <;> simp only [gap] at hqp <;> omega
  rcases hdiv with h2 | h3 | h5
  · exact ⟨2, by omega, by omega, by omega, Nat.dvd_of_mod_eq_zero h2⟩
  · exact ⟨3, by omega, by omega, by omega, Nat.dvd_of_mod_eq_zero h3⟩
  · have hp5 : 5 ≤ p := by
      rcases h with h|h|h|h|h|h|h|h|h|h|h <;>
        rcases h with ⟨rfl, h⟩ <;> simp only [gap] at hqp <;> omega
    exact ⟨5, by omega, by omega, by omega, Nat.dvd_of_mod_eq_zero h5⟩

/-- No prime occurs in an omitted wheel interval. -/
theorem skipped_not_prime (p s q : Nat) (h : Phase p s)
    (hpq : p < q) (hqp : q < p + gap s) : ¬ Prime q := by
  obtain ⟨d, hd2, hdp, hdq, hdvd⟩ := skipped_divisor p s q h hpq hqp
  intro hprime
  exact (prime_iff_no_proper_divisor q).mp hprime |>.2 d hd2 hdq hdvd

/-- Moving directly to the next wheel candidate preserves exactly the flags
that ordinary single-candidate advancement would have produced. -/
theorem skipped_marked (p s k : Nat) (h : Phase p s) :
    Marked (p + gap s) k ↔ Marked (p+1) k := by
  have hg := (gap_bounds p s h).1
  constructor
  · rintro ⟨d, hd2, hdp, hdk, hdvd⟩
    by_cases hd : d < p+1
    · exact ⟨d, hd2, hd, hdk, hdvd⟩
    · obtain ⟨e, he2, hep, hed, hevd⟩ :=
        skipped_divisor p s d h (by omega) hdp
      exact ⟨e, he2, hep, by omega, Nat.dvd_trans hevd hdvd⟩
  · rintro ⟨d, hd2, hdp, hdk, hdvd⟩
    exact ⟨d, hd2, by omega, hdk, hdvd⟩

/-- Prime counts are constant throughout the interval after a candidate and
strictly before its successor. -/
theorem countPrimes_between (p s q : Nat) (h : Phase p s)
    (hpq : p ≤ q) (hqp : q < p + gap s) :
    countPrimes q = countPrimes p := by
  induction q with
  | zero =>
    have : p = 0 := by omega
    simp [this]
  | succ q ih =>
    by_cases heq : p = q+1
    · rw [heq]
    · have hnp : ¬ Prime (q+1) := skipped_not_prime p s (q+1) h (by omega) hqp
      simp only [countPrimes, ite_eq_right hnp, Nat.add_zero]
      exact ih (by omega) (by omega)

/-- All skipped candidates contribute zero to the count. -/
theorem skipped_count (p s : Nat) (h : Phase p s) :
    countPrimes (p + gap s - 1) = countPrimes p := by
  have hg := (gap_bounds p s h).1
  exact countPrimes_between p s (p + gap s - 1) h (by omega) (by omega)

/-- Clipping the last omitted interval to the input also preserves the count;
this handles a wheel step which overshoots the input. -/
theorem countPrimes_gap (n p s : Nat) (h : Phase p s) (hpn : p ≤ n) :
    countPrimes (min n (p + gap s - 1)) = countPrimes p := by
  have hg := (gap_bounds p s h).1
  exact countPrimes_between p s (min n (p + gap s - 1)) h (by omega) (by omega)

end TinyFive.WheelMath
