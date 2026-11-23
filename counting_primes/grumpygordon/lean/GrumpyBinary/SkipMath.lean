import GrumpyTables

/-! The `skip` byte array of the compiled program. Before stage `p`, `skip[i]` is set exactly
when `i` is an odd prime `q < p` or an odd multiple `i ≥ q²` of one: `SkipMarked p i`. -/
namespace TinyFive.GrumpyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon

def SkipMarked (p i : Nat) : Prop :=
  ∃ q, 3 ≤ q ∧ q < p ∧ Prime q ∧ (i = q ∨ (q ∣ i ∧ q * q ≤ i ∧ i % 2 = 1))

noncomputable instance (p i : Nat) : Decidable (SkipMarked p i) := Classical.propDecidable _

theorem prime_factor (n : Nat) (hn : 2 ≤ n) : ∃ q, Prime q ∧ q ∣ n ∧ q ≤ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hp : Prime n
    · exact ⟨n, hp, Nat.dvd_refl n, Nat.le_refl n⟩
    · have h := (not_congr (prime_iff_no_proper_divisor n)).mp hp
      simp only [not_and, Classical.not_forall, Classical.not_not] at h
      obtain ⟨d, hd2, hdn, hdvd⟩ := h hn
      obtain ⟨q, hq, hqd, hqle⟩ := ih d hdn hd2
      exact ⟨q, hq, Nat.dvd_trans hqd hdvd, by omega⟩

theorem prime_factor_sq (n : Nat) (hn : 2 ≤ n) (hnp : ¬ Prime n) :
    ∃ q, Prime q ∧ q ∣ n ∧ q * q ≤ n := by
  have h := (not_congr (prime_iff_no_proper_divisor n)).mp hnp
  simp only [not_and, Classical.not_forall, Classical.not_not] at h
  obtain ⟨d, hd2, hdn, ⟨e, rfl⟩⟩ := h hn
  have he2 : 2 ≤ e := by
    apply Decidable.byContradiction; intro h
    have : e = 0 ∨ e = 1 := by omega
    rcases this with rfl | rfl <;> simp at hdn hn
  have hm : min d e * min d e ≤ d * e :=
    Nat.mul_le_mul (Nat.min_le_left _ _) (Nat.min_le_right _ _)
  obtain ⟨q, hq, hqm, hqle⟩ := prime_factor (min d e) (by omega)
  refine ⟨q, hq, ?_, Nat.le_trans (Nat.mul_le_mul hqle hqle) hm⟩
  rcases Nat.le_total d e with h | h
  · rw [Nat.min_eq_left h] at hqm; exact Nat.dvd_trans hqm (Nat.dvd_mul_right d e)
  · rw [Nat.min_eq_right h] at hqm; exact Nat.dvd_trans hqm (Nat.dvd_mul_left e d)

theorem prime_ge_two {q : Nat} (h : Prime q) : 2 ≤ q := h.1

theorem even_not_prime (n : Nat) (h4 : 4 ≤ n) (he : n % 2 = 0) : ¬ Prime n := by
  intro hp
  exact (prime_iff_no_proper_divisor n).mp hp |>.2 2 (by omega) (by omega)
    (Nat.dvd_of_mod_eq_zero he)

/-- For odd `p`, `skip[p]` is clear exactly when `p` is prime. -/
theorem skip_self_iff (p : Nat) (hp : 3 ≤ p) (hodd : p % 2 = 1) :
    SkipMarked p p ↔ ¬ Prime p := by
  constructor
  · rintro ⟨q, hq3, hqp, hq, h | ⟨hdvd, _, _⟩⟩ hprime
    · omega
    · exact (prime_iff_no_proper_divisor p).mp hprime |>.2 q (by omega) hqp hdvd
  · intro hnp
    obtain ⟨q, hq, hdvd, hsq⟩ := prime_factor_sq p (by omega) hnp
    have hq2 := prime_ge_two hq
    have hq3 : 3 ≤ q := by
      apply Decidable.byContradiction; intro h
      have : q = 2 := by omega
      subst this
      have := Nat.mod_eq_zero_of_dvd hdvd
      omega
    have hqp : q < p := by
      apply Decidable.byContradiction; intro h
      have := Nat.mul_le_mul (show p ≤ q by omega) (show 2 ≤ q by omega)
      omega
    exact ⟨q, hq3, hqp, hq, Or.inr ⟨hdvd, hsq, hodd⟩⟩

/-- Passing a prime stage `p` adds `p` and its odd multiples from `p²`. -/
theorem skip_step_prime (p i : Nat) (hp : 3 ≤ p) (hodd : p % 2 = 1) (hprime : Prime p) :
    SkipMarked (p + 2) i ↔ SkipMarked p i ∨ i = p ∨ (p ∣ i ∧ p * p ≤ i ∧ i % 2 = 1) := by
  constructor
  · rintro ⟨q, hq3, hqp, hq, h⟩
    by_cases hlt : q < p
    · exact Or.inl ⟨q, hq3, hlt, hq, h⟩
    · by_cases he : q = p
      · subst he; exact Or.inr h
      · exact absurd hq (even_not_prime q (by omega) (by omega))
  · rintro (⟨q, hq3, hqp, hq, h⟩ | h | h)
    · exact ⟨q, hq3, by omega, hq, h⟩
    · exact ⟨p, hp, by omega, hprime, Or.inl h⟩
    · exact ⟨p, hp, by omega, hprime, Or.inr h⟩

/-- Passing an odd composite stage changes nothing. -/
theorem skip_step_composite (p i : Nat) (hp : 3 ≤ p) (hodd : p % 2 = 1) (hnp : ¬ Prime p) :
    SkipMarked (p + 2) i ↔ SkipMarked p i := by
  constructor
  · rintro ⟨q, hq3, hqp, hq, h⟩
    by_cases hlt : q < p
    · exact ⟨q, hq3, hlt, hq, h⟩
    · by_cases he : q = p
      · subst he; exact absurd hq hnp
      · exact absurd hq (even_not_prime q (by omega) (by omega))
  · rintro ⟨q, hq3, hqp, hq, h⟩
    exact ⟨q, hq3, by omega, hq, h⟩

/-- After marking stage `p`, the skip test on the live denominators is divisibility by `p`. -/
theorem skip_rough (p v d : Nat) (hp : 3 ≤ p) (hodd : p % 2 = 1) (hprime : Prime p)
    (hd : d ∈ 1 :: roughList p v) : SkipMarked (p + 2) d ↔ d % p = 0 := by
  rcases List.mem_cons.mp hd with rfl | hd
  · constructor
    · rintro ⟨q, hq3, _, _, h | ⟨hdvd, _⟩⟩
      · omega
      · have := Nat.le_of_dvd (by omega) hdvd; omega
    · intro h; rw [Nat.one_mod_eq_one.mpr (by omega)] at h; omega
  obtain ⟨hpd, _, h3, hmk⟩ := mem_rough.mp hd
  constructor
  · rintro ⟨q, hq3, hqp, hq, h⟩
    by_cases hlt : q < p
    · rcases h with rfl | ⟨hdvd, hsq, _⟩
      · omega
      · exact absurd ⟨q, by omega, hlt, by omega, hdvd⟩ hmk
    · by_cases he : q = p
      · subst he
        rcases h with rfl | ⟨hdvd, _⟩
        · simp
        · exact Nat.mod_eq_zero_of_dvd hdvd
      · exact absurd hq (even_not_prime q (by omega) (by omega))
  · intro h0
    have hdvd := Nat.dvd_of_mod_eq_zero h0
    by_cases he : d = p
    · exact ⟨p, hp, by omega, hprime, Or.inl he⟩
    · obtain ⟨m, rfl⟩ := hdvd
      have hm : p ≤ m := by
        apply Decidable.byContradiction; intro hlt
        have hm2 : 2 ≤ m := by
          apply Decidable.byContradiction; intro h
          have : m = 0 ∨ m = 1 := by omega
          rcases this with rfl | rfl <;> simp at he h3
        exact hmk ⟨m, hm2, by omega, by
          have := Nat.mul_le_mul_right m (show 2 ≤ p by omega); omega, Nat.dvd_mul_left m p⟩
      have hodd' : p * m % 2 = 1 := by
        apply Decidable.byContradiction; intro h
        exact hmk ⟨2, by omega, by omega, by omega, Nat.dvd_of_mod_eq_zero (by omega)⟩
      exact ⟨p, hp, by omega, hprime, Or.inr ⟨Nat.dvd_mul_right p m,
        Nat.mul_le_mul_left p hm, hodd'⟩⟩

end TinyFive.GrumpyBinary
