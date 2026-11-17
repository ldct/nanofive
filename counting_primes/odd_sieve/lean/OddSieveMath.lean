import TinyFive.Primes
import TinyFive.SieveMath

/-!
# Arithmetic for the odds-only sieve

Flag index `i` stands for the odd number `2*i+1`. The candidate `p = 2*h+1` has flag index `h`,
and its square has index `sq h = 2*h*(h+1)`. `OM p i` says that an odd candidate below `p` has
marked index `i`; marking starts at the candidate's square. Nothing here mentions the machine.
-/
namespace TinyFive.OddSieveMath

open CountingPrimes

/-- The flag index of `(2*h+1)^2`. -/
def sq (h : Nat) : Nat := 2*h*(h+1)

theorem sq_succ (h : Nat) : sq (h+1) = sq h + (2*h+1) + (2*h+3) := by
  simp only [sq, Nat.mul_add, Nat.add_mul, Nat.mul_one]
  omega

theorem sq_odd (h : Nat) : (2*h+1)*(2*h+1) = 2*sq h + 1 := by
  simp only [sq]
  grind

theorem sq_eq (h : Nat) : sq h = h*(2*h+1) + h := by
  simp only [sq, Nat.mul_add, Nat.mul_one]
  have : 2*h*h = h*(2*h) := Nat.mul_comm _ _
  omega

theorem le_sq (h : Nat) (hh : 1 ≤ h) : 2*h+1 ≤ sq h := by
  have h1 : 1*(2*h+1) ≤ h*(2*h+1) := Nat.mul_le_mul_right _ hh
  have := sq_eq h
  omega

theorem self_le_sq (h : Nat) : h ≤ sq h := by
  have h1 : h*1 ≤ h*(2*h+1) := Nat.mul_le_mul_left _ (by omega)
  have := sq_eq h
  omega

/-- The quotient of the square's index by the candidate. -/
theorem sq_div (h : Nat) : sq h / (2*h+1) = h := by
  rw [sq_eq, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]
  omega

/-- A small index has a small candidate: `sq h < 2^37` forces `h < 2^18`. -/
theorem lt_of_sq_lt (h : Nat) (hs : sq h < 2^37) : h < 2^18 := by
  apply Classical.byContradiction
  intro hc
  have h1 : 2^18 * (2*2^18+1) ≤ h*(2*h+1) := Nat.mul_le_mul (by omega) (by omega)
  have := sq_eq h
  omega

/-- An odd candidate below `p` divides `2*i+1` and has its square at or below it. -/
def OM (p i : Nat) : Prop := ∃ d, 3 ≤ d ∧ d < p ∧ d*d ≤ 2*i+1 ∧ d ∣ 2*i+1

/-- In index space, the multiples of `2*h+1` are spaced `2*h+1` apart from its square. -/
theorem dvd_index (h i : Nat) (hi : sq h ≤ i) :
    (2*h+1) ∣ (i - sq h) ↔ (2*h+1) ∣ 2*i+1 := by
  have he : 2*i+1 = (2*h+1)*(2*h+1) + 2*(i - sq h) := by rw [sq_odd]; omega
  rw [he, Nat.dvd_add_right (Nat.dvd_mul_right _ _)]
  constructor
  · exact fun hd => Nat.dvd_trans hd (Nat.dvd_mul_left _ _)
  · intro hd
    have h1 : (2*h+1) ∣ (2*h+1)*(i - sq h) := Nat.dvd_mul_right _ _
    have h2 : (2*h+1) ∣ h*(2*(i - sq h)) := Nat.dvd_trans hd (Nat.dvd_mul_left _ _)
    have h3 := Nat.dvd_sub h1 h2
    have h4 : (2*h+1)*(i - sq h) - h*(2*(i - sq h)) = i - sq h := by
      have : h*(2*(i - sq h)) = 2*h*(i - sq h) := by
        rw [← Nat.mul_assoc, Nat.mul_comm h 2]
      rw [this, Nat.add_mul, Nat.one_mul]
      omega
    rwa [h4] at h3

private theorem not_even_dvd (h i : Nat) : ¬ (2*h+2) ∣ 2*i+1 := by
  intro hd
  have : 2 ∣ 2*i+1 := Nat.dvd_trans ⟨h+1, by omega⟩ hd
  omega

/-- Processing the candidate `2*h+1` marks its multiples from its square on. -/
theorem om_step (h i : Nat) (hh : 1 ≤ h) :
    OM (2*h+3) i ↔ OM (2*h+1) i ∨ (sq h ≤ i ∧ (2*h+1) ∣ (i - sq h)) := by
  constructor
  · rintro ⟨d, h3, hdp, hdd, hdvd⟩
    by_cases h1 : d < 2*h+1
    · exact Or.inl ⟨d, h3, h1, hdd, hdvd⟩
    · by_cases h2 : d = 2*h+1
      · subst d
        rw [sq_odd] at hdd
        have hi : sq h ≤ i := by omega
        exact Or.inr ⟨hi, (dvd_index h i hi).mpr hdvd⟩
      · have : d = 2*h+2 := by omega
        subst d
        exact absurd hdvd (not_even_dvd h i)
  · rintro (⟨d, h3, hdp, hdd, hdvd⟩ | ⟨hi, hdvd⟩)
    · exact ⟨d, h3, by omega, hdd, hdvd⟩
    · exact ⟨2*h+1, by omega, by omega, by rw [sq_odd]; omega, (dvd_index h i hi).mp hdvd⟩

/-- A marked candidate's multiples from its square on are already marked. -/
theorem om_skip (h i : Nat) (hm : OM (2*h+1) h) : OM (2*h+3) i ↔ OM (2*h+1) i := by
  constructor
  · rintro ⟨d, h3, hdp, hdd, hdvd⟩
    by_cases h1 : d < 2*h+1
    · exact ⟨d, h3, h1, hdd, hdvd⟩
    · by_cases h2 : d = 2*h+1
      · subst d
        obtain ⟨e, he3, hep, hee, hedvd⟩ := hm
        have : 2*h+1 ≤ (2*h+1)*(2*h+1) := Nat.le_mul_self _
        exact ⟨e, he3, hep, by omega, Nat.dvd_trans hedvd hdvd⟩
      · have : d = 2*h+2 := by omega
        subst d
        exact absurd hdvd (not_even_dvd h i)
  · rintro ⟨d, h3, hdp, hdd, hdvd⟩
    exact ⟨d, h3, by omega, hdd, hdvd⟩

/-- Once the candidate's square exceeds `2*i+1`, the marks are exactly the composites. -/
theorem om_final (p i : Nat) (hi : 1 ≤ i) (hlt : 2*i+1 < p*p) :
    OM p i ↔ ¬ Prime (2*i+1) := by
  constructor
  · rintro ⟨d, h3, _, hdd, hdvd⟩ hprime
    have : d*3 ≤ d*d := Nat.mul_le_mul_left _ h3
    exact ((prime_iff_no_proper_divisor _).mp hprime).2 d (by omega) (by omega) hdvd
  · intro hnp
    have hex : ∃ d, 2 ≤ d ∧ d < 2*i+1 ∧ d ∣ 2*i+1 := by
      apply Classical.byContradiction
      intro hno
      exact hnp ((prime_iff_no_proper_divisor _).mpr
        ⟨by omega, fun d h2 hl hd => hno ⟨d, h2, hl, hd⟩⟩)
    obtain ⟨d, hd2, hdm, hdvd⟩ := hex
    have hq : ∃ q, 2 ≤ q ∧ q*q ≤ 2*i+1 ∧ q ∣ 2*i+1 := by
      by_cases hdd : d*d ≤ 2*i+1
      · exact ⟨d, hd2, hdd, hdvd⟩
      · obtain ⟨e, he⟩ := hdvd
        have he2 : 2 ≤ e := by
          apply Classical.byContradiction
          intro hc
          have : d*e ≤ d*1 := Nat.mul_le_mul_left _ (by omega)
          omega
        have hed : e < d := by
          apply Classical.byContradiction
          intro hc
          have : d*d ≤ d*e := Nat.mul_le_mul_left _ (by omega)
          omega
        have : e*e ≤ d*e := Nat.mul_le_mul_right _ (by omega)
        exact ⟨e, he2, by omega, ⟨d, by rw [he, Nat.mul_comm]⟩⟩
    obtain ⟨q, hq2, hqq, hqdvd⟩ := hq
    have hq3 : 3 ≤ q := by
      apply Classical.byContradiction
      intro hc
      have : q = 2 := by omega
      subst q
      omega
    have hqp : q < p := by
      apply Classical.byContradiction
      intro hc
      have : p*p ≤ q*q := Nat.mul_le_mul (by omega) (by omega)
      omega
    exact ⟨q, hq3, hqp, hqq, hqdvd⟩

/-- Index 0, the number 1, is never marked. -/
theorem om_zero (p : Nat) : ¬ OM p 0 := by
  rintro ⟨d, h3, _, hdd, _⟩
  have : d*3 ≤ d*d := Nat.mul_le_mul_left _ h3
  omega

/-- Marks while the candidate `2*h+1` is being processed, with cursor `j`. -/
def IP (h j i : Nat) : Prop :=
  OM (2*h+1) i ∨ (sq h ≤ i ∧ i < j ∧ (2*h+1) ∣ (i - sq h))

theorem ip_start (h i : Nat) : IP h (sq h) i ↔ OM (2*h+1) i := by
  constructor
  · rintro (hm | ⟨h1, h2, _⟩)
    · exact hm
    · omega
  · exact Or.inl

/-- Storing a mark at exactly `j` advances the cursor by the candidate. -/
theorem ip_step (h j i : Nat) (hj : sq h ≤ j) (hd : (2*h+1) ∣ (j - sq h)) :
    IP h (j + (2*h+1)) i ↔ IP h j i ∨ i = j := by
  constructor
  · rintro (hm | ⟨h1, h2, h3⟩)
    · exact Or.inl (Or.inl hm)
    · rcases (SieveMath.next_multiple_gap (2*h+1) (j - sq h) (i - sq h) (by omega) hd h3).mp
        (by omega) with h4 | h4
      · exact Or.inl (Or.inr ⟨h1, by omega, h3⟩)
      · exact Or.inr (by omega)
  · rintro ((hm | ⟨h1, h2, h3⟩) | rfl)
    · exact Or.inl hm
    · exact Or.inr ⟨h1, by omega, h3⟩
    · exact Or.inr ⟨hj, by omega, hd⟩

/-- Below the cursor, the marks are those of the next candidate. -/
theorem ip_done (h j i : Nat) (hh : 1 ≤ h) (hij : i < j) : IP h j i ↔ OM (2*h+3) i := by
  rw [om_step h i hh]
  simp only [IP, hij, true_and]

/-- Sum of a per-index value over the indices below a bound. -/
def csum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k+1 => csum f k + f k

@[simp] theorem csum_zero (f : Nat → Nat) : csum f 0 = 0 := rfl
theorem csum_succ (f : Nat → Nat) (k : Nat) : csum f (k+1) = csum f k + f k := rfl

theorem csum_congr (f g : Nat → Nat) (k : Nat) (h : ∀ i, i < k → f i = g i) :
    csum f k = csum g k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [csum_succ, csum_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

/-- Indices at or above `K` with value zero add nothing. -/
theorem csum_tail (f : Nat → Nat) (K q : Nat) (hz : ∀ i, K ≤ i → f i = 0) (hq : K ≤ q) :
    csum f q = csum f K := by
  induction q with
  | zero => have : K = 0 := by omega
            rw [this]
  | succ q ih =>
    by_cases he : K = q+1
    · rw [he]
    · rw [csum_succ, ih (by omega), hz q (by omega)]
      rfl

theorem csum_add16 (f : Nat → Nat) (q : Nat) :
    csum f (q+16) = csum f q + f q + f (q+1) + f (q+2) + f (q+3) + f (q+4) + f (q+5) + f (q+6)
      + f (q+7) + f (q+8) + f (q+9) + f (q+10) + f (q+11) + f (q+12) + f (q+13) + f (q+14)
      + f (q+15) := rfl

/-- The value of flag `i` when `K` flags are in use and `P` holds of the marked ones. -/
noncomputable def bit (K : Nat) (P : Nat → Prop) (i : Nat) : Nat :=
  open Classical in if i < K ∧ P i then 1 else 0

theorem bit_pos {K : Nat} {P : Nat → Prop} {i : Nat} (h1 : i < K) (h2 : P i) : bit K P i = 1 := by
  simp [bit, h1, h2]

theorem bit_neg {K : Nat} {P : Nat → Prop} {i : Nat} (h : ¬ (i < K ∧ P i)) : bit K P i = 0 := by
  simp only [bit, h, ite_false]

theorem bit_cases (K : Nat) (P : Nat → Prop) (i : Nat) :
    (bit K P i = 0 ∧ ¬ (i < K ∧ P i)) ∨ (bit K P i = 1 ∧ i < K ∧ P i) := by
  by_cases h : i < K ∧ P i
  · exact Or.inr ⟨bit_pos h.1 h.2, h⟩
  · exact Or.inl ⟨bit_neg h, h⟩

theorem bit_le_one (K : Nat) (P : Nat → Prop) (i : Nat) : bit K P i ≤ 1 := by
  rcases bit_cases K P i with h | h <;> omega

theorem bit_congr {K : Nat} {P Q : Nat → Prop} {i : Nat} (h : i < K → (P i ↔ Q i)) :
    bit K P i = bit K Q i := by
  by_cases hi : i < K
  · by_cases hp : P i
    · rw [bit_pos hi hp, bit_pos hi ((h hi).mp hp)]
    · rw [bit_neg (fun hc => hp hc.2), bit_neg (fun hc => hp ((h hi).mpr hc.2))]
  · rw [bit_neg (fun hc => hi hc.1), bit_neg (fun hc => hi hc.1)]

/-- One for a composite odd number `2*i+1 ≥ 3`, zero for a prime and for index 0. -/
def compBit (i : Nat) : Nat := if 1 ≤ i ∧ ¬ Prime (2*i+1) then 1 else 0

/-- The number of flags in use: one per odd number up to `n`, none for `n ≤ 1`. -/
def halfCount (n : Nat) : Nat := (n + if 1 < n then 1 else 0) / 2

theorem halfCount_le (n : Nat) : halfCount n ≤ (n+1)/2 := by
  unfold halfCount
  split <;> omega

private theorem count_identity_aux (n : Nat) :
    countPrimes (n+2) + csum compBit ((n+3)/2) = (n+3)/2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, countPrimes]
    by_cases hpar : n % 2 = 0
    · -- `n+3` is odd, with a new flag index `(n+2)/2`.
      have h1 : (n+1+3)/2 = (n+3)/2 + 1 := by omega
      have h2 : 2*((n+3)/2) + 1 = n+2+1 := by omega
      rw [h1, csum_succ]
      simp only [compBit, h2, show 1 ≤ (n+3)/2 by omega, true_and]
      by_cases hp : Prime (n+2+1)
      · simp only [hp, ite_true, not_true, ite_false]; omega
      · simp only [hp, ite_false, not_false_iff, ite_true]; omega
    · -- `n+3` is even, so it is not prime and adds no flag.
      have h1 : (n+1+3)/2 = (n+3)/2 := by omega
      have hp : ¬ Prime (n+2+1) := by
        intro hp
        exact ((prime_iff_no_proper_divisor _).mp hp).2 2 (by omega) (by omega)
          ⟨(n+3)/2, by omega⟩
      rw [h1]
      simp only [hp, ite_false]
      omega

/-- With index 0 standing in for the prime 2, `π(n)` is the flag count less the composite
flags. -/
theorem count_identity (n : Nat) :
    countPrimes n + csum compBit (halfCount n) = halfCount n := by
  match n with
  | 0 => decide
  | 1 => decide
  | n+2 =>
    have : halfCount (n+2) = (n+3)/2 := by
      simp only [halfCount, show 1 < n+2 by omega, ite_true]
    rw [this]
    exact count_identity_aux n

/-- When the final candidate's square is out of range, the flags in use are the composites. -/
theorem final_bits (K h i : Nat) (hK : K ≤ sq h) (hi : i < K) :
    bit K (OM (2*h+1)) i = compBit i := by
  by_cases h0 : 1 ≤ i
  · have hiff := om_final (2*h+1) i h0 (by rw [sq_odd]; omega)
    by_cases hp : Prime (2*i+1)
    · rw [bit_neg (fun hc => hiff.mp hc.2 hp)]
      simp [compBit, hp]
    · rw [bit_pos hi (hiff.mpr hp)]
      simp [compBit, hp, h0]
  · have : i = 0 := by omega
    subst i
    rw [bit_neg (fun hc => om_zero _ hc.2)]
    simp [compBit]

end TinyFive.OddSieveMath
