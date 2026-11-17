import TinyFive.Primes
import TinyFive.SieveMath

/-!
# The arithmetic behind the Lucy_Hedgehog prime counter

`S P v` is the number of `n` in `[5, v]` that no `d` with `2 ≤ d < P` properly divides, that is,
the numbers that are prime or have no prime factor below `P`. This file proves, without Mathlib,
the four facts the machine proof needs:

* `S_init`: `S 5 v = ((v - 1) / 2 * 2) / 3`, the count of numbers coprime to 6;
* `S_prime_step`: for a prime `p` and `p * p ≤ v`, `S p v = S (p+1) v + (S p (v / p) - S p (p-1))`,
  with `S_small` (`v < p * p`) and `S_composite` (`p` not prime) for the cases that change nothing;
* `S_self`: `S p p = S p (p-1) + 1` exactly when `p` is prime, which is the program's primality test;
* `countPrimes_eq`: once `N < P * P`, `countPrimes N = S P N + 2`.
-/
namespace TinyFive.LucyMath

open CountingPrimes SieveMath

/-! ## Counting the integers in `[1, v]` that satisfy a predicate -/

def count (Q : Nat → Prop) [DecidablePred Q] : Nat → Nat
  | 0 => 0
  | v + 1 => count Q v + if Q (v + 1) then 1 else 0

theorem count_succ (Q : Nat → Prop) [DecidablePred Q] (v : Nat) :
    count Q (v + 1) = count Q v + if Q (v + 1) then 1 else 0 := rfl

theorem count_le (Q : Nat → Prop) [DecidablePred Q] (v : Nat) : count Q v ≤ v := by
  induction v with
  | zero => simp [count]
  | succ v ih => rw [count_succ]; split <;> omega

theorem count_mono (Q : Nat → Prop) [DecidablePred Q] {v w : Nat} (h : v ≤ w) :
    count Q v ≤ count Q w := by
  induction w with
  | zero => rw [show v = 0 by omega]; exact Nat.le_refl _
  | succ w ih =>
    by_cases he : v = w + 1
    · rw [he]; exact Nat.le_refl _
    · have := ih (by omega)
      rw [count_succ]
      omega

theorem count_congr {Q Q' : Nat → Prop} [DecidablePred Q] [DecidablePred Q'] (v : Nat)
    (h : ∀ n, 1 ≤ n → n ≤ v → (Q n ↔ Q' n)) : count Q v = count Q' v := by
  induction v with
  | zero => rfl
  | succ v ih =>
    rw [count_succ, count_succ, ih (fun n h1 h2 => h n h1 (by omega))]
    have := h (v + 1) (by omega) (by omega)
    by_cases hq : Q (v + 1)
    · simp [hq, this.mp hq]
    · have hq' : ¬ Q' (v + 1) := fun h' => hq (this.mpr h')
      simp [hq, hq']

theorem count_zero_of (Q : Nat → Prop) [DecidablePred Q] (v : Nat)
    (h : ∀ n, 1 ≤ n → n ≤ v → ¬ Q n) : count Q v = 0 := by
  induction v with
  | zero => rfl
  | succ v ih =>
    rw [count_succ, ih (fun n h1 h2 => h n h1 (by omega))]
    simp [h (v + 1) (by omega) (by omega)]

theorem count_split (Q R : Nat → Prop) [DecidablePred Q] [DecidablePred R] (v : Nat) :
    count Q v = count (fun n => Q n ∧ R n) v + count (fun n => Q n ∧ ¬ R n) v := by
  induction v with
  | zero => rfl
  | succ v ih =>
    rw [count_succ, count_succ, count_succ, ih]
    by_cases hq : Q (v + 1) <;> by_cases hr : R (v + 1) <;> simp [hq, hr] <;> omega

/-- The multiples `p * m` in `[1, v]` correspond to the `m` in `[1, v / p]`. -/
theorem count_mul (Q : Nat → Prop) [DecidablePred Q] (p : Nat) (_hp : 0 < p) (v : Nat) :
    count (fun n => p ∣ n ∧ Q (n / p)) v = count Q (v / p) := by
  induction v with
  | zero => simp [count]
  | succ v ih =>
    rw [count_succ, ih]
    by_cases hd : p ∣ v + 1
    · have hdiv : (v + 1) / p = v / p + 1 := by rw [Nat.succ_div]; simp [hd]
      rw [hdiv, count_succ]
      simp [hd]
    · have hdiv : (v + 1) / p = v / p := by rw [Nat.succ_div]; simp [hd]
      rw [hdiv]
      simp [hd]

theorem count_from (Q : Nat → Prop) [DecidablePred Q] (a : Nat) {v : Nat} (h : a ≤ v) :
    count Q v = count Q a + count (fun n => a < n ∧ Q n) v := by
  induction v with
  | zero =>
    rw [show a = 0 by omega]
    rfl
  | succ v ih =>
    by_cases he : a = v + 1
    · subst he
      rw [count_zero_of (fun n => v + 1 < n ∧ Q n) (v + 1) (by intro n _ h2 h3; omega)]
      rfl
    · rw [count_succ, count_succ, ih (by omega)]
      by_cases hq : Q (v + 1)
      · simp [hq, show a < v + 1 by omega]; omega
      · simp [hq]

/-! ## The table entries -/

/-- `n ≥ 5` survives stage `P`: no `d` with `2 ≤ d < P` properly divides it. -/
def Surv (P n : Nat) : Prop := 5 ≤ n ∧ ¬ Marked P n

instance (P : Nat) : DecidablePred (Surv P) := fun n => by
  unfold Surv
  infer_instance

/-- The number of survivors of stage `P` in `[5, v]`. -/
def S (P v : Nat) : Nat := count (Surv P) v

theorem S_le (P v : Nat) : S P v ≤ v := count_le _ v

theorem S_mono (P : Nat) {v w : Nat} (h : v ≤ w) : S P v ≤ S P w := count_mono _ h

theorem surv_five (n : Nat) : Surv 5 n ↔ 5 ≤ n ∧ n % 2 = 1 ∧ n % 3 ≠ 0 := by
  constructor
  · rintro ⟨h5, hm⟩
    refine ⟨h5, ?_, ?_⟩
    · apply Decidable.byContradiction
      intro h
      exact hm ⟨2, by omega, by omega, by omega, by omega⟩
    · intro h
      exact hm ⟨3, by omega, by omega, by omega, by omega⟩
  · rintro ⟨h5, h2, h3⟩
    refine ⟨h5, ?_⟩
    rintro ⟨d, hd2, hd5, hdn, hdvd⟩
    have : d = 2 ∨ d = 3 ∨ d = 4 := by omega
    rcases this with h | h | h <;> subst h <;> omega

/-- The tables start as the count of numbers coprime to 6. -/
theorem S_init (v : Nat) : S 5 v = (v - 1) / 2 * 2 / 3 := by
  induction v with
  | zero => rfl
  | succ v ih =>
    rw [S, count_succ, ← S, ih, Nat.add_sub_cancel]
    have h6 : v % 6 = 0 ∨ v % 6 = 1 ∨ v % 6 = 2 ∨ v % 6 = 3 ∨ v % 6 = 4 ∨ v % 6 = 5 := by omega
    by_cases h : Surv 5 (v + 1)
    · simp only [h, ite_true]
      rw [surv_five] at h
      rcases h6 with h6 | h6 | h6 | h6 | h6 | h6 <;> omega
    · simp only [h, ite_false]
      rw [surv_five] at h
      rcases h6 with h6 | h6 | h6 | h6 | h6 | h6 <;> omega

/-- An even number is never a survivor, so `S` is read at odd arguments only. -/
theorem S_even (P : Nat) (hP : 3 ≤ P) (j : Nat) : S P (2 * j + 2) = S P (2 * j + 1) := by
  rw [S, count_succ]
  have : ¬ Surv P (2 * j + 1 + 1) := by
    rintro ⟨h5, hm⟩
    exact hm ⟨2, by omega, by omega, by omega, by omega⟩
  simp [this, S]

/-- `S P v` read through the index `(v - 1) / 2` of the table of odd arguments. -/
theorem S_odd_index (P : Nat) (hP : 3 ≤ P) (v : Nat) (hv : 1 ≤ v) :
    S P (2 * ((v - 1) / 2) + 1) = S P v := by
  by_cases h : v % 2 = 1
  · rw [show 2 * ((v - 1) / 2) + 1 = v by omega]
  · rw [show v = 2 * ((v - 1) / 2) + 2 by omega, S_even P hP]
    congr 1
    omega

/-- Below the stage, the stage does not matter. -/
theorem S_stable {P P' v : Nat} (h : v ≤ P) (h' : v ≤ P') : S P v = S P' v := by
  apply count_congr
  intro n _ hn
  constructor
  · rintro ⟨h5, hm⟩
    exact ⟨h5, fun ⟨d, hd2, _, hdn, hdvd⟩ => hm ⟨d, hd2, by omega, hdn, hdvd⟩⟩
  · rintro ⟨h5, hm⟩
    exact ⟨h5, fun ⟨d, hd2, _, hdn, hdvd⟩ => hm ⟨d, hd2, by omega, hdn, hdvd⟩⟩

/-- A composite stage changes nothing. -/
theorem S_composite (p : Nat) (hp : 2 ≤ p) (hnp : ¬ Prime p) (v : Nat) : S (p + 1) v = S p v := by
  apply count_congr
  intro n _ _
  have hm := (marked_self_iff_not_prime p hp).mpr hnp
  simp only [Surv, composite_skip p n hm]

/-- A stage changes nothing below its square. -/
theorem S_small (p : Nat) (hp : 2 ≤ p) (v : Nat) (hv : v < p * p) : S (p + 1) v = S p v := by
  apply count_congr
  intro n _ hn
  have key : Marked (p + 1) n ↔ Marked p n := by
    rw [marked_step p n hp]
    constructor
    · rintro (h | ⟨hpn, ⟨m, rfl⟩⟩)
      · exact h
      · have hm2 : 2 ≤ m := by
          apply Decidable.byContradiction
          intro h
          have : m = 0 ∨ m = 1 := by omega
          rcases this with h | h <;> subst h <;> simp at hpn
        have hmp : m < p := Nat.lt_of_mul_lt_mul_left (a := p) (by omega)
        have : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp
        exact ⟨m, hm2, hmp, by omega, Nat.dvd_mul_left m p⟩
    · exact Or.inl
  simp only [Surv, key]

theorem coprime_of_lt_prime {d p : Nat} (hp : Prime p) (hd : 1 ≤ d) (hdp : d < p) :
    Nat.Coprime d p := by
  have hg1 : Nat.gcd d p ∣ d := Nat.gcd_dvd_left d p
  have hg2 : Nat.gcd d p ∣ p := Nat.gcd_dvd_right d p
  have hle : Nat.gcd d p ≤ d := Nat.le_of_dvd (by omega) hg1
  have hpos : 0 < Nat.gcd d p := Nat.gcd_pos_of_pos_left p (by omega)
  apply Decidable.byContradiction
  intro hne
  have h2 : 2 ≤ Nat.gcd d p := by
    have : Nat.gcd d p ≠ 1 := hne
    omega
  exact ((prime_iff_no_proper_divisor p).mp hp).2 _ h2 (by omega) hg2

/-- The survivors of stage `p` that stage `p + 1` removes are `p` times the survivors that are at
least `p`. -/
theorem removed_iff (p : Nat) (hp : Prime p) (h5 : 5 ≤ p) (n : Nat) :
    (Surv p n ∧ p < n ∧ p ∣ n) ↔ (p ∣ n ∧ (p - 1 < n / p ∧ Surv p (n / p))) := by
  constructor
  · rintro ⟨⟨h5n, hnm⟩, hpn, ⟨m, rfl⟩⟩
    rw [Nat.mul_div_cancel_left m (by omega : 0 < p)]
    have hm2 : 2 ≤ m := by
      apply Decidable.byContradiction
      intro h
      have : m = 0 ∨ m = 1 := by omega
      rcases this with h | h <;> subst h <;> simp at hpn
    have hlt : m < p * m := by
      have : 2 * m ≤ p * m := Nat.mul_le_mul_right m (by omega)
      omega
    have hmp : p ≤ m := by
      apply Decidable.byContradiction
      intro h
      exact hnm ⟨m, hm2, by omega, hlt, Nat.dvd_mul_left m p⟩
    refine ⟨Nat.dvd_mul_right p m, by omega, by omega, ?_⟩
    rintro ⟨d, hd2, hdp, hdm, hdvd⟩
    exact hnm ⟨d, hd2, hdp, by omega, Nat.dvd_trans hdvd (Nat.dvd_mul_left m p)⟩
  · rintro ⟨⟨m, rfl⟩, hpm, h5m, hnm⟩
    rw [Nat.mul_div_cancel_left m (by omega : 0 < p)] at hpm h5m hnm
    have hlt : p < p * m := by
      have : p * 2 ≤ p * m := Nat.mul_le_mul_left p (by omega)
      omega
    refine ⟨⟨by omega, ?_⟩, hlt, Nat.dvd_mul_right p m⟩
    rintro ⟨d, hd2, hdp, _, hdvd⟩
    have hdm : d ∣ m := (coprime_of_lt_prime hp (by omega) hdp).dvd_of_dvd_mul_left hdvd
    exact hnm ⟨d, hd2, hdp, by omega, hdm⟩

/-- **The stage update.** For a prime `p` and `v ≥ p * p`, stage `p + 1` removes from `S p v` the
multiples `p * m` with `m` a survivor in `[p, v / p]`. -/
theorem S_prime_step (p : Nat) (hp : Prime p) (h5 : 5 ≤ p) (v : Nat) (hv : p ≤ v / p) :
    S p v = S (p + 1) v + (S p (v / p) - S p (p - 1)) := by
  have h1 := count_split (Surv p) (fun n => p < n ∧ p ∣ n) v
  have h2 : count (fun n => Surv p n ∧ ¬ (p < n ∧ p ∣ n)) v = S (p + 1) v := by
    apply count_congr
    intro n _ _
    simp only [Surv, marked_step p n (by omega : 2 ≤ p)]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩
      exact ⟨a, fun h => h.elim b c⟩
    · rintro ⟨a, b⟩
      exact ⟨⟨a, fun h => b (Or.inl h)⟩, fun h => b (Or.inr h)⟩
  have h3 : count (fun n => Surv p n ∧ (p < n ∧ p ∣ n)) v =
      count (fun m => p - 1 < m ∧ Surv p m) (v / p) := by
    rw [← count_mul (fun m => p - 1 < m ∧ Surv p m) p (by omega) v]
    apply count_congr
    intro n _ _
    exact removed_iff p hp h5 n
  have h4 := count_from (Surv p) (p - 1) (v := v / p) (by omega)
  have h5' : S p (p - 1) ≤ S p (v / p) := S_mono p (by omega)
  simp only [S] at *
  omega

/-- The primality test: the entry at `p` exceeds the entry at `p - 1` exactly for a prime. -/
theorem S_self (p : Nat) (h5 : 5 ≤ p) : S p p = S p (p - 1) + if Prime p then 1 else 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [S, count_succ, ← S, Nat.add_sub_cancel]
  have : Surv (q + 1) (q + 1) ↔ Prime (q + 1) := by
    simp only [Surv, marked_self_iff_not_prime (q + 1) (by omega), Decidable.not_not]
    exact ⟨fun h => h.2, fun h => ⟨h5, h⟩⟩
  simp only [this]

theorem not_prime_even (p : Nat) (h : 3 ≤ p) (hodd : p % 2 = 1) : ¬ Prime (p + 1) := by
  intro hp
  exact ((prime_iff_no_proper_divisor (p + 1)).mp hp).2 2 (by omega) (by omega) (by omega)

/-- After the stage of an odd `p`, the even stage `p + 1` changes nothing. -/
theorem S_add_two (p : Nat) (h : 3 ≤ p) (hodd : p % 2 = 1) (v : Nat) : S (p + 2) v = S (p + 1) v :=
  S_composite (p + 1) (by omega) (not_prime_even p h hodd) v

/-- The running count `c = S p (p - 1)` of the primes in `[5, p - 1]` moves to the next odd `p`. -/
theorem S_next_c (p : Nat) (h5 : 5 ≤ p) (hodd : p % 2 = 1) :
    S (p + 2) (p + 1) = S p (p - 1) + if Prime p then 1 else 0 := by
  have h1 : S (p + 2) (p + 1) = S (p + 2) p := by
    obtain ⟨j, rfl⟩ : ∃ j, p = 2 * j + 1 := ⟨p / 2, by omega⟩
    exact S_even _ (by omega) j
  have h2 : S (p + 2) p = S p p := S_stable (by omega) (by omega)
  rw [h1, h2, S_self p h5]

/-- Below the square of the stage, a survivor is a prime. -/
theorem unmarked_iff_prime (P n : Nat) (hn : 2 ≤ n) (hP : n < P * P) :
    ¬ Marked P n ↔ Prime n := by
  constructor
  · intro hm
    by_cases hex : ∃ d, 2 ≤ d ∧ d < n ∧ d ∣ n
    · exfalso
      obtain ⟨d, hd2, hdn, ⟨e, rfl⟩⟩ := hex
      by_cases hdP : d < P
      · exact hm ⟨d, hd2, hdP, hdn, Nat.dvd_mul_right d e⟩
      · have he2 : 2 ≤ e := by
          apply Decidable.byContradiction
          intro h
          have : e = 0 ∨ e = 1 := by omega
          rcases this with h | h <;> subst h <;> simp at hdn
        have heP : e < P := by
          apply Decidable.byContradiction
          intro h
          have := Nat.mul_le_mul (show P ≤ d by omega) (show P ≤ e by omega)
          omega
        have : 2 * e ≤ d * e := Nat.mul_le_mul_right e hd2
        exact hm ⟨e, he2, heP, by omega, Nat.dvd_mul_left e d⟩
    · exact (prime_iff_no_proper_divisor n).mpr
        ⟨hn, fun d h1 h2 h3 => hex ⟨d, h1, h2, h3⟩⟩
  · rintro hp ⟨d, hd2, _, hdn, hdvd⟩
    exact ((prime_iff_no_proper_divisor n).mp hp).2 d hd2 hdn hdvd

theorem countPrimes_eq_count (m : Nat) :
    countPrimes (m + 4) = count (fun n => 5 ≤ n ∧ Prime n) (m + 4) + 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show m + 1 + 4 = (m + 4) + 1 by omega, count_succ, countPrimes, ih]
    by_cases hp : Prime (m + 4 + 1) <;> simp [hp] <;> omega

/-- **The answer.** Once the stage has passed `√N`, the survivors in `[5, N]` are the primes
there, and the primes 2 and 3 are the other two. -/
theorem countPrimes_eq (N P : Nat) (hN : 3 ≤ N) (hP : N < P * P) : countPrimes N = S P N + 2 := by
  have hS : S P N = count (fun n => 5 ≤ n ∧ Prime n) N := by
    apply count_congr
    intro n _ hn
    by_cases h5 : 5 ≤ n
    · simp only [Surv, unmarked_iff_prime P n (by omega) (by omega)]
    · simp [Surv, h5]
  by_cases h4 : 4 ≤ N
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 4 := ⟨N - 4, by omega⟩
    rw [hS, countPrimes_eq_count]
  · have h3 : N = 3 := by omega
    subst h3
    rw [hS]
    decide

/-! ## The integer square root, which sizes the machine's memory -/

/-- `⌊√n⌋`, as Python's `math.isqrt` computes it. -/
def isqrt (n : Nat) : Nat :=
  if n < 4 then (if n = 0 then 0 else 1)
  else
    let s := 2 * isqrt (n / 4)
    if (s + 1) * (s + 1) ≤ n then s + 1 else s
termination_by n
decreasing_by omega

theorem isqrt_spec (n : Nat) : isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [isqrt]
    by_cases h4 : n < 4
    · simp only [h4, ite_true]
      by_cases h0 : n = 0
      · simp [h0]
      · simp only [h0, ite_false]
        omega
    · simp only [h4, ite_false]
      obtain ⟨h1, h2⟩ := ih (n / 4) (by omega)
      generalize isqrt (n / 4) = t at h1 h2
      have e1 : (2 * t) * (2 * t) = 4 * (t * t) := by grind
      have e2 : (2 * t + 1 + 1) * (2 * t + 1 + 1) = 4 * ((t + 1) * (t + 1)) := by grind
      by_cases hs : (2 * t + 1) * (2 * t + 1) ≤ n
      · rw [ite_eq_left hs]
        exact ⟨hs, by omega⟩
      · rw [ite_eq_right hs]
        exact ⟨by omega, by omega⟩

/-- Every `v` with `v * v ≤ n` is at most `isqrt n`, so its slot is inside memory. -/
theorem le_isqrt {v n : Nat} (h : v * v ≤ n) : v ≤ isqrt n := by
  apply Decidable.byContradiction
  intro hlt
  have := Nat.mul_le_mul (show isqrt n + 1 ≤ v by omega) (show isqrt n + 1 ≤ v by omega)
  have := (isqrt_spec n).2
  omega

/-! ## Arithmetic of the loop bounds -/

theorem odd_mul {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) : (a * b) % 2 = 1 := by
  rw [Nat.mul_mod, ha, hb]

/-- `((N - d) >> 1) / d = (N / d - 1) >> 1`: the small-table index of `N / d` from a division by
`d` alone. -/
theorem half_div (N d : Nat) (h : d ≤ N) : (N - d) / 2 / d = (N / d - 1) / 2 := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm 2 d, ← Nat.div_div_eq_div_mul]
  congr 1
  have := Nat.sub_mul_div_of_le N d 1 (by omega)
  simpa using this

theorem scaled_half_div (N d : Nat) (h : d ≤ N) :
    8 * ((N - d) / 2) / (8 * d) = (N / d - 1) / 2 := by
  rw [Nat.mul_div_mul_left _ _ (by omega : 0 < 8), half_div N d h]

theorem scaled_half_div' (v p : Nat) (h : p ≤ v) :
    (8 * v - 8 * p) / (16 * p) = (v / p - 1) / 2 := by
  rw [show 8 * v - 8 * p = 8 * (v - p) by omega, show 16 * p = 8 * (2 * p) by omega,
    Nat.mul_div_mul_left _ _ (by omega : 0 < 8), ← Nat.div_div_eq_div_mul, half_div v p h]

/-- The last `k` whose entry `large[k]` stage `p` must update. -/
def kmax (N r p : Nat) : Nat := if p * p ≤ r then r else N / (p * p)

theorem kmax_iff {N r p k : Nat} (hp : 0 < p) (hr : r * r ≤ N) (hk : k ≤ r) :
    k ≤ kmax N r p ↔ k * (p * p) ≤ N := by
  unfold kmax
  split
  · rename_i h
    exact ⟨fun _ => Nat.le_trans (Nat.mul_le_mul hk h) hr, fun _ => hk⟩
  · exact Nat.le_div_iff_mul_le (Nat.mul_pos hp hp)

theorem kmax_le {N r p k : Nat} (hp : 0 < p) (hpodd : p % 2 = 1) (hrodd : r % 2 = 1)
    (hhi : N < (r + 2) * (r + 2)) (hkodd : k % 2 = 1) (hk : k ≤ kmax N r p) : k ≤ r := by
  unfold kmax at hk
  split at hk
  · exact hk
  · have h1 := (Nat.le_div_iff_mul_le (Nat.mul_pos hp hp)).mp hk
    have hpp := odd_mul hpodd hpodd
    apply Decidable.byContradiction
    intro hc
    have := Nat.mul_le_mul (show r + 2 ≤ k by omega) (show r + 2 ≤ p * p by omega)
    omega

/-- Once `kmax < p + 2`, stage `p` updates no table entry. -/
theorem kmax_tail {N r p : Nat} (h5 : 5 ≤ p) (h : kmax N r p < p + 2) :
    r < p * p ∧ N / (p * p) < p + 2 := by
  unfold kmax at h
  split at h
  · have : 5 * p ≤ p * p := Nat.mul_le_mul_right p h5
    omega
  · exact ⟨by omega, h⟩

theorem kmax_mul_le {N r p : Nat} (hp : 0 < p) (hpr : p ≤ r) (hr : r * r ≤ N) :
    kmax N r p * p ≤ N := by
  unfold kmax
  split
  · exact Nat.le_trans (Nat.mul_le_mul_left r hpr) hr
  · have h1 : N / (p * p) * p ≤ N / (p * p) * (p * p) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left p hp)
    exact Nat.le_trans h1 (Nat.div_mul_le_self N (p * p))

/-- Where the first inner loop stops, the second may start. -/
theorem first_exit {N r p k : Nat} (hp : 1 ≤ p) (hk : k * p ≤ r) (hpp : (p + 2) * p ≤ r)
    (hr : r * r ≤ N) : (k + 2) * (p * p) ≤ N := by
  have e : (k + 2) * (p * p) = (k * p) * p + 2 * (p * p) := by grind
  have h1 : (k * p) * p ≤ r * p := Nat.mul_le_mul_right p hk
  have h2 : p * p ≤ (p + 2) * p := Nat.mul_le_mul_right p (by omega)
  have h3 : p + 2 ≤ (p + 2) * p := Nat.le_mul_of_pos_right _ hp
  have h4 : r * (p + 2) ≤ r * r := Nat.mul_le_mul_left r (by omega)
  have e2 : r * (p + 2) = r * p + 2 * r := by grind
  omega

theorem div_lt_sq_of_not {N p k : Nat} (hk : 0 < k) (h : ¬ k * (p * p) ≤ N) : N / k < p * p := by
  rw [Nat.div_lt_iff_lt_mul hk, Nat.mul_comm]
  omega

theorem div_lt_sq {N p k : Nat} (hp : 0 < p) (h : N / (p * p) < k) : N / k < p * p := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hp hp)).mp h
  exact div_lt_sq_of_not hk (by omega)

theorem tail_next {N p : Nat} (hp : 0 < p) (h : N / (p * p) < p + 2) :
    N / ((p + 2) * (p + 2)) < p + 2 + 2 := by
  have h1 : p * p ≤ (p + 2) * (p + 2) := Nat.mul_le_mul (by omega) (by omega)
  have := Nat.div_le_div_left (a := N) h1 (Nat.mul_pos hp hp)
  omega

theorem r_lt_of_sq {N r : Nat} (h : r * r ≤ N) (hN : N < 100000000000) : r < 316228 := by
  apply Decidable.byContradiction
  intro hc
  have := Nat.mul_le_mul (show 316228 ≤ r by omega) (show 316228 ≤ r by omega)
  omega

end TinyFive.LucyMath
