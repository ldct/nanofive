import GrumpyBinary.Update
import GrumpyBinary.SkipMath

/-! The arithmetic of one sieve round at a prime `p` with `p² ≤ v`: the facts `compact_loop`
and `upd_loop` take as hypotheses, from the counting lemmas of `GrumpyOdd` and `GrumpyTables`. -/
namespace TinyFive.GrumpyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon

theorem alive_odd {p d : Nat} (hp : 3 ≤ p) (h : Alive p d) : d % 2 = 1 := by
  apply Decidable.byContradiction
  intro hd
  exact h.2 ⟨2, Nat.le_refl 2, by omega, by have := h.1; omega, Nat.dvd_of_mod_eq_zero (by omega)⟩

theorem rough_sorted (p v : Nat) (hp : 3 ≤ p) : (1 :: roughList p v).Pairwise (· < ·) := by
  rw [List.pairwise_cons]
  refine ⟨fun a ha => by have := (mem_rough.mp ha).1; omega, ?_⟩
  exact (List.pairwise_lt_range' (s := p) (n := v + 1 - p)).filter _

theorem C_le (p x : Nat) : C p x ≤ x := count_le _ x

theorem C_mono (p : Nat) {x y : Nat} (h : x ≤ y) : C p x ≤ C p y := count_mono _ h

theorem C_odd (p x : Nat) (hp : 3 ≤ p) (hx : x % 2 = 1) : C p (2 * (x / 2) + 1) = C p x := by
  rw [show 2 * (x / 2) + 1 = x by omega]

/-- `N / x ≥ v` for `x ≤ v = isqrt N`. -/
theorem div_ge_isqrt (N x : Nat) (hx : 1 ≤ x) (hxv : x ≤ isqrt N) : isqrt N ≤ N / x := by
  have hv := (isqrt_spec N).1
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  exact Nat.le_trans (Nat.mul_le_mul_left _ hxv) hv

theorem cmath (N p : Nat) (hN : N < 100000000000) (hp3 : 3 ≤ p) (hprime : Prime p)
    (hpp : p * p ≤ isqrt N) :
    CMath (1 :: roughList p (isqrt N)) (fun d => d % p != 0) (fun d => C p (N / d))
      (fun d => C (p + 1) (N / d)) (fun d => C p (N / d / p)) (fun i => C p (2 * i + 1))
      (fun i => if SkipMarked (p + 2) i then 1 else 0) N (isqrt N) p (C p (p - 1)) := by
  have hv := isqrt_spec N
  have hvb := r_lt_of_sq hv.1 hN
  have hpv : p ≤ isqrt N := Nat.le_trans (Nat.le_mul_of_pos_right p (by omega)) hpp
  have hpo : p % 2 = 1 := by
    apply Decidable.byContradiction; intro h
    exact even_not_prime p (by omega) (by omega) hprime
  have hpp3 := Nat.mul_le_mul_left p hp3
  have hmem : ∀ d ∈ 1 :: roughList p (isqrt N), d = 1 ∨ (p ≤ d ∧ d ≤ isqrt N ∧ Alive p d) := by
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Or.inl rfl
    · exact Or.inr (mem_rough.mp hd)
  have hdodd : ∀ d ∈ 1 :: roughList p (isqrt N), d % 2 = 1 := by
    intro d hd
    rcases hmem d hd with rfl | ⟨_, _, ha⟩
    · rfl
    · exact alive_odd hp3 ha
  have hdb : ∀ d ∈ 1 :: roughList p (isqrt N), 1 ≤ d ∧ d ≤ isqrt N := by
    intro d hd
    rcases hmem d hd with rfl | ⟨h1, h2, _⟩
    · omega
    · omega
  have hNd : ∀ d ∈ 1 :: roughList p (isqrt N), p ≤ N / d / p := by
    intro d hd
    have := div_ge_isqrt N d (hdb d hd).1 (hdb d hd).2
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    exact Nat.le_trans hpp this
  refine ⟨hdb, rough_sorted p _ hp3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hp3⟩
  · -- skip
    intro d hd
    have := skip_rough p (isqrt N) d hp3 hpo hprime hd
    by_cases h : d % p = 0
    · rw [if_pos (this.mpr h)]; simp [h]
    · rw [if_neg (fun h' => h (this.mp h'))]; simp [h]
  · -- small
    intro d hd hkeep hdp
    have hdpo : (d * p) % 2 = 1 := odd_mul (hdodd d hd) hpo
    have hd' : d ∈ 1 :: roughList (p + 1) (isqrt N) := by
      rw [rough_next hp3 hpv]
      rcases List.mem_cons.mp hd with rfl | hd
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hd, hkeep⟩)
    have hpr := product_rough hp3 hprime hd' hdp
    have hd1 := (hdb d hd).1
    have hdpp := Nat.mul_le_mul_left d hp3
    have := Nat.le_mul_of_pos_left p (show 0 < d by omega)
    refine ⟨?_, by omega, ?_, ?_⟩
    · rw [C_odd p _ hp3 hdpo]
      exact C_mono p (by omega)
    · rw [C_odd p _ hp3 hdpo]
      exact rough_rank hp3 hpr
    · rw [Nat.div_div_eq_div_mul]
  · -- large
    intro d hd _ hdp
    have hd1 := hdb d hd
    have hdpN : d * p ≤ isqrt N * isqrt N := Nat.mul_le_mul hd1.2 hpv
    have hpos : 0 < d * p := Nat.mul_pos (by omega) (by omega)
    have hq : N / (d * p) ≤ isqrt N := by
      have : N < (d * p) * (isqrt N + 1) := by
        have := Nat.mul_le_mul_right (isqrt N + 1) (show isqrt N + 1 ≤ d * p by omega)
        omega
      have := (Nat.div_lt_iff_lt_mul hpos).mpr (by rw [Nat.mul_comm] at this; exact this)
      omega
    have hq1 : 1 ≤ N / (d * p) := Nat.div_pos (by omega) hpos
    refine ⟨by omega, hq1, hq, ?_⟩
    rw [C_odd_index p hp3 _ hq1, Nat.div_div_eq_div_mul]
  · -- new
    intro d hd _
    have hd1 := hdb d hd
    have hpq := hNd d hd
    have h1 : C p (N / d / p) ≤ C p (N / d) := C_mono p (Nat.div_le_self _ _)
    have h2 : C p (p - 1) ≤ C p (N / d / p) := C_mono p (by omega)
    have h3 := update_eq p (N / d) hp3 hprime
    refine ⟨h1, ?_⟩
    omega
  · intro d hd
    have := C_le p (N / d); have := Nat.div_le_self N d
    omega
  · intro d hd
    have := C_le p (N / d / p); have := Nat.div_le_self (N / d) p; have := Nat.div_le_self N d
    omega
  · intro i hi
    have := C_le p (2 * i + 1)
    omega

/-- The `smalls` update facts of `upd_loop`. -/
theorem upd_math (N p : Nat) (hp3 : 3 ≤ p) (hprime : Prime p) (hpo : p % 2 = 1) (j : Nat) :
    ∀ j', j' % 2 = 1 → p ≤ j' → j' ≤ j → ∀ u, j' * p / 2 ≤ u → u < (j' + 2) * p / 2 →
      u < (isqrt N + 1) / 2 →
      C p (p - 1) ≤ C p (2 * (j' / 2) + 1) ∧
      C p (2 * (j' / 2) + 1) - C p (p - 1) ≤ C p (2 * u + 1) ∧
      C (p + 1) (2 * u + 1) = C p (2 * u + 1) - (C p (2 * (j' / 2) + 1) - C p (p - 1)) := by
  intro j' hj' hpj' _ u h1 h2 _
  have hjpo : (j' * p) % 2 = 1 := odd_mul hj' hpo
  have hjpo2 : ((j' + 2) * p) % 2 = 1 := odd_mul (by omega) hpo
  have hle : (j' + 2) * p = j' * p + 2 * p := by rw [Nat.add_mul, Nat.mul_comm 2 p]
  have hx1 : j' * p ≤ 2 * u + 1 := by omega
  have hx2 : 2 * u + 1 < (j' + 2) * p := by omega
  have hq1 : j' ≤ (2 * u + 1) / p := (Nat.le_div_iff_mul_le (by omega)).mpr hx1
  have hq2 : (2 * u + 1) / p < j' + 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hx2
  have hjj := Nat.mul_le_mul_left j' (show 1 ≤ p by omega)
  rw [C_odd p _ hp3 hj']
  have hc : C p ((2 * u + 1) / p) = C p j' := by
    rw [← C_odd_index p hp3 _ (by omega)]
    congr 1; omega
  have h3 := update_eq p (2 * u + 1) hp3 hprime
  rw [hc] at h3
  refine ⟨C_mono p (by omega), ?_, h3.symm⟩
  have := C_mono p (show j' ≤ 2 * u + 1 by omega)
  omega

theorem upd_math0 (p : Nat) (hp3 : 3 ≤ p) (hpo : p % 2 = 1) (u : Nat) (hu : u < p * p / 2) :
    C (p + 1) (2 * u + 1) = C p (2 * u + 1) := by
  have : (p * p) % 2 = 1 := odd_mul hpo hpo
  exact C_small p _ hp3 (by omega)

end TinyFive.GrumpyBinary
