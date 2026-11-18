import OddSieveMath

/-! Arithmetic specification of the mod-six flag wheel. -/
namespace TinyFive.OddWheelMath
open CountingPrimes OddSieveMath

/-- Flag `i` represents 1, 5, 7, 11, ... . -/
def value (i : Nat) : Nat := if i % 2 = 0 then 3*i+1 else 3*i+2
/-- Number of represented values at most `n`. -/
def E (n : Nat) : Nat := (n+5)/6 + (n+1)/6

theorem value_even (k : Nat) : value (2*k) = 6*k+1 := by
  simp [value]; omega

theorem value_odd (k : Nat) : value (2*k+1) = 6*k+5 := by
  simp [value]; omega

theorem value_mod (i : Nat) : value i % 6 = 1 ∨ value i % 6 = 5 := by
  unfold value
  split <;> omega

theorem value_index (i : Nat) : value i / 3 = i := by
  unfold value
  split <;> omega

theorem value_lt_iff (n i : Nat) : i < E n ↔ value i ≤ n := by
  unfold E value
  split <;> omega

theorem E_formula (n : Nat) : E n = ((n+3)/2*2+2)/3-1 := by
  unfold E
  omega

theorem value_of_wheel (n : Nat) (h : n % 6 = 1 ∨ n % 6 = 5) :
    value (n/3) = n := by
  unfold value
  rcases h with h | h <;> split <;> omega

theorem value_stride (i p : Nat) : value (i+2*p) = value i + 6*p := by
  unfold value
  split <;> split <;> omega

theorem value_stride_many (i p j : Nat) :
    value (i+2*p*j) = value i+6*p*j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : i+2*p*(j+1) = (i+2*p*j)+2*p := by simp [Nat.mul_add, Nat.add_assoc]
    rw [h, value_stride, ih]
    simp [Nat.mul_add, Nat.add_assoc]

/-- Each index-stride marks a genuine multiple from either starting multiplier. -/
theorem progression (start p m j : Nat) (h : value start = p*m) :
    value (start+2*p*j) = p*(m+6*j) := by
  rw [value_stride_many, h]
  grind

theorem E_machine (n : Nat) (hn : 1 ≤ n) :
    E n = (2*((n+3)/2)-1)/3 := by
  unfold E
  omega

/-- A previously processed wheel divisor has marked a number, beginning at its square. -/
def WM (p i : Nat) : Prop := ∃ d, 5 ≤ d ∧ d < p ∧ d*d ≤ value i ∧ d ∣ value i

theorem wm_zero (p : Nat) : ¬ WM p 0 := by
  rintro ⟨d, hd, _, hsq, _⟩
  have := Nat.mul_le_mul_left d hd
  simp [value] at hsq
  omega

theorem wm_skip (p q i : Nat) (hq : value q = p) (hm : WM p q) :
    WM (p+1) i ↔ WM p i := by
  constructor
  · rintro ⟨d, hd, hdp, hsq, hdiv⟩
    by_cases h : d < p
    · exact ⟨d, hd, h, hsq, hdiv⟩
    · have : d = p := by omega
      subst d
      obtain ⟨e, he, hep, heq, hed⟩ := hm
      rw [hq] at hed
      have hpp : p ≤ p*p := Nat.le_mul_self p
      exact ⟨e, he, hep, by omega, Nat.dvd_trans hed hdiv⟩
  · rintro ⟨d, hd, hdp, hsq, hdiv⟩
    exact ⟨d, hd, by omega, hsq, hdiv⟩

theorem wm_step (p i : Nat) (hp : 5 ≤ p) :
    WM (p+1) i ↔ WM p i ∨ (p*p ≤ value i ∧ p ∣ value i) := by
  constructor
  · rintro ⟨d, hd, hdp, hs, hv⟩
    by_cases h : d < p
    · exact Or.inl ⟨d, hd, h, hs, hv⟩
    · have : d = p := by omega
      subst d
      exact Or.inr ⟨hs, hv⟩
  · rintro (⟨d, hd, hdp, hs, hv⟩ | ⟨hs, hv⟩)
    · exact ⟨d, hd, by omega, hs, hv⟩
    · exact ⟨p, hp, by omega, hs, hv⟩

/-- A divisor of a wheel value is itself coprime to six. -/
theorem divisor_wheel (i d : Nat) (hd : d ∣ value i) :
    d % 6 = 1 ∨ d % 6 = 5 := by
  have hm := value_mod i
  have h2 : ¬ 2 ∣ value i := by intro h; have := Nat.mod_eq_zero_of_dvd h; omega
  have h3 : ¬ 3 ∣ value i := by intro h; have := Nat.mod_eq_zero_of_dvd h; omega
  have h2d : ¬ 2 ∣ d := fun h => h2 (Nat.dvd_trans h hd)
  have h3d : ¬ 3 ∣ d := fun h => h3 (Nat.dvd_trans h hd)
  have h2m : d % 2 ≠ 0 := by intro h; exact h2d (Nat.dvd_of_mod_eq_zero h)
  have h3m : d % 3 ≠ 0 := by intro h; exact h3d (Nat.dvd_of_mod_eq_zero h)
  omega

/-- Advance over the non-wheel divisors between consecutive wheel candidates. -/
theorem wm_wheel_step (p gap i : Nat) (hp : 5 ≤ p)
    (hphase : (p % 6 = 5 ∧ gap = 2) ∨ (p % 6 = 1 ∧ gap = 4)) :
    WM (p+gap) i ↔ WM p i ∨ (p*p ≤ value i ∧ p ∣ value i) := by
  constructor
  · rintro ⟨d, hd, hdp, hs, hv⟩
    by_cases h : d < p
    · exact Or.inl ⟨d, hd, h, hs, hv⟩
    · have hm := divisor_wheel i d hv
      have : d = p := by rcases hphase with hphase | hphase <;> omega
      subst d
      exact Or.inr ⟨hs, hv⟩
  · rintro (⟨d, hd, hdp, hs, hv⟩ | ⟨hs, hv⟩)
    · exact ⟨d, hd, by rcases hphase with h | h <;> omega, hs, hv⟩
    · exact ⟨p, hp, by rcases hphase with h | h <;> omega, hs, hv⟩

theorem wm_wheel_skip (p gap q i : Nat) (hp : 5 ≤ p)
    (hphase : (p % 6 = 5 ∧ gap = 2) ∨ (p % 6 = 1 ∧ gap = 4))
    (hq : value q = p) (hm : WM p q) : WM (p+gap) i ↔ WM p i := by
  rw [wm_wheel_step p gap i hp hphase, ← wm_step p i hp, wm_skip p q i hq hm]

theorem wm_initial (i : Nat) : ¬ WM 5 i := by
  rintro ⟨d, hd, hdp, _⟩
  omega

/-- Past the square root, the marked wheel flags are exactly composites (apart from 1). -/
theorem wm_final (p i : Nat) (hi : 1 ≤ i) (hlt : value i < p*p) :
    WM p i ↔ ¬ Prime (value i) := by
  have hv : 5 ≤ value i := by unfold value; split <;> omega
  have hm := value_mod i
  have hnot2 : ¬ 2 ∣ value i := by intro h; have := Nat.mod_eq_zero_of_dvd h; omega
  have hnot3 : ¬ 3 ∣ value i := by intro h; have := Nat.mod_eq_zero_of_dvd h; omega
  constructor
  · rintro ⟨d, hd, _, hdd, hdvd⟩ hprime
    have : d*5 ≤ d*d := Nat.mul_le_mul_left _ hd
    exact ((prime_iff_no_proper_divisor _).mp hprime).2 d (by omega) (by omega) hdvd
  · intro hnp
    have hex : ∃ d, 2 ≤ d ∧ d < value i ∧ d ∣ value i := by
      apply Classical.byContradiction
      intro hno
      exact hnp ((prime_iff_no_proper_divisor _).mpr
        ⟨by omega, fun d h2 hl hd => hno ⟨d, h2, hl, hd⟩⟩)
    obtain ⟨d, hd2, hdm, hdvd⟩ := hex
    have hq : ∃ q, 2 ≤ q ∧ q*q ≤ value i ∧ q ∣ value i := by
      by_cases hdd : d*d ≤ value i
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
    have hq5 : 5 ≤ q := by
      apply Classical.byContradiction
      intro hc
      have : q = 2 ∨ q = 3 ∨ q = 4 := by omega
      rcases this with rfl | rfl | rfl
      · exact hnot2 hqdvd
      · exact hnot3 hqdvd
      · exact hnot2 (Nat.dvd_trans (by decide : 2 ∣ 4) hqdvd)
    have hqp : q < p := by
      apply Classical.byContradiction
      intro hc
      have : p*p ≤ q*q := Nat.mul_le_mul (by omega) (by omega)
      omega
    exact ⟨q, hq5, hqp, hqq, hqdvd⟩

/-- Square indices for the two wheel phases. -/
def sqMinus (k : Nat) : Nat := 12*k*k-4*k
def sqPlus (k : Nat) : Nat := 12*k*k+4*k


theorem sqPlus_value (k : Nat) : value (sqPlus k) = (6*k+1)*(6*k+1) := by
  have he : sqPlus k = 2*(6*k*k+2*k) := by unfold sqPlus; grind
  rw [he, value_even]
  grind

/-- A composite flag, excluding the flag for 1. -/
def compBit (i : Nat) : Nat := if 1 ≤ i ∧ ¬ Prime (value i) then 1 else 0

private theorem count_aux (n : Nat) :
    countPrimes (n+3) + csum compBit (E (n+3)) = E (n+3)+1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n+1+3 = (n+3)+1 by omega, countPrimes]
    by_cases hw : (n+4)%6 = 1 ∨ (n+4)%6 = 5
    · have he : E (n+4) = E (n+3)+1 := by unfold E; omega
      have hv : value (E (n+3)) = n+4 := by
        unfold value E
        rcases hw with h | h <;> split <;> omega
      have hi : 1 ≤ E (n+3) := by unfold E; omega
      rw [show n+3+1 = n+4 by omega, he, csum_succ]
      simp only [compBit, hv, hi, true_and]
      by_cases hp : Prime (n+4) <;> simp [hp] <;> omega
    · have he : E (n+4) = E (n+3) := by unfold E; omega
      have hp : ¬ Prime (n+4) := by
        intro hp
        have hd : 2 ∣ n+4 ∨ 3 ∣ n+4 := by
          rcases Nat.mod_lt (n+4) (by decide : 0 < 6) with h
          omega
        rcases hd with hd | hd
        · exact ((prime_iff_no_proper_divisor _).mp hp).2 2 (by omega) (by omega) hd
        · exact ((prime_iff_no_proper_divisor _).mp hp).2 3 (by omega) (by omega) hd
      rw [show n+3+1 = n+4 by omega, he]
      simp [hp]
      omega

theorem count_identity (n : Nat) (hn : 3 ≤ n) :
    countPrimes n + csum compBit (E n) = E n+1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm] using count_aux k

theorem final_bits (K p i : Nat) (hK : ∀ j, j < K → value j < p*p) (hi : i < K) :
    bit K (WM p) i = compBit i := by
  by_cases h0 : 1 ≤ i
  · have hiff := wm_final p i h0 (hK i hi)
    by_cases hp : Prime (value i)
    · rw [bit_neg (fun hc => hiff.mp hc.2 hp)]
      simp [compBit, hp]
    · rw [bit_pos hi (hiff.mpr hp)]
      simp [compBit, hp, h0]
  · have : i = 0 := by omega
    subst i
    rw [bit_neg (fun hc => wm_zero _ hc.2)]
    simp [compBit]

end TinyFive.OddWheelMath
