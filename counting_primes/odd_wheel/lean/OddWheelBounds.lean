import OddWheelMath
import CountingPrimesOddWheelMachine

namespace TinyFive.OddWheelMath
open CountingPrimesOddWheel

theorem E_le_div3 (n : Nat) : E n ≤ n/3+1 := by unfold E; omega

/-- A paired minus iteration, including a bottom-tested first iteration, fits
provided its first index is at most three candidate widths beyond the input. -/
theorem minus_capacity (n p a b : Nat)
    (hp : p ≤ Nat.sqrt n + 11)
    (ha : a ≤ E n + 3*p + 7)
    (hb : 3*b ≤ 3*a + 2*p + 2) :
    512+a < memSize n ∧ 512+b < memSize n := by
  have he := E_le_div3 n
  unfold memSize
  omega

/-- A paired plus iteration fits, allowing the unconditional initial visit. -/
theorem plus_capacity (n p a b : Nat)
    (hp : p ≤ Nat.sqrt n + 11)
    (ha : a ≤ E n + 2*p + 16)
    (hb : 3*b ≤ 3*a + 4*p + 2) :
    512+a < memSize n ∧ 512+b < memSize n := by
  have he := E_le_div3 n
  unfold memSize
  omega

/-- A later bottom-tested iteration overshoots by at most one stride. -/
theorem next_cursor_bound (E p start j : Nat)
    (h : j = start ∨ ∃ prev, prev < E ∧ j = prev+2*p) :
    j ≤ max start (E+2*p) := by
  rcases h with rfl | ⟨prev, hp, rfl⟩ <;> omega

/-- A square-root bound on every candidate whose predecessor square is in range. -/
theorem candidate_bound (n p gap : Nat) (hgap : gap ≤ 11)
    (hle : p ≤ Nat.sqrt n + gap) : p ≤ Nat.sqrt n + 11 := by omega

theorem le_sqrt_of_sq_le (n p : Nat) (h : p*p ≤ n) : p ≤ Nat.sqrt n := by
  apply Classical.byContradiction
  intro hc
  have hmul := Nat.mul_le_mul (show Nat.sqrt n+1 ≤ p by omega)
    (show Nat.sqrt n+1 ≤ p by omega)
  have hroot := Nat.lt_succ_sqrt n
  simp only [Nat.succ_eq_add_one] at hroot
  omega

/-- Adjacent candidate squares no more than four apart are less than three
current-candidate strides apart in flag space. -/
theorem square_gap_index (r p x a : Nat) (hrp : r ≤ p) (hgap : p ≤ r+4)
    (hx : value x = r*r) (ha : value a = p*p) : a ≤ x+3*p := by
  have hprod : p*p ≤ r*r+8*p := by
    have hg : p-r ≤ 4 := by omega
    have h1 : (p-r)*(p+r) ≤ 4*(p+r) := Nat.mul_le_mul_right _ hg
    have h2 : 4*(p+r) ≤ 8*p := by omega
    have h3 : p*p = r*r+(p-r)*(p+r) := by
      have hh : r+(p-r)=p := by omega
      calc
        p*p = (r+(p-r))*p := by rw [hh]
        _ = r*r+(p-r)*(p+r) := by grind
    omega
  have hxv : 3*x ≤ value x ∧ value x ≤ 3*x+2 := by unfold value; split <;> omega
  have hav : 3*a ≤ value a ∧ value a ≤ 3*a+2 := by unfold value; split <;> omega
  omega

/-- An initial paired minus candidate may exceed the input's square root by
four, because only its previous plus square was compared. -/
theorem following_candidate_bound (n r p : Nat) (hr : r*r ≤ n)
    (hp : p ≤ r+4) : p ≤ Nat.sqrt n+4 := by
  have := le_sqrt_of_sq_le n r hr
  omega

/-- The index gap between paired stores is controlled directly by their
represented product difference. -/
theorem paired_offset (a b p gap : Nat) (hgap : gap ≤ 4)
    (h : value b = value a + p*gap) : 3*b ≤ 3*a + 4*p+2 := by
  have ha : value a ≤ 3*a+2 := by unfold value; split <;> omega
  have hb : 3*b ≤ value b := by unfold value; split <;> omega
  have hp : p*gap ≤ 4*p := by
    have := Nat.mul_le_mul_left p hgap
    simpa [Nat.mul_comm] using this
  omega

theorem paired_minus_offset (a b p : Nat)
    (h : value b = value a + 2*p) : 3*b ≤ 3*a+2*p+2 := by
  have ha : value a ≤ 3*a+2 := by unfold value; split <;> omega
  have hb : 3*b ≤ value b := by unfold value; split <;> omega
  omega

/-- The two progressions enumerate exactly the wheel multipliers at or above
candidate p. -/
theorem multiplier_progressions (p gap m : Nat)
    (hp : (p%6=5 ∧ gap=2) ∨ (p%6=1 ∧ gap=4)) (hm : p ≤ m) :
    (m%6=1 ∨ m%6=5) ↔
      ∃ j, m = p+6*j ∨ m = p+gap+6*j := by
  constructor
  · intro hw
    refine ⟨(m-p)/6, ?_⟩
    rcases hp with hp | hp <;> rcases hw with hw | hw <;> omega
  · rintro ⟨j, h | h⟩ <;> rcases hp with hp | hp <;> omega

/-- The two index progressions are exactly all represented multiples of p
at or beyond p squared. -/
theorem paired_progressions (p gap a b i : Nat) (hp : 0 < p)
    (hphase : (p%6=5 ∧ gap=2) ∨ (p%6=1 ∧ gap=4))
    (ha : value a = p*p) (hb : value b = p*(p+gap)) :
    (p*p ≤ value i ∧ p ∣ value i) ↔
      ∃ j, i = a+2*p*j ∨ i = b+2*p*j := by
  constructor
  · rintro ⟨hsq, ⟨m, hm⟩⟩
    have hmdiv : m ∣ value i := ⟨p, by rw [hm, Nat.mul_comm]⟩
    have hw := divisor_wheel i m hmdiv
    have hpm : p ≤ m := Nat.le_of_mul_le_mul_left (by rw [hm] at hsq; exact hsq) hp
    obtain ⟨j, hj | hj⟩ := (multiplier_progressions p gap m hphase hpm).mp hw
    · refine ⟨j, Or.inl ?_⟩
      have hv : value i = value (a+2*p*j) := by
        rw [progression a p p j ha, hm, hj]
      have := congrArg (fun x : Nat => x / 3) hv
      simpa [value_index] using this
    · refine ⟨j, Or.inr ?_⟩
      have hv : value i = value (b+2*p*j) := by
        rw [progression b p (p+gap) j hb, hm, hj]
      have := congrArg (fun x : Nat => x / 3) hv
      simpa [value_index] using this
  · rintro ⟨j, hj | hj⟩
    · rw [hj, progression a p p j ha]
      exact ⟨Nat.mul_le_mul_left p (by omega), ⟨p+6*j, rfl⟩⟩
    · rw [hj, progression b p (p+gap) j hb]
      exact ⟨Nat.mul_le_mul_left p (by omega), ⟨p+gap+6*j, rfl⟩⟩

/-- Every store in the later minus loop fits, including the unconditional
first store when the new square is already beyond the input. -/
theorem minus_loop_capacity (n r p x start a b : Nat)
    (hrp : r ≤ p) (hgap : p ≤ r+4)
    (hx : x < E n ∨ (r = 7 ∧ x = 16 ∧ p = 11))
    (hxsq : value x = r*r) (hstart : value start = p*p)
    (hcur : a = start ∨ ∃ prev, prev < E n ∧ a = prev+2*p)
    (hpair : value b = value a+2*p) :
    512+a < memSize n ∧ 512+b < memSize n := by
  have hp : p ≤ Nat.sqrt n+11 := by
    rcases hx with hx | ⟨_, _, hp⟩
    · have hr : r*r ≤ n := by rw [← hxsq]; exact (value_lt_iff n x).mp hx
      have := following_candidate_bound n r p hr hgap
      omega
    · omega
  have hs := square_gap_index r p x start hrp hgap hxsq hstart
  have ha : a ≤ E n+3*p+7 := by
    rcases hx with hx | ⟨hr, hx, hp⟩
    · rcases hcur with h | ⟨prev, hprev, h⟩ <;> omega
    · have hstart40 : start = 40 := by
        rw [hp] at hstart
        have hv := value_index start
        rw [hstart] at hv
        omega
      rcases hcur with h | ⟨prev, hprev, h⟩ <;> omega
  exact minus_capacity n p a b (by omega) ha (paired_minus_offset a b p hpair)

/-- Every store in a plus loop fits. The first candidate 7 is unconditional;
subsequent candidates enter only when their squares are below E. -/
theorem plus_loop_capacity (n p start a b : Nat)
    (hstart : value start = p*p)
    (hentry : start < E n ∨ (p = 7 ∧ start = 16))
    (hcur : a = start ∨ ∃ prev, prev < E n ∧ a = prev+2*p)
    (hpair : value b = value a+4*p) :
    512+a < memSize n ∧ 512+b < memSize n := by
  have hp : p ≤ Nat.sqrt n+11 := by
    rcases hentry with hin | ⟨rfl, _⟩
    · have hs : p*p ≤ n := by rw [← hstart]; exact (value_lt_iff n start).mp hin
      have := le_sqrt_of_sq_le n p hs
      omega
    · omega
  have ha : a ≤ E n+2*p+16 := by
    rcases hentry with hin | ⟨_, hs⟩ <;>
      rcases hcur with h | ⟨prev, hprev, h⟩ <;> omega
  have hb := paired_offset a b p 4 (by omega) (by simpa [Nat.mul_comm] using hpair)
  exact plus_capacity n p a b hp ha hb

/-- The two four-byte startup stores (including overwritten zero bytes) fit,
even on the unconditional first pass. -/
theorem five_loop_capacity (n a : Nat)
    (hcur : a = 8 ∨ ∃ prev, prev < E n ∧ a = prev+20) :
    512+a+13 < memSize n := by
  have := E_le_div3 n
  unfold memSize
  rcases hcur with h | ⟨prev, hp, h⟩ <;> omega

/-- Within the documented input range the exact allocation lies below the
RV64 address wraparound. -/
theorem memSize_lt_64 (n : Nat) (hn : n ≤ 10^11-1) : memSize n < 2^64 := by
  have hs : Nat.sqrt n ≤ n := by
    have hsq := Nat.sqrt_le n
    by_cases h : Nat.sqrt n = 0
    · omega
    · have hmul := Nat.mul_le_mul_left (Nat.sqrt n) (show 1 ≤ Nat.sqrt n by omega)
      omega
  unfold memSize
  omega

theorem loops_fit_64 (n a : Nat) (hn : n ≤ 10^11-1)
    (ha : 512+a < memSize n) : 512+a < 2^64 :=
  Nat.lt_trans ha (memSize_lt_64 n hn)

end TinyFive.OddWheelMath
