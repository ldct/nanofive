import OddWheelBounds

namespace TinyFive.CountingPrimesOddWheel

open OddWheelMath OddSieveMath Classical

/-- In-range flags after processing wheel candidates strictly below `p`. -/
def WheelFlags (mem : Array (BitVec 8)) (K p : Nat) : Prop :=
  ∀ i, i < K → mem[512+i]? = some (BitVec.ofNat 8 (bit K (WM p) i))

theorem flags_skip {n p gap q : Nat} {mem : Array (BitVec 8)}
    (hf : WheelFlags mem (E n) p)
    (hp : 5 ≤ p) (hphase : (p%6=5 ∧ gap=2) ∨ (p%6=1 ∧ gap=4))
    (hq : value q = p) (h : q < E n → mem[512+q]? ≠ some 0) :
    WheelFlags mem (E n) (p+gap) := by
  intro i hi
  rw [hf i hi, bit_congr (P := WM p) (Q := WM (p+gap)) ?_]
  intro _
  by_cases hin : q < E n
  · have hm : WM p q := by
      apply Classical.byContradiction
      intro hn
      apply h hin
      rw [hf q hin, bit_neg (fun hc => hn hc.2)]
      rfl
    exact (wm_wheel_skip p gap q i hp hphase hq hm).symm
  · have hp' : n < p := by
      have hv := value_lt_iff n q
      omega
    have hs := Nat.le_mul_self p
    have hvi := (value_lt_iff n i).mp hi
    rw [wm_wheel_step p gap i hp hphase]
    exact ⟨Or.inl, fun h' => h'.resolve_right (fun hc => by omega)⟩

/-- Flags set by the two progressions extend the divisor invariant. The
    in-range writes suffice: an unexecuted iteration has both cursors out of range. -/
theorem flags_mark {K p gap a b : Nat} {mem mem' : Array (BitVec 8)}
    (hf : WheelFlags mem K p) (hp : 5 ≤ p)
    (hphase : (p%6=5 ∧ gap=2) ∨ (p%6=1 ∧ gap=4))
    (ha : value a = p*p) (hb : value b = p*(p+gap))
    (hw : ∀ i, i < K → mem'[512+i]? =
      if (∃ j, i = a+2*p*j ∨ i = b+2*p*j) then some 1 else mem[512+i]?) :
    WheelFlags mem' K (p+gap) := by
  classical
  intro i hi
  rw [hw i hi]
  have hs := wm_wheel_step p gap i hp hphase
  have he := paired_progressions p gap a b i (by omega) hphase ha hb
  by_cases h : ∃ j, i = a+2*p*j ∨ i = b+2*p*j
  · rw [ite_eq_left h, bit_pos hi (hs.mpr (Or.inr (he.mpr h)))]
    rfl
  · rw [ite_eq_right h, hf i hi]
    congr 2
    apply bit_congr
    intro _
    rw [hs, he, or_iff_left h]

theorem final_square {n p a : Nat} (ha : value a = p*p) (h : E n ≤ a) :
    ∀ i, i < E n → value i < p*p := by
  intro i hi
  have hvi := (value_lt_iff n i).mp hi
  have hva := value_lt_iff n a
  omega

end TinyFive.CountingPrimesOddWheel
