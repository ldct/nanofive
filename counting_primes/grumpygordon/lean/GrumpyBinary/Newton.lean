import LucyMath

/-! Newton's iteration for the integer square root, as `isqrt64` in the runtime computes it:
`x = n, y = (x + 1) / 2; while (y < x) { x = y; y = (x + n / x) / 2; }` ends with
`x = isqrt n`. -/
namespace TinyFive.GrumpyBinary
open LucyMath

/-- `x * (2a - x) ≤ a * a`. -/
theorem amgm (x a : Nat) : x * (2 * a - x) ≤ a * a := by
  by_cases h : x ≤ a
  · obtain ⟨d, rfl⟩ : ∃ d, a = x + d := ⟨a - x, by omega⟩
    rw [show 2 * (x + d) - x = x + 2 * d by omega]
    have e1 : x * (x + 2 * d) = x * x + 2 * (x * d) := by grind
    have e2 : (x + d) * (x + d) = x * x + 2 * (x * d) + d * d := by grind
    omega
  · by_cases h2 : x ≤ 2 * a
    · obtain ⟨z, d, rfl, rfl⟩ : ∃ z d, a = z + d ∧ x = z + 2 * d := ⟨2 * a - x, x - a, by omega, by omega⟩
      rw [show 2 * (z + d) - (z + 2 * d) = z by omega]
      have e1 : (z + 2 * d) * z = z * z + 2 * (z * d) := by grind
      have e2 : (z + d) * (z + d) = z * z + 2 * (z * d) + d * d := by grind
      omega
    · rw [show 2 * a - x = 0 by omega]; simp

/-- One Newton step never goes below the square root. -/
theorem newton_ge (n x : Nat) (hx : 1 ≤ x) : isqrt n ≤ (x + n / x) / 2 := by
  apply Decidable.byContradiction
  intro hlt
  have hr := (isqrt_spec n).1
  generalize hy : (x + n / x) / 2 = y at hlt
  generalize hq : n / x = q at hy
  have hq1 : n < x * (q + 1) := by
    rw [← hq]
    have := Nat.lt_mul_div_succ n (show 0 < x by omega)
    exact this
  have hsq : (y + 1) * (y + 1) ≤ n := by
    have := Nat.mul_le_mul (show y + 1 ≤ isqrt n by omega) (show y + 1 ≤ isqrt n by omega)
    omega
  -- x * (q + 1) ≤ x * (2y + 2 - x) ≤ (y + 1)^2
  have hxq : q + 1 + x ≤ 2 * (y + 1) := by omega
  have key : x * (q + 1) ≤ (y + 1) * (y + 1) := by
    have h1 : x * (q + 1) ≤ x * (2 * (y + 1) - x) := Nat.mul_le_mul_left x (by omega)
    have h2 : x * (2 * (y + 1) - x) ≤ (y + 1) * (y + 1) := amgm x (y + 1)
    omega
  omega

/-- Above the square root, a Newton step strictly decreases. -/
theorem newton_lt (n x : Nat) (hx : isqrt n < x) : (x + n / x) / 2 < x := by
  have h2 := (isqrt_spec n).2
  have hxx : n < x * x := Nat.lt_of_lt_of_le h2 (Nat.mul_le_mul hx hx)
  have : n / x < x := (Nat.div_lt_iff_lt_mul (by omega)).mpr hxx
  omega

end TinyFive.GrumpyBinary
