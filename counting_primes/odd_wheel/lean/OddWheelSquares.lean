import OddWheelBounds

namespace TinyFive.OddWheelMath

theorem minus_square_add (k : Nat) :
    sqMinus (k+1) = sqPlus k + 8*k + 8*(k+1) := by
  unfold sqMinus sqPlus
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem plus_square_add (k : Nat) :
    sqPlus (k+1) = sqMinus (k+1) + 8*(k+1) := by
  rw [minus_square_add]
  unfold sqPlus
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem minus_square_value (k : Nat) :
    value (sqMinus (k+1)) = (6*k+5)*(6*k+5) := by
  rw [minus_square_add]
  have he : sqPlus k + 8*k + 8*(k+1) = 2*(6*k*k+10*k+4) := by
    unfold sqPlus
    grind
  rw [he, value_even]
  grind

theorem plus_second_value (k : Nat) :
    value (sqPlus k + 8*k+1) = (6*k+1)*(6*k+5) := by
  have he : sqPlus k+8*k+1 = 2*(6*k*k+6*k)+1 := by
    unfold sqPlus
    grind
  rw [he, value_odd]
  grind

theorem minus_second_value (k : Nat) :
    value (sqMinus (k+1)+4*k+3) = (6*k+5)*(6*k+7) := by
  rw [minus_square_add]
  have he : sqPlus k+8*k+8*(k+1)+4*k+3 = 2*(6*k*k+12*k+5)+1 := by
    unfold sqPlus
    grind
  rw [he, value_odd]
  grind

theorem pair_k_le (n k : Nat) (hk : k = 1 ∨ sqPlus k < E n) :
    k ≤ Nat.sqrt n+1 := by
  rcases hk with rfl | h
  · omega
  · have hv := (value_lt_iff n _).mp h
    rw [sqPlus_value] at hv
    have := le_sqrt_of_sq_le n _ hv
    omega

end TinyFive.OddWheelMath
