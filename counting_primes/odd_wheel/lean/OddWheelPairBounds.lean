import OddWheelSquares
import OddWheelMarking

namespace TinyFive.CountingPrimesOddWheel
open OddWheelMath

/-- Absolute pair-index bound over the supported input range. -/
theorem pair_k_small (n k : Nat) (hn : n < 10^11)
    (hk : k = 1 ∨ sqPlus k < E n) : k ≤ 316228 := by
  have h := pair_k_le n k hk
  have hs := Nat.sqrt_le n
  by_cases hc : k ≤ 316228
  · exact hc
  · have hroot : 316228 ≤ Nat.sqrt n := by omega
    have hm := Nat.mul_le_mul hroot hroot
    omega

/-- All quadratic candidate cursors are far below the RV64 wrap boundary. -/
theorem pair_cursors_small (n k : Nat) (hn : n < 10^11)
    (hk : k = 1 ∨ sqPlus k < E n) :
    sqPlus k + 32*k + 32 < 2^64 := by
  have h := pair_k_small n k hn hk
  have hh := Nat.mul_le_mul h h
  unfold sqPlus
  rw [show 12*k*k = 12*(k*k) by simp [Nat.mul_assoc]]
  omega

end TinyFive.CountingPrimesOddWheel
