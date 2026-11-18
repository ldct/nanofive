import OddWheelOuterInv
import OddWheelPlus
import OddWheelMinus
import OddWheelPairBounds

namespace TinyFive.CountingPrimesOddWheel

open OddWheelMath

theorem pair_correct (n : Nat) (hn : n < 10^11) : OuterPairSpec n "" := by
  intro k x mem he
  obtain ⟨hc, he⟩ := he
  have hentry : k = 1 ∨ sqPlus k < E n := he.symm
  have hx : PairInv x (E n) k :=
    ⟨hc.bound, hc.marker, hc.square, hc.delta, hc.stride, hc.candidate⟩
  obtain ⟨fp, y, mem', hbfp, hy5, hy7, hy11, hy14, hy15, hy16, hm, hf, hplus⟩ :=
    plus_candidate_correct n k x mem hn hc.positive hentry hc.layout hc.flags hx
  obtain ⟨fm, z, mem'', hbfm, hz, hm', hf', hminus⟩ :=
    minus_candidate_correct n k y mem' hn hc.positive hentry hm hf
      hy5 hy7 hy11 hy14 hy15 hy16
  refine ⟨fp+fm, z, mem'', by rw [run_add, hplus, hminus], by omega, ?_⟩
  have hsq : sqPlus (k+1) < 2^64 := by
    have h := pair_cursors_small n k hn hentry
    rw [plus_square_add, minus_square_add]
    omega
  exact ⟨by omega, hz.1, hz.2.1, hsq, hz.2.2.1, hz.2.2.2.1,
    hz.2.2.2.2.1, hz.2.2.2.2.2, hm', hf'⟩

end TinyFive.CountingPrimesOddWheel
