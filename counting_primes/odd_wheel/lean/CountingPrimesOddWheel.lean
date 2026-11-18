import OddWheelSetup
import OddWheelStartupMarks
import OddWheelOuter
import OddWheelOuterLoop
import OddWheelCountAll

namespace TinyFive.CountingPrimesOddWheel

open CountingPrimes SieveMemory OddWheelMath

/-- A loose upper bound on modeled instruction count. -/
def budget (n : Nat) : Nat := 33 + 326*n + (15+10*(n+1))*(n+2)

private theorem budget_mono {a b : Nat} (h : a ≤ b) : budget a ≤ budget b := by
  unfold budget
  have hmul : (15+10*(a+1))*(a+2) ≤ (15+10*(b+1))*(b+2) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

private theorem final_count (n p : Nat) (h3 : 3 ≤ n)
    (hfinal : ∀ i, i < E n → value i < p*p) :
    BitVec.ofNat 64 (E n+1) - BitVec.ofNat 64 (OddSieveMath.csum (OddSieveMath.bit (E n) (WM p)) (E n)) =
      BitVec.ofNat 64 (countPrimes n) := by
  rw [OddSieveMath.csum_congr _ _ _ (fun i hi => final_bits _ _ i hfinal hi),
    ← count_identity n h3, BitVec.ofNat_add, BitVec.add_sub_cancel]

/-- The original 82 loaded RV64I instructions print `π(n)` and a newline and
exit with status zero for every input in the supported range. -/
theorem correct (n : Nat) (hn : n < 10^11) :
    ∃ fuel, fuel ≤ budget n ∧
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n") := by
  by_cases h3 : 3 ≤ n
  · have hE' := E_le_div3 n
    have hE : E n ≤ n := by omega
    have he0 : 0 < E n := by unfold E; omega
    have he64 : E n < 2^37 := by omega
    obtain ⟨x, hx5, hx7, hx11, hx16, hinit⟩ := initialize_regs n hn h3
    rw [← E_machine n (by omega)] at hx5
    obtain ⟨f5, y, mem, hbf5, hy5, hy7, hy16, hmem, hflags, hfive⟩ :=
      five_correct n x hn hx5 hx7 hx11 hx16
    obtain ⟨z, hzrun, hz⟩ := outer_init n y mem "" hmem hy5 hy7 hy16 hflags
    obtain ⟨fo, k, u, mem', horun, hbfo, hu, _, hfinal⟩ :=
      outer_loop n "" (by omega) (pair_correct n hn) 1 z mem hz
    have hcode := hu.layout.code_eq.mono (show 328 ≤ 512 by decide)
    let f := OddSieveMath.bit (E n) (WM (6*k+1))
    obtain ⟨fc, v, hbfc, hv10, hcrun⟩ :=
      count_correct (E n) f u mem' "" ⟨he0,he64⟩ (OddSieveMath.bit_le_one _ _)
        hcode hu.flags (flag_padding hu.layout.code_eq) hu.bound
    rw [show f = OddSieveMath.bit (E n) (WM (6*k+1)) by rfl, final_count n (6*k+1) h3 hfinal] at hv10
    have hp := print_correct (countPrimes n) (by have := countPrimes_le n; omega)
      v mem' hcode hv10
    refine ⟨18+f5+3+fo+fc+7, ?_, ?_⟩
    · have hmul : (15+10*(E n+1))*(E n+2) ≤ (15+10*(n+1))*(n+2) :=
        Nat.mul_le_mul (by omega) (by omega)
      unfold budget
      omega
    · rw [run_add, run_add, run_add, run_add, run_add, hinit, hfive, hzrun, horun, hcrun]
      exact hp
  · exact ⟨13, by unfold budget; omega, small_correct n (by omega)⟩

/-- One fuel allocation covers every supported input. -/
theorem correct_uniform_fuel :
    ∃ fuel, ∀ n < 10^11,
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n") := by
  refine ⟨budget (10^11), fun n hn => ?_⟩
  obtain ⟨fuel, hf, h⟩ := correct n hn
  exact is_exited_with_output_mono (Nat.le_trans hf (budget_mono (by omega))) h

end TinyFive.CountingPrimesOddWheel
