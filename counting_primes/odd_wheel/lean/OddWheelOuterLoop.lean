import OddWheelOuterInv

namespace TinyFive.CountingPrimesOddWheel
open OddWheelMath SieveMemory

/-- The three real instructions at PC88 establish the first pair's invariant. -/
theorem outer_init (n : Nat) (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hm : Layout image 512 (memSize n) mem)
    (h5 : x.get 5 = BitVec.ofNat 64 (E n)) (h7 : x.get 7 = 16777217)
    (h16 : x.get 16 = BitVec.ofNat 64 2)
    (hf : WheelFlags mem (E n) 7) :
    ∃ x', run 3 ⟨x, 88, mem, [], out, .running⟩ =
      ⟨x', 100, mem, [], out, .running⟩ ∧ OuterEntry n 1 x' mem := by
  refine ⟨((x.set 12 16).set 14 8).set 15 10, mark_pair_init x mem out (hm.code_eq.mono (by omega)), ?_⟩
  constructor
  · constructor <;> simp [Regs.get_set, h5, h7, h16, sqPlus, hm, hf]
  · exact Or.inr rfl

private theorem k_le_square (k : Nat) : k ≤ sqPlus k := by
  unfold sqPlus
  omega

/-- Any sequence of complete pairs terminates at PC200. The only assumed
machine-specific fact is the one-pair specification above. -/
theorem outer_loop (n : Nat) (out : String) (hE : E n < 2^64)
    (hpair : OuterPairSpec n out) (k : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (hin : OuterEntry n k x mem) :
    ∃ fuel k' x' mem', run fuel ⟨x, 100, mem, [], out, .running⟩ =
      ⟨x', 200, mem', [], out, .running⟩ ∧
      fuel ≤ (15+10*(E n+1))*(E n+2) ∧
      OuterCore n k' x' mem' ∧ E n ≤ sqPlus k' ∧
      (∀ i, i < E n → value i < (6*k'+1)*(6*k'+1)) := by
  have aux : ∀ fuel k x mem, E n+1 < k+fuel → OuterEntry n k x mem →
      ∃ steps k' x' mem', run steps ⟨x, 100, mem, [], out, .running⟩ =
        ⟨x', 200, mem', [], out, .running⟩ ∧
        steps ≤ (15+10*(E n+1))*fuel ∧ OuterCore n k' x' mem' ∧
        E n ≤ sqPlus k' ∧
        (∀ i, i < E n → value i < (6*k'+1)*(6*k'+1)) := by
    intro fuel
    induction fuel with
    | zero =>
      intro k x mem hb hi
      have hs := k_le_square k
      rcases hi.2 with hs' | rfl <;> omega
    | succ fuel ih =>
      intro k x mem hb hi
      obtain ⟨steps, y, mem', hr, hsteps, hc⟩ := hpair k x mem hi
      have hbranch := mark_pair_next y mem' out (hc.layout.code_eq.mono (by omega))
      rw [hc.square, hc.bound] at hbranch
      by_cases hs : sqPlus (k+1) < E n
      · have hs64 : sqPlus (k+1) < 2^64 := by omega
        have hu : (BitVec.ofNat 64 (sqPlus (k+1))).ult (BitVec.ofNat 64 (E n)) = true := by
          simp [BitVec.ult, Nat.mod_eq_of_lt hs64, Nat.mod_eq_of_lt hE, hs]
        rw [hu] at hbranch
        simp only [ite_true] at hbranch
        obtain ⟨steps', k', z, mem'', ht, hsteps', hc', he, hf⟩ :=
          ih (k+1) y mem' (by omega) ⟨hc, Or.inl hs⟩
        refine ⟨steps+1+steps', k', z, mem'', ?_, ?_, hc', he, hf⟩
        · rw [run_add, run_add, hr, hbranch, ht]
        · rw [Nat.mul_succ]; omega
      · have hsq64 : (BitVec.ofNat 64 (sqPlus (k+1))).toNat ≥ E n := by
          simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc.square64]
          omega
        have hu : (BitVec.ofNat 64 (sqPlus (k+1))).ult (BitVec.ofNat 64 (E n)) = false := by
          simp [BitVec.ult, Nat.mod_eq_of_lt hc.square64, Nat.mod_eq_of_lt hE, hs]
        rw [hu] at hbranch
        simp only [Bool.false_eq_true, ite_false] at hbranch
        refine ⟨steps+1, k+1, y, mem', ?_, ?_, hc, by omega, ?_⟩
        · rw [run_add, hr, hbranch]
        · rw [Nat.mul_succ]; omega
        · exact final_square (sqPlus_value (k+1)) (by omega)
  exact aux (E n+2) k x mem (by omega) hin

end TinyFive.CountingPrimesOddWheel
