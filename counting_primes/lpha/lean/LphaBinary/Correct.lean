import LphaBinary.Finish
import CountingPrimesLoad

/-! The recompiled RV64IM lpha binary meets `CountingPrimes.IsCorrect`. -/
namespace TinyFive.LphaBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

theorem prog_len : 4 * prog.length ≤ 1536 := by decide +kernel

theorem mem0_size : initial'.mem.size = 4194304 := load_mem_size 64 prog 4194304 [] (by have := prog_len; omega)

theorem mem0_prefix : Prefix image initial'.mem 1536 :=
  load_prefix 64 prog 1536 4194304 [] [] prog_len (by decide)

theorem mem0_zero (i : Nat) (h1 : 1536 ≤ i) (h2 : i < 4194304) : initial'.mem[i]? = some 0 :=
  load_mem_zero 64 prog 4194304 [] i (by have := prog_len; omega) h2

/-- Every run of the machine on an input below `10^11` prints `π(n)`, for some fuel. -/
theorem correct (n : Nat) (hn : n < 10 ^ 11) :
    ∃ fuel, is_exited_with_output (run fuel (initial'.loadInput n)) (toString (countPrimes n) ++ "\n") := by
  have hx : ∀ r : Reg, r ≠ 10 → (initial'.x.set 10 (bv n)).get r = 0 := by
    intro r hr
    have hx0 : initial'.x = ⟨Vector.replicate 32 0⟩ := rfl
    rw [Regs.get_set, if_neg (Ne.symm hr), hx0]
    simp [Regs.get]
  have h10 : (initial'.x.set 10 (bv n)).get 10 = bv n := by simp [Regs.get_set]
  have hst : initial'.loadInput n = ⟨initial'.x.set 10 (bv n), 0, initial'.mem, [], "", .running⟩ := rfl
  rw [hst]
  rcases Nat.lt_or_ge n 2 with h | h
  · refine ⟨15, ?_⟩
    have := small01 _ _ "" n mem0_prefix mem0_size hx h10 (by omega)
    have hc : countPrimes n = 0 := by
      rcases Nat.lt_or_ge n 1 with h1 | h1
      · obtain rfl : n = 0 := by omega
        rfl
      · obtain rfl : n = 1 := by omega
        rfl
    rw [hc]; simpa using this
  · obtain ⟨n1, y1, m1, r1, hinv1⟩ := setup_run _ _ "" n mem0_prefix mem0_size mem0_zero hx h10 h hn
    obtain ⟨n2, a, y2, m2, r2, hinv2, hcut⟩ := outer_loop n 3 y1 m1 "" hinv1
    obtain ⟨n3, h3⟩ := lfinish_run n a y2 m2 "" hinv2 hcut
    refine ⟨n1 + (n2 + n3), ?_⟩
    rw [run_add, run_add, r1, r2]
    simpa using h3

/-- One fuel value works for every input below a bound. -/
theorem uniform (B : Nat) :
    ∃ fuel, ∀ n < B, n < 10 ^ 11 →
      is_exited_with_output (run fuel (initial'.loadInput n)) (toString (countPrimes n) ++ "\n") := by
  induction B with
  | zero => exact ⟨0, fun n hn => by omega⟩
  | succ B ih =>
    obtain ⟨F, hF⟩ := ih
    by_cases hB : B < 10 ^ 11
    · obtain ⟨f, hf⟩ := correct B hB
      refine ⟨max F f, fun n hn hn' => ?_⟩
      rcases Nat.lt_or_ge n B with h | h
      · exact is_exited_with_output_mono (Nat.le_max_left _ _) (hF n h hn')
      · obtain rfl : n = B := by omega
        exact is_exited_with_output_mono (Nat.le_max_right _ _) hf
    · exact ⟨F, fun n hn hn' => hF n (by omega) hn'⟩

/-- `initial'` meets the specification. -/
theorem isCorrect : IsCorrect initial' := by
  obtain ⟨F, hF⟩ := uniform (10 ^ 11)
  exact isCorrect_of_load prog (fun _ => 4194304) 4194304 (fun _ _ => by have := prog_len; omega)
    (fun _ _ => Nat.le_refl _) ⟨F, fun n hn => hF n hn hn⟩

/-- `initial'` holds `1353` nonzero bytes (the code). Zero padding is free. -/
theorem programSize_eq : programSize initial' = 1353 := by
  rw [initial', programSize_load prog 1536 4194304 prog_len (by omega)]
  unfold programSize load
  dsimp only
  rw [List.countP_toArray]
  decide +kernel

end TinyFive.LphaBinary
