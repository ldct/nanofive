import ZjyBinary.Setup
import CountingPrimesLoad

/-! The recompiled RV64IM zjy2008 binary meets `CountingPrimes.IsCorrect`. -/
namespace TinyFive.ZjyBinary
open CountingPrimes SieveMath LucyMath GrumpyGordon SieveMemory GrumpyBinary

local notation "bv" => BitVec.ofNat 64

theorem prog_len : 4 * prog.length ≤ 1520 := by decide +kernel

theorem mem0_size : initial'.mem.size = 4194304 := load_mem_size 64 prog 4194304 [] (by have := prog_len; omega)

theorem mem0_prefix : Prefix image initial'.mem 1520 :=
  load_prefix 64 prog 1520 4194304 [] [] prog_len (by decide)

theorem mem0_heap : readBytes initial'.mem 1512 8 = some (bv 1520) := by
  rw [readBytes_congr initial'.mem image 1512 8 (fun j _ h2 => mem0_prefix j (by omega))]
  decide +kernel

/-- Every run of the machine on an input below `10^11` prints `π(n)`, for some fuel. -/
theorem correct (n : Nat) (hn : n < 10 ^ 11) :
    ∃ fuel, is_exited_with_output (run fuel (initial'.loadInput n)) (toString (countPrimes n) ++ "\n") := by
  have hmem : Prefix image initial'.mem 1480 := fun i hi => mem0_prefix i (by omega)
  have hx : ∀ r : Reg, r ≠ 10 → (initial'.x.set 10 (bv n)).get r = 0 := by
    intro r hr
    have hx0 : initial'.x = ⟨Vector.replicate 32 0⟩ := rfl
    rw [Regs.get_set, if_neg (Ne.symm hr), hx0]
    simp [Regs.get]
  have h10 : (initial'.x.set 10 (bv n)).get 10 = bv n := by simp [Regs.get_set]
  have hst : initial'.loadInput n = ⟨initial'.x.set 10 (bv n), 0, initial'.mem, [], "", .running⟩ := rfl
  rw [hst]
  rcases Nat.lt_or_ge n 7 with h | h
  · obtain ⟨y, m, r1, pre, sz, ra, y2, y10⟩ := setup_small _ _ "" n hmem mem0_size hx h10 (by omega)
    have hc : countPrimes n ≤ n := countPrimes_le n
    have := fin_ret y m "" (countPrimes n) pre sz y10 y2 (by omega) ra
    refine ⟨23 + 18, ?_⟩
    rw [run_add, r1]
    simpa using this
  · obtain ⟨n1, a, y1, m1, r1, hz, hcut, y2, y8, y9, y18⟩ :=
      pi_run _ _ "" n mem0_prefix mem0_size mem0_heap hx h10 h (by omega)
    obtain ⟨n2, h2⟩ := finish_run n a y1 m1 "" hz hcut y2 y18 y8 y9
    refine ⟨n1 + n2, ?_⟩
    rw [run_add, r1]
    simpa using h2

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

/-- `initial'` holds `1239` nonzero bytes (code, the wheel table and the heap cursor). Zero
padding is free. -/
theorem programSize_eq : programSize initial' = 1239 := by
  rw [initial', programSize_load prog 1520 4194304 prog_len (by omega)]
  unfold programSize load
  dsimp only
  rw [List.countP_toArray]
  decide +kernel

end TinyFive.ZjyBinary
