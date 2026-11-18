import OddWheelFiveMem
import OddWheelFiveLoop
import OddWheelFlags
import OddWheelLoops
import OddWheelSetup

namespace TinyFive.CountingPrimesOddWheel

open OddWheelMath OddSieveMath SieveMemory

/-- The special pass for 5, including the unconditional first pair of word stores. -/
theorem five_correct (n : Nat) (x : Regs 64) (hn : n < 10^11)
    (h5 : x.get 5 = BitVec.ofNat 64 (E n)) (h7 : x.get 7 = 16777217)
    (h11 : x.get 11 = 8) (h16 : x.get 16 = 2) :
    ∃ fuel y mem', fuel ≤ 4*(E n+1) ∧ y.get 5 = BitVec.ofNat 64 (E n) ∧
      y.get 7 = 16777217 ∧ y.get 16 = 2 ∧ Layout image 512 (memSize n) mem' ∧
      WheelFlags mem' (E n) 7 ∧
      run fuel ⟨x, 72, (initial n).mem, [], "", .running⟩ = ⟨y, 88, mem', [], "", .running⟩ := by
  classical
  let k := pairCount 8 20 (E n)-1
  let mem := (initial n).mem
  have hcount := pairCount_properties 8 20 (E n) (by decide)
  have ht : k+1 = pairCount 8 20 (E n) := by dsimp [k]; omega
  have hE := E_le_div3 n
  have h64 := memSize_lt_64 n (by omega)
  have hcont : ∀ j, j < k+1 → j = 0 ∨ 8+20*j < E n := by
    intro j hj
    by_cases hz : j = 0
    · exact Or.inl hz
    · exact Or.inr ((hcount.2.2 j (by omega)).mpr (by omega))
  have hstop : E n ≤ 8+20*(k+1) := by
    have h := hcount.2.2 (k+1) (by omega)
    omega
  have hcap : ∀ j, j < k+1 → 512+8+20*j+13 < memSize n := by
    intro j hj
    rw [Nat.add_assoc 512 8 (20*j)]
    apply five_loop_capacity n (8+20*j)
    cases j with
    | zero => exact Or.inl rfl
    | succ j =>
      have hj' := (hcont (j+1) hj).resolve_left (by omega)
      exact Or.inr ⟨8+20*j, by omega, by omega⟩
  have hk := hcap k (by omega)
  have hr := five_loop x mem "" (memSize n) 8 (E n) k (initial_layout n) hk
    (by omega) (by omega) (hcont k (by omega)) hstop h11 h7 h5
  have hm := initial_full_layout n
  let mem' := fiveMemory mem 8 (k+1)
  have hm' : Layout image 512 (memSize n) mem' :=
    fiveMemory_layout_full mem 8 (k+1) (memSize n) hm
  refine ⟨4*(k+1), x.set 11 (BitVec.ofNat 64 (8+20*(k+1))), mem', by omega,
    by simp [Regs.get_set, h5], by simp [Regs.get_set, h7], by simp [Regs.get_set, h16],
    hm', ?_, hr⟩
  intro i hi
  have hread := fiveMemory_read mem 8 (k+1) (512+i) (by omega)
    (by rw [hm.size_eq]; unfold memSize; omega)
    (fun a ha ha' => initial_zero n a (by omega) (by rwa [hm.size_eq] at ha'))
    (fun j hj => by rw [hm.size_eq]; exact hcap j hj)
  have heq : (∃ j, j < k+1 ∧
      (512+i = 512+8+20*j ∨ 512+i = 512+8+20*j+3 ∨
       512+i = 512+8+20*j+10 ∨ 512+i = 512+8+20*j+13)) ↔ WM 7 i := by
    rw [five_marks]
    constructor
    · rintro ⟨j, _, he⟩
      refine ⟨j, ?_⟩
      rcases he with he | he | he | he <;> omega
    · rintro ⟨j, he⟩
      refine ⟨j, ?_, ?_⟩
      · by_cases hj : j = 0
        · omega
        · rw [ht]
          apply (hcount.2.2 j (by omega)).mp
          rcases he with he | he | he | he <;> omega
      · rcases he with he | he | he | he <;> omega
  change (fiveMemory mem 8 (k+1))[512+i]? = _
  rw [hread]
  by_cases hw : WM 7 i
  · rw [ite_eq_left (heq.mpr hw), bit_pos hi hw]
  · rw [ite_eq_right (fun h => hw (heq.mp h)), bit_neg (fun h => hw h.2)]

end TinyFive.CountingPrimesOddWheel
