import OddWheelFlags
import OddWheelSquares
import OddWheelLoops

namespace TinyFive.CountingPrimesOddWheel

open OddWheelMath SieveMemory

set_option maxHeartbeats 1000000 in
theorem minus_candidate_correct (n k : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (hn : n < 10^11) (hk : 1 ≤ k) (hentry : k=1 ∨ sqPlus k < E n)
    (hm : Layout image 512 (memSize n) mem) (hf : WheelFlags mem (E n) (6*k+5))
    (h5 : x.get 5 = BitVec.ofNat 64 (E n)) (h7 : x.get 7 = 16777217)
    (h11 : x.get 11 = BitVec.ofNat 64 (sqMinus (k+1)))
    (h14 : x.get 14 = BitVec.ofNat 64 (8*(k+1)))
    (h15 : x.get 15 = BitVec.ofNat 64 (12*k-2))
    (h16 : x.get 16 = BitVec.ofNat 64 (2*k)) :
    ∃ fuel y mem', fuel ≤ 7+5*(E n+1) ∧ PairInv y (E n) (k+1) ∧
      Layout image 512 (memSize n) mem' ∧ WheelFlags mem' (E n) (6*(k+1)+1) ∧
      run fuel ⟨x, 148, mem, [], "", .running⟩ = ⟨y, 196, mem', [], "", .running⟩ := by
  classical
  let p := 6*k+5
  let a := sqMinus (k+1)
  let b := a+4*k+3
  let d := 2*p
  let q := 2*k+1
  have hp : 5 ≤ p := by dsimp [p]; omega
  have hd : 0 < d := by dsimp [d]; omega
  have ha : value a = p*p := minus_square_value k
  have hb : value b = p*(p+2) := by
    dsimp [b,a,p]
    rw [minus_second_value]
  have hab : a ≤ b := by dsimp [b]; omega
  have hq : value q = p := value_odd k
  have hnext : p+2 = 6*(k+1)+1 := by dsimp [p]; omega
  have hphase : (p%6=5 ∧ 2=2) ∨ (p%6=1 ∧ 2=4) := by dsimp [p]; omega
  have hcap64 := memSize_lt_64 n (by omega)
  have hentry' : sqPlus k < E n ∨ (6*k+1 = 7 ∧ sqPlus k = 16 ∧ p = 11) := by
    rcases hentry with rfl | ht
    · exact Or.inr (by decide)
    · exact Or.inl ht
  have bounds : ∀ j, j = 0 ∨ a+d*j < E n →
      512+(a+d*j) < memSize n ∧ 512+(b+d*j) < memSize n := by
    intro j hj
    have hcur : a+d*j = a ∨ ∃ prev, prev < E n ∧ a+d*j = prev+2*p := by
      rcases j with _ | j
      · exact Or.inl (by simp)
      · right
        have hprev : a+d*j ≤ a+d*(j+1) := Nat.add_le_add_left
          (Nat.mul_le_mul_left d (by omega)) a
        refine ⟨a+d*j, ?_, ?_⟩
        · omega
        · simp [d, Nat.mul_add, Nat.add_assoc]
    have hpair : value (b+d*j) = value (a+d*j)+2*p := by
      change value (b+2*p*j) = value (a+2*p*j)+2*p
      rw [value_stride_many, value_stride_many, ha, hb, Nat.mul_add]
      rw [Nat.mul_comm p 2]
      omega
    exact minus_loop_capacity n (6*k+1) p (sqPlus k) a _ _ (by dsimp [p]; omega)
      (by dsimp [p]; omega) hentry' (sqPlus_value k) ha hcur hpair
  have hqcap : 512+q < memSize n := by
    have h := (bounds 0 (Or.inl rfl)).1
    have hs := Nat.le_mul_self p
    have hqa : q ≤ a := by
      have hv : value a ≤ 3*a+2 := by unfold value; split <;> omega
      dsimp [p,q] at hs ⊢
      rw [← ha] at hs
      omega
    simp only [Nat.mul_zero, Nat.add_zero] at h
    omega
  have hxread : ∃ v, mem[512+q]? = some v := by
    have h : 512+q < mem.size := by rwa [hm.size_eq]
    exact ⟨mem[512+q], Array.getElem?_eq_getElem h⟩
  obtain ⟨v,hv⟩ := hxread
  let y := ((x.set 15 (x.get 15+12)).set 16 (x.get 16+2)).set 12 (x.get 11+x.get 14)
  have hxy := minus_header_arithmetic x mem "" (hm.code_eq.mono (by omega))
  have hy : PairInv y (E n) (k+1) := by
    simp only [PairInv, y, Regs.get_set, h5,h7,h11,h14,h15,h16]
    repeat' constructor
    · change BitVec.ofNat 64 a + BitVec.ofNat 64 (8*(k+1)) = _
      rw [← BitVec.ofNat_add, ← plus_square_add]
      rfl
    · change BitVec.ofNat 64 (12*k-2) + BitVec.ofNat 64 12 = _
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    · change BitVec.ofNat 64 (2*k) + BitVec.ofNat 64 2 = _
      rw [← BitVec.ofNat_add]
      congr 1
  have hy11 : y.get 11 = BitVec.ofNat 64 a := by simp [y, Regs.get_set, h11, a]
  have hy16 := hy.2.2.2.2.2
  let z := y.set 6 (v.setWidth 64)
  have hyz := minus_flag_test_byte y mem "" q v (hm.code_eq.mono (by omega))
    (by omega) (by exact hy.2.2.2.2.2) hv
  have hz : PairInv z (E n) (k+1) := by
    simpa [z, PairInv, Regs.get_set] using hy
  by_cases hzero : v.setWidth 64 = 0#64
  · let w := (z.set 13 (z.get 11+z.get 16)).set 13 (z.get 11+z.get 16+z.get 16)
    have hzw := minus_prepare z mem "" (hm.code_eq.mono (by omega))
    have hyz' : run 2 ⟨y, 160, mem, [], "", .running⟩ = ⟨z, 168, mem, [], "", .running⟩ := by
      simpa [z, hzero] using hyz
    have hw : PairInv w (E n) (k+1) := by
      simpa [w, PairInv, Regs.get_set] using hz
    have hw11 : w.get 11 = BitVec.ofNat 64 a := by simp [w, z, Regs.get_set, hy11]
    have hw13 : w.get 13 = BitVec.ofNat 64 (b+1) := by
      have hz11 : z.get 11 = BitVec.ofNat 64 a := by simp [z, Regs.get_set, hy11]
      have hz16 : z.get 16 = BitVec.ofNat 64 (2*(k+1)) := hz.2.2.2.2.2
      have he : w.get 13 = z.get 11 + z.get 16 + z.get 16 := by simp [w, Regs.get_set]
      rw [he, hz11, hz16, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 1
      dsimp [b]; omega
    have hw15 : w.get 15 = BitVec.ofNat 64 d := by
      rw [hw.2.2.2.2.1]
      congr 1
      dsimp [d,p]; omega
    have hbounds : ∀ j, j = 0 ∨ a+d*j < E n →
        512+(a+d*j) < memSize n ∧ 512+(b+d*j) < memSize n ∧
        512+(a+d*j) < 2^64 ∧ 512+(b+d*j) < 2^64 ∧
        a+d*(j+1) < 2^64 ∧ b+d*(j+1)+1 < 2^64 := by
      intro j hj
      obtain ⟨hl,hr⟩ := bounds j hj
      have hs : Nat.sqrt n ≤ n := by
        have hm' := Nat.sqrt_le n
        by_cases he : Nat.sqrt n = 0
        · omega
        · have := Nat.mul_le_mul_left (Nat.sqrt n) (show 1 ≤ Nat.sqrt n by omega)
          omega
      have hk' := pair_k_le n k hentry
      have hc : memSize n < 10^12 := by unfold memSize; omega
      have hd' : d < 10^13 := by dsimp [d,p]; omega
      simp only [Nat.mul_add, Nat.mul_one]
      exact ⟨hl,hr,by omega,by omega,by omega,by omega⟩
    have hE := E_le_div3 n
    obtain ⟨t, hmt, _, _, ht, hrun⟩ :=
      mark_minus_loop a b d (E n) (memSize n) w mem "" hd (by omega) hm hbounds
        hw11 hw13 hw15 hw.1 hw.2.1
    let mem' := pairMarks (pairCount a d (E n)) a b d mem
    have hft : WheelFlags mem' (E n) (p+2) := by
      apply flags_mark hf hp hphase ha hb
      intro i hi
      have hpc := (pairCount_properties a d (E n) hd).2.2
      have hbc : ∀ j, j < pairCount a d (E n) →
          512+(a+d*j) < mem.size ∧ 512+(b+d*j) < mem.size := by
        intro j hj
        rw [hm.size_eq]
        apply bounds
        by_cases hn : j = 0
        · exact Or.inl hn
        · exact Or.inr ((hpc j (by omega)).mpr hj)
      have hic : 512+i < mem.size := by rw [hm.size_eq]; unfold memSize; omega
      change _ = (if (∃ j, i = a+d*j ∨ i = b+d*j) then some 1 else _)
      rw [pairMarks_get _ _ _ _ _ _ hic hbc]
      congr 1
      apply propext
      constructor
      · rintro ⟨j, _, hj⟩
        exact ⟨j, hj⟩
      · rintro ⟨j, hj⟩
        refine ⟨j, ?_, hj⟩
        by_cases hz : j = 0
        · rw [hz]; exact (pairCount_properties a d (E n) hd).1
        · apply (hpc j (by omega)).mp
          rcases hj with hj | hj <;> omega
    rw [hnext] at hft
    refine ⟨3+2+2+5*pairCount a d (E n), t, mem', ?_, ?_, hmt, hft, ?_⟩
    · have h := (pairCount_properties a d (E n) hd).2.1
      omega
    · simpa [PairInv, ht] using hw
    · change run (3+2+2+_) _ = _
      rw [run_add, run_add, run_add]
      change run _ (run 2 (run 2 (run 3 ⟨x, 148, mem, [], "", .running⟩))) = _
      rw [hxy]
      change run _ (run 2 (run 2 ⟨y, 160, mem, [], "", .running⟩)) = _
      rw [hyz', hzw]
      exact hrun
  · have hskip : WheelFlags mem (E n) (p+2) := by
      apply flags_skip hf hp hphase hq
      intro _ hz
      rw [hv] at hz
      have hv0 : v = 0 := Option.some.inj hz
      exact hzero (by rw [hv0]; rfl)
    rw [hnext] at hskip
    refine ⟨5, z, mem, by omega, hz, hm, hskip, ?_⟩
    have hyz' : run 2 ⟨y, 160, mem, [], "", .running⟩ = ⟨z, 196, mem, [], "", .running⟩ := by
      simpa [z, hzero] using hyz
    change run (3+2) _ = _
    rw [run_add, hxy]
    exact hyz'

end TinyFive.CountingPrimesOddWheel
