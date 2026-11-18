import OddWheelLoops
import OddWheelFlags
import OddWheelSquares

namespace TinyFive.CountingPrimesOddWheel
open SieveMemory OddWheelMath Classical

/-- The finite bottom-tested loop marks precisely the two infinite progressions
    at every index which will later be counted. -/
theorem pairMarks_counted (a b d K cap : Nat) (mem : Array (BitVec 8))
    (hd : 0 < d) (hab : a ≤ b) (hm : Layout image 512 cap mem)
    (hK : 512+K ≤ cap)
    (hb : ∀ j, j = 0 ∨ a+d*j < K → 512+(a+d*j) < cap ∧ 512+(b+d*j) < cap) :
    ∀ i, i < K → (pairMarks (pairCount a d K) a b d mem)[512+i]? =
      if ∃ j, i = a+d*j ∨ i = b+d*j then some 1 else mem[512+i]? := by
  classical
  have hp := pairCount_properties a d K hd
  intro i hi
  have hcap : ∀ j, j < pairCount a d K →
      512+(a+d*j) < mem.size ∧ 512+(b+d*j) < mem.size := by
    intro j hj
    have hactive : j = 0 ∨ a+d*j < K := by
      by_cases hz : j = 0
      · exact Or.inl hz
      · exact Or.inr ((hp.2.2 j (by omega)).mpr hj)
    rw [hm.size_eq]
    exact hb j hactive
  rw [pairMarks_get _ _ _ _ _ _ (by rw [hm.size_eq]; omega) hcap]
  congr 1
  apply propext
  constructor
  · rintro ⟨j, _, hj⟩
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_, hj⟩
    by_cases hz : j = 0
    · subst j; exact hp.1
    · apply (hp.2.2 j (by omega)).mp
      rcases hj with h | h <;> omega

/-- Execute one first-kind candidate, parameterized by its proven cursor
    arithmetic and memory bounds. This includes both the skip and mark paths. -/
theorem plus_candidate_general (n p q a b : Nat) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String) (v : BitVec 8)
    (hp : 5 ≤ p) (hphase : p%6=1) (hq : value q = p)
    (ha : value a = p*p) (hbval : value b = p*(p+4)) (hab : a ≤ b)
    (hm : Layout image 512 (memSize n) mem)
    (hflags : WheelFlags mem (E n) p) (hcap : 512+E n ≤ memSize n)
    (hbound : ∀ j, j = 0 ∨ a+2*p*j < E n →
      512+(a+2*p*j) < memSize n ∧ 512+(b+2*p*j) < memSize n ∧
      512+(a+2*p*j) < 2^64 ∧ 512+(b+2*p*j) < 2^64 ∧
      a+2*p*(j+1) < 2^64 ∧ b+2*p*(j+1)+7 < 2^64)
    (hq64 : q+512 < 2^64) (hread : mem[512+q]? = some v)
    (h5 : x.get 5 = BitVec.ofNat 64 (E n)) (h7 : x.get 7 = 16777217)
    (h12 : x.get 12 = BitVec.ofNat 64 a) (h16 : x.get 16 = BitVec.ofNat 64 q)
    (h13 : x.get 12 + x.get 14 = BitVec.ofNat 64 (b+7))
    (h17 : x.get 15 + 4#64 = BitVec.ofNat 64 (2*p)) (hE : E n < 2^64) :
    ∃ fuel y mem', fuel ≤ 4+5*(E n+1) ∧ Layout image 512 (memSize n) mem' ∧
      WheelFlags mem' (E n) (p+4) ∧
      (∀ r, r ≠ 6 → r ≠ 12 → r ≠ 13 → r ≠ 17 → y.get r = x.get r) ∧
      run fuel ⟨x, 112, mem, [], out, .running⟩ = ⟨y, 148, mem', [], out, .running⟩ := by
  let z := x.set 6 (v.setWidth 64)
  have htest := plus_flag_test_byte x mem out q v (hm.code_eq.mono (by omega)) hq64 h16 hread
  by_cases hv : v.setWidth 64 = 0#64
  · have ht : run 2 ⟨x, 112, mem, [], out, .running⟩ = ⟨z, 120, mem, [], out, .running⟩ := by
      simpa [z, hv] using htest
    let w := (z.set 13 (z.get 12 + z.get 14)).set 17 (z.get 15 + 4)
    have hprep := plus_prepare z mem out (hm.code_eq.mono (by omega))
    have w12 : w.get 12 = BitVec.ofNat 64 a := by simp [w, z, Regs.get_set, h12]
    have w13 : w.get 13 = BitVec.ofNat 64 (b+7) := by simp [w, z, Regs.get_set, h13]
    have w17 : w.get 17 = BitVec.ofNat 64 (2*p) := by simp [w, z, Regs.get_set, h17]
    have w5 : w.get 5 = BitVec.ofNat 64 (E n) := by simp [w, z, Regs.get_set, h5]
    have w7 : w.get 7 = 16777217 := by simp [w, z, Regs.get_set, h7]
    obtain ⟨y, hl, _, _, hr, hs⟩ := mark_plus_loop a b (2*p) (E n) (memSize n)
      w mem out (by omega) hE hm hbound w12 w13 w17 w5 w7
    have hflags' : WheelFlags (pairMarks (pairCount a (2*p) (E n)) a b (2*p) mem)
        (E n) (p+4) := by
      apply flags_mark hflags hp (Or.inr ⟨hphase, rfl⟩) ha hbval
      exact pairMarks_counted a b (2*p) (E n) (memSize n) mem (by omega) hab hm hcap
        (by intro j hj; exact ⟨(hbound j hj).1, (hbound j hj).2.1⟩)
    have hcount := (pairCount_properties a (2*p) (E n) (by omega)).2.1
    refine ⟨4+5*pairCount a (2*p) (E n), y, _, by omega, hl, hflags', ?_, ?_⟩
    · intro r h6 h12' h13' h17'
      rw [hr r h12' h13']
      by_cases hz : r = 0
      · subst r; simp [Regs.get_zero]
      · simp [w, z, Regs.get_set, hz, Ne.symm h6, Ne.symm h13', Ne.symm h17']
    · rw [show 4+5*pairCount a (2*p) (E n) = 2+(2+5*pairCount a (2*p) (E n)) by omega,
        run_add, ht, run_add, hprep]
      exact hs
  · have ht : run 2 ⟨x, 112, mem, [], out, .running⟩ = ⟨z, 148, mem, [], out, .running⟩ := by
      simpa [z, hv] using htest
    have hnonzero : q < E n → mem[512+q]? ≠ some 0 := by
      intro _ hz
      rw [hread] at hz
      have : v = 0 := Option.some.inj hz
      subst v
      simp at hv
    refine ⟨2, z, mem, by omega, hm, flags_skip hflags hp (Or.inr ⟨hphase, rfl⟩) hq hnonzero, ?_, ht⟩
    intro r h6 _ _ _
    by_cases hz : r = 0
    · subst r; simp [Regs.get_zero]
    · simp [z, Regs.get_set, hz, Ne.symm h6]

set_option maxHeartbeats 1000000 in
/-- Execute the plus candidate from the pair header to the minus header. -/
theorem plus_candidate_correct (n k : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (hn : n < 10^11) (hk : 1 ≤ k) (hentry : k=1 ∨ sqPlus k < E n)
    (hm : Layout image 512 (memSize n) mem) (hf : WheelFlags mem (E n) (6*k+1))
    (hin : PairInv x (E n) k) :
    ∃ fuel y mem', fuel ≤ 7+5*(E n+1) ∧
      y.get 5 = BitVec.ofNat 64 (E n) ∧ y.get 7 = 16777217 ∧
      y.get 11 = BitVec.ofNat 64 (sqMinus (k+1)) ∧
      y.get 14 = BitVec.ofNat 64 (8*(k+1)) ∧
      y.get 15 = BitVec.ofNat 64 (12*k-2) ∧ y.get 16 = BitVec.ofNat 64 (2*k) ∧
      Layout image 512 (memSize n) mem' ∧ WheelFlags mem' (E n) (6*k+5) ∧
      run fuel ⟨x, 100, mem, [], "", .running⟩ = ⟨y, 148, mem', [], "", .running⟩ := by
  classical
  let p := 6*k+1
  let a := sqPlus k
  let b := a+8*k+1
  let d := 2*p
  let q := 2*k
  have hp : 5 ≤ p := by dsimp [p]; omega
  have ha : value a = p*p := sqPlus_value k
  have hb : value b = p*(p+4) := by
    dsimp [b,a,p]; rw [plus_second_value]
  have hab : a ≤ b := by dsimp [b]; omega
  have hq : value q = p := value_even k
  have hentry' : a < E n ∨ (p = 7 ∧ a = 16) := by
    rcases hentry with rfl | h
    · exact Or.inr (by decide)
    · exact Or.inl h
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
    have hpair : value (b+d*j) = value (a+d*j)+4*p := by
      change value (b+2*p*j) = value (a+2*p*j)+4*p
      rw [value_stride_many, value_stride_many, ha, hb, Nat.mul_add]
      rw [Nat.mul_comm p 4]
      omega
    exact plus_loop_capacity n p a _ _ ha hentry' hcur hpair
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
  have hbounds : ∀ j, j = 0 ∨ a+d*j < E n →
      512+(a+d*j) < memSize n ∧ 512+(b+d*j) < memSize n ∧
      512+(a+d*j) < 2^64 ∧ 512+(b+d*j) < 2^64 ∧
      a+d*(j+1) < 2^64 ∧ b+d*(j+1)+7 < 2^64 := by
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
  let y := ((x.set 11 (x.get 12 + x.get 14)).set 14 (x.get 14 + 8)).set 11
        (x.get 12 + x.get 14 + (x.get 14 + 8))
  have hxy := pair_header_arithmetic x mem "" (hm.code_eq.mono (by omega))
  have hy5 : y.get 5 = BitVec.ofNat 64 (E n) := by simp [y, Regs.get_set, hin.1]
  have hy7 : y.get 7 = 16777217 := by simp [y, Regs.get_set, hin.2.1]
  have hy11 : y.get 11 = BitVec.ofNat 64 (sqMinus (k+1)) := by
    simp only [y, Regs.get_set, hin.2.2.1, hin.2.2.2.1]
    change BitVec.ofNat 64 a + BitVec.ofNat 64 (8*k) + (BitVec.ofNat 64 (8*k) + 8#64) = _
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    rw [minus_square_add]
    dsimp [a]; omega
  have hy14 : y.get 14 = BitVec.ofNat 64 (8*(k+1)) := by
    simp [y, Regs.get_set, hin.2.2.2.1, ← BitVec.ofNat_add, Nat.mul_add]
  have hy15 : y.get 15 = BitVec.ofNat 64 (12*k-2) := by simp [y, Regs.get_set, hin.2.2.2.2.1]
  have hy16 : y.get 16 = BitVec.ofNat 64 q := by simp [y, Regs.get_set, hin.2.2.2.2.2, q]
  have hy12 : y.get 12 = BitVec.ofNat 64 a := by simp [y, Regs.get_set, hin.2.2.1, a, sqPlus]
  have hy13 : y.get 12 + y.get 14 = BitVec.ofNat 64 (b+7) := by
    rw [hy12, hy14, ← BitVec.ofNat_add]
    congr 1
  have hy17 : y.get 15 + 4#64 = BitVec.ofNat 64 (2*p) := by
    rw [hy15, ← BitVec.ofNat_add]; congr 1
    dsimp [p]; omega
  have he := E_le_div3 n
  obtain ⟨fuel, z, mem', hfuel, hl, hflags, hr, hrun⟩ :=
    plus_candidate_general n p q a b y mem "" v hp (by dsimp [p]; omega) hq ha hb hab
      hm hf (by unfold memSize; omega) hbounds (by have := memSize_lt_64 n (by omega); omega)
      hv hy5 hy7 hy12 hy16 hy13 hy17 (by omega)
  refine ⟨3+fuel, z, mem', by omega, ?_, ?_, ?_, ?_, ?_, ?_, hl, ?_, ?_⟩
  · rw [hr 5 (by decide) (by decide) (by decide) (by decide)]; exact hy5
  · rw [hr 7 (by decide) (by decide) (by decide) (by decide)]; exact hy7
  · rw [hr 11 (by decide) (by decide) (by decide) (by decide)]; exact hy11
  · rw [hr 14 (by decide) (by decide) (by decide) (by decide)]; exact hy14
  · rw [hr 15 (by decide) (by decide) (by decide) (by decide)]; exact hy15
  · rw [hr 16 (by decide) (by decide) (by decide) (by decide)]; exact hy16
  · simpa [p] using hflags
  · rw [run_add, hxy]; exact hrun

end TinyFive.CountingPrimesOddWheel
