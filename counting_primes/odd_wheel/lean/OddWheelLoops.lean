import OddWheelMarking

namespace TinyFive.CountingPrimesOddWheel
open SieveMemory

/-- Memory after n paired byte-store iterations. -/
def pairMarks : Nat → Nat → Nat → Nat → Array (BitVec 8) → Array (BitVec 8)
  | 0, _, _, _, m => m
  | n+1, a, b, d, m => pairMarks n (a+d) (b+d) d
      ((m.setIfInBounds (512+a) 1#8).setIfInBounds (512+b) 1#8)

/-- Bounded execution of the actual first marking back-edge.  The branch
conditions explicitly characterize the number of completed iterations. -/
theorem mark_plus_n (n a b d E cap : Nat) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String)
    (hn : 0 < n)
    (hm : Layout image 512 cap mem)
    (hbnd : ∀ j, j < n → 512+(a+d*j) < cap ∧ 512+(b+d*j) < cap ∧
      512+(a+d*j) < 2^64 ∧ 512+(b+d*j) < 2^64)
    (hnext : ∀ j, j < n → a+d*(j+1) < 2^64 ∧ b+d*(j+1)+7 < 2^64)
    (hbranch : ∀ j, j < n → (a+d*(j+1) < E ↔ j+1 < n))
    (hE : E < 2^64)
    (h12 : x.get 12 = BitVec.ofNat 64 a)
    (h13 : x.get 13 = BitVec.ofNat 64 (b+7))
    (h17 : x.get 17 = BitVec.ofNat 64 d)
    (h5 : x.get 5 = BitVec.ofNat 64 E)
    (h7 : x.get 7 = 16777217) :
    ∃ y, Layout image 512 cap (pairMarks n a b d mem) ∧
      y.get 12 = BitVec.ofNat 64 (a+d*n) ∧
      y.get 13 = BitVec.ofNat 64 (b+d*n+7) ∧
      (∀ r, r ≠ 12 → r ≠ 13 → y.get r = x.get r) ∧
      run (5*n) ⟨x, 128, mem, [], out, .running⟩ =
        ⟨y, 148, pairMarks n a b d mem, [], out, .running⟩ := by
  induction n generalizing a b x mem with
  | zero => omega
  | succ n ih =>
    let m := (mem.setIfInBounds (512+a) 1#8).setIfInBounds (512+b) 1#8
    let y := (x.set 12 (x.get 12 + x.get 17)).set 13 (x.get 13 + x.get 17)
    have bounds := hbnd 0 (by omega)
    have next := hnext 0 (by omega)
    have it := mark_plus_iteration x mem out cap a b hm (by simpa using bounds.1)
      (by simpa using bounds.2.1) (by simpa using bounds.2.2.1)
      (by simpa using bounds.2.2.2) h12 h13 h7
    have hy12 : y.get 12 = BitVec.ofNat 64 (a+d) := by
      simp [y, Regs.get_set, h12, h17, ← BitVec.ofNat_add]
    have hy13 : y.get 13 = BitVec.ofNat 64 (b+d+7) := by
      simp [y, Regs.get_set, h13, h17, ← BitVec.ofNat_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hyp : ∀ r, r ≠ 12 → r ≠ 13 → y.get r = x.get r := by
      intro r hr hs; by_cases hzero : r = 0
      · subst r; simp [Regs.get]
      · simp [y, Regs.get_set, Ne.symm hr, Ne.symm hs, hzero]
    have branch : (x.get 12 + x.get 17).ult (x.get 5) = decide (a+d < E) := by
      rw [h12, h17, h5, ← BitVec.ofNat_add]
      simp [BitVec.ult, Nat.mod_eq_of_lt (by simpa using next.1), Nat.mod_eq_of_lt hE]
    cases n with
    | zero =>
      have hnlt : ¬ a+d < E := by have := hbranch 0 (by omega); simp at this; omega
      refine ⟨y, ?_, ?_, ?_, hyp, ?_⟩
      · simpa [pairMarks, m] using it.1
      · simpa using hy12
      · simpa using hy13
      · simpa [pairMarks, m, y, branch, hnlt] using it.2
    | succ n =>
      have hlt : a+d < E := by have := hbranch 0 (by omega); simp at this; exact this
      have hbnd' : ∀ j, j < n+1 → 512+((a+d)+d*j) < cap ∧ 512+((b+d)+d*j) < cap ∧
          512+((a+d)+d*j) < 2^64 ∧ 512+((b+d)+d*j) < 2^64 := by
        intro j hj; have h := hbnd (j+1) (by omega); simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hnext' : ∀ j, j < n+1 → (a+d)+d*(j+1) < 2^64 ∧ (b+d)+d*(j+1)+7 < 2^64 := by
        intro j hj; have h := hnext (j+1) (by omega); simp only [Nat.mul_add] at h ⊢; omega
      have hbranch' : ∀ j, j < n+1 → ((a+d)+d*(j+1) < E ↔ j+1 < n+1) := by
        intro j hj; have h := hbranch (j+1) (by omega); simp only [Nat.mul_add] at h ⊢; omega
      obtain ⟨z, hzmem, hz12, hz13, hzother, hzrun⟩ := ih (a+d) (b+d) y m (by omega) it.1 hbnd' hnext' hbranch' hy12 hy13 (by simp [hyp 17 (by decide) (by decide), h17]) (by simp [hyp 5 (by decide) (by decide), h5]) (by simp [hyp 7 (by decide) (by decide), h7])
      refine ⟨z, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [pairMarks, m] using hzmem
      · rw [hz12]; congr 1; simp only [Nat.mul_add]; omega
      · rw [hz13]; congr 1; simp only [Nat.mul_add]; omega
      · intro r hr hs; rw [hzother r hr hs, hyp r hr hs]
      · rw [show 5*(n+1+1) = 5+5*(n+1) by omega, run_add]
        simp only [branch, hlt, decide_true, ↓reduceIte] at it
        rw [it.2]
        simpa [pairMarks, m, y] using hzrun

/-- Bounded execution of the actual second marking back-edge.  The branch
conditions explicitly characterize the number of completed iterations. -/
theorem mark_minus_n (n a b d E cap : Nat) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String)
    (hn : 0 < n)
    (hm : Layout image 512 cap mem)
    (hbnd : ∀ j, j < n → 512+(a+d*j) < cap ∧ 512+(b+d*j) < cap ∧
      512+(a+d*j) < 2^64 ∧ 512+(b+d*j) < 2^64)
    (hnext : ∀ j, j < n → a+d*(j+1) < 2^64 ∧ b+d*(j+1)+1 < 2^64)
    (hbranch : ∀ j, j < n → (a+d*(j+1) < E ↔ j+1 < n))
    (hE : E < 2^64)
    (h11 : x.get 11 = BitVec.ofNat 64 a)
    (h13 : x.get 13 = BitVec.ofNat 64 (b+1))
    (h15 : x.get 15 = BitVec.ofNat 64 d)
    (h5 : x.get 5 = BitVec.ofNat 64 E)
    (h7 : x.get 7 = 16777217) :
    ∃ y, Layout image 512 cap (pairMarks n a b d mem) ∧
      y.get 11 = BitVec.ofNat 64 (a+d*n) ∧
      y.get 13 = BitVec.ofNat 64 (b+d*n+1) ∧
      (∀ r, r ≠ 11 → r ≠ 13 → y.get r = x.get r) ∧
      run (5*n) ⟨x, 176, mem, [], out, .running⟩ =
        ⟨y, 196, pairMarks n a b d mem, [], out, .running⟩ := by
  induction n generalizing a b x mem with
  | zero => omega
  | succ n ih =>
    let m := (mem.setIfInBounds (512+a) 1#8).setIfInBounds (512+b) 1#8
    let y := (x.set 11 (x.get 11 + x.get 15)).set 13 (x.get 13 + x.get 15)
    have bounds := hbnd 0 (by omega)
    have next := hnext 0 (by omega)
    have it := mark_minus_iteration x mem out cap a b hm (by simpa using bounds.1)
      (by simpa using bounds.2.1) (by simpa using bounds.2.2.1)
      (by simpa using bounds.2.2.2) h11 h13 h7
    have hy11 : y.get 11 = BitVec.ofNat 64 (a+d) := by
      simp [y, Regs.get_set, h11, h15, ← BitVec.ofNat_add]
    have hy13 : y.get 13 = BitVec.ofNat 64 (b+d+1) := by
      simp [y, Regs.get_set, h13, h15, ← BitVec.ofNat_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hyp : ∀ r, r ≠ 11 → r ≠ 13 → y.get r = x.get r := by
      intro r hr hs; by_cases hzero : r = 0
      · subst r; simp [Regs.get]
      · simp [y, Regs.get_set, Ne.symm hr, Ne.symm hs, hzero]
    have branch : (x.get 11 + x.get 15).ult (x.get 5) = decide (a+d < E) := by
      rw [h11, h15, h5, ← BitVec.ofNat_add]
      simp [BitVec.ult, Nat.mod_eq_of_lt (by simpa using next.1), Nat.mod_eq_of_lt hE]
    cases n with
    | zero =>
      have hnlt : ¬ a+d < E := by have := hbranch 0 (by omega); simp at this; omega
      refine ⟨y, ?_, ?_, ?_, hyp, ?_⟩
      · simpa [pairMarks, m] using it.1
      · simpa using hy11
      · simpa using hy13
      · simpa [pairMarks, m, y, branch, hnlt] using it.2
    | succ n =>
      have hlt : a+d < E := by have := hbranch 0 (by omega); simp at this; exact this
      have hbnd' : ∀ j, j < n+1 → 512+((a+d)+d*j) < cap ∧ 512+((b+d)+d*j) < cap ∧
          512+((a+d)+d*j) < 2^64 ∧ 512+((b+d)+d*j) < 2^64 := by
        intro j hj; have h := hbnd (j+1) (by omega); simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hnext' : ∀ j, j < n+1 → (a+d)+d*(j+1) < 2^64 ∧ (b+d)+d*(j+1)+1 < 2^64 := by
        intro j hj; have h := hnext (j+1) (by omega); simp only [Nat.mul_add] at h ⊢; omega
      have hbranch' : ∀ j, j < n+1 → ((a+d)+d*(j+1) < E ↔ j+1 < n+1) := by
        intro j hj; have h := hbranch (j+1) (by omega); simp only [Nat.mul_add] at h ⊢; omega
      obtain ⟨z, hzmem, hz11, hz13, hzother, hzrun⟩ := ih (a+d) (b+d) y m (by omega) it.1 hbnd' hnext' hbranch' hy11 hy13 (by simp [hyp 15 (by decide) (by decide), h15]) (by simp [hyp 5 (by decide) (by decide), h5]) (by simp [hyp 7 (by decide) (by decide), h7])
      refine ⟨z, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [pairMarks, m] using hzmem
      · rw [hz11]; congr 1; simp only [Nat.mul_add]; omega
      · rw [hz13]; congr 1; simp only [Nat.mul_add]; omega
      · intro r hr hs; rw [hzother r hr hs, hyp r hr hs]
      · rw [show 5*(n+1+1) = 5+5*(n+1) by omega, run_add]
        simp only [branch, hlt, decide_true, ↓reduceIte] at it
        rw [it.2]
        simpa [pairMarks, m, y] using hzrun

/-- Extensional characterization of the bytes written by a bounded paired loop. -/
theorem pairMarks_get (n a b d i : Nat) (mem : Array (BitVec 8))
    (hi : 512+i < mem.size)
    (hb : ∀ j, j < n → 512+(a+d*j) < mem.size ∧ 512+(b+d*j) < mem.size) :
    (pairMarks n a b d mem)[512+i]? =
      if ∃ j, j < n ∧ (i = a+d*j ∨ i = b+d*j) then some 1#8 else mem[512+i]? := by
  classical
  induction n generalizing a b mem with
  | zero => simp [pairMarks]
  | succ n ih =>
    let m := (mem.setIfInBounds (512+a) 1#8).setIfInBounds (512+b) 1#8
    have hm : m.size = mem.size := by simp [m, size_update]
    have hb' : ∀ j, j < n → 512+((a+d)+d*j) < m.size ∧ 512+((b+d)+d*j) < m.size := by
      intro j hj
      rw [hm]
      have h := hb (j+1) (by omega)
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have he : (∃ j, j < n+1 ∧ (i = a+d*j ∨ i = b+d*j)) ↔
        i = a ∨ i = b ∨ ∃ j, j < n ∧ (i = (a+d)+d*j ∨ i = (b+d)+d*j) := by
      constructor
      · rintro ⟨j, hj, h⟩
        cases j with
        | zero => simp only [Nat.mul_zero, Nat.add_zero] at h; rcases h with h | h <;> simp [h]
        | succ j =>
          right; right; refine ⟨j, by omega, ?_⟩
          simp only [Nat.mul_add] at h ⊢
          omega
      · intro h
        rcases h with h | h | ⟨j, hj, h⟩
        · exact ⟨0, by omega, by simpa using Or.inl h⟩
        · exact ⟨0, by omega, by simpa using Or.inr h⟩
        · refine ⟨j+1, by omega, ?_⟩
          simp only [Nat.mul_add] at h ⊢
          omega
    simp only [pairMarks]
    rw [ih (a+d) (b+d) m (by rw [hm]; exact hi) hb']
    simp only [he]
    by_cases ha : i = a <;> by_cases hc : i = b
    · subst i; subst b
      have hr : m[512+a]? = some 1#8 := by
        dsimp [m]; rw [Array.getElem?_setIfInBounds_self_of_lt (by simp; exact hi)]
      simp [hr]
    · subst i
      have hr : m[512+a]? = some 1#8 := by
        dsimp [m]
        rw [Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_self_of_lt hi]
      simp [hr]
    · subst i
      have hr : m[512+b]? = some 1#8 := by
        dsimp [m]; rw [Array.getElem?_setIfInBounds_self_of_lt (by simp; exact hi)]
      simp [hr]
    · have hr : m[512+i]? = mem[512+i]? := by
        dsimp [m]
        rw [Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_ne (by omega)]
      simp [ha, hc, hr]

/-- Number of executions of the do-while loop. -/
def pairCount (a d E : Nat) : Nat := (E-a-1)/d+1

theorem pairCount_properties (a d E : Nat) (hd : 0 < d) :
    0 < pairCount a d E ∧ pairCount a d E ≤ E+1 ∧
    (∀ j, 0 < j → (a+d*j < E ↔ j < pairCount a d E)) := by
  have hdiv := Nat.div_le_self (E-a-1) d
  refine ⟨by simp [pairCount], by dsimp [pairCount]; omega, ?_⟩
  intro j hj
  by_cases ha : a < E
  · have h := Nat.le_div_iff_mul_le (x := j) (y := E-a-1) hd
    simp only [pairCount]
    rw [show (a+d*j < E) ↔ j*d ≤ E-a-1 by rw [Nat.mul_comm j d]; omega]
    omega
  · have hzero : E-a-1 = 0 := by omega
    simp only [pairCount, hzero, Nat.zero_div, Nat.zero_add]
    have hmul := Nat.le_mul_of_pos_left j hd
    omega

/-- The first real marking loop terminates with at most 5*(E+1) instructions.
The zeroth iteration is unconditional, even if its initial cursor exceeds E. -/
theorem mark_plus_loop (a b d E cap : Nat) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String)
    (hd : 0 < d) (hE : E < 2^64)
    (hm : Layout image 512 cap mem)
    (hb : ∀ j, j = 0 ∨ a+d*j < E →
      512+(a+d*j) < cap ∧ 512+(b+d*j) < cap ∧
      512+(a+d*j) < 2^64 ∧ 512+(b+d*j) < 2^64 ∧
      a+d*(j+1) < 2^64 ∧ b+d*(j+1)+7 < 2^64)
    (h12 : x.get 12 = BitVec.ofNat 64 a)
    (h13 : x.get 13 = BitVec.ofNat 64 (b+7))
    (h17 : x.get 17 = BitVec.ofNat 64 d)
    (h5 : x.get 5 = BitVec.ofNat 64 E) (h7 : x.get 7 = 16777217) :
    ∃ y, Layout image 512 cap (pairMarks (pairCount a d E) a b d mem) ∧
      y.get 12 = BitVec.ofNat 64 (a+d*pairCount a d E) ∧
      y.get 13 = BitVec.ofNat 64 (b+d*pairCount a d E+7) ∧
      (∀ r, r ≠ 12 → r ≠ 13 → y.get r = x.get r) ∧
      run (5*pairCount a d E) ⟨x, 128, mem, [], out, .running⟩ =
        ⟨y, 148, pairMarks (pairCount a d E) a b d mem, [], out, .running⟩ := by
  have hp := pairCount_properties a d E hd
  have active : ∀ j, j < pairCount a d E → j = 0 ∨ a+d*j < E := by
    intro j hj; by_cases h : j = 0
    · exact Or.inl h
    · exact Or.inr ((hp.2.2 j (by omega)).mpr hj)
  apply mark_plus_n (pairCount a d E) a b d E cap x mem out hp.1 hm
  · intro j hj; have h := hb j (active j hj); exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · intro j hj; have h := hb j (active j hj); exact h.2.2.2.2
  · intro j hj; exact hp.2.2 (j+1) (by omega)
  · exact hE
  · exact h12
  · exact h13
  · exact h17
  · exact h5
  · exact h7

/-- The second real marking loop terminates with at most 5*(E+1) instructions.
The zeroth iteration is unconditional, even if its initial cursor exceeds E. -/
theorem mark_minus_loop (a b d E cap : Nat) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String)
    (hd : 0 < d) (hE : E < 2^64)
    (hm : Layout image 512 cap mem)
    (hb : ∀ j, j = 0 ∨ a+d*j < E →
      512+(a+d*j) < cap ∧ 512+(b+d*j) < cap ∧
      512+(a+d*j) < 2^64 ∧ 512+(b+d*j) < 2^64 ∧
      a+d*(j+1) < 2^64 ∧ b+d*(j+1)+1 < 2^64)
    (h11 : x.get 11 = BitVec.ofNat 64 a)
    (h13 : x.get 13 = BitVec.ofNat 64 (b+1))
    (h15 : x.get 15 = BitVec.ofNat 64 d)
    (h5 : x.get 5 = BitVec.ofNat 64 E) (h7 : x.get 7 = 16777217) :
    ∃ y, Layout image 512 cap (pairMarks (pairCount a d E) a b d mem) ∧
      y.get 11 = BitVec.ofNat 64 (a+d*pairCount a d E) ∧
      y.get 13 = BitVec.ofNat 64 (b+d*pairCount a d E+1) ∧
      (∀ r, r ≠ 11 → r ≠ 13 → y.get r = x.get r) ∧
      run (5*pairCount a d E) ⟨x, 176, mem, [], out, .running⟩ =
        ⟨y, 196, pairMarks (pairCount a d E) a b d mem, [], out, .running⟩ := by
  have hp := pairCount_properties a d E hd
  have active : ∀ j, j < pairCount a d E → j = 0 ∨ a+d*j < E := by
    intro j hj; by_cases h : j = 0
    · exact Or.inl h
    · exact Or.inr ((hp.2.2 j (by omega)).mpr hj)
  apply mark_minus_n (pairCount a d E) a b d E cap x mem out hp.1 hm
  · intro j hj; have h := hb j (active j hj); exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · intro j hj; have h := hb j (active j hj); exact h.2.2.2.2
  · intro j hj; exact hp.2.2 (j+1) (by omega)
  · exact hE
  · exact h11
  · exact h13
  · exact h15
  · exact h5
  · exact h7

open Classical in
/-- On in-range indices, the actual stores realize exactly the union of
    the old marked predicate and the two arithmetic progressions. -/
theorem pairMarks_flags (a b d E cap : Nat) (mem : Array (BitVec 8))
    (P : Nat → Prop) [DecidablePred P] (hd : 0 < d) (hab : a ≤ b)
    (hm : Layout image 512 cap mem) (hcap : 512+E ≤ cap)
    (hb : ∀ j, j = 0 ∨ a+d*j < E →
      512+(a+d*j) < cap ∧ 512+(b+d*j) < cap)
    (hf : ∀ i, i < E → mem[512+i]? = some (if P i then 1#8 else 0#8)) :
    ∀ i, i < E → (pairMarks (pairCount a d E) a b d mem)[512+i]? =
      some (if P i ∨ (∃ j, i = a+d*j ∨ i = b+d*j) then 1#8 else 0#8) := by
  classical
  intro i hi
  have hp := pairCount_properties a d E hd
  have bounds : ∀ j, j < pairCount a d E →
      512+(a+d*j) < mem.size ∧ 512+(b+d*j) < mem.size := by
    intro j hj
    have active : j = 0 ∨ a+d*j < E := by
      by_cases h : j = 0
      · exact Or.inl h
      · exact Or.inr ((hp.2.2 j (by omega)).mpr hj)
    rw [hm.size_eq]; exact hb j active
  have hx : (∃ j, j < pairCount a d E ∧ (i = a+d*j ∨ i = b+d*j)) ↔
      ∃ j, i = a+d*j ∨ i = b+d*j := by
    constructor
    · rintro ⟨j, _, h⟩; exact ⟨j, h⟩
    · rintro ⟨j, h⟩
      refine ⟨j, ?_, h⟩
      by_cases hj : j = 0
      · rw [hj]; exact hp.1
      · apply (hp.2.2 j (by omega)).mp
        rcases h with h | h <;> omega
  rw [pairMarks_get _ _ _ _ _ _ (by rw [hm.size_eq]; omega) bounds, hf i hi]
  simp only [hx]
  by_cases hP : P i <;> by_cases hX : ∃ j, i = a+d*j ∨ i = b+d*j <;> simp [hP, hX]

end TinyFive.CountingPrimesOddWheel
