import OddWheelCount

namespace TinyFive.CountingPrimesOddWheel

open OddSieveMath SieveMemory

private theorem prefix_sum_mono (f : Nat → Nat) {a b : Nat} (h : a ≤ b) :
    csum f a ≤ csum f b := by
  induction b with
  | zero => simp_all
  | succ b ih =>
    by_cases hab : a ≤ b
    · have := ih hab
      rw [csum_succ]
      omega
    · have : a = b+1 := by omega
      simp [this]

set_option maxRecDepth 10000 in
private theorem count_blocks (E : Nat) (f : Nat → Nat) (mem : Array (BitVec 8)) (out : String)
    (hE : E < 2^37) (hf : ∀ i, f i ≤ 1) (hmem : Prefix image mem 328)
    (flags : ∀ i, i < E → mem[512+i]? = some (BitVec.ofNat 8 (f i)))
    (pad : ∀ i, 496 ≤ i → i < 512 → mem[i]? = some 0)
    (q : Nat) (x : Regs 64) (a : BitVec 64) (hq : 0 < q) (hqE : q ≤ E)
    (h5 : x.get 5 = BitVec.ofNat 64 q) (h10 : x.get 10 = a) :
    ∃ fuel y, fuel ≤ 322*q ∧ y.get 10 = a - BitVec.ofNat 64 (csum f q) ∧
      run fuel ⟨x, 204, mem, [], out, .running⟩ = ⟨y, 292, mem, [], out, .running⟩ := by
  obtain ⟨steps, q', y, hsteps, hlt, _, _, hy10, hy5, hr⟩ :=
    count_chunk E q f a hE hq hqE hf x mem out hmem flags pad h5 h10
  by_cases hz : q' = 0
  · subst q'
    exact ⟨steps, y, by omega, by simpa using hy10, hr⟩
  · obtain ⟨rest, z, hrest, hz10, hzrun⟩ :=
      count_blocks E f mem out hE hf hmem flags pad q' y _ (by omega) (by omega)
        (hy5 (by omega)) hy10
    have hsum := Nat.sub_add_cancel (prefix_sum_mono f (Nat.le_of_lt hlt))
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, hsum] at hz10
    exact ⟨steps+rest, z, by omega, hz10,
      by simpa only [run_add, hr, hz, ite_false] using hzrun⟩
termination_by q

/-- The reverse counting pass consumes every live flag exactly once. -/
theorem count_correct (E : Nat) (f : Nat → Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hE : 0 < E ∧ E < 2^37) (hf : ∀ i, f i ≤ 1) (hmem : Prefix image mem 328)
    (flags : ∀ i, i < E → mem[512+i]? = some (BitVec.ofNat 8 (f i)))
    (pad : ∀ i, 496 ≤ i → i < 512 → mem[i]? = some 0)
    (h5 : x.get 5 = BitVec.ofNat 64 E) :
    ∃ fuel y, fuel ≤ 1+322*E ∧
      y.get 10 = BitVec.ofNat 64 (E+1) - BitVec.ofNat 64 (csum f E) ∧
      run fuel ⟨x, 200, mem, [], out, .running⟩ = ⟨y, 292, mem, [], out, .running⟩ := by
  obtain ⟨y, hy10, hy5, hyr⟩ := count_entry E x mem out hmem h5
  obtain ⟨fuel, z, hb, hz, hzr⟩ :=
    count_blocks E f mem out hE.2 hf hmem flags pad E y _ hE.1 (Nat.le_refl _) hy5 hy10
  exact ⟨1+fuel, z, by omega, hz, by rw [run_add, hyr, hzr]⟩

end TinyFive.CountingPrimesOddWheel
