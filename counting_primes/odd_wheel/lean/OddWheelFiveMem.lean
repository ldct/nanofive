import OddWheelFive

namespace TinyFive.CountingPrimesOddWheel
open SieveMemory
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem fiveMemory_read_below (mem : Array (BitVec 8)) (a t i : Nat)
    (hi : i < 512+a) : (fiveMemory mem a t)[i]? = mem[i]? := by
  induction t generalizing mem a with
  | zero => rfl
  | succ t ih =>
    rw [fiveMemory_succ, ih _ _ (by omega)]
    simp only [fiveWord, Array.getElem?_setIfInBounds, size_update]
    simp only [if_neg (show 512+a+10+3 ≠ i by omega),
      if_neg (show 512+a+10+2 ≠ i by omega), if_neg (show 512+a+10+1 ≠ i by omega),
      if_neg (show 512+a+10 ≠ i by omega), if_neg (show 512+a+3 ≠ i by omega),
      if_neg (show 512+a+2 ≠ i by omega), if_neg (show 512+a+1 ≠ i by omega),
      if_neg (show 512+a ≠ i by omega)]

theorem fiveMemory_read_from (mem : Array (BitVec 8)) (a t i : Nat)
    (hi : 512+a ≤ i) (his : i < mem.size)
    (hz : ∀ q, 512+a ≤ q → q < mem.size → mem[q]? = some 0#8)
    (hb : ∀ j, j < t → 512+a+20*j+13 < mem.size) :
    (fiveMemory mem a t)[i]? =
      if ∃ j, j < t ∧ (i = 512+a+20*j ∨ i = 512+a+20*j+3 ∨
        i = 512+a+20*j+10 ∨ i = 512+a+20*j+13)
      then some 1#8 else some 0#8 := by
  induction t generalizing mem a with
  | zero => simp [fiveMemory_zero, hz i hi his]
  | succ t ih =>
    let m := fiveWord (fiveWord mem (512+a)) (512+a+10)
    have hs : m.size = mem.size := by simp [m, fiveWord, size_update]
    have hread : ∀ q, m[q]? = if q = 512+a+13 ∨ q = 512+a+10 ∨ q = 512+a+3 ∨ q = 512+a then some 1#8 else if q = 512+a+12 ∨ q = 512+a+11 ∨ q = 512+a+2 ∨ q = 512+a+1 then some 0#8 else mem[q]? := by
      intro q
      exact five_stores_read mem (512+a) q (hb 0 (by omega))
    by_cases hlow : i < 512+a+20
    · rw [fiveMemory_succ, fiveMemory_read_below m (a+20) t i (by omega), hread]
      have heq : (∃ j, j < t+1 ∧ (i = 512+a+20*j ∨ i = 512+a+20*j+3 ∨
          i = 512+a+20*j+10 ∨ i = 512+a+20*j+13)) ↔
          (i = 512+a+13 ∨ i = 512+a+10 ∨ i = 512+a+3 ∨ i = 512+a) := by
        constructor
        · rintro ⟨j, hj, h | h | h | h⟩ <;> omega
        · intro h; refine ⟨0, by omega, ?_⟩; simp only [Nat.mul_zero, Nat.add_zero]; omega
      simp only [heq]
      split <;> simp_all [hz i hi his]
    · have hz' : ∀ q, 512+(a+20) ≤ q → q < m.size → m[q]? = some 0#8 := by
        intro q hq hqs
        rw [hread]
        have hn : ¬ (q = 512+a+13 ∨ q = 512+a+10 ∨ q = 512+a+3 ∨ q = 512+a) := by omega
        simp only [if_neg hn]
        split
        · rfl
        · exact hz q (by omega) (by simpa [hs] using hqs)
      have hb' : ∀ j, j < t → 512+(a+20)+20*j+13 < m.size := by
        intro j hj
        rw [hs]
        have h := hb (j+1) (by omega)
        omega
      rw [fiveMemory_succ, ih m (a+20) (by omega) (by simpa [hs] using his) hz' hb']
      have heq : (∃ j, j < t ∧ (i = 512+(a+20)+20*j ∨ i = 512+(a+20)+20*j+3 ∨ i = 512+(a+20)+20*j+10 ∨ i = 512+(a+20)+20*j+13)) ↔
          (∃ j, j < t+1 ∧ (i = 512+a+20*j ∨ i = 512+a+20*j+3 ∨ i = 512+a+20*j+10 ∨ i = 512+a+20*j+13)) := by
        constructor
        · rintro ⟨j, hj, h⟩
          refine ⟨j+1, by omega, ?_⟩
          rcases h with h | h | h | h <;> omega
        · rintro ⟨j, hj, h⟩
          have hj0 : 0 < j := by rcases h with h | h | h | h <;> omega
          refine ⟨j-1, by omega, ?_⟩
          rcases h with h | h | h | h <;> omega
      simp only [heq]

theorem fiveMemory_read (mem : Array (BitVec 8)) (a t i : Nat)
    (hi : 512 ≤ i)
    (his : i < mem.size)
    (hz : ∀ q, 512 ≤ q → q < mem.size → mem[q]? = some 0#8)
    (hb : ∀ j, j < t → 512+a+20*j+13 < mem.size) :
    (fiveMemory mem a t)[i]? =
      if ∃ j, j < t ∧ (i = 512+a+20*j ∨ i = 512+a+20*j+3 ∨
        i = 512+a+20*j+10 ∨ i = 512+a+20*j+13)
      then some 1#8 else some 0#8 := by
  by_cases h : i < 512+a
  · rw [fiveMemory_read_below mem a t i h, hz i hi his]
    have : ¬ ∃ j, j < t ∧ (i = 512+a+20*j ∨ i = 512+a+20*j+3 ∨ i = 512+a+20*j+10 ∨ i = 512+a+20*j+13) := by
      rintro ⟨j, hj, h1 | h1 | h1 | h1⟩ <;> omega
    simp [this]
  · exact fiveMemory_read_from mem a t i (by omega) his (by intro q hq hqs; exact hz q (by omega) hqs) hb

end TinyFive.CountingPrimesOddWheel
