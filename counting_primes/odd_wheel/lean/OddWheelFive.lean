import CountingPrimesOddWheelMachine
import OddWheelMath

namespace TinyFive.CountingPrimesOddWheel
open SieveMemory

/-- The actual little-endian word store: 01 00 00 01, without an alignment assumption. -/
def fiveWord (mem : Array (BitVec 8)) (a : Nat) : Array (BitVec 8) :=
  (((mem.setIfInBounds a 1#8).setIfInBounds (a+1) 0#8).setIfInBounds (a+2) 0#8).setIfInBounds (a+3) 1#8

theorem five_write (mem : Array (BitVec 8)) (a : Nat) (h : a+3 < mem.size) :
    writeBytes mem a (16777217#64) 4 = some (fiveWord mem a) := by
  simp [writeBytes, fiveWord, size_update, show a < mem.size by omega,
    show a+1 < mem.size by omega, show a+1+1 < mem.size by omega,
    show a+1+1+1 < mem.size by omega, Nat.add_assoc]

macro "five_exec" : tactic =>
  `(tactic| simp [run, step_image, code, prog, decode, exec, Machine.setReg, Machine.advance,
      Machine.fail, alu, ecall, Width.bytes, Regs.get_set, BranchOp.taken, *])

/-- Two actual unaligned word stores in one iteration, including their zero bytes. -/
theorem five_stores (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (cap a : Nat) (hm : Layout image 328 cap mem)
    (ha : 512+a+13 < cap) (ha64 : 512+a+13 < 2^64)
    (h11 : x.get 11 = BitVec.ofNat 64 a) (h7 : x.get 7 = 16777217) :
    run 2 ⟨x, 72, mem, [], out, .running⟩ =
      ⟨x, 80, fiveWord (fiveWord mem (512+a)) (512+a+10), [], out, .running⟩ := by
  have hm1 : Layout image 328 cap (fiveWord mem (512+a)) := by
    unfold fiveWord
    exact (((hm.update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)
  have hmem := hm.code_eq
  have hmem1 := hm1.code_eq
  have hw1 := five_write mem (512+a) (by rw [hm.size_eq]; omega)
  have hw2 := five_write (fiveWord mem (512+a)) (512+a+10) (by rw [hm1.size_eq]; omega)
  have hmoda : (a+512) % 18446744073709551616 = 512+a := by
    rw [Nat.add_comm]; apply Nat.mod_eq_of_lt; omega
  have hmodb : (a+522) % 18446744073709551616 = 512+a+10 := by
    have : a+522 = 512+a+10 := by omega
    rw [this]; apply Nat.mod_eq_of_lt; omega
  five_exec

/-- Cursor update and branch at the end of a five iteration. -/
theorem five_advance (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hm : Prefix image mem 328) :
    run 2 ⟨x, 80, mem, [], out, .running⟩ =
      ⟨x.set 11 (x.get 11 + 20#64),
       if (x.get 11 + 20#64).ult (x.get 5) then 72 else 88,
       mem, [], out, .running⟩ := by
  cases h : (x.get 11 + 20#64).ult (x.get 5) <;> five_exec

/-- One complete loop iteration, with precise branch and preserved registers. -/
theorem five_iteration (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (cap a E : Nat) (hm : Layout image 328 cap mem)
    (ha : 512+a+13 < cap) (ha64 : 512+a+20 < 2^64) (hE : E < 2^64)
    (h11 : x.get 11 = BitVec.ofNat 64 a) (h7 : x.get 7 = 16777217)
    (h5 : x.get 5 = BitVec.ofNat 64 E) :
    run 4 ⟨x, 72, mem, [], out, .running⟩ =
      ⟨x.set 11 (BitVec.ofNat 64 (a+20)),
       if a+20 < E then 72 else 88,
       fiveWord (fiveWord mem (512+a)) (512+a+10), [], out, .running⟩ := by
  have hm1 : Layout image 328 cap (fiveWord mem (512+a)) := by
    unfold fiveWord
    exact (((hm.update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)
  have hm2 : Layout image 328 cap (fiveWord (fiveWord mem (512+a)) (512+a+10)) := by
    unfold fiveWord
    exact (((hm1.update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)
  rw [show 4 = 2+2 by rfl, run_add, five_stores x mem out cap a hm ha (by omega) h11 h7,
    five_advance x _ out hm2.code_eq]
  rw [h11, h5, ← BitVec.ofNat_add]
  simp [BitVec.ult, Nat.mod_eq_of_lt (show a+20 < 2^64 by omega), Nat.mod_eq_of_lt hE]

/-- Memory after consecutive groups beginning at cursor `a`. -/
def fiveMemory (mem : Array (BitVec 8)) (a : Nat) (t : Nat) : Array (BitVec 8) :=
  Nat.rec (motive := fun _ => Array (BitVec 8) → Nat → Array (BitVec 8))
    (fun m _ => m)
    (fun _ prev m j => prev (fiveWord (fiveWord m (512+j)) (512+j+10)) (j+20))
    t mem a

theorem fiveMemory_zero (mem : Array (BitVec 8)) (a : Nat) :
    fiveMemory mem a 0 = mem := rfl

theorem fiveMemory_succ (mem : Array (BitVec 8)) (a k : Nat) :
    fiveMemory mem a (k+1) =
      fiveMemory (fiveWord (fiveWord mem (512+a)) (512+a+10)) (a+20) k := by
  unfold fiveMemory
  rfl

theorem fiveMemory_layout (mem : Array (BitVec 8)) (a k cap : Nat)
    (hm : Layout image 328 cap mem) : Layout image 328 cap (fiveMemory mem a k) := by
  induction k generalizing mem a with
  | zero => exact hm
  | succ k ih =>
    apply ih
    unfold fiveWord
    exact (((((((hm.update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)

theorem fiveMemory_layout_full (mem : Array (BitVec 8)) (a k cap : Nat)
    (hm : Layout image 512 cap mem) : Layout image 512 cap (fiveMemory mem a k) := by
  induction k generalizing mem a with
  | zero => exact hm
  | succ k ih =>
    apply ih
    unfold fiveWord
    exact (((((((hm.update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)).update _ _ (by omega)

/-- Readback of both stores, accounting for the four zero padding bytes. -/
theorem five_stores_read (mem : Array (BitVec 8)) (a q : Nat)
    (h : a+13 < mem.size) :
    (fiveWord (fiveWord mem a) (a+10))[q]? =
      if q = a+13 ∨ q = a+10 ∨ q = a+3 ∨ q = a then some 1#8
      else if q = a+12 ∨ q = a+11 ∨ q = a+2 ∨ q = a+1 then some 0#8
      else mem[q]? := by
  simp only [fiveWord, Array.getElem?_setIfInBounds, size_update]
  simp (disch := omega) only [if_pos, Nat.add_assoc]
  grind (splits := 30)

/-- The four byte positions selected by each iteration are exactly the wheel
    indices whose represented values are multiples of five at least 25. -/
theorem five_marks (i : Nat) :
    OddWheelMath.WM 7 i ↔ ∃ k, i = 8+20*k ∨ i = 11+20*k ∨
      i = 18+20*k ∨ i = 21+20*k := by
  have hw := OddWheelMath.divisor_wheel i
  have hv := OddWheelMath.value_mod i
  unfold OddWheelMath.WM OddWheelMath.value
  constructor
  · rintro ⟨d, hd, hlt, hs, dvd⟩
    have hd' : d = 5 ∨ d = 6 := by omega
    rcases hd' with rfl | rfl
    · obtain ⟨q, hq⟩ := dvd
      by_cases hi : i % 2 = 0 <;> simp [hi] at hs hq <;> refine ⟨(i-8)/20, ?_⟩ <;> omega
    · have hm := hw 6 dvd
      omega
  · rintro ⟨k, h | h | h | h⟩ <;> subst i <;>
      refine ⟨5, by omega, by omega, ?_, ?_⟩ <;>
      simp [Nat.add_mod, Nat.mul_mod] <;> omega

end TinyFive.CountingPrimesOddWheel
