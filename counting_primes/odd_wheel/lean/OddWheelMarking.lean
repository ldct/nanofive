import CountingPrimesOddWheelMachine

namespace TinyFive.CountingPrimesOddWheel
open SieveMemory

macro "wheel_exec" : tactic =>
  `(tactic| simp [run, step_image, code, prog, decode, exec, Machine.setReg, Machine.advance,
      Machine.fail, alu, ecall, Width.bytes, Regs.get_set, BranchOp.taken, *])

/-- Initialize the paired-candidate marking cursor after the special 5 loop. -/
theorem mark_pair_init (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 328) :
    run 3 ⟨x, 88, mem, [], out, .running⟩ =
      ⟨((x.set 12 16).set 14 8).set 15 10, 100, mem, [], out, .running⟩ := by
  wheel_exec

/-- The final branch of each pair compares the next square index against E. -/
theorem mark_pair_next (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 328) :
    run 1 ⟨x, 196, mem, [], out, .running⟩ =
      ⟨x, if (x.get 12).ult (x.get 5) then 100 else 200, mem, [], out, .running⟩ := by
  cases h : (x.get 12).ult (x.get 5) <;> wheel_exec

/-- The two real byte stores in the 6k+1 marking loop. -/
theorem mark_plus_stores (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (cap a b : Nat) (hm : Layout image 328 cap mem)
    (ha : 512+a < cap) (hb : 512+b < cap)
    (ha64 : 512+a < 2^64) (hb64 : 512+b < 2^64)
    (h12 : x.get 12 = BitVec.ofNat 64 a)
    (h13 : x.get 13 = BitVec.ofNat 64 (b+7))
    (h7 : x.get 7 = 16777217) :
    run 2 ⟨x, 128, mem, [], out, .running⟩ =
      ⟨x, 136, (mem.setIfInBounds (512+a) 1#8).setIfInBounds (512+b) 1#8,
        [], out, .running⟩ := by
  have hm1 := hm.update (512+a) 1#8 (by omega)
  have hmem := hm.code_eq
  have hmem1 := hm1.code_eq
  have hw1 : writeBytes mem (512+a) (16777217#64) 1 =
      some (mem.setIfInBounds (512+a) 1#8) := by
    simpa using writeBytes_byte mem (512+a) (16777217#64) (by rw [hm.size_eq]; exact ha)
  have hw2 : writeBytes (mem.setIfInBounds (512+a) 1#8) (512+b) (16777217#64) 1 =
      some ((mem.setIfInBounds (512+a) 1#8).setIfInBounds (512+b) 1#8) := by
    simpa using writeBytes_byte (mem.setIfInBounds (512+a) 1#8) (512+b) (16777217#64)
      (by rw [size_update, hm.size_eq]; exact hb)
  have hmoda := Nat.mod_eq_of_lt ha64
  have hmodb := Nat.mod_eq_of_lt hb64
  have hmod13 := Nat.mod_eq_of_lt (show b+7 < 2^64 by omega)
  have hmoda2 : (a+512) % 18446744073709551616 = 512+a := by
    rw [Nat.add_comm]; exact hmoda
  have hmodb2 : (b+7+505) % 18446744073709551616 = 512+b := by
    have : b+7+505 = 512+b := by omega
    rw [this]; exact hmodb
  wheel_exec

/-- The two real byte stores in the 6k-1 marking loop. -/
theorem mark_minus_stores (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (cap a b : Nat) (hm : Layout image 328 cap mem)
    (ha : 512+a < cap) (hb : 512+b < cap)
    (ha64 : 512+a < 2^64) (hb64 : 512+b < 2^64)
    (h11 : x.get 11 = BitVec.ofNat 64 a)
    (h13 : x.get 13 = BitVec.ofNat 64 (b+1))
    (h7 : x.get 7 = 16777217) :
    run 2 ⟨x, 176, mem, [], out, .running⟩ =
      ⟨x, 184, (mem.setIfInBounds (512+a) 1#8).setIfInBounds (512+b) 1#8,
        [], out, .running⟩ := by
  have hm1 := hm.update (512+a) 1#8 (by omega)
  have hmem := hm.code_eq
  have hmem1 := hm1.code_eq
  have hw1 : writeBytes mem (512+a) (16777217#64) 1 =
      some (mem.setIfInBounds (512+a) 1#8) := by
    simpa using writeBytes_byte mem (512+a) (16777217#64) (by rw [hm.size_eq]; exact ha)
  have hw2 : writeBytes (mem.setIfInBounds (512+a) 1#8) (512+b) (16777217#64) 1 =
      some ((mem.setIfInBounds (512+a) 1#8).setIfInBounds (512+b) 1#8) := by
    simpa using writeBytes_byte (mem.setIfInBounds (512+a) 1#8) (512+b) (16777217#64)
      (by rw [size_update, hm.size_eq]; exact hb)
  have hmoda := Nat.mod_eq_of_lt ha64
  have hmodb := Nat.mod_eq_of_lt hb64
  have hmod13 := Nat.mod_eq_of_lt (show b+1 < 2^64 by omega)
  have hmoda2 : (a+512) % 18446744073709551616 = 512+a := by
    rw [Nat.add_comm]; exact hmoda
  have hmodb2 : (b+1+511) % 18446744073709551616 = 512+b := by
    have : b+1+511 = 512+b := by omega
    rw [this]; exact hmodb
  wheel_exec

/-- Arithmetic and back-edge of the first of the two marking loops. -/
theorem mark_plus_advance (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hm : Prefix image mem 328) :
    run 3 ⟨x, 136, mem, [], out, .running⟩ =
      ⟨(x.set 12 (x.get 12 + x.get 17)).set 13 (x.get 13 + x.get 17),
        if (x.get 12 + x.get 17).ult (x.get 5) then 128 else 148,
        mem, [], out, .running⟩ := by
  cases h : (x.get 12 + x.get 17).ult (x.get 5) <;> wheel_exec

/-- Arithmetic and back-edge of the second of the two marking loops. -/
theorem mark_minus_advance (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hm : Prefix image mem 328) :
    run 3 ⟨x, 184, mem, [], out, .running⟩ =
      ⟨(x.set 11 (x.get 11 + x.get 15)).set 13 (x.get 13 + x.get 15),
        if (x.get 11 + x.get 15).ult (x.get 5) then 176 else 196,
        mem, [], out, .running⟩ := by
  cases h : (x.get 11 + x.get 15).ult (x.get 5) <;> wheel_exec


/-- Both stores leave the entire image, including count padding, unchanged. -/
theorem mark_stores_preserve_padding (cap a b : Nat) (mem : Array (BitVec 8))
    (hm : Layout image 512 cap mem) :
    Layout image 512 cap
      ((mem.setIfInBounds (512+a) 1#8).setIfInBounds (512+b) 1#8) := by
  exact (hm.update _ _ (by omega)).update _ _ (by omega)

/-- One complete first-loop iteration, including both actual stores and its back-edge. -/
theorem mark_plus_iteration (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (cap a b : Nat) (hm : Layout image 512 cap mem)
    (ha : 512+a < cap) (hb : 512+b < cap)
    (ha64 : 512+a < 2^64) (hb64 : 512+b < 2^64)
    (h12 : x.get 12 = BitVec.ofNat 64 a)
    (h13 : x.get 13 = BitVec.ofNat 64 (b+7))
    (h7 : x.get 7 = 16777217) :
    let m := (mem.setIfInBounds (512+a) 1#8).setIfInBounds (512+b) 1#8
    Layout image 512 cap m ∧
    run 5 ⟨x, 128, mem, [], out, .running⟩ =
      ⟨(x.set 12 (x.get 12 + x.get 17)).set 13 (x.get 13 + x.get 17),
        if (x.get 12 + x.get 17).ult (x.get 5) then 128 else 148,
        m, [], out, .running⟩ := by
  have hm328 : Layout image 328 cap mem := ⟨hm.size_eq, hm.code_eq.mono (by omega)⟩
  have hm' := mark_stores_preserve_padding cap a b mem hm
  constructor
  · exact hm'
  · rw [show 5 = 2+3 by rfl, run_add,
      mark_plus_stores x mem out cap a b hm328 ha hb ha64 hb64 h12 h13 h7]
    exact mark_plus_advance x _ out (hm'.code_eq.mono (by omega))

/-- One complete second-loop iteration, including both actual stores and its back-edge. -/
theorem mark_minus_iteration (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (cap a b : Nat) (hm : Layout image 512 cap mem)
    (ha : 512+a < cap) (hb : 512+b < cap)
    (ha64 : 512+a < 2^64) (hb64 : 512+b < 2^64)
    (h11 : x.get 11 = BitVec.ofNat 64 a)
    (h13 : x.get 13 = BitVec.ofNat 64 (b+1))
    (h7 : x.get 7 = 16777217) :
    let m := (mem.setIfInBounds (512+a) 1#8).setIfInBounds (512+b) 1#8
    Layout image 512 cap m ∧
    run 5 ⟨x, 176, mem, [], out, .running⟩ =
      ⟨(x.set 11 (x.get 11 + x.get 15)).set 13 (x.get 13 + x.get 15),
        if (x.get 11 + x.get 15).ult (x.get 5) then 176 else 196,
        m, [], out, .running⟩ := by
  have hm328 : Layout image 328 cap mem := ⟨hm.size_eq, hm.code_eq.mono (by omega)⟩
  have hm' := mark_stores_preserve_padding cap a b mem hm
  constructor
  · exact hm'
  · rw [show 5 = 2+3 by rfl, run_add,
      mark_minus_stores x mem out cap a b hm328 ha hb ha64 hb64 h11 h13 h7]
    exact mark_minus_advance x _ out (hm'.code_eq.mono (by omega))

/-- Compute the next two square cursors at the start of a candidate pair. -/
theorem pair_header_arithmetic (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hm : Prefix image mem 328) :
    run 3 ⟨x, 100, mem, [], out, .running⟩ =
      ⟨((x.set 11 (x.get 12 + x.get 14)).set 14 (x.get 14 + 8)).set 11
        (x.get 12 + x.get 14 + (x.get 14 + 8)), 112, mem, [], out, .running⟩ := by
  wheel_exec

/-- Prepare the two progression cursors of a fresh 6k+1 candidate. -/
theorem plus_prepare (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hm : Prefix image mem 328) :
    run 2 ⟨x, 120, mem, [], out, .running⟩ =
      ⟨(x.set 13 (x.get 12 + x.get 14)).set 17 (x.get 15 + 4),
        128, mem, [], out, .running⟩ := by
  wheel_exec

/-- Advance the pair variables before the 6k-1 flag test. -/
theorem minus_header_arithmetic (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hm : Prefix image mem 328) :
    run 3 ⟨x, 148, mem, [], out, .running⟩ =
      ⟨((x.set 15 (x.get 15 + 12)).set 16 (x.get 16 + 2)).set 12
        (x.get 11 + x.get 14), 160, mem, [], out, .running⟩ := by
  wheel_exec

/-- Prepare the second progression cursor of a fresh 6k-1 candidate. -/
theorem minus_prepare (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hm : Prefix image mem 328) :
    run 2 ⟨x, 168, mem, [], out, .running⟩ =
      ⟨(x.set 13 (x.get 11 + x.get 16)).set 13
        (x.get 11 + x.get 16 + x.get 16), 176, mem, [], out, .running⟩ := by
  wheel_exec

/-- Inspect the first candidate's actual byte and branch to mark or skip it. -/
theorem plus_flag_test (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (i v : Nat) (hm : Prefix image mem 328) (hi : i+512 < 2^64)
    (h16 : x.get 16 = BitVec.ofNat 64 i) (hv : v ≤ 1)
    (hread : mem[512+i]? = some (BitVec.ofNat 8 v)) :
    run 2 ⟨x, 112, mem, [], out, .running⟩ =
      ⟨x.set 6 (BitVec.ofNat 64 v), if v = 0 then 120 else 148,
        mem, [], out, .running⟩ := by
  have hmod : i % 18446744073709551616 = i := Nat.mod_eq_of_lt (by omega)
  have hmod2 : (i+512) % 18446744073709551616 = 512+i := by
    rw [Nat.add_comm]; exact Nat.mod_eq_of_lt (by omega)
  have hzero : v = 0 ∨ v = 1 := by omega
  rcases hzero with rfl | rfl <;> wheel_exec

/-- Inspect the second candidate's actual byte and branch to mark or skip it. -/
theorem minus_flag_test (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (i v : Nat) (hm : Prefix image mem 328) (hi : i+512 < 2^64)
    (h16 : x.get 16 = BitVec.ofNat 64 (i+1)) (hv : v ≤ 1)
    (hread : mem[512+i]? = some (BitVec.ofNat 8 v)) :
    run 2 ⟨x, 160, mem, [], out, .running⟩ =
      ⟨x.set 6 (BitVec.ofNat 64 v), if v = 0 then 168 else 196,
        mem, [], out, .running⟩ := by
  have hmod : (i+1) % 18446744073709551616 = i+1 := Nat.mod_eq_of_lt (by omega)
  have hmod2 : (i+1+511) % 18446744073709551616 = 512+i := by
    have : i+1+511 = 512+i := by omega
    rw [this]; exact Nat.mod_eq_of_lt (by omega)
  have hzero : v = 0 ∨ v = 1 := by omega
  rcases hzero with rfl | rfl <;> wheel_exec

/-- The first flag test also handles arbitrary bytes beyond the counted range. -/
theorem plus_flag_test_byte (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (i : Nat) (v : BitVec 8) (hm : Prefix image mem 328) (hi : i+512 < 2^64)
    (h16 : x.get 16 = BitVec.ofNat 64 i) (hread : mem[512+i]? = some v) :
    run 2 ⟨x, 112, mem, [], out, .running⟩ =
      ⟨x.set 6 (v.setWidth 64), if v.setWidth 64 = 0 then 120 else 148,
        mem, [], out, .running⟩ := by
  have hmod : i % 18446744073709551616 = i := Nat.mod_eq_of_lt (by omega)
  have hmod2 : (i+512) % 18446744073709551616 = 512+i := by
    rw [Nat.add_comm]; exact Nat.mod_eq_of_lt (by omega)
  by_cases hv : v.setWidth 64 = 0#64 <;> wheel_exec

/-- The second flag test also handles arbitrary bytes beyond the counted range. -/
theorem minus_flag_test_byte (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (i : Nat) (v : BitVec 8) (hm : Prefix image mem 328) (hi : i+512 < 2^64)
    (h16 : x.get 16 = BitVec.ofNat 64 (i+1)) (hread : mem[512+i]? = some v) :
    run 2 ⟨x, 160, mem, [], out, .running⟩ =
      ⟨x.set 6 (v.setWidth 64), if v.setWidth 64 = 0 then 168 else 196,
        mem, [], out, .running⟩ := by
  have hmod : (i+1) % 18446744073709551616 = i+1 := Nat.mod_eq_of_lt (by omega)
  have hmod2 : (i+1+511) % 18446744073709551616 = 512+i := by
    have : i+1+511 = 512+i := by omega
    rw [this]; exact Nat.mod_eq_of_lt (by omega)
  by_cases hv : v.setWidth 64 = 0#64 <;> wheel_exec

/-- Polynomial cursor invariant for the start of pair k (k starts at one). -/
def PairInv (x : Regs 64) (E k : Nat) : Prop :=
  x.get 5 = BitVec.ofNat 64 E ∧ x.get 7 = 16777217 ∧
  x.get 12 = BitVec.ofNat 64 (12*k*k + 4*k) ∧
  x.get 14 = BitVec.ofNat 64 (8*k) ∧
  x.get 15 = BitVec.ofNat 64 (12*k - 2) ∧
  x.get 16 = BitVec.ofNat 64 (2*k)

/-- The cursor recurrence computes the next pair's first square. -/
theorem pair_square_recurrence (k : Nat) :
    (12*k*k + 4*k) + 8*k + 8*(k+1) + 8*(k+1) =
      12*(k+1)*(k+1) + 4*(k+1) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
  omega

/-- The initial cursor registers establish the polynomial invariant. -/
theorem pair_init_inv (x : Regs 64) (E : Nat)
    (h5 : x.get 5 = BitVec.ofNat 64 E) (h7 : x.get 7 = 16777217)
    (h16 : x.get 16 = 2) :
    PairInv (((x.set 12 16).set 14 8).set 15 10) E 1 := by
  simp [PairInv, Regs.get_set, h5, h7, h16]

end TinyFive.CountingPrimesOddWheel
