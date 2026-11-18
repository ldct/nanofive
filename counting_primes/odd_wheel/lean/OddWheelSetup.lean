import CountingPrimesOddWheelMachine
import OddWheelDivision

namespace TinyFive.CountingPrimesOddWheel

open CountingPrimes SieveMemory

private theorem initial_eq (n : Nat) :
    initial n = ⟨(⟨Vector.replicate 32 0⟩ : Regs 64).set 10 (BitVec.ofNat 64 n),
      0, (initial n).mem, [], "", .running⟩ := rfl

theorem initial_zero (n a : Nat) (ha : 328 ≤ a) (hs : a < memSize n) :
    (initial n).mem[a]? = some 0 :=
  load_mem_zero 64 prog (memSize n) [] a ha hs

theorem initial_full_layout (n : Nat) : Layout image 512 (memSize n) (initial n).mem :=
  load_layout 64 prog 512 (memSize n) [] [] (by decide) (by unfold memSize; omega)

theorem flag_padding {mem : Array (BitVec 8)} (h : Prefix image mem 512)
    (a : Nat) (ha : 496 ≤ a) (ha' : a < 512) : mem[a]? = some 0 := by
  rw [h a ha']
  exact load_mem_zero 64 prog 512 [] a (by change 328 ≤ a; omega) ha'

macro "setup_exec" : tactic =>
  `(tactic| simp [run, step_image, code, prog, decode, exec, Machine.setReg, Machine.advance,
      Machine.fail, alu, ecall, Width.bytes, Regs.get_set, BranchOp.taken, *])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem small (n : Nat) (hn : n < 3) :
    is_exited_with_output (run 13 (initial n)) (toString (countPrimes n) ++ "\n") := by
  have hmem := (initial_layout n).code_eq
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn' with rfl | rfl | rfl <;> rw [initial_eq] <;> setup_exec <;> decide

private theorem shiftRight_nat (a k : Nat) (ha : a < 2^64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2^k) := by
  apply BitVec.eq_of_toNat_eq
  have hdiv := Nat.div_le_self a (2^k)
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show a / 2^k < 2^64 by omega)]

private theorem shiftLeft_nat (a k : Nat) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2^k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_mul_mod]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initialize_regs (n : Nat) (hn : n < 10^11) (h3 : 3 ≤ n) :
    let E := (2*((n+3)/2)-1)/3
    ∃ x, x.get 5 = BitVec.ofNat 64 E ∧ x.get 7 = 16777217 ∧
      x.get 11 = 8 ∧ x.get 16 = 2 ∧
      run 18 (initial n) = ⟨x, 72, (initial n).mem, [], "", .running⟩ := by
  let E := (2*((n+3)/2)-1)/3
  let mem := (initial n).mem
  let x : Regs 64 := (⟨Vector.replicate 32 0⟩ : Regs 64).set 10 (BitVec.ofNat 64 n)
  have hmem : Prefix image mem 328 := (initial_layout n).code_eq
  let m := (n+3)/2
  let y := 21845*m
  let a := y/65536
  let b := (y+a)/65536
  have hsum : y+b < 2^64 := by dsimp [b,a,y,m]; omega
  have hdiv : (y+b)/32768 = E := OddWheelDivision.division_correct n hn
  have h0 : (BitVec.ofNat 64 n + 3#64) >>> (1 : Nat) = BitVec.ofNat 64 m := by
    change (BitVec.ofNat 64 n + BitVec.ofNat 64 3) >>> 1 = _
    rw [← BitVec.ofNat_add, shiftRight_nat _ _ (by omega)]
  have htest : (2#64).ult (BitVec.ofNat 64 m) = true := by
    have hm : m < 2^64 := by dsimp [m]; omega
    have hm' : 2 < m := by dsimp [m]; omega
    simp [BitVec.ult, Nat.mod_eq_of_lt hm, hm']
  have h1 : BitVec.ofNat 64 m + (BitVec.ofNat 64 m <<< (2 : Nat)) = BitVec.ofNat 64 (5*m) := by
    rw [shiftLeft_nat, ← BitVec.ofNat_add]; congr 1; omega
  have h2 : BitVec.ofNat 64 (5*m) + (BitVec.ofNat 64 (5*m) <<< (4 : Nat)) = BitVec.ofNat 64 (85*m) := by
    rw [shiftLeft_nat, ← BitVec.ofNat_add]; congr 1; omega
  have h3' : BitVec.ofNat 64 (85*m) + (BitVec.ofNat 64 (85*m) <<< (8 : Nat)) = BitVec.ofNat 64 y := by
    rw [shiftLeft_nat, ← BitVec.ofNat_add]; congr 1; dsimp [y]; omega
  have h4 : BitVec.ofNat 64 y >>> (16 : Nat) = BitVec.ofNat 64 a :=
    shiftRight_nat _ _ (by omega)
  have h5 : (BitVec.ofNat 64 a + BitVec.ofNat 64 y) >>> (16 : Nat) = BitVec.ofNat 64 b := by
    rw [← BitVec.ofNat_add, Nat.add_comm, shiftRight_nat _ _]
    dsimp [a,y,m]; omega
  have h6 : (BitVec.ofNat 64 y + BitVec.ofNat 64 b) >>> (15 : Nat) = BitVec.ofNat 64 E := by
    rw [← BitVec.ofNat_add, shiftRight_nat _ _ hsum, hdiv]
  change ∃ z, z.get 5 = BitVec.ofNat 64 E ∧ z.get 7 = 16777217 ∧ z.get 11 = 8 ∧
    z.get 16 = 2 ∧ run 18 (initial n) = ⟨z, 72, mem, [], "", .running⟩
  rw [initial_eq]
  change ∃ z, _ ∧ _ ∧ _ ∧ _ ∧ run 18 ⟨x, 0, mem, [], "", .running⟩ = ⟨z, 72, mem, [], "", .running⟩
  have hx : x.get 10 = BitVec.ofNat 64 n := by simp [x, Regs.get_set]
  setup_exec
  refine ⟨_, ?_, ?_, ?_, ?_, rfl⟩ <;> simp [Regs.get_set]

private theorem toInt_nat (c : Nat) (hc : c < 2^63) :
    (BitVec.ofNat 64 c).toInt = (c : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have h64 : c < 2^64 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, show 2*c < 2^64 by omega]

private theorem nat_int_string (c : Nat) : toString (c : Int) = toString c := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem print_correct (c : Nat) (hc : c < 2^63) (x : Regs 64) (mem : Array (BitVec 8))
    (hmem : Prefix image mem 328) (h10 : x.get 10 = BitVec.ofNat 64 c) :
    is_exited_with_output (run 7 ⟨x, 292, mem, [], "", .running⟩) (toString c ++ "\n") := by
  have hs := toInt_nat c hc
  have ht := nat_int_string c
  change _ ∧ _
  setup_exec
  rfl

theorem small_correct (n : Nat) (hn : n < 3) :
    is_exited_with_output (run 13 (initial n)) (toString (countPrimes n) ++ "\n") :=
  small n hn

end TinyFive.CountingPrimesOddWheel
