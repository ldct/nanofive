import TinyFive.Machine
import TinyFive.Primes
import CountingPrimesLoad
import OddSieveProgram
import TinyFive.SieveMemory
import TinyFive.SieveMath
import TinyFive.TrialDivisionCost
import OddSieveMath

/-! An odds-only Sieve of Eratosthenes with a word-summing count, on the actual RV64I machine.
Flag byte `i` at `BASE + i` stands for the odd number `2*i+1`; `K = halfCount n` flags are in
use, and `π(n)` is `K` less the number of marked flags, index 0 standing in for the prime 2.

`correct` gives exit code zero and output `π(n)` within `72 + 33*n` instructions for every
`n < 10^11`. A candidate `p` with `p*p ≤ n` costs at most `8 + 3*(K/p)` instructions; charging
that to every integer from 3 up to `2^19` lets the shared dyadic bound
`TrialDivisionCost.quotientSum_le_dyadic` cover the quotients with 19 blocks. The count costs at
most `22 + 10*(K/16) + 12*(K/496)`.

The count loads four words per iteration and adds them, keeping four byte lanes. The proof
tracks the lanes as four natural numbers (`inner_correct`), each at most 124 within a chunk, so
the lanes never carry into each other and `fold_lanes` recovers their sum. The last iteration
reads up to 15 bytes past the flags; `Flags` therefore covers `K + 16` bytes, the last 16 of
which are never written. -/
namespace TinyFive.CountingPrimesOddSieve
open CountingPrimes SieveMemory OddSieveMath
open TrialDivisionCost (quotientSum quotientSum_succ quotientSum_append quotientSum_le_dyadic)

/-- The memory size `counting_primes_odd_sieve.py` allocates: the code area, one flag per odd
number up to `n`, and 16 bytes of padding for the word-summing count. -/
def memSize (n : Nat) : Nat := 256 + (n+1)/2 + 16

def initial (n : Nat) : Machine 64 :=
  (load 64 prog (memSize n) []).setReg 10 (BitVec.ofNat 64 n)
def image : Array (BitVec 8) := (load 64 prog 256 []).mem

def code : List Instr := [
  .opImm .add 30 0 1, .op .sltu 5 30 10, .op .add 5 5 10, .opImm .srl 10 5 1,
  .opImm .add 12 10 256, .opImm .add 28 0 257, .opImm .add 29 0 260, .opImm .add 31 0 3,
  .branch .bgeu 29 12 48,
  .load .byte false 5 28 0, .branch .bne 5 0 20, .opImm .add 6 29 0,
  .store .byte 30 6 0, .op .add 6 6 31, .branch .bltu 6 12 (-8),
  .opImm .add 28 28 1, .op .add 29 29 31, .opImm .add 31 31 2, .op .add 29 29 31,
  .branch .bltu 29 12 (-40),
  .opImm .add 11 0 256,
  .opImm .add 6 0 0, .opImm .add 7 11 496, .branch .bgeu 12 7 8, .opImm .add 7 12 0,
  .load .word true 5 11 0, .op .add 6 6 5, .load .word true 5 11 4, .op .add 6 6 5,
  .load .word true 5 11 8, .op .add 6 6 5, .load .word true 5 11 12, .op .add 6 6 5,
  .opImm .add 11 11 16, .branch .bltu 11 7 (-36),
  .opImm .srl 5 6 16, .op .add 6 6 5, .opImm .and 5 6 255, .op .sub 10 10 5,
  .opImm .srl 6 6 8, .opImm .and 6 6 255, .op .sub 10 10 6,
  .branch .bltu 11 12 (-84),
  .opImm .add 17 0 1, .ecall, .opImm .add 10 0 10, .opImm .add 17 0 11, .ecall,
  .opImm .add 17 0 10, .ecall]

theorem fetch : ∀ pc, pc < 200 → pc % 4 = 0 →
    (readBytes image pc 4).bind (decode 64) = some (code.getD (pc/4) .ecall) := by
  decide +kernel

theorem step_image (x : Regs 64) (pc : BitVec 64) (mem : Array (BitVec 8))
    (out : String) (st : Status) (hmem : Prefix image mem 200)
    (h : pc.toNat < 200) (h4 : pc.toNat % 4 = 0) :
    step ⟨x, pc, mem, [], out, st⟩ =
      exec (code.getD (pc.toNat/4) .ecall) ⟨x, pc, mem, [], out, st⟩ := by
  apply step_of_prefix _ image 200 hmem (by change pc.toNat + 4 ≤ 200; omega)
  exact fetch _ h h4

macro "odd_exec" : tactic =>
  `(tactic| simp [run, step_image, code, exec, Machine.setReg, Machine.advance,
      Machine.fail, alu, ecall, Width.bytes, Regs.get_set, BranchOp.taken, *])

private theorem nat_ult (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem toNat_nat (a : Nat) (ha : a < 2^64) : (BitVec.ofNat 64 a).toNat = a := by
  simp [Nat.mod_eq_of_lt ha]

theorem initial_layout (n : Nat) : Layout image 200 (memSize n) (initial n).mem := by
  exact load_layout_boundary 64 prog 200 256 (memSize n) [] []
    (by decide) (by decide) (by unfold memSize; omega)

/-- The outer-loop registers: `a0 = K`, `a2 = BASE + K`, `t5 = 1`, and for the candidate
`p = 2*h+1`: `t3` the address of its flag, `t4` the address of the flag of `p*p`, `t6 = p`. -/
def Inv (x : Regs 64) (K h : Nat) : Prop :=
  x.get 10 = BitVec.ofNat 64 K ∧ x.get 12 = BitVec.ofNat 64 (256+K) ∧ x.get 30 = 1 ∧
  x.get 28 = BitVec.ofNat 64 (256+h) ∧ x.get 29 = BitVec.ofNat 64 (256 + sq h) ∧
  x.get 31 = BitVec.ofNat 64 (2*h+1)

private theorem half_shift (m : Nat) (hm : m < 2^64) :
    BitVec.ofNat 64 m >>> 1 = BitVec.ofNat 64 (m/2) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hm,
    Nat.mod_eq_of_lt (show m/2 < 2^64 by omega)]

private theorem initialize_regs (n : Nat) (hn : n < 10^11) :
    ∃ x, Inv x (halfCount n) 1 ∧ run 8 (initial n) =
      ⟨x, 32, (initial n).mem, [], "", .running⟩ := by
  let x : Regs 64 := (⟨Vector.replicate 32 0⟩ : Regs 64).set 10 (BitVec.ofNat 64 n)
  let mem := (load 64 prog (memSize n) []).mem
  have hi : initial n = ⟨x, 0, mem, [], "", .running⟩ := rfl
  have hmem : Prefix image mem 200 := (initial_layout n).code_eq
  change ∃ y, Inv y (halfCount n) 1 ∧ run 8 (initial n) = ⟨y, 32, mem, [], "", .running⟩
  rw [hi]
  obtain ⟨c, hcdef⟩ : ∃ c : Nat, c = if 1 < n then 1 else 0 := ⟨_, rfl⟩
  have hc1 : c ≤ 1 := by split at hcdef <;> omega
  have hx10 : x.get 10 = BitVec.ofNat 64 n := by simp [x, Regs.get_set]
  have hc : (if (1#64).ult (BitVec.ofNat 64 n) = true then 1#64 else 0#64) = BitVec.ofNat 64 c := by
    have := nat_ult 1 n (by omega) (by omega)
    by_cases h1 : 1 < n <;> simp [hcdef, h1, this]
  have hs : (BitVec.ofNat 64 c + BitVec.ofNat 64 n) >>> 1 = BitVec.ofNat 64 (halfCount n) := by
    rw [← BitVec.ofNat_add, half_shift _ (by omega)]
    simp only [halfCount, hcdef, Nat.add_comm]
  have hk : BitVec.ofNat 64 (halfCount n) + 256#64 = BitVec.ofNat 64 (256 + halfCount n) := by
    rw [Nat.add_comm, BitVec.ofNat_add]
  clear hcdef
  refine ⟨((((((((x.set 30 1).set 5 (BitVec.ofNat 64 c)).set 5
    (BitVec.ofNat 64 c + BitVec.ofNat 64 n)).set 10
    (BitVec.ofNat 64 (halfCount n))).set 12 (BitVec.ofNat 64 (256 + halfCount n))).set 28 257).set 29
    260).set 31 3), ?_, ?_⟩
  · simp [Inv, Regs.get_set, sq]
  · odd_exec


private theorem mod64 (a : Nat) (h : a < 2^64) : a % 18446744073709551616 = a :=
  Nat.mod_eq_of_lt h

private theorem ofNat_congr {a b : Nat} (h : a = b) : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
  rw [h]

private theorem addr_ult (a b : Nat) (ha : 256 + a < 2^64) (hb : 256 + b < 2^64) :
    (BitVec.ofNat 64 (256+a)).ult (BitVec.ofNat 64 (256+b)) = decide (a < b) := by
  rw [nat_ult _ _ ha hb]
  simp

/-- Flag `i` is the byte at `BASE + i`. The 16 bytes after the `K` flags in use are part of the
invariant because the count reads them. -/
def Flags (mem : Array (BitVec 8)) (K : Nat) (f : Nat → Nat) : Prop :=
  ∀ i, i < K+16 → mem[256+i]? = some (BitVec.ofNat 8 (f i))

private theorem Flags.congr {mem : Array (BitVec 8)} {K : Nat} {f g : Nat → Nat}
    (h : Flags mem K f) (hfg : ∀ i, f i = g i) : Flags mem K g :=
  fun i hi => by rw [← hfg i]; exact h i hi

private theorem first_check (K h : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 200) (hi : Inv x K h)
    (hK : K < 2^37) (hs : sq h < 2^40) :
    run 1 ⟨x, 32, mem, [], out, .running⟩ =
      ⟨x, if sq h < K then 36 else 80, mem, [], out, .running⟩ := by
  obtain ⟨h10, h12, h30, h28, h29, h31⟩ := hi
  have hb := addr_ult (sq h) K (by omega) (by omega)
  by_cases hlt : sq h < K
  · simp only [hlt, ite_true]
    odd_exec
  · simp only [hlt, ite_false]
    odd_exec

private theorem header_marked (K h : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 200) (hi : Inv x K h)
    (hh : 256 + h < 2^64)
    (hread : mem[256+h]? = some 1#8) :
    ∃ x', Inv x' K h ∧
      run 2 ⟨x, 36, mem, [], out, .running⟩ = ⟨x', 60, mem, [], out, .running⟩ := by
  obtain ⟨h10, h12, h30, h28, h29, h31⟩ := hi
  have hmod := mod64 _ hh
  refine ⟨x.set 5 1, ?_, ?_⟩
  · simp [Inv, Regs.get_set, *]
  · odd_exec

private theorem header_fresh (K h : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 200) (hi : Inv x K h)
    (hh : 256 + h < 2^64)
    (hread : mem[256+h]? = some 0#8) :
    ∃ x', Inv x' K h ∧ x'.get 6 = BitVec.ofNat 64 (256 + sq h) ∧
      run 3 ⟨x, 36, mem, [], out, .running⟩ = ⟨x', 48, mem, [], out, .running⟩ := by
  obtain ⟨h10, h12, h30, h28, h29, h31⟩ := hi
  have hmod := mod64 _ hh
  refine ⟨(x.set 5 0).set 6 (BitVec.ofNat 64 (256 + sq h)), ?_, ?_, ?_⟩
  · simp [Inv, Regs.get_set, *]
  · simp [Regs.get_set]
  · odd_exec

private theorem mark_step (K h j cap : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Layout image 200 cap mem) (hcap : 256 + K ≤ cap)
    (hK : K < 2^37) (hh : h < 2^37) (hi : Inv x K h)
    (hj : x.get 6 = BitVec.ofNat 64 (256+j)) (hjK : j < K) :
    ∃ x', Inv x' K h ∧ x'.get 6 = BitVec.ofNat 64 (256 + (j + (2*h+1))) ∧
      run 3 ⟨x, 48, mem, [], out, .running⟩ =
        ⟨x', if j + (2*h+1) < K then 48 else 60, mem.setIfInBounds (256+j) 1#8, [], out,
          .running⟩ := by
  obtain ⟨h10, h12, h30, h28, h29, h31⟩ := hi
  have hmod := mod64 (256+j) (by omega)
  have hcode := hmem.code_eq
  have hcode' := (hmem.update (256+j) (1#8) (by omega)).code_eq
  have hwrite : writeBytes mem (256+j) (1#64) 1 = some (mem.setIfInBounds (256+j) 1#8) :=
    writeBytes_byte mem _ _ (by rw [hmem.size_eq]; omega)
  have he : BitVec.ofNat 64 (256+j) + BitVec.ofNat 64 (2*h+1) =
      BitVec.ofNat 64 (256 + (j + (2*h+1))) := by
    rw [← BitVec.ofNat_add]; exact ofNat_congr (by omega)
  have hb := addr_ult (j + (2*h+1)) K (by omega) (by omega)
  refine ⟨x.set 6 (BitVec.ofNat 64 (256 + (j + (2*h+1)))), ?_, ?_, ?_⟩
  · simp [Inv, Regs.get_set, *]
  · simp [Regs.get_set]
  · by_cases hlt : j + (2*h+1) < K
    · simp only [hlt, ite_true]
      odd_exec
    · simp only [hlt, ite_false]
      odd_exec

private theorem advance (K h : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 200) (hi : Inv x K h)
    (hK : K < 2^37) (hs : sq h < 2^37) :
    ∃ x', Inv x' K (h+1) ∧
      run 5 ⟨x, 60, mem, [], out, .running⟩ =
        ⟨x', if sq (h+1) < K then 36 else 80, mem, [], out, .running⟩ := by
  obtain ⟨h10, h12, h30, h28, h29, h31⟩ := hi
  have hle := self_le_sq h
  have hsq := sq_succ h
  have e28 : BitVec.ofNat 64 (256+h) + 1#64 = BitVec.ofNat 64 (256+(h+1)) := by
    rw [← BitVec.ofNat_add]; exact ofNat_congr (by omega)
  have e31 : BitVec.ofNat 64 (2*h+1) + 2#64 = BitVec.ofNat 64 (2*(h+1)+1) := by
    rw [← BitVec.ofNat_add]; exact ofNat_congr (by omega)
  have e29a : BitVec.ofNat 64 (256 + sq h) + BitVec.ofNat 64 (2*h+1) =
      BitVec.ofNat 64 (256 + sq h + (2*h+1)) := by
    rw [← BitVec.ofNat_add]
  have e29 : BitVec.ofNat 64 (256 + sq h + (2*h+1)) + BitVec.ofNat 64 (2*(h+1)+1) =
      BitVec.ofNat 64 (256 + sq (h+1)) := by
    rw [← BitVec.ofNat_add]; exact ofNat_congr (by omega)
  have hb := addr_ult (sq (h+1)) K (by omega) (by omega)
  clear hsq hle
  refine ⟨(((x.set 28 (BitVec.ofNat 64 (256+(h+1)))).set 29
    (BitVec.ofNat 64 (256 + sq h + (2*h+1)))).set 31 (BitVec.ofNat 64 (2*(h+1)+1))).set 29
    (BitVec.ofNat 64 (256 + sq (h+1))), ?_, ?_⟩
  · simp [Inv, Regs.get_set, *]
  · by_cases hlt : sq (h+1) < K
    · simp only [hlt, ite_true]
      odd_exec
    · simp only [hlt, ite_false]
      odd_exec

/-- A real byte store advances the arithmetic marking invariant. -/
private theorem flags_update (K h j : Nat) (mem : Array (BitVec 8))
    (hsize : 256 + j < mem.size) (hjs : sq h ≤ j) (hjK : j < K)
    (hdiv : (2*h+1) ∣ (j - sq h)) (hf : Flags mem K (bit K (IP h j))) :
    Flags (mem.setIfInBounds (256+j) 1#8) K (bit K (IP h (j + (2*h+1)))) := by
  intro i hi
  by_cases he : i = j
  · subst i
    rw [Array.getElem?_setIfInBounds_self_of_lt hsize,
      bit_pos hjK ((ip_step h j j hjs hdiv).mpr (Or.inr rfl))]
  · rw [Array.getElem?_setIfInBounds_ne (by omega), hf i hi]
    have : bit K (IP h (j + (2*h+1))) i = bit K (IP h j) i :=
      bit_congr (fun _ => by rw [ip_step h j i hjs hdiv]; simp [he])
    rw [this]

/-- The marking loop for one candidate: it terminates with the next candidate's marks. -/
private theorem mark_correct (K h j cap : Nat) (hK : K < 2^37) (hh : 1 ≤ h)
    (hcap : 256 + K ≤ cap) (hjs : sq h ≤ j) (hjK : j < K) (hdiv : (2*h+1) ∣ (j - sq h))
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hi : Inv x K h) (hj : x.get 6 = BitVec.ofNat 64 (256+j))
    (hmem : Layout image 200 cap mem) (hf : Flags mem K (bit K (IP h j))) :
    ∃ fuel x' mem', fuel + 3*(j/(2*h+1)) ≤ 3 + 3*(K/(2*h+1)) ∧
      Inv x' K h ∧ Layout image 200 cap mem' ∧
      Flags mem' K (bit K (OM (2*h+3))) ∧
      run fuel ⟨x, 48, mem, [], out, .running⟩ = ⟨x', 60, mem', [], out, .running⟩ := by
  have hhs := self_le_sq h
  obtain ⟨y, hy, hyj, hs⟩ := mark_step K h j cap x mem out hmem hcap hK (by omega) hi hj hjK
  have hl := hmem.update (256+j) (1#8) (by omega)
  have hg := flags_update K h j mem (by rw [hmem.size_eq]; omega) hjs hjK hdiv hf
  by_cases hlt : j + (2*h+1) < K
  · simp only [hlt, ite_true] at hs
    obtain ⟨fuel, z, mem', hfuel, hz, hm, hf', ht⟩ :=
      mark_correct K h (j + (2*h+1)) cap hK hh hcap (by omega) hlt
        (by rw [show j + (2*h+1) - sq h = (j - sq h) + (2*h+1) by omega]
            exact Nat.dvd_add hdiv (Nat.dvd_refl _))
        y (mem.setIfInBounds (256+j) 1#8) out hy hyj hl hg
    have hq : (j + (2*h+1))/(2*h+1) = j/(2*h+1) + 1 := Nat.add_div_right j (by omega)
    refine ⟨3+fuel, z, mem', by omega, hz, hm, hf', ?_⟩
    rw [run_add, hs, ht]
  · simp only [hlt, ite_false] at hs
    have hq : j/(2*h+1) ≤ K/(2*h+1) := Nat.div_le_div_right (by omega)
    refine ⟨3, y, _, by omega, hy, hl, ?_, hs⟩
    exact hg.congr (fun i => bit_congr (fun hiK => ip_done h _ i hh (by omega)))
termination_by K - j

/-- One candidate, from its flag test to the point where the next one is set up. -/
private theorem candidate_correct (K h cap : Nat) (hK : K < 2^37) (hh : 1 ≤ h)
    (hcap : 256 + K ≤ cap) (hsK : sq h < K)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (hi : Inv x K h)
    (hmem : Layout image 200 cap mem) (hf : Flags mem K (bit K (OM (2*h+1)))) :
    ∃ fuel y mem', fuel ≤ 3 + 3*(K/(2*h+1)) ∧
      Inv y K h ∧ Layout image 200 cap mem' ∧
      Flags mem' K (bit K (OM (2*h+3))) ∧
      run fuel ⟨x, 36, mem, [], out, .running⟩ = ⟨y, 60, mem', [], out, .running⟩ := by
  have hhs := self_le_sq h
  have hread := hf h (by omega)
  rcases bit_cases K (OM (2*h+1)) h with ⟨hb, _⟩ | ⟨hb, _, hm⟩
  · rw [hb] at hread
    obtain ⟨y, hy, hyj, hs⟩ := header_fresh K h x mem out hmem.code_eq hi (by omega) hread
    obtain ⟨fuel, z, mem', hfuel, hz, hl, hg, ht⟩ := mark_correct K h (sq h) cap hK hh hcap
      (Nat.le_refl _) hsK (by simp) y mem out hy hyj hmem
      (hf.congr (fun i => bit_congr (fun _ => (ip_start h i).symm)))
    rw [sq_div] at hfuel
    refine ⟨3+fuel, z, mem', by omega, hz, hl, hg, ?_⟩
    rw [run_add, hs, ht]
  · rw [hb] at hread
    obtain ⟨y, hy, hs⟩ := header_marked K h x mem out hmem.code_eq hi (by omega) hread
    refine ⟨2, y, mem, by omega, hy, hmem, ?_, hs⟩
    exact hf.congr (fun i => bit_congr (fun _ => (om_skip h i hm).symm))

/-- The outer loop, entered with the square of the candidate in range. It ends at the count with
the square of the final candidate out of range. -/
private theorem outer_correct (K h cap : Nat) (hK : K < 2^37) (hh : 1 ≤ h)
    (hcap : 256 + K ≤ cap) (hsK : sq h < K)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (hi : Inv x K h)
    (hmem : Layout image 200 cap mem) (hf : Flags mem K (bit K (OM (2*h+1)))) :
    ∃ fuel h' y mem', fuel ≤ 8*(K-h) + 3*quotientSum K (2*h+1) (2*(262144-h)) ∧
      1 ≤ h' ∧ K ≤ sq h' ∧ Inv y K h' ∧ Layout image 200 cap mem' ∧
      Flags mem' K (bit K (OM (2*h'+1))) ∧
      run fuel ⟨x, 36, mem, [], out, .running⟩ = ⟨y, 80, mem', [], out, .running⟩ := by
  have hhs := self_le_sq h
  have hh18 : h < 262144 := lt_of_sq_lt h (by omega)
  obtain ⟨a, y, mem', ha, hy, hl, hg, hs⟩ :=
    candidate_correct K h cap hK hh hcap hsK x mem out hi hmem hf
  obtain ⟨z, hz, ht⟩ := advance K h y mem' out hl.code_eq hy hK (by omega)
  have hlen : 2*(262144-h) = 2*(262144-(h+1)) + 1 + 1 := by omega
  have hqs : quotientSum K (2*h+1) (2*(262144-h)) =
      K/(2*h+1) + (K/(2*h+1+1) + quotientSum K (2*(h+1)+1) (2*(262144-(h+1)))) := by
    rw [hlen, quotientSum_succ, quotientSum_succ, show 2*h+1+1+1 = 2*(h+1)+1 by omega]
  generalize K/(2*h+1) = q1 at ha hqs
  generalize K/(2*h+1+1) = q2 at hqs
  by_cases hlt : sq (h+1) < K
  · simp only [hlt, ite_true] at ht
    have hhs' := self_le_sq (h+1)
    obtain ⟨c, h', w, mem'', hc, hh', hK', hw, hl', hg', hu⟩ :=
      outer_correct K (h+1) cap hK (by omega) hcap hlt z mem' out hz hl hg
    refine ⟨(a+5)+c, h', w, mem'', by omega, hh', hK', hw, hl', hg', ?_⟩
    rw [run_add, run_add, hs, ht, hu]
  · simp only [hlt, ite_false] at ht
    refine ⟨a+5, h+1, z, mem', by omega, by omega, by omega, hz, hl, hg, ?_⟩
    rw [run_add, hs, ht]
termination_by K - h

/-- A word load of four flag bytes, each 0 or 1, is their little-endian sum. -/
private theorem read_word (mem : Array (BitVec 8)) (a f0 f1 f2 f3 : Nat)
    (h0 : mem[a]? = some (BitVec.ofNat 8 f0)) (h1 : mem[a+1]? = some (BitVec.ofNat 8 f1))
    (h2 : mem[a+2]? = some (BitVec.ofNat 8 f2)) (h3 : mem[a+3]? = some (BitVec.ofNat 8 f3))
    (b0 : f0 ≤ 1) (b1 : f1 ≤ 1) (b2 : f2 ≤ 1) (b3 : f3 ≤ 1) :
    (readBytes mem a 4).map (BitVec.signExtend 64) =
      some (BitVec.ofNat 64 (f0 + 256*f1 + 65536*f2 + 16777216*f3)) := by
  have h2' : mem[a+1+1]? = some (BitVec.ofNat 8 f2) := h2
  have h3' : mem[a+1+1+1]? = some (BitVec.ofNat 8 f3) := h3
  have c0 : f0 = 0 ∨ f0 = 1 := by omega
  have c1 : f1 = 0 ∨ f1 = 1 := by omega
  have c2 : f2 = 0 ∨ f2 = 1 := by omega
  have c3 : f3 = 0 ∨ f3 = 1 := by omega
  simp only [readBytes, h0, h1, h2', h3']
  rcases c0 with rfl | rfl <;> rcases c1 with rfl | rfl <;> rcases c2 with rfl | rfl <;>
    rcases c3 with rfl | rfl <;> decide

/-- The two-step fold of four byte lanes, none above 124. -/
private theorem fold_lanes (l0 l1 l2 l3 : Nat) (h0 : l0 ≤ 124) (h1 : l1 ≤ 124) (h2 : l2 ≤ 124)
    (h3 : l3 ≤ 124) (t : BitVec 64)
    (ht : t = BitVec.ofNat 64 (l0 + 256*l1 + 65536*l2 + 16777216*l3)) :
    (t + t >>> 16) &&& 255#64 = BitVec.ofNat 64 (l0 + l2) ∧
    ((t + t >>> 16) >>> 8) &&& 255#64 = BitVec.ofNat 64 (l1 + l3) := by
  subst t
  have hm : ∀ a : Nat, a &&& 255 = a % 256 := fun a => Nat.and_two_pow_sub_one_eq_mod a 8
  obtain ⟨w, hw⟩ : ∃ w, w = l0 + 256*l1 + 65536*l2 + 16777216*l3 := ⟨_, rfl⟩
  rw [← hw]
  have e1 : w % 2^64 = w := by omega
  have e2 : w / 2^16 = l2 + 256*l3 := by omega
  have e3 : (w + (l2 + 256*l3)) % 2^64 = w + (l2 + 256*l3) := by omega
  have e4 : (w + (l2 + 256*l3)) / 2^8 = l1 + l3 + 256*l2 + 65536*l3 := by omega
  have e5 : (l1 + l3 + 256*l2 + 65536*l3) % 256 = l1 + l3 := by omega
  have e6 : (l1 + l3) % 2^64 = l1 + l3 := by omega
  have e7 : (w + (l2 + 256*l3)) % 256 = l0 + l2 := by omega
  have e8 : (l0 + l2) % 2^64 = l0 + l2 := by omega
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, hm, e1, e2, e3, e4, e5, e6, e7, e8]

/-- The count-loop registers: `a0` the running count, `a2 = BASE + K`, `t2` the chunk end,
`a1` the read pointer and `t1` the lane sums. -/
def CInv (x : Regs 64) (a : BitVec 64) (K T q w : Nat) : Prop :=
  x.get 10 = a ∧ x.get 12 = BitVec.ofNat 64 (256+K) ∧ x.get 7 = BitVec.ofNat 64 (256+T) ∧
  x.get 11 = BitVec.ofNat 64 (256+q) ∧ x.get 6 = BitVec.ofNat 64 w

private theorem inner_step (K T q w W0 W1 W2 W3 : Nat) (a : BitVec 64) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String) (hmem : Prefix image mem 200)
    (hq : q < 2^40) (hT : T < 2^40) (hi : CInv x a K T q w)
    (r0 : (readBytes mem (256+q) 4).map (BitVec.signExtend 64) = some (BitVec.ofNat 64 W0))
    (r1 : (readBytes mem (256+q+4) 4).map (BitVec.signExtend 64) = some (BitVec.ofNat 64 W1))
    (r2 : (readBytes mem (256+q+8) 4).map (BitVec.signExtend 64) = some (BitVec.ofNat 64 W2))
    (r3 : (readBytes mem (256+q+12) 4).map (BitVec.signExtend 64) = some (BitVec.ofNat 64 W3)) :
    ∃ x', CInv x' a K T (q+16) (w+W0+W1+W2+W3) ∧
      run 10 ⟨x, 100, mem, [], out, .running⟩ =
        ⟨x', if q+16 < T then 100 else 140, mem, [], out, .running⟩ := by
  obtain ⟨h10, h12, h7, h11, h6⟩ := hi
  obtain ⟨v0, hv0, hs0⟩ := Option.map_eq_some_iff.mp r0
  obtain ⟨v1, hv1, hs1⟩ := Option.map_eq_some_iff.mp r1
  obtain ⟨v2, hv2, hs2⟩ := Option.map_eq_some_iff.mp r2
  obtain ⟨v3, hv3, hs3⟩ := Option.map_eq_some_iff.mp r3
  clear r0 r1 r2 r3
  have m0 := mod64 (256+q) (by omega)
  have m1 := mod64 (256+q+4) (by omega)
  have m2 := mod64 (256+q+8) (by omega)
  have m3 := mod64 (256+q+12) (by omega)
  have e11 : BitVec.ofNat 64 (256+q) + 16#64 = BitVec.ofNat 64 (256+(q+16)) := by
    rw [← BitVec.ofNat_add]; exact ofNat_congr (by omega)
  have hb := addr_ult (q+16) T (by omega) (by omega)
  refine ⟨((((((((x.set 5 (BitVec.ofNat 64 W0)).set 6 (BitVec.ofNat 64 w + BitVec.ofNat 64 W0)).set 5
    (BitVec.ofNat 64 W1)).set 6 (BitVec.ofNat 64 w + BitVec.ofNat 64 W0 + BitVec.ofNat 64 W1)).set 5
    (BitVec.ofNat 64 W2)).set 6
    (BitVec.ofNat 64 w + BitVec.ofNat 64 W0 + BitVec.ofNat 64 W1 + BitVec.ofNat 64 W2)).set 5
    (BitVec.ofNat 64 W3)).set 6
    (BitVec.ofNat 64 w + BitVec.ofNat 64 W0 + BitVec.ofNat 64 W1 + BitVec.ofNat 64 W2
      + BitVec.ofNat 64 W3)).set 11 (BitVec.ofNat 64 (256+(q+16))), ?_, ?_⟩
  · simp [CInv, Regs.get_set, BitVec.ofNat_add, *]
  · by_cases hlt : q+16 < T
    · simp only [hlt, ite_true]
      odd_exec
    · simp only [hlt, ite_false]
      odd_exec

private theorem chunk_head (K q : Nat) (a : BitVec 64) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String) (hmem : Prefix image mem 200)
    (hK : K < 2^37) (hq : q < 2^38)
    (h10 : x.get 10 = a) (h12 : x.get 12 = BitVec.ofNat 64 (256+K))
    (h11 : x.get 11 = BitVec.ofNat 64 (256+q)) :
    ∃ fuel T x', fuel ≤ 4 ∧ ((T = q+496 ∧ q+496 ≤ K) ∨ (T = K ∧ K < q+496)) ∧
      CInv x' a K T q 0 ∧
      run fuel ⟨x, 84, mem, [], out, .running⟩ = ⟨x', 100, mem, [], out, .running⟩ := by
  have e7 : BitVec.ofNat 64 (256+q) + 496#64 = BitVec.ofNat 64 (256+(q+496)) := by
    rw [← BitVec.ofNat_add]; exact ofNat_congr (by omega)
  have hb := addr_ult K (q+496) (by omega) (by omega)
  by_cases hlt : K < q+496
  · refine ⟨4, K, ((x.set 6 0).set 7 (BitVec.ofNat 64 (256+(q+496)))).set 7
      (BitVec.ofNat 64 (256+K)), by omega, Or.inr ⟨rfl, hlt⟩, ?_, ?_⟩
    · simp [CInv, Regs.get_set, *]
    · odd_exec
  · refine ⟨3, q+496, (x.set 6 0).set 7 (BitVec.ofNat 64 (256+(q+496))), by omega,
      Or.inl ⟨rfl, by omega⟩, ?_, ?_⟩
    · simp [CInv, Regs.get_set, *]
    · odd_exec

private theorem fold_block (K T q w l0 l1 l2 l3 : Nat) (a : BitVec 64) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String) (hmem : Prefix image mem 200)
    (hK : K < 2^37) (hq : q < 2^38) (hi : CInv x a K T q w)
    (hw : w = l0 + 256*l1 + 65536*l2 + 16777216*l3)
    (h0 : l0 ≤ 124) (h1 : l1 ≤ 124) (h2 : l2 ≤ 124) (h3 : l3 ≤ 124) :
    ∃ x', x'.get 10 = a - BitVec.ofNat 64 (l0+l2) - BitVec.ofNat 64 (l1+l3) ∧
      x'.get 12 = BitVec.ofNat 64 (256+K) ∧ x'.get 11 = BitVec.ofNat 64 (256+q) ∧
      run 8 ⟨x, 140, mem, [], out, .running⟩ =
        ⟨x', if q < K then 84 else 172, mem, [], out, .running⟩ := by
  obtain ⟨h10, h12, h7, h11, h6⟩ := hi
  obtain ⟨t, ht⟩ : ∃ t, t = BitVec.ofNat 64 w := ⟨_, rfl⟩
  rw [← ht] at h6
  obtain ⟨hA, hB⟩ := fold_lanes l0 l1 l2 l3 h0 h1 h2 h3 t (by rw [ht, hw])
  have hb := addr_ult q K (by omega) (by omega)
  clear ht hw
  refine ⟨((((((x.set 5 (t >>> 16)).set 6 (t + t >>> 16)).set 5 (BitVec.ofNat 64 (l0+l2))).set 10
    (a - BitVec.ofNat 64 (l0+l2))).set 6 ((t + t >>> 16) >>> 8)).set 6
    (BitVec.ofNat 64 (l1+l3))).set 10
    (a - BitVec.ofNat 64 (l0+l2) - BitVec.ofNat 64 (l1+l3)), ?_, ?_, ?_, ?_⟩
  · simp [Regs.get_set]
  · simp [Regs.get_set, *]
  · simp [Regs.get_set, *]
  · by_cases hlt : q < K
    · simp only [hlt, ite_true]
      odd_exec
    · simp only [hlt, ite_false]
      odd_exec

private theorem final_block (c : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 200) (h10 : x.get 10 = BitVec.ofNat 64 c) :
    (run 7 ⟨x, 172, mem, [], out, .running⟩).status = .exited 0 ∧
    (run 7 ⟨x, 172, mem, [], out, .running⟩).output =
      out ++ toString (BitVec.ofNat 64 c).toInt ++ "\n" := by
  odd_exec
  rfl

/-- The sign-extended word at flag index `a`, when every flag is 0 or 1. -/
private theorem flag_word (mem : Array (BitVec 8)) (K : Nat) (f : Nat → Nat)
    (hfl : Flags mem K f) (hf1 : ∀ i, f i ≤ 1) (a : Nat) (ha : a + 4 ≤ K + 16) :
    (readBytes mem (256+a) 4).map (BitVec.signExtend 64) =
      some (BitVec.ofNat 64 (f a + 256*f (a+1) + 65536*f (a+2) + 16777216*f (a+3))) :=
  read_word mem (256+a) _ _ _ _ (hfl a (by omega)) (hfl (a+1) (by omega)) (hfl (a+2) (by omega))
    (hfl (a+3) (by omega)) (hf1 _) (hf1 _) (hf1 _) (hf1 _)

/-- The inner count loop of one chunk starting at `c0`: the four lanes `l0..l3` count the set
flags in `[c0, q)` by index mod 4, and none exceeds 124 because a chunk has at most 496 flags. -/
private theorem inner_correct (K T c0 q l0 l1 l2 l3 : Nat) (f : Nat → Nat) (a : BitVec 64)
    (hK : K < 2^37) (hf1 : ∀ i, f i ≤ 1)
    (hc0 : c0 ≤ q) (hmod : (q - c0) % 16 = 0) (hqK : q ≤ K) (hq : q + 16 ≤ c0 + 496)
    (hT : T ≤ c0 + 496) (hTK : T ≤ K)
    (hl0 : 4*l0 ≤ q - c0) (hl1 : 4*l1 ≤ q - c0) (hl2 : 4*l2 ≤ q - c0) (hl3 : 4*l3 ≤ q - c0)
    (hsum : csum f c0 + (l0+l1+l2+l3) = csum f q)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 200) (hfl : Flags mem K f)
    (hi : CInv x a K T q (l0 + 256*l1 + 65536*l2 + 16777216*l3)) :
    ∃ fuel q' m0 m1 m2 m3 x', 16*fuel = 10*(q' - q) ∧ (q' - q) % 16 = 0 ∧ q < q' ∧ T ≤ q' ∧ q' ≤ c0 + 496 ∧
      (q' < T + 16 ∨ q' = q + 16) ∧ m0 ≤ 124 ∧ m1 ≤ 124 ∧ m2 ≤ 124 ∧ m3 ≤ 124 ∧
      csum f c0 + (m0+m1+m2+m3) = csum f q' ∧
      CInv x' a K T q' (m0 + 256*m1 + 65536*m2 + 16777216*m3) ∧
      run fuel ⟨x, 100, mem, [], out, .running⟩ = ⟨x', 140, mem, [], out, .running⟩ := by
  have r0 : (readBytes mem (256+q) 4).map (BitVec.signExtend 64) = some (BitVec.ofNat 64
      (f q + 256*f (q+1) + 65536*f (q+2) + 16777216*f (q+3))) :=
    flag_word mem K f hfl hf1 q (by omega)
  have r1 : (readBytes mem (256+q+4) 4).map (BitVec.signExtend 64) = some (BitVec.ofNat 64
      (f (q+4) + 256*f (q+5) + 65536*f (q+6) + 16777216*f (q+7))) :=
    flag_word mem K f hfl hf1 (q+4) (by omega)
  have r2 : (readBytes mem (256+q+8) 4).map (BitVec.signExtend 64) = some (BitVec.ofNat 64
      (f (q+8) + 256*f (q+9) + 65536*f (q+10) + 16777216*f (q+11))) :=
    flag_word mem K f hfl hf1 (q+8) (by omega)
  have r3 : (readBytes mem (256+q+12) 4).map (BitVec.signExtend 64) = some (BitVec.ofNat 64
      (f (q+12) + 256*f (q+13) + 65536*f (q+14) + 16777216*f (q+15))) :=
    flag_word mem K f hfl hf1 (q+12) (by omega)
  obtain ⟨y, hy, hs⟩ := inner_step K T q _ _ _ _ _ a x mem out hmem (by omega) (by omega) hi
    r0 r1 r2 r3
  have hcs := csum_add16 f q
  have b0 := hf1 q; have b1 := hf1 (q+1); have b2 := hf1 (q+2); have b3 := hf1 (q+3)
  have b4 := hf1 (q+4); have b5 := hf1 (q+5); have b6 := hf1 (q+6); have b7 := hf1 (q+7)
  have b8 := hf1 (q+8); have b9 := hf1 (q+9); have b10 := hf1 (q+10); have b11 := hf1 (q+11)
  have b12 := hf1 (q+12); have b13 := hf1 (q+13); have b14 := hf1 (q+14); have b15 := hf1 (q+15)
  have hw : l0 + 256*l1 + 65536*l2 + 16777216*l3
      + (f q + 256*f (q+1) + 65536*f (q+2) + 16777216*f (q+3))
      + (f (q+4) + 256*f (q+5) + 65536*f (q+6) + 16777216*f (q+7))
      + (f (q+8) + 256*f (q+9) + 65536*f (q+10) + 16777216*f (q+11))
      + (f (q+12) + 256*f (q+13) + 65536*f (q+14) + 16777216*f (q+15)) =
      (l0 + f q + f (q+4) + f (q+8) + f (q+12))
      + 256*(l1 + f (q+1) + f (q+5) + f (q+9) + f (q+13))
      + 65536*(l2 + f (q+2) + f (q+6) + f (q+10) + f (q+14))
      + 16777216*(l3 + f (q+3) + f (q+7) + f (q+11) + f (q+15)) := by omega
  rw [hw] at hy
  by_cases hlt : q + 16 < T
  · simp only [hlt, ite_true] at hs
    obtain ⟨fuel, q', m0, m1, m2, m3, z, hfuel, hmod', hqq, hTq, hq496, hor, hm0, hm1, hm2, hm3,
        hsum', hz, ht⟩ :=
      inner_correct K T c0 (q+16) _ _ _ _ f a hK hf1 (by omega) (by omega) (by omega) (by omega)
        hT hTK (by omega) (by omega) (by omega) (by omega) (by omega) y mem out hmem hfl hy
    refine ⟨10+fuel, q', m0, m1, m2, m3, z, by omega, by omega, by omega, hTq, hq496, by omega,
      hm0, hm1, hm2, hm3, hsum', hz, ?_⟩
    rw [run_add, hs, ht]
  · simp only [hlt, ite_false] at hs
    exact ⟨10, q+16, _, _, _, _, y, by omega, by omega, by omega, by omega, by omega, Or.inr rfl,
      by omega, by omega, by omega, by omega, by omega, hy, hs⟩
termination_by c0 + 496 - q

private theorem count_sub (k : BitVec 64) (c a b c' : Nat) (h : c + (a + b) = c') :
    k - BitVec.ofNat 64 c - BitVec.ofNat 64 a - BitVec.ofNat 64 b = k - BitVec.ofNat 64 c' := by
  subst h
  simp only [BitVec.ofNat_add]
  grind

/-- The chunked count: from any chunk start to the output code, subtracting every set flag. -/
private theorem count_correct (K q : Nat) (f : Nat → Nat) (hK : K < 2^37)
    (hf1 : ∀ i, f i ≤ 1) (hfz : ∀ i, K ≤ i → f i = 0) (hqK : q ≤ K)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hmem : Prefix image mem 200) (hfl : Flags mem K f)
    (h10 : x.get 10 = BitVec.ofNat 64 K - BitVec.ofNat 64 (csum f q))
    (h12 : x.get 12 = BitVec.ofNat 64 (256+K)) (h11 : x.get 11 = BitVec.ofNat 64 (256+q)) :
    ∃ fuel x', fuel ≤ 22 + 10*((K-q)/16) + 12*((K-q)/496) ∧
      x'.get 10 = BitVec.ofNat 64 K - BitVec.ofNat 64 (csum f K) ∧
      run fuel ⟨x, 84, mem, [], out, .running⟩ = ⟨x', 172, mem, [], out, .running⟩ := by
  obtain ⟨fa, T, y, hfa, hT, hy, hs⟩ := chunk_head K q _ x mem out hmem hK (by omega) h10 h12 h11
  obtain ⟨fb, q', m0, m1, m2, m3, z, hfb, hmod', hqq, hTq, hq496, hor, hm0, hm1, hm2, hm3, hsum, hz, ht⟩ :=
    inner_correct K T q q 0 0 0 0 f _ hK hf1 (Nat.le_refl _) (by omega) hqK (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      y mem out hmem hfl hy
  obtain ⟨u, hu10, hu12, hu11, hv⟩ := fold_block K T q' _ m0 m1 m2 m3 _ z mem out hmem hK
    (by omega) hz rfl hm0 hm1 hm2 hm3
  rw [count_sub _ (csum f q) (m0+m2) (m1+m3) (csum f q') (by omega)] at hu10
  by_cases hlt : q' < K
  · simp only [hlt, ite_true] at hv
    obtain ⟨fc, v, hfc, hv10, hw⟩ := count_correct K q' f hK hf1 hfz (by omega) u mem out hmem hfl
      hu10 hu12 hu11
    refine ⟨((fa+fb)+8)+fc, v, by omega, hv10, ?_⟩
    rw [run_add, run_add, run_add, hs, ht, hv, hw]
  · simp only [hlt, ite_false] at hv
    rw [csum_tail f K q' hfz (by omega)] at hu10
    refine ⟨(fa+fb)+8, u, by omega, hu10, ?_⟩
    rw [run_add, run_add, hs, ht, hv]
termination_by K - q

/-- Flags start clear because of the actual machine loader, and so does the padding. -/
theorem initial_flags (n K : Nat) (hK : K ≤ (n+1)/2) :
    Flags (initial n).mem K (bit K (OM 3)) := by
  intro i hi
  have hz : (initial n).mem[256+i]? = some (0#8) :=
    load_mem_zero 64 prog (memSize n) [] (256+i) (by change 200 ≤ 256+i; omega)
      (by unfold memSize; omega)
  rw [hz, bit_neg (fun hc => by obtain ⟨d, h3, hd, _⟩ := hc.2; omega)]

/-- All of the marking, from the first range check to the start of the count. -/
private theorem marking (K cap : Nat) (hK : K < 2^37) (hcap : 256 + K ≤ cap)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String) (hi : Inv x K 1)
    (hmem : Layout image 200 cap mem) (hf : Flags mem K (bit K (OM 3))) :
    ∃ fuel h' y mem', fuel ≤ 1 + 65*K ∧ 1 ≤ h' ∧ K ≤ sq h' ∧ Inv y K h' ∧
      Layout image 200 cap mem' ∧ Flags mem' K (bit K (OM (2*h'+1))) ∧
      run fuel ⟨x, 32, mem, [], out, .running⟩ = ⟨y, 80, mem', [], out, .running⟩ := by
  have hs1 : sq 1 = 4 := rfl
  have hc := first_check K 1 x mem out hmem.code_eq hi hK (by rw [hs1]; omega)
  by_cases hlt : sq 1 < K
  · simp only [hlt, ite_true] at hc
    obtain ⟨fuel, h', y, mem', hfuel, hh', hK', hy, hl, hg, hu⟩ :=
      outer_correct K 1 cap hK (by omega) hcap hlt x mem out hi hmem hf
    have h2 := quotientSum_le_dyadic K 19 (524286+1) (by decide)
    rw [quotientSum_succ] at h2
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hfuel h2
    refine ⟨1+fuel, h', y, mem', by omega, hh', hK', hy, hl, hg, ?_⟩
    rw [run_add, hc, hu]
  · simp only [hlt, ite_false] at hc
    exact ⟨1, 1, x, mem, by omega, by omega, by omega, hi, hmem, hf, hc⟩

private theorem toInt_nat (c : Nat) (hc : c < 2^63) :
    (BitVec.ofNat 64 c).toInt = (c : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have h64 : c < 2^64 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, show 2*c < 2^64 by omega]

private theorem nat_int_string (c : Nat) : toString (c : Int) = toString c := rfl

/-- **Correctness with an instruction budget.** For every input below `10^11`, the loaded
RV64I program exits with code zero after printing `π(n)` and a newline, within `72 + 33*n`
modeled instructions. The proof includes instruction decoding, the actual flag-byte stores and
the word loads of the count. -/
theorem correct (n : Nat) (hn : n < 10^11) :
    ∃ fuel, fuel ≤ 72 + 33*n ∧
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n") := by
  have hKle := halfCount_le n
  have hid := count_identity n
  obtain ⟨x, hx, hs⟩ := initialize_regs n hn
  generalize halfCount n = K at hKle hid hx
  have hK : K < 2^37 := by omega
  obtain ⟨fm, h', y, mem', hfm, hh', hKs, hy, hl, hg, hm⟩ :=
    marking K (memSize n) hK (by unfold memSize; omega) x (initial n).mem "" hx
      (initial_layout n) (initial_flags n K hKle)
  obtain ⟨h10, h12, _⟩ := hy
  have h80 : run 1 ⟨y, 80, mem', [], "", .running⟩ =
      ⟨y.set 11 256, 84, mem', [], "", .running⟩ := by
    have := hl.code_eq
    odd_exec
  obtain ⟨fc, z, hfc, hz10, hc⟩ := count_correct K 0 (bit K (OM (2*h'+1))) hK
    (bit_le_one _ _) (fun i hi => bit_neg (by omega)) (Nat.zero_le _) (y.set 11 256) mem' ""
    hl.code_eq hg (by simp [Regs.get_set, h10]) (by simp [Regs.get_set, h12])
    (by simp [Regs.get_set])
  have hcs : csum (bit K (OM (2*h'+1))) K = csum compBit K :=
    csum_congr _ _ _ (fun i hi => final_bits K h' i hKs hi)
  have ha0 : BitVec.ofNat 64 K - BitVec.ofNat 64 (csum compBit K) =
      BitVec.ofNat 64 (countPrimes n) := by
    have : BitVec.ofNat 64 K =
        BitVec.ofNat 64 (countPrimes n) + BitVec.ofNat 64 (csum compBit K) := by
      rw [← BitVec.ofNat_add, hid]
    rw [this, BitVec.add_sub_cancel]
  rw [hcs, ha0] at hz10
  have hd := final_block (countPrimes n) z mem' "" hl.code_eq hz10
  have hcp : countPrimes n < 2^63 := by have := countPrimes_le n; omega
  refine ⟨(((8+fm)+1)+fc)+7, by omega, ?_, ?_⟩
  · simpa only [run_add, hs, hm, h80, hc] using hd.1
  · simpa only [run_add, hs, hm, h80, hc, toInt_nat _ hcp, nat_int_string,
      String.empty_append] using hd.2

/-- One fuel value works for every input below `10^11`. -/
theorem correct_uniform_fuel :
    ∃ fuel, ∀ n < 10^11,
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n") := by
  refine ⟨72 + 33*10^11, fun n hn => ?_⟩
  obtain ⟨fuel, hb, h⟩ := correct n hn
  exact is_exited_with_output_mono (by omega) h

/-- `initial'` meets the specification. -/
theorem isCorrect : IsCorrect initial' :=
  isCorrect_of_load prog memSize (256 + (10^11 + 1) / 2 + 16)
    (fun _ _ => by have : 4 * prog.length ≤ 256 := (by decide); unfold memSize; omega)
    (fun _ hn => by unfold memSize; omega)
    correct_uniform_fuel

/-- `initial'` holds 161 nonzero bytes. Zero padding is free, so the size bound rules out
lookup tables. -/
theorem programSize_eq : programSize initial' = 161 := by
  rw [initial', programSize_load prog 256 (256 + (10^11 + 1) / 2 + 16) (by decide) (by omega)]
  decide +kernel

end TinyFive.CountingPrimesOddSieve
