import TinyFive.CountingPrimes
import TinyFive.SieveMemory
import TinyFive.SieveMath

/-!
# RV32I byte-sieve machine correctness

The loaded program uses a zero-initialized, writable byte array at address 128. Its code
occupies addresses 0 through 99 and is preserved by every store. `correct` proves termination
and exact prime-count output for natural inputs up to `2^30-1`, relative to `TinyFive.Machine`.
Equality with the Python instruction list and correspondence of the emulator with the Lean
model are separate validation boundaries.

The specification is `CountingPrimes.countPrimes`; its `countPrimes_eq_filter` and
`prime_iff_no_proper_divisor` theorems identify it with the finite count of conventional primes.
The proof tracks every flag byte by `SieveMath.Marked`, and each store advances
`SieveMath.InProgress`. Decreasing cursor/candidate measures prove termination; the sieve
contains no trial-division loop or division instruction.
-/
namespace TinyFive.CountingPrimesSieve
open CountingPrimes SieveMemory SieveMath

/-- The twenty-five instruction words of `counting_primes_sieve.py`. -/
def prog : List (BitVec 32) := [
  0x00200293, 0x00000313, 0x00100f13, 0x08000f93, 0x02556a63,
  0x005f8e33, 0x000e4e83, 0x020e9063, 0x00130313, 0x005283b3,
  0x00756a63, 0x007f8e33, 0x01ee0023, 0x005383b3, 0xff1ff06f,
  0x00128293, 0xfd1ff06f, 0x00030513, 0x00100893, 0x00000073,
  0x00a00513, 0x00b00893, 0x00000073, 0x00a00893, 0x00000073]

/-- Preload the input and allocate one zeroed flag byte for every index through `n`. -/
def initial (n : Nat) : Machine 32 :=
  (load 32 prog (128+n+1) []).setReg 10 (BitVec.ofNat 32 n)

def image : Array (BitVec 8) := (load 32 prog 128 []).mem

def code : List Instr := [
  .opImm .add 5 0 2, .opImm .add 6 0 0,
  .opImm .add 30 0 1, .opImm .add 31 0 128,
  .branch .bltu 10 5 52, .op .add 28 31 5, .load .byte false 29 28 0,
  .branch .bne 29 0 32, .opImm .add 6 6 1, .op .add 7 5 5,
  .branch .bltu 10 7 20, .op .add 28 31 7, .store .byte 30 28 0,
  .op .add 7 7 5, .jal 0 (-16), .opImm .add 5 5 1, .jal 0 (-48),
  .opImm .add 10 6 0, .opImm .add 17 0 1, .ecall,
  .opImm .add 10 0 10, .opImm .add 17 0 11, .ecall,
  .opImm .add 17 0 10, .ecall]

/-- Every encoded instruction is decoded by kernel evaluation, not assumed. -/
theorem fetch : ∀ pc, pc < 100 → pc % 4 = 0 →
    (readBytes image pc 4).bind (decode 32) = some (code.getD (pc/4) .ecall) := by
  decide +kernel

theorem step_image (x : Regs 32) (pc : BitVec 32) (mem : Array (BitVec 8))
    (out : String) (st : Status) (hmem : Prefix image mem 100)
    (h : pc.toNat < 100) (h4 : pc.toNat % 4 = 0) :
    step ⟨x, pc, mem, [], out, st⟩ =
      exec (code.getD (pc.toNat/4) .ecall) ⟨x, pc, mem, [], out, st⟩ := by
  apply step_of_prefix _ image 100 hmem (by change pc.toNat + 4 ≤ 100; omega)
  exact fetch _ h h4

macro "sieve_exec" : tactic =>
  `(tactic| simp [run, step_image, code, exec, Machine.setReg, Machine.advance,
      Machine.fail, alu, ecall, Width.bytes, Regs.get_set, BranchOp.taken, *])

/-- Live registers: input, candidate, count, byte marker, and data-array base. -/
def Inv (x : Regs 32) (n p c : Nat) : Prop :=
  x.get 10 = BitVec.ofNat 32 n ∧ x.get 5 = BitVec.ofNat 32 p ∧
  x.get 6 = BitVec.ofNat 32 c ∧ x.get 30 = 1 ∧ x.get 31 = 128

private theorem nat_ult (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    (BitVec.ofNat 32 a).ult (BitVec.ofNat 32 b) = decide (a < b) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem nat_address (p : Nat) (hp : 128+p < 2^32) :
    (128#32 + BitVec.ofNat 32 p).toNat = 128+p := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem header_marked (n p c : Nat) (x : Regs 32) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 100) (hi : Inv x n p c)
    (hn : n < 2^32) (hp : 128+p < 2^32) (hpn : p ≤ n)
    (hread : readBytes mem (128+p) 1 = some 1#8) :
    ∃ x', Inv x' n p c ∧
      run 4 ⟨x, 16, mem, [], out, .running⟩ = ⟨x', 60, mem, [], out, .running⟩ := by
  obtain ⟨h10, h5, h6, h30, h31⟩ := hi
  have hb : (BitVec.ofNat 32 n).ult (BitVec.ofNat 32 p) = false := by
    rw [nat_ult n p hn (by omega)]
    simp [show ¬ n < p by omega]
  have ha := nat_address p hp
  refine ⟨(x.set 28 (128 + BitVec.ofNat 32 p)).set 29 1, ?_, ?_⟩
  · simp [Inv, Regs.get_set, *]
  · sieve_exec

private theorem header_fresh (n p c : Nat) (x : Regs 32) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 100) (hi : Inv x n p c)
    (hn : n < 2^32) (hp : 128+p < 2^32) (hpn : p ≤ n)
    (hread : readBytes mem (128+p) 1 = some 0#8) :
    ∃ x', Inv x' n p (c+1) ∧ x'.get 7 = BitVec.ofNat 32 (p+p) ∧
      run 6 ⟨x, 16, mem, [], out, .running⟩ = ⟨x', 40, mem, [], out, .running⟩ := by
  obtain ⟨h10, h5, h6, h30, h31⟩ := hi
  have hb : (BitVec.ofNat 32 n).ult (BitVec.ofNat 32 p) = false := by
    rw [nat_ult n p hn (by omega)]
    simp [show ¬ n < p by omega]
  have ha := nat_address p hp
  refine ⟨(((x.set 28 (128 + BitVec.ofNat 32 p)).set 29 0).set 6
    (BitVec.ofNat 32 c + 1)).set 7 (BitVec.ofNat 32 p + BitVec.ofNat 32 p), ?_, ?_, ?_⟩
  · simp [Inv, Regs.get_set, BitVec.ofNat_add, *]
  · simp [Regs.get_set, BitVec.ofNat_add]
  · sieve_exec

private theorem mark_done (n p c j : Nat) (x : Regs 32) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 100) (hi : Inv x n p c)
    (hj : x.get 7 = BitVec.ofNat 32 j) (hn32 : n < 2^32) (hj32 : j < 2^32)
    (hdone : n < j) :
    run 1 ⟨x, 40, mem, [], out, .running⟩ = ⟨x, 60, mem, [], out, .running⟩ := by
  have hb : (BitVec.ofNat 32 n).ult (BitVec.ofNat 32 j) = true := by
    rw [nat_ult n j hn32 hj32]
    simp [hdone]
  have h10 := hi.1
  sieve_exec

private theorem mark_step (n p c j : Nat) (x : Regs 32) (mem : Array (BitVec 8))
    (out : String) (hmem : Layout image 100 (128+n+1) mem) (hi : Inv x n p c)
    (hj : x.get 7 = BitVec.ofNat 32 j) (hn32 : n < 2^32) (hjaddr : 128+j < 2^32)
    (hjn : j ≤ n) :
    ∃ x', Inv x' n p c ∧ x'.get 7 = BitVec.ofNat 32 (j+p) ∧
      run 5 ⟨x, 40, mem, [], out, .running⟩ =
        ⟨x', 40, mem.setIfInBounds (128+j) 1#8, [], out, .running⟩ := by
  obtain ⟨h10, h5, h6, h30, h31⟩ := hi
  have hb : (BitVec.ofNat 32 n).ult (BitVec.ofNat 32 j) = false := by
    rw [nat_ult n j hn32 (by omega)]
    simp [show ¬ n < j by omega]
  have ha := nat_address j hjaddr
  have hcode := hmem.code_eq
  have hcode' := hmem.update (128+j) (1#8) (by omega) |>.code_eq
  have hwrite : writeBytes mem (128+j) (1#32) 1 =
      some (mem.setIfInBounds (128+j) 1#8) := by
    exact writeBytes_byte mem _ _ (by rw [hmem.size_eq]; omega)
  refine ⟨(((x.set 28 (128 + BitVec.ofNat 32 j)).set 7
    (BitVec.ofNat 32 j + BitVec.ofNat 32 p)).set 0 60), ?_, ?_, ?_⟩
  · simp [Inv, Regs.get_set, *]
  · simp [Regs.get_set, BitVec.ofNat_add]
  · sieve_exec

private theorem outer_next (n p c : Nat) (x : Regs 32) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 100) (hi : Inv x n p c) :
    ∃ x', Inv x' n (p+1) c ∧
      run 2 ⟨x, 60, mem, [], out, .running⟩ = ⟨x', 16, mem, [], out, .running⟩ := by
  obtain ⟨h10, h5, h6, h30, h31⟩ := hi
  refine ⟨(x.set 5 (BitVec.ofNat 32 p + 1)).set 0 68, ?_, ?_⟩
  · simp [Inv, Regs.get_set, BitVec.ofNat_add, *]
  · sieve_exec

private theorem outer_done (n p c : Nat) (x : Regs 32) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 100) (hi : Inv x n p c)
    (hn32 : n < 2^32) (hp32 : p < 2^32) (hdone : n < p) :
    (run 9 ⟨x, 16, mem, [], out, .running⟩).status = .exited 0 ∧
    (run 9 ⟨x, 16, mem, [], out, .running⟩).output =
      out ++ toString (BitVec.ofNat 32 c).toInt ++ "\n" := by
  obtain ⟨h10, h5, h6, h30, h31⟩ := hi
  have hb : (BitVec.ofNat 32 n).ult (BitVec.ofNat 32 p) = true := by
    rw [nat_ult n p hn32 hp32]
    simp [hdone]
  sieve_exec
  rfl

/-- A precise description of every flag byte in the active range. -/
def Flags (mem : Array (BitVec 8)) (n : Nat) (P : Nat → Prop) [DecidablePred P] : Prop :=
  ∀ k, 2 ≤ k → k ≤ n → readBytes mem (128+k) 1 = some (if P k then 1#8 else 0#8)

/-- A real byte store advances the arithmetic inner-loop invariant. -/
private theorem flags_update (n p j : Nat) (mem : Array (BitVec 8))
    (hmem : Layout image 100 (128+n+1) mem) (hp : 0 < p) (hpj : p < j)
    (hj : p ∣ j) (hjn : j ≤ n) (hf : Flags mem n (InProgress p j)) :
    Flags (mem.setIfInBounds (128+j) 1#8) n (InProgress p (j+p)) := by
  intro k hk hkn
  by_cases he : k = j
  · subst k
    rw [read_update_same mem (128+j) (1#8) (by rw [hmem.size_eq]; omega)]
    have hm : InProgress p (j+p) j := (progress_step p j j hp hpj hj).mpr (Or.inr rfl)
    simp [hm]
  · rw [read_update_other mem (128+j) (128+k) (1#8) (by omega), hf k hk hkn]
    have heq : InProgress p (j+p) k ↔ InProgress p j k := by
      rw [progress_step p j k hp hpj hj]
      simp [he]
    simp only [heq]

/-- Termination and complete memory correctness of the machine's marking loop. -/
private theorem mark_correct (n p c j : Nat) (hn : n ≤ 2^30-1) (hp : 2 ≤ p)
    (hpn : p ≤ n) (hjmin : p+p ≤ j) (hjmax : j ≤ n+p) (hdiv : p ∣ j)
    (x : Regs 32) (mem : Array (BitVec 8)) (out : String)
    (hi : Inv x n p c) (hj : x.get 7 = BitVec.ofNat 32 j)
    (hmem : Layout image 100 (128+n+1) mem) (hf : Flags mem n (InProgress p j)) :
    ∃ fuel x' mem', Inv x' n p c ∧ Layout image 100 (128+n+1) mem' ∧
      Flags mem' n (Marked (p+1)) ∧
      run fuel ⟨x, 40, mem, [], out, .running⟩ = ⟨x', 60, mem', [], out, .running⟩ := by
  by_cases hdone : n < j
  · refine ⟨1, x, mem, hi, hmem, ?_, ?_⟩
    · intro k hk hkn
      have hiff := progress_done p j k hp (show k < j by omega)
      simpa only [hiff] using hf k hk hkn
    · exact mark_done n p c j x mem out hmem.code_eq hi hj (by omega) (by omega) hdone
  · have hjn : j ≤ n := by omega
    obtain ⟨y, hy, hyj, hs⟩ := mark_step n p c j x mem out hmem hi hj
      (by omega) (by omega) hjn
    have hl := hmem.update (128+j) (1#8) (by omega)
    have hg := flags_update n p j mem hmem (by omega) (by omega) hdiv hjn hf
    obtain ⟨more, z, mem', hz, hm, hf', ht⟩ :=
      mark_correct n p c (j+p) hn hp hpn (by omega) (by omega)
        (Nat.dvd_add hdiv (Nat.dvd_refl p)) y (mem.setIfInBounds (128+j) 1#8) out hy hyj hl hg
    refine ⟨5 + more, z, mem', hz, hm, hf', ?_⟩
    rw [run_add, hs, ht]
termination_by n+1-j

private theorem countPrimes_step (p : Nat) (hp : 0 < p) :
    countPrimes p = countPrimes (p-1) + if Prime p then 1 else 0 := by
  cases p with
  | zero => omega
  | succ p => rfl

/-- One complete sieve candidate, including the actual marking stores when fresh. -/
private theorem candidate_correct (n p : Nat) (hn : n ≤ 2^30-1) (hp : 2 ≤ p)
    (hpn : p ≤ n) (x : Regs 32) (mem : Array (BitVec 8)) (out : String)
    (hi : Inv x n p (countPrimes (p-1)))
    (hmem : Layout image 100 (128+n+1) mem) (hf : Flags mem n (Marked p)) :
    ∃ fuel y mem', Inv y n p (countPrimes p) ∧ Layout image 100 (128+n+1) mem' ∧
      Flags mem' n (Marked (p+1)) ∧
      run fuel ⟨x, 16, mem, [], out, .running⟩ = ⟨y, 60, mem', [], out, .running⟩ := by
  by_cases hm : Marked p p
  · have hnp := (marked_self_iff_not_prime p hp).mp hm
    have hc : countPrimes p = countPrimes (p-1) := by
      simp [countPrimes_step p (by omega), hnp]
    have hread : readBytes mem (128+p) 1 = some 1#8 := by
      simpa only [ite_eq_left hm] using hf p hp hpn
    obtain ⟨y, hy, hs⟩ := header_marked n p (countPrimes (p-1)) x mem out hmem.code_eq
      hi (by omega) (by omega) hpn hread
    refine ⟨4, y, mem, ?_, hmem, ?_, hs⟩
    · simpa only [hc] using hy
    · intro k hk hkn
      simpa only [composite_skip p k hm] using hf k hk hkn
  · have hprime : Prime p := by
      by_cases h : Prime p
      · exact h
      · exact False.elim (hm ((marked_self_iff_not_prime p hp).mpr h))
    have hc : countPrimes p = countPrimes (p-1) + 1 := by
      simp [countPrimes_step p (by omega), hprime]
    have hread : readBytes mem (128+p) 1 = some 0#8 := by
      simpa only [ite_eq_right hm] using hf p hp hpn
    obtain ⟨y, hy, hyj, hs⟩ := header_fresh n p (countPrimes (p-1)) x mem out hmem.code_eq
      hi (by omega) (by omega) hpn hread
    have hy' : Inv y n p (countPrimes p) := by simpa only [hc] using hy
    have hfstart : Flags mem n (InProgress p (p+p)) := by
      intro k hk hkn
      simpa only [progress_start] using hf k hk hkn
    obtain ⟨fuel, z, mem', hz, hl, hg, ht⟩ := mark_correct n p (countPrimes p) (p+p)
      hn hp hpn (by omega) (by omega) (Nat.dvd_add (Nat.dvd_refl p) (Nat.dvd_refl p))
      y mem out hy' hyj hmem hfstart
    refine ⟨6 + fuel, z, mem', hz, hl, hg, ?_⟩
    rw [run_add, hs, ht]

private theorem toInt_nat (c : Nat) (hc : c < 2^31) :
    (BitVec.ofNat 32 c).toInt = (c : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have h32 : c < 2^32 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32, show 2*c < 2^32 by omega]

private theorem nat_int_string (c : Nat) : toString (c : Int) = toString c := rfl

/-- Outer-loop invariant and termination, with mutable data but immutable code. -/
private theorem outer_correct (n p : Nat) (hn : n ≤ 2^30-1) (hp : 2 ≤ p)
    (hpn : p ≤ n+1) (x : Regs 32) (mem : Array (BitVec 8)) (out : String)
    (hi : Inv x n p (countPrimes (p-1)))
    (hmem : Layout image 100 (128+n+1) mem) (hf : Flags mem n (Marked p)) :
    ∃ fuel, (run fuel ⟨x, 16, mem, [], out, .running⟩).status = .exited 0 ∧
      (run fuel ⟨x, 16, mem, [], out, .running⟩).output =
        out ++ toString (countPrimes n) ++ "\n" := by
  by_cases hdone : n < p
  · have he : p-1 = n := by omega
    have hc : countPrimes n < 2^31 := by have := countPrimes_le n; omega
    refine ⟨9, ?_⟩
    have hd := outer_done n p (countPrimes (p-1)) x mem out hmem.code_eq hi
      (by omega) (by omega) hdone
    simpa only [he, toInt_nat _ hc, nat_int_string] using hd
  · obtain ⟨fuel, y, mem', hy, hl, hg, hs⟩ :=
      candidate_correct n p hn hp (by omega) x mem out hi hmem hf
    obtain ⟨z, hz, ht⟩ := outer_next n p (countPrimes p) y mem' out hl.code_eq hy
    have hz' : Inv z n (p+1) (countPrimes ((p+1)-1)) := by simpa using hz
    obtain ⟨more, hm⟩ := outer_correct n (p+1) hn (by omega) (by omega)
      z mem' out hz' hl hg
    refine ⟨fuel + 2 + more, ?_⟩
    rwa [run_add, run_add, hs, ht]
termination_by n+1-p

/-- The loader allocates every flag and keeps the code in the protected prefix. -/
theorem initial_layout (n : Nat) : Layout image 100 (128+n+1) (initial n).mem := by
  exact load_layout_boundary 32 prog 100 128 (128+n+1) [] []
    (by decide) (by decide) (by omega)

/-- Flags start clear because of the actual machine loader, not an abstract sieve assumption. -/
theorem initial_flags (n : Nat) : Flags (initial n).mem n (Marked 2) := by
  intro k hk hkn
  have hz : (initial n).mem[128+k]? = some (0#8) := by
    apply load_mem_zero 32 prog (128+n+1) [] (128+k)
    · change 100 ≤ 128+k
      omega
    · omega
  simpa only [readBytes_byte, ite_eq_right (marked_two k)] using hz

private theorem initialize_regs (n : Nat) :
    ∃ x, Inv x n 2 0 ∧ run 4 (initial n) =
      ⟨x, 16, (initial n).mem, [], "", .running⟩ := by
  let x : Regs 32 := (⟨Vector.replicate 32 0⟩ : Regs 32).set 10 (BitVec.ofNat 32 n)
  let mem := (load 32 prog (128+n+1) []).mem
  have hi : initial n = ⟨x, 0, mem, [], "", .running⟩ := rfl
  have hmem : Prefix image mem 100 := (initial_layout n).code_eq
  change ∃ y, Inv y n 2 0 ∧ run 4 (initial n) = ⟨y, 16, mem, [], "", .running⟩
  rw [hi]
  refine ⟨(((x.set 5 2).set 6 0).set 30 1).set 31 128, ?_, ?_⟩
  · simp [Inv, x, Regs.get_set]
  · sieve_exec

/-- **Full RV32I sieve machine correctness.** With the integer input preloaded in `a0`
and a dynamically sized zeroed byte array, the program terminates with exit code zero and
prints precisely the number of primes at most `n`, followed by a newline. The bound ensures
that doubled multiples, byte addresses, and the signed printed count cannot overflow.
There is no fuel, flag-correctness, or termination assumption. -/
theorem correct (n : Nat) (hn : n ≤ 2^30-1) :
    ∃ fuel, (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" := by
  obtain ⟨x, hx, hs⟩ := initialize_regs n
  have hl := initial_layout n
  by_cases hsmall : n < 2
  · have hc : countPrimes n = 0 := by
      have : n = 0 ∨ n = 1 := by omega
      obtain rfl | rfl := this <;> simp
    have hd := outer_done n 2 0 x (initial n).mem "" hl.code_eq hx
      (by omega) (by decide) hsmall
    refine ⟨4 + 9, ?_⟩
    rw [run_add, hs]
    simpa only [hc, toInt_nat 0 (by decide), nat_int_string, String.empty_append] using hd
  · have hi : Inv x n 2 (countPrimes (2-1)) := by simpa using hx
    obtain ⟨fuel, hf⟩ := outer_correct n 2 hn (by decide) (by omega)
      x (initial n).mem "" hi hl (initial_flags n)
    refine ⟨4 + fuel, ?_⟩
    rw [run_add, hs]
    simpa using hf

end TinyFive.CountingPrimesSieve
