import TinyFive.Machine
import TinyFive.Primes
import TinyFive.SieveMemory
import TinyFive.SieveMath
import SieveCost
import SieveCostBound

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

## Instruction counts

`correct_with_time` executes the explicit `SieveCost.instructionCount n` budget.
`running_before` and `exited_iff_count_le` prove this is the exact first-exit count, not just
an upper bound obtained by giving a stopped machine extra fuel. `correct_bounded` gives the
simple bound `13 + (n-1)*(9+5*n)`. `correct_under_10000` proves a stricter practical bound for
all `n ≤ 600`; `still_running_10000` proves that 10,000 is not a bound for the whole valid
input domain. These count modeled RV32I instructions, including system calls, not wall time
or the host wrapper's input parsing and memory allocation.
`correct_under_rv32_dyadic_cap` gives the tighter uniform bound `< 2^38` for
the whole supported domain, using only elementary dyadic blocks.
-/
namespace TinyFive.CountingPrimesSieve
open CountingPrimes SieveMemory SieveMath SieveCost

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

/-- The output suffix has not exited immediately before its last instruction. -/
private theorem outer_last_running (n p c : Nat) (x : Regs 32) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 100) (hi : Inv x n p c)
    (hn32 : n < 2^32) (hp32 : p < 2^32) (hdone : n < p) :
    (run 8 ⟨x, 16, mem, [], out, .running⟩).status = .running := by
  obtain ⟨h10, h5, h6, h30, h31⟩ := hi
  have hb : (BitVec.ofNat 32 n).ult (BitVec.ofNat 32 p) = true := by
    rw [nat_ult n p hn32 hp32]
    simp [hdone]
  sieve_exec

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

/-- Exact instruction budget and complete memory correctness of the marking loop. -/
private theorem mark_correct (n p c j : Nat) (hn : n ≤ 2^30-1) (hp : 2 ≤ p)
    (hpn : p ≤ n) (hjmin : p+p ≤ j) (hjmax : j ≤ n+p) (hdiv : p ∣ j)
    (x : Regs 32) (mem : Array (BitVec 8)) (out : String)
    (hi : Inv x n p c) (hj : x.get 7 = BitVec.ofNat 32 j)
    (hmem : Layout image 100 (128+n+1) mem) (hf : Flags mem n (InProgress p j)) :
    ∃ x' mem', Inv x' n p c ∧ Layout image 100 (128+n+1) mem' ∧
      Flags mem' n (Marked (p+1)) ∧
      run (markCost n p j) ⟨x, 40, mem, [], out, .running⟩ = ⟨x', 60, mem', [], out, .running⟩ := by
  by_cases hdone : n < j
  · refine ⟨x, mem, hi, hmem, ?_, ?_⟩
    · intro k hk hkn
      have hiff := progress_done p j k hp (show k < j by omega)
      simpa only [hiff] using hf k hk hkn
    · rw [markCost_done n p j hdone hjmax]
      exact mark_done n p c j x mem out hmem.code_eq hi hj (by omega) (by omega) hdone
  · have hjn : j ≤ n := by omega
    obtain ⟨y, hy, hyj, hs⟩ := mark_step n p c j x mem out hmem hi hj
      (by omega) (by omega) hjn
    have hl := hmem.update (128+j) (1#8) (by omega)
    have hg := flags_update n p j mem hmem (by omega) (by omega) hdiv hjn hf
    obtain ⟨z, mem', hz, hm, hf', ht⟩ :=
      mark_correct n p c (j+p) hn hp hpn (by omega) (by omega)
        (Nat.dvd_add hdiv (Nat.dvd_refl p)) y (mem.setIfInBounds (128+j) 1#8) out hy hyj hl hg
    refine ⟨z, mem', hz, hm, hf', ?_⟩
    rw [markCost_step n p j (by omega) hjn, run_add, hs, ht]
termination_by n+1-j

private theorem countPrimes_step (p : Nat) (hp : 0 < p) :
    countPrimes p = countPrimes (p-1) + if Prime p then 1 else 0 := by
  cases p with
  | zero => omega
  | succ p => rfl

/-- One complete candidate with its instruction budget, including actual marking stores. -/
private theorem candidate_correct (n p : Nat) (hn : n ≤ 2^30-1) (hp : 2 ≤ p)
    (hpn : p ≤ n) (x : Regs 32) (mem : Array (BitVec 8)) (out : String)
    (hi : Inv x n p (countPrimes (p-1)))
    (hmem : Layout image 100 (128+n+1) mem) (hf : Flags mem n (Marked p)) :
    ∃ y mem', Inv y n p (countPrimes p) ∧ Layout image 100 (128+n+1) mem' ∧
      Flags mem' n (Marked (p+1)) ∧
      run (candidateCost n p - 2) ⟨x, 16, mem, [], out, .running⟩ =
        ⟨y, 60, mem', [], out, .running⟩ := by
  by_cases hm : Marked p p
  · have hnp := (marked_self_iff_not_prime p hp).mp hm
    have hc : countPrimes p = countPrimes (p-1) := by
      simp [countPrimes_step p (by omega), hnp]
    have hread : readBytes mem (128+p) 1 = some 1#8 := by
      simpa only [ite_eq_left hm] using hf p hp hpn
    obtain ⟨y, hy, hs⟩ := header_marked n p (countPrimes (p-1)) x mem out hmem.code_eq
      hi (by omega) (by omega) hpn hread
    refine ⟨y, mem, ?_, hmem, ?_, ?_⟩
    · simpa only [hc] using hy
    · intro k hk hkn
      simpa only [composite_skip p k hm] using hf k hk hkn
    · simpa [candidateCost, hnp] using hs
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
    obtain ⟨z, mem', hz, hl, hg, ht⟩ := mark_correct n p (countPrimes p) (p+p)
      hn hp hpn (by omega) (by omega) (Nat.dvd_add (Nat.dvd_refl p) (Nat.dvd_refl p))
      y mem out hy' hyj hmem hfstart
    refine ⟨z, mem', hz, hl, hg, ?_⟩
    have hcost : candidateCost n p - 2 = 6 + markCost n p (p+p) := by
      rw [markCost_start n p (by omega) hpn]
      simp [candidateCost, hprime]
      omega
    rw [hcost, run_add, hs, ht]

private theorem toInt_nat (c : Nat) (hc : c < 2^31) :
    (BitVec.ofNat 32 c).toInt = (c : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have h32 : c < 2^32 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32, show 2*c < 2^32 by omega]

private theorem nat_int_string (c : Nat) : toString (c : Int) = toString c := rfl

/-- Outer-loop correctness and exact first-exit budget, with mutable data and immutable code. -/
private theorem outer_correct (n p : Nat) (hn : n ≤ 2^30-1) (hp : 2 ≤ p)
    (hpn : p ≤ n+1) (x : Regs 32) (mem : Array (BitVec 8)) (out : String)
    (hi : Inv x n p (countPrimes (p-1)))
    (hmem : Layout image 100 (128+n+1) mem) (hf : Flags mem n (Marked p)) :
    (run (9 + scanCost n p (n+1-p)) ⟨x, 16, mem, [], out, .running⟩).status = .exited 0 ∧
      (run (9 + scanCost n p (n+1-p)) ⟨x, 16, mem, [], out, .running⟩).output =
        out ++ toString (countPrimes n) ++ "\n" ∧
      (run (9 + scanCost n p (n+1-p) - 1) ⟨x, 16, mem, [], out, .running⟩).status =
        .running := by
  by_cases hdone : n < p
  · have he : p-1 = n := by omega
    have hc : countPrimes n < 2^31 := by have := countPrimes_le n; omega
    have hz : n+1-p = 0 := by omega
    rw [hz, scanCost_zero]
    have hd := outer_done n p (countPrimes (p-1)) x mem out hmem.code_eq hi
      (by omega) (by omega) hdone
    refine ⟨hd.1, ?_, ?_⟩
    · simpa only [he, toInt_nat _ hc, nat_int_string] using hd.2
    · exact outer_last_running n p (countPrimes (p-1)) x mem out hmem.code_eq hi
        (by omega) (by omega) hdone
  · obtain ⟨y, mem', hy, hl, hg, hs⟩ :=
      candidate_correct n p hn hp (by omega) x mem out hi hmem hf
    obtain ⟨z, hz, ht⟩ := outer_next n p (countPrimes p) y mem' out hl.code_eq hy
    have hz' : Inv z n (p+1) (countPrimes ((p+1)-1)) := by simpa using hz
    have hm := outer_correct n (p+1) hn (by omega) (by omega)
      z mem' out hz' hl hg
    have hlen : n+1-p = (n+1-(p+1))+1 := by omega
    have hcost : 9 + scanCost n p (n+1-p) =
        (candidateCost n p - 2) + 2 + (9 + scanCost n (p+1) (n+1-(p+1))) := by
      rw [hlen, scanCost_succ]
      have hc : 2 ≤ candidateCost n p := by unfold candidateCost; split <;> omega
      omega
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hcost,
        run_add (candidateCost n p - 2 + 2) (9 + scanCost n (p+1) (n+1-(p+1))),
        run_add (candidateCost n p - 2) 2, hs, ht] using hm.1
    · simpa only [hcost,
        run_add (candidateCost n p - 2 + 2) (9 + scanCost n (p+1) (n+1-(p+1))),
        run_add (candidateCost n p - 2) 2, hs, ht] using hm.2.1
    · have hprev : 9 + scanCost n p (n+1-p) - 1 =
          (candidateCost n p - 2 + 2) + (9 + scanCost n (p+1) (n+1-(p+1)) - 1) := by
        omega
      rw [hprev,
        run_add (candidateCost n p - 2 + 2) (9 + scanCost n (p+1) (n+1-(p+1)) - 1),
        run_add (candidateCost n p - 2) 2, hs, ht]
      exact hm.2.2
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

/-- The timed machine execution exits at the budget, and is still running one step earlier. -/
private theorem correct_timed (n : Nat) (hn : n ≤ 2^30-1) :
    (run (instructionCount n) (initial n)).status = .exited 0 ∧
      (run (instructionCount n) (initial n)).output = toString (countPrimes n) ++ "\n" ∧
      (run (instructionCount n - 1) (initial n)).status = .running := by
  obtain ⟨x, hx, hs⟩ := initialize_regs n
  have hl := initial_layout n
  by_cases hsmall : n < 2
  · have hc : countPrimes n = 0 := by
      have : n = 0 ∨ n = 1 := by omega
      obtain rfl | rfl := this <;> simp
    have hd := outer_done n 2 0 x (initial n).mem "" hl.code_eq hx
      (by omega) (by decide) hsmall
    rw [instructionCount_small n hsmall]
    refine ⟨?_, ?_, ?_⟩
    · change (run (4+9) (initial n)).status = .exited 0
      rw [run_add, hs]
      exact hd.1
    · change (run (4+9) (initial n)).output = toString (countPrimes n) ++ "\n"
      rw [run_add, hs]
      simpa only [hc, toInt_nat 0 (by decide), nat_int_string, String.empty_append] using hd.2
    · change (run (4+8) (initial n)).status = .running
      rw [run_add, hs]
      exact outer_last_running n 2 0 x (initial n).mem "" hl.code_eq hx
        (by omega) (by decide) hsmall
  · have hi : Inv x n 2 (countPrimes (2-1)) := by simpa using hx
    have hf := outer_correct n 2 hn (by decide) (by omega)
      x (initial n).mem "" hi hl (initial_flags n)
    have hcost : instructionCount n = 4 + (9 + scanCost n 2 (n+1-2)) := by
      unfold instructionCount
      have : n+1-2 = n-1 := by omega
      rw [this]
      omega
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hcost, run_add 4 (9 + scanCost n 2 (n+1-2)), hs] using hf.1
    · simpa only [hcost, run_add 4 (9 + scanCost n 2 (n+1-2)), hs,
        String.empty_append] using hf.2.1
    · have hprev : instructionCount n - 1 = 4 + (9 + scanCost n 2 (n+1-2) - 1) := by
        omega
      rw [hprev, run_add, hs]
      exact hf.2.2

/-- **Timed RV32I sieve correctness.** The explicit instruction budget is sufficient for
termination with exit code zero and the exact prime-count output. It includes initialization,
all sieve branches/loads/stores, and output/exit instructions, but not host-side input parsing. -/
theorem correct_with_time (n : Nat) (hn : n ≤ 2^30-1) :
    (run (instructionCount n) (initial n)).status = .exited 0 ∧
      (run (instructionCount n) (initial n)).output = toString (countPrimes n) ++ "\n" :=
  ⟨(correct_timed n hn).1, (correct_timed n hn).2.1⟩

private theorem run_stopped {w : Nat} (fuel : Nat) (m : Machine w)
    (h : m.status ≠ .running) : run fuel m = m := by
  cases fuel <;> simp [run, h]

/-- A machine cannot stop and later return to the running status. -/
private theorem running_of_later {w : Nat} (a b : Nat) (m : Machine w) (hab : a ≤ b)
    (hb : (run b m).status = .running) : (run a m).status = .running := by
  by_cases ha : (run a m).status = .running
  · exact ha
  · have hsplit : b = a + (b-a) := by omega
    have he : run b m = run a m := by
      rw [hsplit, run_add]
      exact run_stopped _ _ ha
    rw [he] at hb
    exact False.elim (ha hb)

/-- The budget is exact: no smaller number of instructions has reached exit or fault.
This rules out merely padding an earlier terminating run with unused fuel. -/
theorem running_before (n : Nat) (hn : n ≤ 2^30-1) (fuel : Nat)
    (ht : fuel < instructionCount n) : (run fuel (initial n)).status = .running := by
  exact running_of_later fuel (instructionCount n - 1) (initial n) (by omega)
    (correct_timed n hn).2.2

/-- Characterization of the exact first-exit instruction count. -/
theorem exited_iff_count_le (n : Nat) (hn : n ≤ 2^30-1) (fuel : Nat) :
    (run fuel (initial n)).status = .exited 0 ↔ instructionCount n ≤ fuel := by
  constructor
  · intro he
    by_cases ht : instructionCount n ≤ fuel
    · exact ht
    · have hr := running_before n hn fuel (by omega)
      rw [he] at hr
      contradiction
  · intro ht
    have hs := (correct_with_time n hn).1
    have hsplit : fuel = instructionCount n + (fuel-instructionCount n) := by omega
    rw [hsplit, run_add, run_stopped]
    · exact hs
    · rw [hs]
      decide

/-- A simple polynomial machine-instruction bound, valid for the entire supported domain. -/
theorem correct_bounded (n : Nat) (hn : n ≤ 2^30-1) :
    ∃ fuel, fuel ≤ 13+(n-1)*(9+5*n) ∧
      (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" :=
  ⟨instructionCount n, instructionCount_upper n, correct_with_time n hn⟩

/-- A concrete useful bound: every input at most 600 exits in fewer than 10,000 instructions. -/
theorem correct_under_10000 (n : Nat) (hn : n ≤ 600) :
    ∃ fuel, fuel < 10000 ∧ (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" :=
  ⟨instructionCount n, instructionCount_lt_10000 n hn, correct_with_time n (by omega)⟩

/-- A loose uniform finite bound for every supported RV32 input. -/
theorem correct_under_rv32_cap (n : Nat) (hn : n ≤ 2^30-1) :
    ∃ fuel, fuel < 2^63 ∧ (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" :=
  ⟨instructionCount n, instructionCount_rv32_cap n hn, correct_with_time n hn⟩

/-- Every supported RV32 input exits in fewer than `2^38` modeled instructions.
The dyadic overcount includes every candidate, not just primes, and does not
evaluate the instruction-count function at the maximum input. -/
theorem correct_under_rv32_dyadic_cap (n : Nat) (hn : n ≤ 2^30-1) :
    ∃ fuel, fuel < 2^38 ∧ (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" :=
  ⟨instructionCount n, instructionCount_rv32_dyadic_cap n hn, correct_with_time n hn⟩

/-- The literal dyadic instruction bound, uniformly for the complete valid input domain. -/
theorem correct_bounded_rv32_dyadic (n : Nat) (hn : n ≤ 2^30-1) :
    ∃ fuel, fuel ≤ 165356240746 ∧ (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" :=
  ⟨instructionCount n, instructionCount_rv32_dyadic_bound n hn, correct_with_time n hn⟩

/-- Ten thousand instructions is not a bound over all valid inputs: this valid input is
still running at that point. The proof uses the lower cost bound, not a long evaluated trace. -/
theorem still_running_10000 : (run 10000 (initial 2000)).status = .running := by
  apply running_before 2000 (by decide) 10000
  have h := instructionCount_lower 2000
  omega

/-- The original existential correctness API, now with a proved instruction budget. -/
theorem correct (n : Nat) (hn : n ≤ 2^30-1) :
    ∃ fuel, (run fuel (initial n)).status = .exited 0 ∧
      (run fuel (initial n)).output = toString (countPrimes n) ++ "\n" :=
  ⟨instructionCount n, correct_with_time n hn⟩

end TinyFive.CountingPrimesSieve
