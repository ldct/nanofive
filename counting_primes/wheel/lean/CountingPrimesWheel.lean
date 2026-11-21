import TinyFive.Machine
import TinyFive.Primes
import CountingPrimesSpec
import TinyFive.SieveMemory
import TinyFive.SieveMath
import TinyFive.TrialDivisionCost
import WheelMath

/-! A mod-30 candidate wheel on the actual RV64I machine. Flags retain the
full byte-array representation; marking visits every multiple. The immutable
11-byte gap table is protected together with the decoded instruction bytes.

`correct` gives exit code zero and output `π(n)` within `15 + 191*n` instructions for every
`n < 10^11`. Each visited candidate `p` costs at most `11 + 5*(n/p)` instructions (four to test
its flag, up to seven to step the wheel, and the marking loop for a prime). Charging that to
every integer from 2 to `n`, not only to wheel candidates, lets the shared dyadic bound
`TrialDivisionCost.quotientSum_le_dyadic` cover the quotients. -/
namespace TinyFive.CountingPrimesWheel
open CountingPrimes SieveMemory SieveMath WheelMath
open TrialDivisionCost (quotientSum quotientSum_succ quotientSum_append quotientSum_le_dyadic)

def prog : List (BitVec 32) := [
  0x00200293, 0x00000313, 0x00100f13, 0x10000f93, 0x00000593,
  0x00b00613, 0x04556463, 0x005f8e33, 0x000e4e83, 0x020e9063,
  0x00130313, 0x005283b3, 0x00756a63, 0x007f8e33, 0x01ee0023,
  0x005383b3, 0xff1ff06f, 0x08058e13, 0x000e4e83, 0x01d282b3,
  0x00158593, 0xfcc5e2e3, 0x00300593, 0xfbdff06f, 0x00030513,
  0x00100893, 0x00000073, 0x00a00513, 0x00b00893, 0x00000073,
  0x00a00893, 0x00000073, 0x04020201, 0x04020402, 0x00060206]

def initial (n : Nat) : Machine 64 :=
  (load 64 prog (256+n+1) []).setReg 10 (BitVec.ofNat 64 n)
def image : Array (BitVec 8) := (load 64 prog 256 []).mem

def code : List Instr := [
  .opImm .add 5 0 2, .opImm .add 6 0 0,
  .opImm .add 30 0 1, .opImm .add 31 0 256,
  .opImm .add 11 0 0, .opImm .add 12 0 11,
  .branch .bltu 10 5 72, .op .add 28 31 5, .load .byte false 29 28 0,
  .branch .bne 29 0 32, .opImm .add 6 6 1, .op .add 7 5 5,
  .branch .bltu 10 7 20, .op .add 28 31 7, .store .byte 30 28 0,
  .op .add 7 7 5, .jal 0 (-16),
  .opImm .add 28 11 128, .load .byte false 29 28 0,
  .op .add 5 5 29, .opImm .add 11 11 1,
  .branch .bltu 11 12 (-60), .opImm .add 11 0 3, .jal 0 (-68),
  .opImm .add 10 6 0, .opImm .add 17 0 1, .ecall,
  .opImm .add 10 0 10, .opImm .add 17 0 11, .ecall,
  .opImm .add 17 0 10, .ecall]

theorem fetch : ∀ pc, pc < 128 → pc % 4 = 0 →
    (readBytes image pc 4).bind (decode 64) = some (code.getD (pc/4) .ecall) := by
  decide +kernel

theorem step_image (x : Regs 64) (pc : BitVec 64) (mem : Array (BitVec 8))
    (out : String) (st : Status) (hmem : Prefix image mem 140)
    (h : pc.toNat < 128) (h4 : pc.toNat % 4 = 0) :
    step ⟨x, pc, mem, [], out, st⟩ =
      exec (code.getD (pc.toNat/4) .ecall) ⟨x, pc, mem, [], out, st⟩ := by
  apply step_of_prefix _ image 140 hmem (by change pc.toNat + 4 ≤ 140; omega)
  exact fetch _ h h4

macro "wheel_exec" : tactic =>
  `(tactic| simp [run, step_image, code, exec, Machine.setReg, Machine.advance,
      Machine.fail, alu, ecall, Width.bytes, Regs.get_set, BranchOp.taken, *])

def Inv (s : Nat) (x : Regs 64) (n p c : Nat) : Prop :=
  x.get 10 = BitVec.ofNat 64 n ∧ x.get 5 = BitVec.ofNat 64 p ∧
  x.get 6 = BitVec.ofNat 64 c ∧ x.get 30 = 1 ∧ x.get 31 = 256 ∧ x.get 11 = BitVec.ofNat 64 s ∧ x.get 12 = 11

variable {s : Nat}

private theorem nat_ult (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem nat_address (p : Nat) (hp : 256+p < 2^64) :
    (256#64 + BitVec.ofNat 64 p).toNat = 256+p := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem header_marked (n p c : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 140) (hi : Inv s x n p c)
    (hn : n < 2^64) (hp : 256+p < 2^64) (hpn : p ≤ n)
    (hread : readBytes mem (256+p) 1 = some 1#8) :
    ∃ x', Inv s x' n p c ∧
      run 4 ⟨x, 24, mem, [], out, .running⟩ = ⟨x', 68, mem, [], out, .running⟩ := by
  obtain ⟨h10, h5, h6, h30, h31, h11, h12⟩ := hi
  have hb : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 p) = false := by
    rw [nat_ult n p hn (by omega)]
    simp [show ¬ n < p by omega]
  have ha := nat_address p hp
  refine ⟨(x.set 28 (256 + BitVec.ofNat 64 p)).set 29 1, ?_, ?_⟩
  · simp [Inv, Regs.get_set, *]
  · wheel_exec

private theorem header_fresh (n p c : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 140) (hi : Inv s x n p c)
    (hn : n < 2^64) (hp : 256+p < 2^64) (hpn : p ≤ n)
    (hread : readBytes mem (256+p) 1 = some 0#8) :
    ∃ x', Inv s x' n p (c+1) ∧ x'.get 7 = BitVec.ofNat 64 (p+p) ∧
      run 6 ⟨x, 24, mem, [], out, .running⟩ = ⟨x', 48, mem, [], out, .running⟩ := by
  obtain ⟨h10, h5, h6, h30, h31, h11, h12⟩ := hi
  have hb : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 p) = false := by
    rw [nat_ult n p hn (by omega)]
    simp [show ¬ n < p by omega]
  have ha := nat_address p hp
  refine ⟨(((x.set 28 (256 + BitVec.ofNat 64 p)).set 29 0).set 6
    (BitVec.ofNat 64 c + 1)).set 7 (BitVec.ofNat 64 p + BitVec.ofNat 64 p), ?_, ?_, ?_⟩
  · simp [Inv, Regs.get_set, BitVec.ofNat_add, *]
  · simp [Regs.get_set, BitVec.ofNat_add]
  · wheel_exec

private theorem mark_done (n p c j : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 140) (hi : Inv s x n p c)
    (hj : x.get 7 = BitVec.ofNat 64 j) (hn64 : n < 2^64) (hj64 : j < 2^64)
    (hdone : n < j) :
    run 1 ⟨x, 48, mem, [], out, .running⟩ = ⟨x, 68, mem, [], out, .running⟩ := by
  have hb : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 j) = true := by
    rw [nat_ult n j hn64 hj64]
    simp [hdone]
  have h10 := hi.1
  wheel_exec

private theorem mark_step (n p c j : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Layout image 140 (256+n+1) mem) (hi : Inv s x n p c)
    (hj : x.get 7 = BitVec.ofNat 64 j) (hn64 : n < 2^64) (hjaddr : 256+j < 2^64)
    (hjn : j ≤ n) :
    ∃ x', Inv s x' n p c ∧ x'.get 7 = BitVec.ofNat 64 (j+p) ∧
      run 5 ⟨x, 48, mem, [], out, .running⟩ =
        ⟨x', 48, mem.setIfInBounds (256+j) 1#8, [], out, .running⟩ := by
  obtain ⟨h10, h5, h6, h30, h31, h11, h12⟩ := hi
  have hb : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 j) = false := by
    rw [nat_ult n j hn64 (by omega)]
    simp [show ¬ n < j by omega]
  have ha := nat_address j hjaddr
  have hcode := hmem.code_eq
  have hcode' := hmem.update (256+j) (1#8) (by omega) |>.code_eq
  have hwrite : writeBytes mem (256+j) (1#64) 1 =
      some (mem.setIfInBounds (256+j) 1#8) := by
    exact writeBytes_byte mem _ _ (by rw [hmem.size_eq]; omega)
  refine ⟨(((x.set 28 (256 + BitVec.ofNat 64 j)).set 7
    (BitVec.ofNat 64 j + BitVec.ofNat 64 p)).set 0 68), ?_, ?_, ?_⟩
  · simp [Inv, Regs.get_set, *]
  · simp [Regs.get_set, BitVec.ofNat_add]
  · wheel_exec

private theorem outer_done (n p c : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 140) (hi : Inv s x n p c)
    (hn64 : n < 2^64) (hp64 : p < 2^64) (hdone : n < p) :
    (run 9 ⟨x, 24, mem, [], out, .running⟩).status = .exited 0 ∧
    (run 9 ⟨x, 24, mem, [], out, .running⟩).output =
      out ++ toString (BitVec.ofNat 64 c).toInt ++ "\n" := by
  obtain ⟨h10, h5, h6, h30, h31, h11, h12⟩ := hi
  have hb : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 p) = true := by
    rw [nat_ult n p hn64 hp64]
    simp [hdone]
  wheel_exec
  rfl

def Flags (mem : Array (BitVec 8)) (n : Nat) (P : Nat → Prop) [DecidablePred P] : Prop :=
  ∀ k, 2 ≤ k → k ≤ n → readBytes mem (256+k) 1 = some (if P k then 1#8 else 0#8)

/-- A real byte store advances the arithmetic inner-loop invariant. -/
private theorem flags_update (n p j : Nat) (mem : Array (BitVec 8))
    (hmem : Layout image 140 (256+n+1) mem) (hp : 0 < p) (hpj : p < j)
    (hj : p ∣ j) (hjn : j ≤ n) (hf : Flags mem n (InProgress p j)) :
    Flags (mem.setIfInBounds (256+j) 1#8) n (InProgress p (j+p)) := by
  intro k hk hkn
  by_cases he : k = j
  · subst k
    rw [read_update_same mem (256+j) (1#8) (by rw [hmem.size_eq]; omega)]
    have hm : InProgress p (j+p) j := (progress_step p j j hp hpj hj).mpr (Or.inr rfl)
    simp [hm]
  · rw [read_update_other mem (256+j) (256+k) (1#8) (by omega), hf k hk hkn]
    have heq : InProgress p (j+p) k ↔ InProgress p j k := by
      rw [progress_step p j k hp hpj hj]
      simp [he]
    simp only [heq]

/-- Termination and complete byte-memory correctness of the marking loop. -/
private theorem mark_correct (n p c j : Nat) (hn : n < 10^11) (hp : 2 ≤ p)
    (hpn : p ≤ n) (hjmin : p+p ≤ j) (hjmax : j ≤ n+p) (hdiv : p ∣ j)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hi : Inv s x n p c) (hj : x.get 7 = BitVec.ofNat 64 j)
    (hmem : Layout image 140 (256+n+1) mem) (hf : Flags mem n (InProgress p j)) :
    ∃ fuel x' mem', fuel + 5*(j/p) ≤ 6 + 5*(n/p) ∧
      Inv s x' n p c ∧ Layout image 140 (256+n+1) mem' ∧
      Flags mem' n (Marked (p+1)) ∧
      run fuel ⟨x, 48, mem, [], out, .running⟩ = ⟨x', 68, mem', [], out, .running⟩ := by
  by_cases hdone : n < j
  · have hq : j/p ≤ n/p + 1 := by
      have := Nat.div_le_div_right (c := p) hjmax
      rwa [Nat.add_div_right n (by omega)] at this
    refine ⟨1, x, mem, by omega, hi, hmem, ?_, ?_⟩
    · intro k hk hkn
      have hiff := progress_done p j k hp (show k < j by omega)
      simpa only [hiff] using hf k hk hkn
    · exact mark_done n p c j x mem out hmem.code_eq hi hj (by omega) (by omega) hdone
  · have hjn : j ≤ n := by omega
    obtain ⟨y, hy, hyj, hs⟩ := mark_step n p c j x mem out hmem hi hj
      (by omega) (by omega) hjn
    have hl := hmem.update (256+j) (1#8) (by omega)
    have hg := flags_update n p j mem hmem (by omega) (by omega) hdiv hjn hf
    obtain ⟨fuel, z, mem', hfuel, hz, hm, hf', ht⟩ :=
      mark_correct n p c (j+p) hn hp hpn (by omega) (by omega)
        (Nat.dvd_add hdiv (Nat.dvd_refl p)) y (mem.setIfInBounds (256+j) 1#8) out hy hyj hl hg
    have hq : (j+p)/p = j/p + 1 := Nat.add_div_right j (by omega)
    refine ⟨5+fuel, z, mem', by omega, hz, hm, hf', ?_⟩
    rw [run_add, hs, ht]
termination_by n+1-j

private theorem countPrimes_step (p : Nat) (hp : 0 < p) :
    countPrimes p = countPrimes (p-1) + if Prime p then 1 else 0 := by
  cases p with
  | zero => omega
  | succ p => rfl

private theorem candidate_correct (n p : Nat) (hn : n < 10^11) (hp : 2 ≤ p)
    (hpn : p ≤ n) (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hi : Inv s x n p (countPrimes (p-1)))
    (hmem : Layout image 140 (256+n+1) mem) (hf : Flags mem n (Marked p)) :
    ∃ fuel y mem', fuel ≤ 4 + 5*(n/p) ∧
      Inv s y n p (countPrimes p) ∧ Layout image 140 (256+n+1) mem' ∧
      Flags mem' n (Marked (p+1)) ∧
      run fuel ⟨x, 24, mem, [], out, .running⟩ =
        ⟨y, 68, mem', [], out, .running⟩ := by
  by_cases hm : Marked p p
  · have hnp := (marked_self_iff_not_prime p hp).mp hm
    have hc : countPrimes p = countPrimes (p-1) := by
      simp [countPrimes_step p (by omega), hnp]
    have hread : readBytes mem (256+p) 1 = some 1#8 := by
      simpa only [ite_eq_left hm] using hf p hp hpn
    obtain ⟨y, hy, hs⟩ := header_marked n p (countPrimes (p-1)) x mem out hmem.code_eq
      hi (by omega) (by omega) hpn hread
    refine ⟨4, y, mem, by omega, ?_, hmem, ?_, ?_⟩
    · simpa only [hc] using hy
    · intro k hk hkn
      simpa only [composite_skip p k hm] using hf k hk hkn
    · exact hs
  · have hprime : Prime p := by
      by_cases h : Prime p
      · exact h
      · exact False.elim (hm ((marked_self_iff_not_prime p hp).mpr h))
    have hc : countPrimes p = countPrimes (p-1) + 1 := by
      simp [countPrimes_step p (by omega), hprime]
    have hread : readBytes mem (256+p) 1 = some 0#8 := by
      simpa only [ite_eq_right hm] using hf p hp hpn
    obtain ⟨y, hy, hyj, hs⟩ := header_fresh n p (countPrimes (p-1)) x mem out hmem.code_eq
      hi (by omega) (by omega) hpn hread
    have hy' : Inv s y n p (countPrimes p) := by simpa only [hc] using hy
    have hfstart : Flags mem n (InProgress p (p+p)) := by
      intro k hk hkn
      simpa only [progress_start] using hf k hk hkn
    obtain ⟨fuel, z, mem', hfuel, hz, hl, hg, ht⟩ := mark_correct n p (countPrimes p) (p+p)
      hn hp hpn (by omega) (by omega) (Nat.dvd_add (Nat.dvd_refl p) (Nat.dvd_refl p))
      y mem out hy' hyj hmem hfstart
    have hq : (p+p)/p = 2 := by
      rw [Nat.add_div_right p (by omega), Nat.div_self (by omega)]
    refine ⟨6+fuel, z, mem', by omega, hz, hl, hg, ?_⟩
    rw [run_add, hs, ht]

/-- Every gap byte is read from the loaded, protected machine image. -/
theorem table_read : ∀ s, s < 11 →
    readBytes image (128+s) 1 = some (BitVec.ofNat 8 (gap s)) := by
  decide +kernel

private theorem outer_next (n p c : Nat) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (hmem : Prefix image mem 140) (hi : Inv s x n p c)
    (hs : s < 11) :
    ∃ fuel x', fuel ≤ 7 ∧ Inv (nextPhase s) x' n (p+gap s) c ∧
      run fuel ⟨x, 68, mem, [], out, .running⟩ = ⟨x', 24, mem, [], out, .running⟩ := by
  obtain ⟨h10, h5, h6, h30, h31, h11, h12⟩ := hi
  have hr : readBytes mem (128+s) 1 = some (BitVec.ofNat 8 (gap s)) := by
    rw [readBytes_prefix hmem _ _ (by omega)]
    exact table_read s hs
  have ha : (BitVec.ofNat 64 s + 128).toNat = 128+s := by
    change (s % 18446744073709551616 + 128) % 18446744073709551616 = 128+s
    omega
  have hr' : mem[(s+128)%18446744073709551616]? = some (BitVec.ofNat 8 (gap s)) := by
    simpa [Nat.mod_eq_of_lt (show s+128<18446744073709551616 by omega), Nat.add_comm] using hr
  by_cases hlt : s+1 < 11
  · have hb : (BitVec.ofNat 64 s + 1).ult 11 = true := by
      change (BitVec.ofNat 64 s + BitVec.ofNat 64 1).ult (BitVec.ofNat 64 11) = true
      rw [← BitVec.ofNat_add]
      change (BitVec.ofNat 64 (s+1)).ult (BitVec.ofNat 64 11) = true
      rw [nat_ult (s+1) 11 (by omega) (by omega)]
      simp [hlt]
    have hg : (BitVec.ofNat 8 (gap s)).setWidth 64 = BitVec.ofNat 64 (gap s) := by
      have : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 ∨ s = 10 := by omega
      rcases this with h|h|h|h|h|h|h|h|h|h|h <;> subst s <;> decide
    refine ⟨5, (((x.set 28 (BitVec.ofNat 64 s + 128)).set 29
      (BitVec.ofNat 64 (gap s))).set 5 (BitVec.ofNat 64 p + BitVec.ofNat 64 (gap s))).set 11
      (BitVec.ofNat 64 s + 1), by omega, ?_, ?_⟩
    · simp [Inv, Regs.get_set, nextPhase, BitVec.ofNat_add, *]
    · wheel_exec
      exact hb
  · have he : s = 10 := by omega
    subst s
    refine ⟨7, (((((x.set 28 138).set 29 6).set 5
      (BitVec.ofNat 64 p + 6)).set 11 11).set 11 3).set 0 96, by omega, ?_, ?_⟩
    · simp [Inv, Regs.get_set, nextPhase, gap, BitVec.ofNat_add, *]
    · simp only [gap] at hr hr'
      wheel_exec

private theorem toInt_nat (c : Nat) (hc : c < 2^63) :
    (BitVec.ofNat 64 c).toInt = (c : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have h64 : c < 2^64 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, show 2*c < 2^64 by omega]

private theorem nat_int_string (c : Nat) : toString (c : Int) = toString c := rfl

theorem initial_layout (n : Nat) : Layout image 140 (256+n+1) (initial n).mem := by
  exact load_layout_boundary 64 prog 140 256 (256+n+1) [] []
    (by decide) (by decide) (by omega)

/-- Flags start clear because of the actual machine loader, not an abstract sieve assumption. -/
theorem initial_flags (n : Nat) : Flags (initial n).mem n (Marked 2) := by
  intro k hk hkn
  have hz : (initial n).mem[256+k]? = some (0#8) := by
    apply load_mem_zero 64 prog (256+n+1) [] (256+k)
    · change 140 ≤ 256+k
      omega
    · omega
  simpa only [readBytes_byte, ite_eq_right (marked_two k)] using hz

private theorem initialize_regs (n : Nat) :
    ∃ x, Inv 0 x n 2 0 ∧ run 6 (initial n) =
      ⟨x, 24, (initial n).mem, [], "", .running⟩ := by
  let x : Regs 64 := (⟨Vector.replicate 32 0⟩ : Regs 64).set 10 (BitVec.ofNat 64 n)
  let mem := (load 64 prog (256+n+1) []).mem
  have hi : initial n = ⟨x, 0, mem, [], "", .running⟩ := rfl
  have hmem : Prefix image mem 140 := (initial_layout n).code_eq
  change ∃ y, Inv 0 y n 2 0 ∧ run 6 (initial n) = ⟨y, 24, mem, [], "", .running⟩
  rw [hi]
  refine ⟨(((((x.set 5 2).set 6 0).set 30 1).set 31 256).set 11 0).set 12 11, ?_, ?_⟩
  · simp [Inv, x, Regs.get_set]
  · wheel_exec

/-- The outer invariant is clipped to the input to account for the final wheel gap. -/
private theorem outer_correct (n p s : Nat) (hn : n < 10^11)
    (hphase : Phase p s) (hpn : p ≤ n+6)
    (x : Regs 64) (mem : Array (BitVec 8)) (out : String)
    (hi : Inv s x n p (countPrimes (min n (p-1))))
    (hmem : Layout image 140 (256+n+1) mem) (hf : Flags mem n (Marked p)) :
    ∃ fuel, fuel ≤ 9 + 11*(n+1-p) + 5*quotientSum n p (n+1-p) ∧
      (run fuel ⟨x, 24, mem, [], out, .running⟩).status = .exited 0 ∧
      (run fuel ⟨x, 24, mem, [], out, .running⟩).output =
        out ++ toString (countPrimes n) ++ "\n" := by
  have hp := (phase_bounds p s hphase).2
  by_cases hdone : n < p
  · have he : min n (p-1) = n := Nat.min_eq_left (by omega)
    have hc : countPrimes n < 2^63 := by have := countPrimes_le n; omega
    have hd := outer_done n p (countPrimes (min n (p-1))) x mem out hmem.code_eq hi
      (by omega) (by omega) hdone
    refine ⟨9, by omega, hd.1, ?_⟩
    simpa only [he, toInt_nat _ hc, nat_int_string] using hd.2
  · have hple : p ≤ n := by omega
    have he : min n (p-1) = p-1 := Nat.min_eq_right (by omega)
    have hi' : Inv s x n p (countPrimes (p-1)) := by simpa only [he] using hi
    obtain ⟨a, y, mem', ha, hy, hl, hg, hs⟩ :=
      candidate_correct n p hn hp hple x mem out hi' hmem hf
    obtain ⟨b, z, hb, hz, ht⟩ := outer_next n p (countPrimes p) y mem' out hl.code_eq hy
      (phase_bounds p s hphase).1
    have hgap := gap_bounds p s hphase
    have hz' : Inv (nextPhase s) z n (p+gap s)
        (countPrimes (min n (p+gap s-1))) := by
      rw [countPrimes_gap n p s hphase hple]
      exact hz
    have hg' : Flags mem' n (Marked (p+gap s)) := by
      intro k hk hkn
      simpa only [skipped_marked p s k hphase] using hg k hk hkn
    obtain ⟨c, hcb, hc, ho⟩ := outer_correct n (p+gap s) (nextPhase s) hn
      (phase_step p s hphase) (by omega) z mem' out hz' hl hg'
    -- The integers skipped between wheel candidates only add to the quotient sum.
    have hskip : quotientSum n (p+gap s) (n+1-(p+gap s)) ≤ quotientSum n (p+1) (n-p) := by
      by_cases hfit : p + gap s ≤ n+1
      · have hlen : n-p = (gap s - 1) + (n+1-(p+gap s)) := by omega
        rw [hlen, quotientSum_append, show p+1+(gap s - 1) = p+gap s by omega]
        omega
      · rw [show n+1-(p+gap s) = 0 by omega]
        simp
    have hhead : quotientSum n p (n+1-p) = n/p + quotientSum n (p+1) (n-p) := by
      rw [show n+1-p = (n-p)+1 by omega, quotientSum_succ]
    refine ⟨(a+b)+c, by omega, ?_, ?_⟩
    · simpa only [run_add (a+b) c, run_add a b, hs, ht] using hc
    · simpa only [run_add (a+b) c, run_add a b, hs, ht] using ho
termination_by n+1-p

/-- **Correctness with an instruction budget.** For every input below `10^11`, the loaded
RV64I program exits with code zero after printing `π(n)` and a newline, within
`15 + 191*n` modeled instructions. The proof includes instruction decoding, actual flag-byte
stores and table-byte loads. -/
theorem correct (n : Nat) (hn : n < 10^11) :
    ∃ fuel, fuel ≤ 15+191*n ∧
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n") := by
  obtain ⟨x, hx, hs⟩ := initialize_regs n
  have hcount : countPrimes (min n (2-1)) = 0 := by
    have hsmall : min n (2-1) = 0 ∨ min n (2-1) = 1 := by omega
    obtain h | h := hsmall <;> rw [h] <;> rfl
  have hi : Inv 0 x n 2 (countPrimes (min n (2-1))) := by
    simpa only [hcount] using hx
  obtain ⟨fuel, hb, he, ho⟩ := outer_correct n 2 0 hn phase_initial (by omega)
    x (initial n).mem "" hi (initial_layout n) (initial_flags n)
  have hq := quotientSum_le_dyadic n 36 (n+1-2) (by omega)
  refine ⟨6+fuel, by omega, ?_, ?_⟩
  · simpa only [run_add, hs] using he
  · simpa only [run_add, hs, String.empty_append] using ho

/-- One fuel value works for every input below `10^11`. -/
theorem correct_uniform_fuel :
    ∃ fuel, ∀ n < 10^11,
      is_exited_with_output (run fuel (initial n)) (toString (countPrimes n) ++ "\n") := by
  refine ⟨15+191*10^11, fun n hn => ?_⟩
  obtain ⟨fuel, hb, h⟩ := correct n hn
  exact is_exited_with_output_mono (by omega) h

/-- **Correctness with program size.** With memory for the flags of every input below `10^11`, the
loaded program satisfies `IsCorrect`, and its memory holds only 106 nonzero bytes. Zero padding
is free, so the size bound rules out lookup tables. -/
theorem correct_with_size : ∃ m, IsCorrect m ∧ programSize m = 106 := by
  refine ⟨load 64 prog (256+10^11) [], ?_, ?_⟩
  · exact isCorrect_of_load prog (fun n => 256+n+1) (256+10^11)
      (fun _ _ => by have : 4 * prog.length ≤ 256 := (by decide); omega)
      (fun _ hn => by omega)
      correct_uniform_fuel
  · rw [programSize_load prog 256 (256+10^11) (by decide) (by omega)]
    decide +kernel

end TinyFive.CountingPrimesWheel
