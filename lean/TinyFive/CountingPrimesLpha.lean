import Lean
import TinyFive.Lemmas
import TinyFive.CountingPrimesLpha.Code

/-!
# Correctness of `counting_primes_lpha.py` (in progress)

`counting_primes_lpha.py` is a Library Checker "Counting Primes" submission compiled to 1261
words of RV32IM code: `_start`, `main` (read `N`, call `prime_count`, print the result),
`prime_count` (Lucy/min_25 prime counting), `memset`, and libgcc's 64-bit division. This file
proves it correct on the machine model of `TinyFive.Machine`, in the style of
`TinyFive.Abc101a`, except for `prime_count` itself.

## What is proven

`correct`: on an input made of some non-digits, then the decimal digits of a number
`N ≤ 10^11`, then anything that does not start with a digit, the machine loaded with `prog`
reaches, after some number of steps, a state that has exited with code 0 and has printed
`π(N) mod 2^32` followed by a newline. `correct'` drops the `mod 2^32`.

The input condition is what `read_u64` needs: it skips non-digits until the first digit (and
loops forever at the end of an input with no digit), then reads digits until a non-digit or the
end of the input.

## What is not proven yet

Two statements are `sorry`:

* `prime_count_spec`: the machine code of `prime_count` (address 48), entered from `main`,
  returns to `main` with `π(N)` in `a0`, `sp` restored, the image intact and `main`'s frame
  untouched. This covers `memset`, `__udivdi3` and the Lucy/min_25 loops, and with them the
  mathematics that the algorithm counts primes (which needs, among other things, Bertrand's
  postulate: the first loop over `roughs` breaks before running off the end of the array
  because some prime lies in `(√N / p, √N]`).
* `primeCount_lt`: `π(10^11) < 2^32`. Only `correct'` uses it.

## Proof structure

1. `Code.lean` holds `prog` and its decoding `code`, with `decode_prog` checked by the kernel.
   `ImageOK` says memory holds the image; `step_code` turns it into a rewrite rule for one
   step. The simproc `reduceInstrAt` looks up an instruction by address.
2. `sym_exec` runs a machine forward by simplification, as in `Abc101a`. It is used on blocks
   of at most about 15 instructions, because unfolding `run` costs time quadratic in the number
   of steps. Loads and stores at an address computed from a register go through `step_load`
   and `step_store`, because letting `simp` rewrite the address inside the `match` on
   `readBytes`/`writeBytes` produces proofs that the kernel takes minutes to reject.
3. `main` before the call: `main_entry`, `skip_loop` and `digit_loop` (induction on the
   skipped characters and on the digits), combined in `read_number`.
4. `main` after the call: the digit loop of `print_u64` divides by 10 with `remu 5` and a
   multiplication by the inverse of 5 (`div10_lo`, `div10_hi`); `digits_store` (strong
   induction on `n`) stores the digits in `buf`, `print_loop` prints them back, and
   `print_tail` returns from `main` into `exit(0)`. `print_all` combines them and relates the
   printed characters to `toString` through `revDigits`.
5. `correct` chains `start`, `read_number`, `prime_count_spec` and `print_all`.

The three `bv_decide` calls in `digit_step` and `digit_step_eof` (the 64-bit `n * 10 + d` done
with 32-bit register pairs) rely on `Lean.ofReduceBool`, unlike the rest of the proof.

What is not proven here is that `prog` is the list of the same name in
`counting_primes_lpha.py`; `counting_primes_lpha_lean_test.py` checks that.
-/

namespace TinyFive.CountingPrimesLpha

set_option maxRecDepth 100000

/-- The memory size `counting_primes_lpha.py` runs with. -/
abbrev memSize : Nat := 0x400000

/-- Memory holds the image from address 0 and has its full size. -/
structure ImageOK (mem : Array (BitVec 8)) : Prop where
  size : mem.size = memSize
  words : WordsAt mem 0 prog

set_option maxRecDepth 100000 in
theorem prog_length : prog.length = 1340 := by decide +kernel

set_option maxRecDepth 100000 in
theorem code_length : code.length = 1261 := by decide +kernel

theorem decode_code (k : Nat) (hk : k < 1261) :
    decode 32 (prog[k]'(by rw [prog_length]; omega)) = some (code.getD k .ecall) := by
  have e := congrArg (·[k]?) decode_prog
  simp only [List.getElem?_map, List.getElem?_take, show k < codeWords from hk, ite_true] at e
  rw [List.getElem?_eq_getElem (by rw [prog_length]; omega),
    List.getElem?_eq_getElem (by rw [code_length]; omega)] at e
  simp only [Option.map_some, Option.some.injEq] at e
  rw [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [code_length]; omega)]
  rfl

theorem fetch {mem : Array (BitVec 8)} (h : ImageOK mem) (k : Nat) (hk : k < 1261) :
    (readBytes mem (4 * k) 4).bind (decode 32) = some (code.getD k .ecall) := by
  have := h.words.read k (by rw [prog_length]; omega)
  rw [Nat.zero_add] at this
  rw [this, Option.bind_some, decode_code k hk]

/-- The instruction at word `k` of the image. -/
def instrAt (k : Nat) : Instr := code.getD k .ecall

theorem step_code {mem : Array (BitVec 8)} (h : ImageOK mem) (x : Regs 32) (pc : BitVec 32)
    (inp : List Char) (out : String) (st : Status) (hpc : pc.toNat < 4 * 1261)
    (h4 : pc.toNat % 4 = 0) :
    step ⟨x, pc, mem, inp, out, st⟩ =
      exec (instrAt (pc.toNat / 4)) ⟨x, pc, mem, inp, out, st⟩ := by
  have e : pc.toNat = 4 * (pc.toNat / 4) := by omega
  simp only [step]
  rw [e, fetch h _ (by omega)]
  rw [← e]
  rfl

/-! ## Reading characters -/

theorem toNat_lt32 (c : Char) : c.toNat < 4294967296 := c.val.toNat_lt

theorem isDigit_iff' (c : Char) : c.isDigit ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  rw [Char.isDigit_iff_toNat]; rfl

/-- The test `a0 - '0' ≤ 9` (unsigned) that the program uses for a digit. -/
theorem digit_cond (c : Char) :
    (9#32).ult (BitVec.ofNat 32 c.toNat + 4294967248#32) = !c.isDigit := by
  have h1 := toNat_lt32 c
  have e := isDigit_iff' c
  rw [Bool.eq_iff_iff, Bool.not_eq_true', ← Bool.not_eq_true, e, BitVec.ult, decide_eq_true_iff,
    BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

theorem digit_val (c : Char) (h : c.isDigit) :
    BitVec.ofNat 32 c.toNat + 4294967248#32 = BitVec.ofNat 32 (c.toNat - 48) := by
  have h1 := toNat_lt32 c
  have e := (isDigit_iff' c).1 h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

theorem digit_le (c : Char) (h : c.isDigit) :
    (9#32).ult (BitVec.ofNat 32 (c.toNat - 48)) = false := by
  rw [← digit_val c h, digit_cond, h]; rfl

/-- At the end of the input, `read_char` gives `-1`, which is not a digit. -/
theorem eof_cond : (9#32).ult (4294967295#32 + 4294967248#32) = true := by decide

open Lean Meta Simp in
/-- Look up entry `n` of `code` for a literal `n`, without unfolding the whole list in `simp`. -/
simproc reduceInstrAt (instrAt _) := fun e => do
  unless e.isAppOfArity ``instrAt 1 do return .continue
  let some _ ← getNatValue? e.appArg! | return .continue
  let r ← withTransparency .all <| whnf e
  unless r.getAppFn.isConst && r.getAppFn.constName!.getPrefix == ``Instr do return .continue
  return .done { expr := r }

/-- Symbolic execution: run a machine whose state is given explicitly, with concrete `pc`. -/
theorem mulAlu_mul (a b : BitVec 32) : mulAlu .mul a b = a * b := rfl

theorem mulAlu_mulhu (a b : BitVec 32) :
    mulAlu .mulhu a b = ((a.setWidth 64 * b.setWidth 64) >>> 32).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  have hab := Nat.mul_lt_mul'' ha hb
  simp only [mulAlu, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    Nat.mod_eq_of_lt (a := a.toNat * b.toNat) (by omega)]

theorem mulAlu_divu (a b : BitVec 32) : mulAlu .divu a b = if b = 0 then -1 else a / b := rfl

theorem mulAlu_remu (a b : BitVec 32) : mulAlu .remu a b = if b = 0 then a else a % b := rfl

theorem ult_self' {w : Nat} (a : BitVec w) : a.ult a = false := by
  simp [BitVec.ult]

macro "sym_exec" : tactic =>
  `(tactic| simp [run, step_code, reduceInstrAt, exec, Machine.setReg, Machine.advance,
      Machine.fail, alu, mulAlu_mul, mulAlu_mulhu, mulAlu_divu, mulAlu_remu, ecall, Regs.get_set, BranchOp.taken, Width.bytes, digit_cond,
      digit_val, digit_le, eof_cond, ult_self', -BitVec.toNat_add, *])

macro "sym_exec" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [run, step_code, reduceInstrAt, exec, Machine.setReg, Machine.advance,
      Machine.fail, alu, mulAlu_mul, mulAlu_mulhu, mulAlu_divu, mulAlu_remu, ecall, Regs.get_set, BranchOp.taken, Width.bytes, digit_cond,
      digit_val, digit_le, eof_cond, ult_self', -BitVec.toNat_add, $ts,*, *])

/-- `_start`: set up the stack and call `main`. -/
theorem start (input : List Char) :
    ∃ x : Regs 32, x.get 2 = 0x400000 ∧ x.get 1 = 8 ∧
      run 2 (load 32 prog memSize input) = ⟨x, 2472, (load 32 prog memSize input).mem, input, "", .running⟩ := by
  have hm : ImageOK (load 32 prog memSize input).mem :=
    ⟨load_size _ _ _ _ (by rw [prog_length]; decide), load_wordsAt _ _ _ _⟩
  generalize hmem : (load 32 prog memSize input).mem = mem at hm
  have : load 32 prog memSize input = ⟨⟨Vector.replicate 32 0⟩, 0, mem, input, "", .running⟩ := by
    rw [← hmem]; rfl
  rw [this]
  sym_exec

/-! ## `main` -/

theorem ImageOK.write {mem mem' : Array (BitVec 8)} {k a n : Nat} {v : BitVec k} (h : ImageOK mem)
    (hw : writeBytes mem a v n = some mem') (ha : 4 * 1340 ≤ a) : ImageOK mem' where
  size := (writeBytes_size hw).trans h.size
  words k hk j hj := by
    rw [writeBytes_frame hw _ (by rw [prog_length] at hk; omega)]
    exact h.words k hk j hj

/-- The prologue of `main` and its first `read_char`. -/
theorem main_entry (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (c : Char)
    (rest : List Char) (hsp : x.get 2 = 0x400000) :
    ∃ mem', ImageOK mem' ∧ readBytes mem' 0x3ffffc 4 = some (x.get 1) ∧ ∃ x' : Regs 32,
      run 7 ⟨x, 2472, mem, c :: rest, "", .running⟩ =
        ⟨x', if c.isDigit then 2516 else 2500, mem', rest, "", .running⟩ ∧
      x'.get 2 = 0x3fffd0 ∧ x'.get 15 = 9 ∧ (c.isDigit → x'.get 10 = BitVec.ofNat 32 (c.toNat - 48)) := by
  obtain ⟨mem', hw⟩ := writeBytes_isSome (mem := mem) (addr := 0x3ffffc) (n := 4) (x.get 1)
    (by rw [hm.size]; decide)
  have hm' := hm.write hw (by decide)
  have hr : readBytes mem' 0x3ffffc 4 = some (x.get 1) :=
    readBytes_four fun k hk => by simpa using writeBytes_written hw k hk
  refine ⟨mem', hm', hr, ?_⟩
  cases hd : c.isDigit <;> sym_exec

/-- One trip round the loop that skips what precedes the number. -/
theorem skip_step (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (c : Char)
    (rest : List Char) (out : String) (h9 : x.get 15 = 9) :
    ∃ x' : Regs 32,
      run 4 ⟨x, 2500, mem, c :: rest, out, .running⟩ =
        ⟨x', if c.isDigit then 2516 else 2500, mem, rest, out, .running⟩ ∧
      x'.get 2 = x.get 2 ∧ x'.get 15 = 9 ∧ (c.isDigit → x'.get 10 = BitVec.ofNat 32 (c.toNat - 48)) := by
  cases hd : c.isDigit <;> sym_exec

/-- One trip round the loop that reads the digits. -/
theorem digit_step (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (c : Char)
    (rest : List Char) (out : String) (h9 : x.get 16 = 9) (hd0 : (x.get 10).toNat < 10) :
    ∃ x' : Regs 32,
      run 21 ⟨x, 2528, mem, c :: rest, out, .running⟩ =
        ⟨x', if c.isDigit then 2528 else 2612, mem, rest, out, .running⟩ ∧
      x'.get 2 = x.get 2 ∧ x'.get 16 = 9 ∧ (c.isDigit → x'.get 10 = BitVec.ofNat 32 (c.toNat - 48)) ∧
      x'.get 11 ++ x'.get 15 = (x.get 11 ++ x.get 15) * 10 + (x.get 10).setWidth 64 := by
  have hd0 : (x.get 10).ult 10 := by simp [BitVec.ult, hd0]
  cases hd : c.isDigit <;> sym_exec <;>
  · generalize x.get 10 = a at *
    generalize x.get 11 = b at *
    generalize x.get 15 = l at *
    bv_decide

/-- The last trip round the digit loop, at the end of the input. -/
theorem digit_step_eof (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (out : String)
    (h9 : x.get 16 = 9) (hd0 : (x.get 10).toNat < 10) :
    ∃ x' : Regs 32,
      run 21 ⟨x, 2528, mem, [], out, .running⟩ = ⟨x', 2612, mem, [], out, .running⟩ ∧
      x'.get 2 = x.get 2 ∧
      x'.get 11 ++ x'.get 15 = (x.get 11 ++ x.get 15) * 10 + (x.get 10).setWidth 64 := by
  have hd0 : (x.get 10).ult 10 := by simp [BitVec.ult, hd0]
  sym_exec
  generalize x.get 10 = a at *
  generalize x.get 11 = b at *
  generalize x.get 15 = l at *
  bv_decide

/-- The value of a string of decimal digits. -/
def digitsValue (ds : List Char) : Nat := ds.foldl (fun n c => 10 * n + (c.toNat - 48)) 0

theorem mul10_add (v : BitVec 64) (acc d : Nat) (hv : v = BitVec.ofNat 64 acc) :
    v * 10 + (BitVec.ofNat 32 d).setWidth 64 = BitVec.ofNat 64 (10 * acc + d % 2 ^ 32) := by
  subst hv
  have h10 : (10 : BitVec 64).toNat = 10 := rfl
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, h10]
  omega

/-- The loop that reads the digits, from the state where `a0` holds digit `d` and the pair
`a1:a5` holds the value `acc` of the digits before it. -/
theorem digit_loop (ds post : List Char) (hds : ∀ c ∈ ds, c.isDigit)
    (hpost : ∀ c ∈ post.head?, c.isDigit = false) (x : Regs 32) (mem : Array (BitVec 8))
    (hm : ImageOK mem) (out : String) (acc d : Nat) (hd : d < 10) (h9 : x.get 16 = 9)
    (ha0 : x.get 10 = BitVec.ofNat 32 d) (hacc : x.get 11 ++ x.get 15 = BitVec.ofNat 64 acc) :
    ∃ n, ∃ x' : Regs 32,
      run n ⟨x, 2528, mem, ds ++ post, out, .running⟩ = ⟨x', 2612, mem, post.drop 1, out, .running⟩ ∧
      x'.get 2 = x.get 2 ∧
      x'.get 11 ++ x'.get 15 =
        BitVec.ofNat 64 (ds.foldl (fun n c => 10 * n + (c.toNat - 48)) (10 * acc + d)) := by
  have hd0 : (x.get 10).toNat < 10 := by simp [ha0]; omega
  have hd32 : d % 2 ^ 32 = d := Nat.mod_eq_of_lt (by omega)
  induction ds generalizing x acc d with
  | nil =>
    cases post with
    | nil =>
      obtain ⟨x', hrun, h2, hv⟩ := digit_step_eof x mem hm out h9 hd0
      exact ⟨21, x', hrun, h2, by rw [hv, ha0, mul10_add _ acc d hacc, hd32]; rfl⟩
    | cons c rest =>
      have hc : c.isDigit = false := hpost c (by simp)
      obtain ⟨x', hrun, h2, -, -, hv⟩ := digit_step x mem hm c rest out h9 hd0
      simp only [hc, Bool.false_eq_true, ite_false] at hrun
      exact ⟨21, x', hrun, h2, by rw [hv, ha0, mul10_add _ acc d hacc, hd32]; rfl⟩
  | cons c ds ih =>
    have hc : c.isDigit = true := hds c (by simp)
    obtain ⟨x', hrun, h2, h9', hd', hv⟩ := digit_step x mem hm c (ds ++ post) out h9 hd0
    simp only [hc, ite_true] at hrun
    have hcd := (isDigit_iff' c).1 hc
    obtain ⟨n, x'', hrun', h2', hv'⟩ := ih (fun c h => hds c (by simp [h])) x'
      (10 * acc + d) (c.toNat - 48) (by omega) h9' (hd' hc)
      (by rw [hv, ha0, mul10_add _ acc d hacc, hd32]) (by simp [hd' hc]; omega)
      (Nat.mod_eq_of_lt (by omega))
    refine ⟨21 + n, x'', ?_, h2'.trans h2, ?_⟩
    · rw [run_add, List.cons_append, hrun, hrun']
    · rw [hv']; rfl

/-- The loop that skips what precedes the number, from its head to the first digit. -/
theorem skip_loop (pre : List Char) (hpre : ∀ c ∈ pre, c.isDigit = false) (d : Char)
    (hd : d.isDigit) (rest : List Char) (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem)
    (out : String) (h9 : x.get 15 = 9) :
    ∃ n, ∃ x' : Regs 32,
      run n ⟨x, 2500, mem, pre ++ d :: rest, out, .running⟩ = ⟨x', 2516, mem, rest, out, .running⟩ ∧
      x'.get 2 = x.get 2 ∧ x'.get 10 = BitVec.ofNat 32 (d.toNat - 48) := by
  induction pre generalizing x with
  | nil =>
    obtain ⟨x', hrun, h2, -, h10⟩ := skip_step x mem hm d rest out h9
    simp only [hd, ite_true] at hrun
    exact ⟨4, x', hrun, h2, h10 hd⟩
  | cons c pre ih =>
    have hc : c.isDigit = false := hpre c (by simp)
    obtain ⟨x', hrun, h2, h9', -⟩ := skip_step x mem hm c (pre ++ d :: rest) out h9
    simp only [hc, Bool.false_eq_true, ite_false] at hrun
    obtain ⟨n, x'', hrun', h2', h10⟩ := ih (fun c h => hpre c (by simp [h])) x' h9'
    exact ⟨4 + n, x'', by rw [run_add, List.cons_append, hrun, hrun'], h2'.trans h2, h10⟩

/-- Clearing the accumulator before the digit loop. -/
theorem digit_init (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (inp : List Char)
    (out : String) :
    ∃ x' : Regs 32,
      run 3 ⟨x, 2516, mem, inp, out, .running⟩ = ⟨x', 2528, mem, inp, out, .running⟩ ∧
      x'.get 2 = x.get 2 ∧ x'.get 10 = x.get 10 ∧ x'.get 16 = 9 ∧ x'.get 11 ++ x'.get 15 = (0 : BitVec 64) := by
  sym_exec

/-- The call `prime_count(n)`. -/
theorem call_prime_count (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem)
    (inp : List Char) (out : String) :
    ∃ x' : Regs 32,
      run 2 ⟨x, 2612, mem, inp, out, .running⟩ = ⟨x', 48, mem, inp, out, .running⟩ ∧
      x'.get 2 = x.get 2 ∧ x'.get 1 = 2620 ∧ x'.get 11 ++ x'.get 10 = x.get 11 ++ x.get 15 := by
  sym_exec

/-- `main` up to the call of `prime_count`: read the number. -/
theorem read_number (pre ds post : List Char) (hpre : ∀ c ∈ pre, c.isDigit = false)
    (hds : ds ≠ []) (hds' : ∀ c ∈ ds, c.isDigit) (hpost : ∀ c ∈ post.head?, c.isDigit = false)
    (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (hsp : x.get 2 = 0x400000) :
    ∃ n mem', ∃ x' : Regs 32,
      run n ⟨x, 2472, mem, pre ++ ds ++ post, "", .running⟩ =
        ⟨x', 48, mem', post.drop 1, "", .running⟩ ∧
      ImageOK mem' ∧ readBytes mem' 0x3ffffc 4 = some (x.get 1) ∧
      x'.get 2 = 0x3fffd0 ∧ x'.get 1 = 2620 ∧
      x'.get 11 ++ x'.get 10 = BitVec.ofNat 64 (digitsValue ds) := by
  obtain _ | ⟨d, ds⟩ := ds
  · exact absurd rfl hds
  have hd : d.isDigit := hds' d (by simp)
  have hdn := (isDigit_iff' d).1 hd
  -- reach the first digit
  have first : ∃ n mem', ∃ x' : Regs 32,
      run n ⟨x, 2472, mem, pre ++ (d :: ds) ++ post, "", .running⟩ =
        ⟨x', 2516, mem', ds ++ post, "", .running⟩ ∧
      ImageOK mem' ∧ readBytes mem' 0x3ffffc 4 = some (x.get 1) ∧
      x'.get 2 = 0x3fffd0 ∧ x'.get 10 = BitVec.ofNat 32 (d.toNat - 48) := by
    cases pre with
    | nil =>
      obtain ⟨mem', hm', hr, x', hrun, h2, -, h10⟩ := main_entry x mem hm d (ds ++ post) hsp
      simp only [hd, ite_true] at hrun
      exact ⟨7, mem', x', by simpa using hrun, hm', hr, h2, h10 hd⟩
    | cons c pre =>
      have hc : c.isDigit = false := hpre c (by simp)
      obtain ⟨mem', hm', hr, x', hrun, h2, h9, -⟩ :=
        main_entry x mem hm c (pre ++ d :: (ds ++ post)) hsp
      simp only [hc, Bool.false_eq_true, ite_false] at hrun
      obtain ⟨n, x'', hrun', h2', h10⟩ :=
        skip_loop pre (fun c h => hpre c (by simp [h])) d hd (ds ++ post) x' mem' hm' "" h9
      refine ⟨7 + n, mem', x'', ?_, hm', hr, h2'.trans h2, h10⟩
      rw [run_add]
      simp only [List.cons_append, List.append_assoc] at hrun ⊢
      rw [hrun, hrun']
  obtain ⟨n1, mem', x1, hrun1, hm', hr, h2, h10⟩ := first
  obtain ⟨x2, hrun2, h2', h10', h16, hacc⟩ := digit_init x1 mem' hm' (ds ++ post) ""
  obtain ⟨n3, x3, hrun3, h3, hv⟩ := digit_loop ds post (fun c h => hds' c (by simp [h])) hpost
    x2 mem' hm' "" 0 (d.toNat - 48) (by omega) h16 (h10'.trans h10) (by rw [hacc]; rfl)
  obtain ⟨x4, hrun4, h4, h1, h4v⟩ := call_prime_count x3 mem' hm' (post.drop 1) ""
  refine ⟨n1 + 3 + n3 + 2, mem', x4, ?_, hm', hr, ?_, h1, ?_⟩
  · rw [run_add, run_add, run_add, hrun1, hrun2, hrun3, hrun4]
  · rw [h4, h3, h2', h2]
  · rw [h4v, hv]
    simp [digitsValue, List.foldl]

/-! ## Printing the result -/

theorem print_setup (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (inp : List Char)
    (out : String) :
    ∃ x' : Regs 32,
      run 10 ⟨x, 2620, mem, inp, out, .running⟩ = ⟨x', 2660, mem, inp, out, .running⟩ ∧
      x'.get 2 = x.get 2 ∧ x'.get 13 = x.get 10 ∧ x'.get 14 = 0 ∧ x'.get 16 = 0 ∧
      x'.get 6 = x.get 2 + 12 ∧ x'.get 29 = 5 ∧ x'.get 11 = 0xcccccccd ∧ x'.get 28 = 0xcccccccc ∧
      x'.get 30 = 9 := by
  sym_exec

/-! Division by 10 as the compiled code does it: `n - n % 5` times the inverse of 5. -/

theorem div10_nat_a (K : Nat) (h : K < 858993460) (hp : 0 < K) :
    5 * K * 3435973836 % 4294967296 = 4294967296 - 4 * K := by omega
theorem div10_nat_b (K : Nat) (h : K < 858993460) :
    5 * K % 18446744073709551616 * 3435973837 % 18446744073709551616 / 4294967296
        % 4294967296 = 4 * K := by
  have e2 : 5 * K * 3435973837 = K + 4 * K * 4294967296 := by omega
  rw [Nat.mod_eq_of_lt (a := 5 * K) (by omega), e2,
    Nat.mod_eq_of_lt (a := K + 4 * K * 4294967296) (by omega),
    Nat.add_mul_div_right K (4 * K) (show 0 < 4294967296 by decide),
    Nat.div_eq_of_lt (a := K) (by omega), Nat.zero_add]
  omega
theorem toNat_umod5 (m : BitVec 32) : (m % 5#32).toNat = m.toNat % 5 := by simp [BitVec.toNat_umod]
theorem div10_hi (m : BitVec 32) :
    (m - m % 5#32) * 3435973836#32 +
      BitVec.setWidth 32 ((BitVec.setWidth 64 (m - m % 5#32) * 3435973837#64) >>> 32) = 0#32 := by
  have hm := m.isLt
  apply BitVec.eq_of_toNat_eq
  have h1 := toNat_umod5 m
  have h2 : (m - m % 5#32).toNat = 5 * (m.toNat / 5) := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; omega), h1]; omega
  have hK : m.toNat / 5 < 858993460 := by omega
  have c1 : (3435973836#32).toNat = 3435973836 := rfl
  have c2 : (3435973837#64).toNat = 3435973837 := rfl
  have c0 : (0#32).toNat = 0 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_mul, BitVec.toNat_setWidth, h2, c1, c2, c0, Nat.shiftRight_eq_div_pow]
  generalize m.toNat / 5 = K at *
  rcases Nat.eq_zero_or_pos K with rfl | hpos
  · simp
  · have := div10_nat_a K hK hpos
    have := div10_nat_b K hK
    simp only [Nat.reducePow] at *
    omega

theorem div10_lo (m : BitVec 32) :
    (m - m % 5#32) * 3435973837#32 = BitVec.ofNat 32 (m.toNat / 5) := by
  have hm := m.isLt
  apply BitVec.eq_of_toNat_eq
  have h1 : (m % 5#32).toNat = m.toNat % 5 := by simp [BitVec.toNat_umod]
  have h2 : (m - m % 5#32).toNat = m.toNat - m.toNat % 5 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; omega), h1]
  rw [BitVec.toNat_mul, h2]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The registers the digit loop keeps fixed. -/
def PrintRegs (x : Regs 32) (sp : BitVec 32) : Prop :=
  x.get 2 = sp ∧ x.get 6 = sp + 12 ∧ x.get 11 = 0xcccccccd ∧ x.get 28 = 0xcccccccc ∧
    x.get 29 = 5 ∧ x.get 30 = 9

/-- First part of the digit loop: `a5 = n - n % 5`, for `n` in `a3` and `a4 = 0`. -/
theorem digit_out_a (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (inp : List Char)
    (out : String) (sp : BitVec 32) (hp : PrintRegs x sp) (h14 : x.get 14 = 0) :
    ∃ x' : Regs 32,
      run 11 ⟨x, 2660, mem, inp, out, .running⟩ = ⟨x', 2704, mem, inp, out, .running⟩ ∧
      PrintRegs x' sp ∧ x'.get 13 = x.get 13 ∧ x'.get 14 = 0 ∧ x'.get 17 = 0 ∧
      x'.get 5 = x.get 13 ∧ x'.get 16 = x.get 16 + 1 ∧ x'.get 12 = sp + 12 + (x.get 16 + 1) ∧
      x'.get 15 = x.get 13 - x.get 13 % 5 := by
  obtain ⟨h2, h6, h11, h28, h29, h30⟩ := hp
  sym_exec [PrintRegs]
  generalize x.get 13 = m
  have h1 := toNat_umod5 m
  rw [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; omega), h1]
  omega

/-- Second part of the digit loop: divide by 10 and form the digit. -/
theorem digit_out_b (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (inp : List Char)
    (out : String) (sp : BitVec 32) (hp : PrintRegs x sp) (h14 : x.get 14 = 0)
    (h15 : x.get 15 = x.get 13 - x.get 13 % 5) :
    ∃ x' : Regs 32,
      run 15 ⟨x, 2704, mem, inp, out, .running⟩ = ⟨x', 2764, mem, inp, out, .running⟩ ∧
      PrintRegs x' sp ∧ x'.get 13 = x.get 13 ∧ x'.get 14 = 0 ∧ x'.get 17 = x.get 17 ∧
      x'.get 5 = x.get 5 ∧ x'.get 16 = x.get 16 ∧ x'.get 12 = x.get 12 ∧
      x'.get 15 = x.get 13 / 10 ∧ x'.get 10 = x.get 13 % 10 + 48 := by
  obtain ⟨h2, h6, h11, h28, h29, h30⟩ := hp
  sym_exec [PrintRegs, div10_hi, div10_lo]
  generalize x.get 13 = m
  have hm := m.isLt
  have hq : BitVec.ofNat 32 (m.toNat / 5) >>> 1 = m / 10#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have : (10#32).toNat = 10 := rfl
    rw [this]
    omega
  refine ⟨hq, ?_⟩
  rw [hq]
  apply BitVec.eq_of_toNat_eq
  have h10 : (10#32).toNat = 10 := rfl
  have hd : (m / 10#32).toNat = m.toNat / 10 := by rw [BitVec.toNat_udiv, h10]
  have hs : ((m / 10#32) <<< 3 + (m / 10#32) <<< 1).toNat = m.toNat / 10 * 10 := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, hd,
      Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    omega
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hs]; omega), hs, BitVec.toNat_umod, h10]
  omega

/-- A store, stepped without `simp` looking inside the address. -/
theorem step_store {mem mem' : Array (BitVec 8)} (hm : ImageOK mem) {x : Regs 32} {pc : BitVec 32}
    {inp : List Char} {out : String} {width : Width} {rs2 rs1 : Reg} {imm : BitVec 12} (k : Nat)
    (hpc : pc.toNat = 4 * k) (hk' : k < 1261)
    (hw : writeBytes mem (x.get rs1 + imm.signExtend 32).toNat (x.get rs2) width.bytes = some mem')
    (hk : instrAt k = .store width rs2 rs1 imm) :
    step ⟨x, pc, mem, inp, out, .running⟩ = ⟨x, pc + 4, mem', inp, out, .running⟩ := by
  rw [step_code hm _ _ _ _ _ (by omega) (by omega), show pc.toNat / 4 = k by omega, hk]
  simp only [exec, hw, Machine.advance]

/-- A load, stepped without `simp` looking inside the address. -/
theorem step_load {mem : Array (BitVec 8)} (hm : ImageOK mem) {x : Regs 32} {pc : BitVec 32}
    {inp : List Char} {out : String} {width : Width} {signed : Bool} {rd rs1 : Reg}
    {imm : BitVec 12} {v : BitVec (8 * width.bytes)} (k : Nat)
    (hpc : pc.toNat = 4 * k) (hk' : k < 1261)
    (hr : readBytes mem (x.get rs1 + imm.signExtend 32).toNat width.bytes = some v)
    (hk : instrAt k = .load width signed rd rs1 imm) :
    step ⟨x, pc, mem, inp, out, .running⟩ =
      ⟨x.set rd (if signed then v.signExtend 32 else v.setWidth 32), pc + 4, mem, inp, out,
        .running⟩ := by
  rw [step_code hm _ _ _ _ _ (by omega) (by omega), show pc.toNat / 4 = k by omega, hk]
  simp only [exec, hr, Machine.advance, Machine.setReg]

theorem run_succ_of_step {x : Regs 32} {pc : BitVec 32} {mem : Array (BitVec 8)} {inp : List Char}
    {out : String} {m' : Machine 32} (n : Nat)
    (h : step ⟨x, pc, mem, inp, out, .running⟩ = m') :
    run (n + 1) ⟨x, pc, mem, inp, out, .running⟩ = run n m' := by
  rw [← h]; rfl

/-- Third part of the digit loop: store the digit and loop while `n > 9`. -/
theorem digit_out_c (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (inp : List Char)
    (out : String) (h17 : x.get 17 = 0) (mem' : Array (BitVec 8))
    (hw : writeBytes mem (x.get 12 + BitVec.signExtend 32 (-1 : BitVec 12)).toNat (x.get 10) 1 =
      some mem')
    (hm' : ImageOK mem') (h30 : x.get 30 = 9) :
    ∃ x' : Regs 32,
      run 4 ⟨x, 2764, mem, inp, out, .running⟩ =
        ⟨x', if (9#32).ult (x.get 5) then 2660 else 2780, mem', inp, out, .running⟩ ∧
      (∀ r : Reg, r ≠ 13 → x'.get r = x.get r) ∧ x'.get 13 = x.get 15 := by
  rw [run_succ_of_step 3 (step_store hm (width := .byte) (rs2 := 10) (rs1 := 12) (imm := -1) 691 (by decide) (by decide) hw (by simp only [reduceInstrAt]))]
  cases h : (9#32).ult (x.get 5) <;> sym_exec <;> intro r hr <;> split <;> simp_all <;>
    intro h <;> exact absurd h.symm hr

/-! ### Decimal digits -/

/-- The decimal digits of `n`, least significant first. -/
def revDigits (n : Nat) : List Nat :=
  if n < 10 then [n] else n % 10 :: revDigits (n / 10)

theorem revDigits_lt (n : Nat) : ∀ d ∈ revDigits n, d < 10 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold revDigits
    split
    · simp; omega
    · intro d hd
      simp at hd
      rcases hd with rfl | hd
      · omega
      · exact ih (n / 10) (by omega) d hd

theorem revDigits_length (n : Nat) (h : n < 2 ^ 32) : (revDigits n).length ≤ 10 := by
  have key : ∀ k n, n < 10 ^ (k + 1) → (revDigits n).length ≤ k + 1 := by
    intro k
    induction k with
    | zero => intro n h; unfold revDigits; simp at h; simp [h]
    | succ k ih =>
      intro n h
      unfold revDigits
      split
      · simp
      · have := ih (n / 10) (by rw [Nat.pow_succ] at h; omega)
        simp; omega
  exact key 9 n (by omega)

theorem toDigits_revDigits (n : Nat) :
    Nat.toDigits 10 n = ((revDigits n).map Nat.digitChar).reverse := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by omega)]
    unfold revDigits
    split
    · simp
    · rw [ih (n / 10) (by omega)]
      simp

theorem digitChar_eq (d : Nat) (h : d < 10) : Nat.digitChar d = Char.ofNat (48 + d) := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl

/-- Where `main` keeps `buf`: `sp + 12`, with `sp = 0x3fffd0`. -/
abbrev bufAddr : Nat := 0x3fffdc

theorem store_addr (i : Nat) (hi : i < 20) :
    ((4194256 : BitVec 32) + 12 + (BitVec.ofNat 32 i + 1) + BitVec.signExtend 32 (-1 : BitVec 12)).toNat =
      bufAddr + i := by
  have c0 : BitVec.signExtend 32 (-1 : BitVec 12) = 4294967295#32 := by decide
  have c1 : ((4194256 : BitVec 32) + 12 : BitVec 32) = 4194268#32 := rfl
  have c2 : (4294967295#32).toNat = 4294967295 := rfl
  have c3 : (4194268#32).toNat = 4194268 := rfl
  have c4 : (1 : BitVec 32).toNat = 1 := rfl
  rw [c0, c1, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, c2, c3, c4, BitVec.toNat_ofNat]
  simp only [bufAddr]
  omega

theorem ofNat_succ32 (i : Nat) (hi : i < 20) : BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  have c4 : (1 : BitVec 32).toNat = 1 := rfl
  rw [BitVec.toNat_add, c4, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem buf_ptr (i : Nat) (hi : i < 20) :
    (4194256 : BitVec 32) + 12 + (BitVec.ofNat 32 i + 1) = BitVec.ofNat 32 (bufAddr + i + 1) := by
  apply BitVec.eq_of_toNat_eq
  have c1 : ((4194256 : BitVec 32) + 12 : BitVec 32) = 4194268#32 := rfl
  have c3 : (4194268#32).toNat = 4194268 := rfl
  have c4 : (1 : BitVec 32).toNat = 1 := rfl
  rw [c1, BitVec.toNat_add, BitVec.toNat_add, c3, c4, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [bufAddr]
  omega

theorem ofNat_umod10 (n : Nat) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 n % 10 = BitVec.ofNat 32 (n % 10) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod]
  have hn' : n < 4294967296 := hn
  have c : (10 : BitVec 32).toNat = 10 := rfl
  simp only [BitVec.toNat_ofNat, Nat.reducePow, c]
  rw [Nat.mod_eq_of_lt hn']
  omega

theorem ofNat_udiv10 (n : Nat) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 n / 10 = BitVec.ofNat 32 (n / 10) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv]
  have hn' : n < 4294967296 := hn
  have c : (10 : BitVec 32).toNat = 10 := rfl
  simp only [BitVec.toNat_ofNat, Nat.reducePow, c]
  rw [Nat.mod_eq_of_lt hn']
  omega

theorem digit_byte (n : Nat) (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 32 n % 10 + 48) >>> (8 * 0)).setWidth 8 = BitVec.ofNat 8 (48 + n % 10) := by
  rw [ofNat_umod10 n hn]
  apply BitVec.eq_of_toNat_eq
  have c : (48 : BitVec 32).toNat = 48 := rfl
  simp only [Nat.mul_zero, BitVec.ushiftRight_zero, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat, c]
  omega

theorem ult9 (n : Nat) (hn : n < 2 ^ 32) : (9#32).ult (BitVec.ofNat 32 n) = decide (9 < n) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hn]

/-- The loop of `print_u64` that stores the digits of `n`, least significant first, at
`buf + i`. -/
theorem digits_store (n : Nat) (hn : n < 2 ^ 32) (i : Nat) (hi : i + (revDigits n).length ≤ 20)
    (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (inp : List Char) (out : String)
    (hp : PrintRegs x 0x3fffd0) (h13 : x.get 13 = BitVec.ofNat 32 n) (h14 : x.get 14 = 0)
    (h16 : x.get 16 = BitVec.ofNat 32 i) :
    ∃ k mem', ∃ x' : Regs 32,
      run k ⟨x, 2660, mem, inp, out, .running⟩ = ⟨x', 2780, mem', inp, out, .running⟩ ∧
      ImageOK mem' ∧ PrintRegs x' 0x3fffd0 ∧
      x'.get 12 = BitVec.ofNat 32 (bufAddr + i + (revDigits n).length) ∧
      (∀ k (hk : k < (revDigits n).length),
        mem'[bufAddr + i + k]? = some (BitVec.ofNat 8 (48 + (revDigits n)[k]))) ∧
      (∀ a, a < bufAddr + i ∨ bufAddr + i + (revDigits n).length ≤ a → mem'[a]? = mem[a]?) := by
  induction n using Nat.strongRecOn generalizing i x mem with
  | _ n ih =>
  have hL : 1 ≤ (revDigits n).length := by unfold revDigits; split <;> simp
  obtain ⟨x1, hrun1, hp1, h13', h14', h17', h5', h16', h12', h15'⟩ :=
    digit_out_a x mem hm inp out _ hp h14
  obtain ⟨x2, hrun2, hp2, h13'', h14'', h17'', h5'', h16'', h12'', h15'', h10''⟩ :=
    digit_out_b x1 mem hm inp out _ hp1 h14' (by rw [h15', h13'])
  have haddr : (x2.get 12 + BitVec.signExtend 32 (-1 : BitVec 12)).toNat = bufAddr + i := by
    rw [h12'', h12', h16, ← store_addr i (by omega)]
  obtain ⟨mem', hw⟩ := writeBytes_isSome (mem := mem) (addr := bufAddr + i) (n := 1) (x2.get 10)
    (by rw [hm.size]; simp only [bufAddr, memSize]; omega)
  have hm' := hm.write hw (by simp only [bufAddr]; omega)
  rw [← haddr] at hw
  obtain ⟨x3, hrun3, hx3, h13'''⟩ :=
    digit_out_c x2 mem hm inp out (by rw [h17'', h17']) mem' hw hm' (by rw [hp2.2.2.2.2.2])
  have hrun : run 30 ⟨x, 2660, mem, inp, out, .running⟩ =
      ⟨x3, if 9 < n then 2660 else 2780, mem', inp, out, .running⟩ := by
    rw [show 30 = 11 + (15 + 4) by rfl, run_add, hrun1, run_add, hrun2, hrun3, h5'', h5', h13,
      ult9 n hn]
    simp
  have hbyte : mem'[bufAddr + i]? = some (BitVec.ofNat 8 (48 + n % 10)) := by
    rw [haddr] at hw
    have := writeBytes_written hw 0 (by omega)
    rw [Nat.add_zero, h10'', h13', h13, digit_byte n hn] at this
    exact this
  have hframe : ∀ a, a ≠ bufAddr + i → mem'[a]? = mem[a]? := by
    rw [haddr] at hw
    intro a ha
    exact writeBytes_frame hw a (by omega)
  have hp3 : PrintRegs x3 0x3fffd0 := by
    obtain ⟨a, b, c, d, e, f⟩ := hp2
    exact ⟨(hx3 2 (by decide)).trans a, (hx3 6 (by decide)).trans b, (hx3 11 (by decide)).trans c,
      (hx3 28 (by decide)).trans d, (hx3 29 (by decide)).trans e, (hx3 30 (by decide)).trans f⟩
  have h12x3 : x3.get 12 = BitVec.ofNat 32 (bufAddr + i + 1) := by
    rw [hx3 12 (by decide), h12'', h12', h16, buf_ptr i (by omega)]
  by_cases h9 : 9 < n
  · -- more digits
    have hrev : revDigits n = n % 10 :: revDigits (n / 10) := by
      rw [revDigits, if_neg (by omega)]
    rw [hrev] at hi ⊢
    simp only [List.length_cons] at hi
    obtain ⟨k, mem'', x', hrun', hm'', hp', h12f, hdig, hfr⟩ :=
      ih (n / 10) (by omega) (by omega) (i + 1) (by omega) x3 mem' hm' hp3
        (by rw [h13''', h15'', h13', h13, ofNat_udiv10 n hn])
        (by rw [hx3 14 (by decide), h14''])
        (by
          rw [hx3 16 (by decide), h16'', h16', h16, ofNat_succ32 i (by omega)])
    refine ⟨30 + k, mem'', x', ?_, hm'', hp', ?_, ?_, ?_⟩
    · rw [run_add, hrun, if_pos h9, hrun']
    · rw [h12f]; simp only [List.length_cons]
      rw [show bufAddr + (i + 1) + (revDigits (n / 10)).length =
        bufAddr + i + ((revDigits (n / 10)).length + 1) by omega]
    · intro k hk
      cases k with
      | zero =>
        rw [hfr _ (by omega), Nat.add_zero, hbyte]
        rfl
      | succ k =>
        have := hdig k (by simp at hk; omega)
        rw [show bufAddr + i + (k + 1) = bufAddr + (i + 1) + k by omega, this]
        rfl
    · intro a ha
      simp only [List.length_cons] at ha
      rw [hfr a (by omega), hframe a (by omega)]
  · -- last digit
    have hrev : revDigits n = [n] := by rw [revDigits, if_pos (by omega)]
    rw [hrev]
    refine ⟨30, mem', x3, ?_, hm', hp3, ?_, ?_, ?_⟩
    · rw [hrun, if_neg h9]
    · rw [h12x3]; rfl
    · intro k hk
      simp at hk
      subst hk
      rw [Nat.add_zero, hbyte, Nat.mod_eq_of_lt (by omega)]
      rfl
    · intro a ha
      exact hframe a (by simp at ha; omega)


theorem load_addr (p : Nat) (hp : p + 1 < 2 ^ 32) :
    (BitVec.ofNat 32 (p + 1) + BitVec.signExtend 32 (-1 : BitVec 12)).toNat = p := by
  have c0 : BitVec.signExtend 32 (-1 : BitVec 12) = 4294967295#32 := by decide
  have c2 : (4294967295#32).toNat = 4294967295 := rfl
  rw [c0, BitVec.toNat_add, c2, BitVec.toNat_ofNat]
  omega

/-- One trip round the loop of `print_u64` that prints the stored digits. -/
theorem print_step (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (inp : List Char)
    (out : String) (p : Nat) (hp : p + 1 < 2 ^ 32) (b : BitVec 8) (hb : mem[p]? = some b)
    (h15 : x.get 15 = BitVec.ofNat 32 (p + 1)) :
    ∃ x' : Regs 32,
      run 5 ⟨x, 2784, mem, inp, out, .running⟩ =
        ⟨x', if x.get 6 = BitVec.ofNat 32 (p + 1) + 4294967295#32 then 2804 else 2784, mem, inp,
          out.push (Char.ofNat (b.toNat % 256)), .running⟩ ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 15 → r ≠ 17 → x'.get r = x.get r) ∧ x'.get 17 = 11 ∧
      x'.get 15 = BitVec.ofNat 32 (p + 1) + 4294967295#32 := by
  have hr : readBytes mem (x.get 15 + BitVec.signExtend 32 (-1 : BitVec 12)).toNat 1 =
      some (b.cast (by rfl)) := by
    rw [h15, load_addr p hp]; exact readBytes_one hb
  rw [run_succ_of_step 4 (step_load hm (width := .byte) (signed := false) (rd := 10) (rs1 := 15)
    (imm := -1) 696 (by decide) (by decide) hr (by simp only [reduceInstrAt]))]
  sym_exec
  refine ⟨_, by split <;> rfl, ?_, ?_, ?_⟩
  · intro r h1 h2 h3
    simp only [Regs.get_set, Ne.symm h1, Ne.symm h2, Ne.symm h3, if_false]
    split <;> simp_all
  · simp [Regs.get_set]
  · simp [Regs.get_set]

theorem ptr_dec (j : Nat) (hj : j < 20) :
    BitVec.ofNat 32 (bufAddr + j + 1) + 4294967295#32 = BitVec.ofNat 32 (bufAddr + j) := by
  apply BitVec.eq_of_toNat_eq
  have c2 : (4294967295#32).toNat = 4294967295 := rfl
  rw [BitVec.toNat_add, c2, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [bufAddr]
  omega

theorem buf_eq (j : Nat) (hj : j < 20) :
    ((4194256 : BitVec 32) + 12 = BitVec.ofNat 32 (bufAddr + j)) ↔ j = 0 := by
  have c1 : ((4194256 : BitVec 32) + 12 : BitVec 32) = BitVec.ofNat 32 4194268 := rfl
  rw [c1]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, bufAddr] at this
    omega
  · intro h; subst h; rfl

theorem digit_char (d : Nat) (hd : d < 10) :
    Char.ofNat ((BitVec.ofNat 8 (48 + d)).toNat % 256) = Char.ofNat (48 + d) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The loop of `print_u64` that prints the first `j` stored digits, last first. -/
theorem print_loop (ds : List Nat) (hds : ∀ d ∈ ds, d < 10) (hL : ds.length ≤ 20)
    (mem : Array (BitVec 8)) (hm : ImageOK mem) (inp : List Char)
    (hmem : ∀ k (hk : k < ds.length), mem[bufAddr + k]? = some (BitVec.ofNat 8 (48 + ds[k])))
    (j : Nat) (hj : 1 ≤ j) (hjL : j ≤ ds.length) (x : Regs 32) (out : String)
    (hp : PrintRegs x 0x3fffd0) (h15 : x.get 15 = BitVec.ofNat 32 (bufAddr + j)) :
    ∃ n out', ∃ x' : Regs 32,
      run n ⟨x, 2784, mem, inp, out, .running⟩ = ⟨x', 2804, mem, inp, out', .running⟩ ∧
      PrintRegs x' 0x3fffd0 ∧ x'.get 17 = 11 ∧
      out'.toList = out.toList ++ ((ds.take j).reverse.map fun d => Char.ofNat (48 + d)) := by
  induction j generalizing x out with
  | zero => omega
  | succ j ih =>
    have hd := hds ds[j] (List.getElem_mem _)
    obtain ⟨x', hrun, hx', h17, h15'⟩ := print_step x mem hm inp out (bufAddr + j) (by simp only [bufAddr]; omega)
      _ (hmem j (by omega)) (by rw [h15]; rfl)
    rw [ptr_dec j (by omega), hp.2.1, show (0x3fffd0 : BitVec 32) = 4194256 from rfl,
      digit_char _ hd] at hrun
    rw [ptr_dec j (by omega)] at h15'
    have hp' : PrintRegs x' 0x3fffd0 := by
      obtain ⟨a, b, c, d, e, f⟩ := hp
      exact ⟨(hx' 2 (by decide) (by decide) (by decide)).trans a,
        (hx' 6 (by decide) (by decide) (by decide)).trans b,
        (hx' 11 (by decide) (by decide) (by decide)).trans c,
        (hx' 28 (by decide) (by decide) (by decide)).trans d,
        (hx' 29 (by decide) (by decide) (by decide)).trans e,
        (hx' 30 (by decide) (by decide) (by decide)).trans f⟩
    have htake : (ds.take (j + 1)).reverse = ds[j] :: (ds.take j).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
      simp
    by_cases hj0 : j = 0
    · subst hj0
      have e : ((4194256 : BitVec 32) + 12 = BitVec.ofNat 32 (bufAddr + 0)) := (buf_eq 0 (by omega)).2 rfl
      rw [if_pos e] at hrun
      refine ⟨5, _, x', hrun, hp', h17, ?_⟩
      rw [String.toList_push, htake]
      simp
    · rw [if_neg (fun h => hj0 ((buf_eq j (by omega)).1 h))] at hrun
      obtain ⟨n, out', x'', hrun', hp'', h17', hout⟩ := ih (by omega) (by omega) x' _ hp' h15'
      refine ⟨5 + n, out', x'', by rw [run_add, hrun, hrun'], hp'', h17', ?_⟩
      rw [hout, String.toList_push, htake]
      simp

theorem print_mv (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (inp : List Char)
    (out : String) :
    ∃ x' : Regs 32,
      run 1 ⟨x, 2780, mem, inp, out, .running⟩ = ⟨x', 2784, mem, inp, out, .running⟩ ∧
      (∀ r : Reg, r ≠ 15 → x'.get r = x.get r) ∧ x'.get 15 = x.get 12 := by
  sym_exec
  intro r hr
  simp only [Regs.get_set, Ne.symm hr, if_false]
  split <;> simp_all

/-- The newline, the return from `main`, and `exit(0)`. -/
theorem print_tail (x : Regs 32) (mem : Array (BitVec 8)) (hm : ImageOK mem) (inp : List Char)
    (out : String) (h2 : x.get 2 = 0x3fffd0) (h17 : x.get 17 = 11)
    (hra : readBytes mem 0x3ffffc 4 = some 8) :
    (run 8 ⟨x, 2804, mem, inp, out, .running⟩).status = .exited 0 ∧
      (run 8 ⟨x, 2804, mem, inp, out, .running⟩).output = out.push (Char.ofNat 10) := by
  have hr : ∀ x' : Regs 32, x'.get 2 = 0x3fffd0 →
      readBytes mem (x'.get 2 + BitVec.signExtend 32 (44 : BitVec 12)).toNat Width.word.bytes =
        some (8 : BitVec 32) := by
    intro x' h; rw [h]; exact hra
  have h1 : ∃ x1 : Regs 32, run 2 ⟨x, 2804, mem, inp, out, .running⟩ =
      ⟨x1, 2812, mem, inp, out.push (Char.ofNat 10), .running⟩ ∧ x1.get 2 = 0x3fffd0 := by
    sym_exec
  obtain ⟨x1, hrun1, h12⟩ := h1
  rw [show 8 = 2 + (1 + 5) by rfl, run_add, hrun1, run_add,
    run_succ_of_step 0 (step_load hm (width := .word) (signed := true) (rd := 1) (rs1 := 2)
      (imm := 44) 703 (by decide) (by decide) (hr x1 h12) (by simp only [reduceInstrAt]))]
  sym_exec

theorem toString_toList (r : Nat) :
    (toString r).toList = (revDigits r).reverse.map fun d => Char.ofNat (48 + d) := by
  show (Nat.repr r).toList = _
  rw [Nat.repr, String.toList_ofList, toDigits_revDigits, List.map_reverse]
  congr 1
  apply List.map_congr_left
  intro d hd
  exact digitChar_eq d (revDigits_lt r d hd)

/-- `print_u64` on the value `r` returned by `prime_count`, then the return from `main` and
`exit(0)`. -/
theorem print_all (r : Nat) (hr : r < 2 ^ 32) (x : Regs 32) (mem : Array (BitVec 8))
    (hm : ImageOK mem) (inp : List Char) (out : String) (h2 : x.get 2 = 0x3fffd0)
    (h10 : x.get 10 = BitVec.ofNat 32 r) (hra : readBytes mem 0x3ffffc 4 = some 8) :
    ∃ n, (run n ⟨x, 2620, mem, inp, out, .running⟩).status = .exited 0 ∧
      (run n ⟨x, 2620, mem, inp, out, .running⟩).output = out ++ toString r ++ "\n" := by
  have hL := revDigits_length r hr
  have hL1 : 1 ≤ (revDigits r).length := by unfold revDigits; split <;> simp
  obtain ⟨x1, hrun1, h2', h13, h14, h16, h6, h29, h11, h28, h30⟩ := print_setup x mem hm inp out
  have hp1 : PrintRegs x1 0x3fffd0 := ⟨h2'.trans h2, by rw [h6, h2], h11, h28, h29, h30⟩
  obtain ⟨k, mem', x2, hrun2, hm', hp2, h12f, hdig, hfr⟩ :=
    digits_store r hr 0 (by omega) x1 mem hm inp out hp1 (h13.trans h10) h14 (by rw [h16]; rfl)
  obtain ⟨x3, hrun3, hx3, h15⟩ := print_mv x2 mem' hm' inp out
  have hp3 : PrintRegs x3 0x3fffd0 := by
    obtain ⟨a, b, c, d, e, f⟩ := hp2
    exact ⟨(hx3 2 (by decide)).trans a, (hx3 6 (by decide)).trans b, (hx3 11 (by decide)).trans c,
      (hx3 28 (by decide)).trans d, (hx3 29 (by decide)).trans e, (hx3 30 (by decide)).trans f⟩
  obtain ⟨n4, out', x4, hrun4, hp4, h17, hout⟩ :=
    print_loop (revDigits r) (revDigits_lt r) (by omega) mem' hm' inp
      (fun k hk => by simpa using hdig k hk) _ hL1 (Nat.le_refl _) x3 out hp3
      (by rw [h15, h12f, Nat.add_zero])
  have hra' : readBytes mem' 0x3ffffc 4 = some 8 := by
    rw [← hra]
    apply readBytes_congr
    intro a h1 _
    exact hfr a (Or.inr (by simp only [bufAddr] at *; omega))
  obtain ⟨hst, hout'⟩ := print_tail x4 mem' hm' inp out' hp4.1 h17 hra'
  refine ⟨10 + k + 1 + n4 + 8, ?_, ?_⟩
  · rw [run_add, run_add, run_add, run_add, hrun1, hrun2, hrun3, hrun4, hst]
  · rw [run_add, run_add, run_add, run_add, hrun1, hrun2, hrun3, hrun4, hout']
    apply String.toList_inj.mp
    rw [String.toList_push, hout, List.take_length, String.toList_append, String.toList_append,
      toString_toList]
    rfl

/-! ## The specification -/

/-- Whether `p` is prime. -/
def isPrime (p : Nat) : Bool := 2 ≤ p && (List.range p).all fun d => d < 2 || p % d != 0

/-- `π(n)`, the number of primes up to `n`. -/
def primeCount (n : Nat) : Nat := ((List.range (n + 1)).filter isPrime).length

example : primeCount 100 = 25 := by decide

/-! ## `prime_count` -/

/-- **Not yet proven.** The function `prime_count` at address 48, called from `main`: it returns
to `ra` with `π(N)` in `a0` (as the `uint32_t` it is declared to return), having restored `sp`,
kept the image intact and left `main`'s frame alone. Everything it does happens below `sp`.

This is where the work that remains lies: `memset`, `__udivdi3` (with `__clz_tab`), and the
loops of the Lucy/min_25 algorithm over the stack arrays, against a proof that the algorithm
counts primes. -/
theorem prime_count_spec (N : Nat) (hN : N ≤ 10 ^ 11) (x : Regs 32) (mem : Array (BitVec 8))
    (hm : ImageOK mem) (inp : List Char) (out : String) (hsp : x.get 2 = 0x3fffd0)
    (hra : x.get 1 = 2620) (ha : x.get 11 ++ x.get 10 = BitVec.ofNat 64 N) :
    ∃ n mem', ∃ x' : Regs 32,
      run n ⟨x, 48, mem, inp, out, .running⟩ = ⟨x', 2620, mem', inp, out, .running⟩ ∧
      ImageOK mem' ∧ x'.get 2 = 0x3fffd0 ∧ x'.get 10 = BitVec.ofNat 32 (primeCount N) ∧
      ∀ a, 0x3fffd0 ≤ a → mem'[a]? = mem[a]? := by
  sorry

/-- **Not yet proven.** `π(10^11) = 4118054813 < 2^32`, so the `uint32_t` result does not wrap. -/
theorem primeCount_lt (N : Nat) (hN : N ≤ 10 ^ 11) : primeCount N < 2 ^ 32 := by
  sorry

/-! ## Correctness -/

theorem load_imageOK (input : List Char) : ImageOK (load 32 prog memSize input).mem :=
  ⟨load_size _ _ _ _ (by rw [prog_length]; decide), load_wordsAt _ _ _ _⟩

/-- **Correctness of `counting_primes_lpha.py`**, given `prime_count_spec`. On an input that is
some non-digits, then a number `N ≤ 10^11` in decimal, then anything not starting with a digit,
the program exits with code 0 having printed `π(N)` (as a `uint32_t`) and a newline. -/
theorem correct (pre ds post : List Char) (hpre : ∀ c ∈ pre, c.isDigit = false)
    (hds : ds ≠ []) (hds' : ∀ c ∈ ds, c.isDigit) (hpost : ∀ c ∈ post.head?, c.isDigit = false)
    (hN : digitsValue ds ≤ 10 ^ 11) :
    ∃ n, (run n (load 32 prog memSize (pre ++ ds ++ post))).status = .exited 0 ∧
      (run n (load 32 prog memSize (pre ++ ds ++ post))).output =
        toString (primeCount (digitsValue ds) % 2 ^ 32) ++ "\n" := by
  obtain ⟨x0, h2, h1, hrun0⟩ := start (pre ++ ds ++ post)
  obtain ⟨n1, mem1, x1, hrun1, hm1, hra1, h21, h11, hv1⟩ :=
    read_number pre ds post hpre hds hds' hpost x0 _ (load_imageOK _) h2
  obtain ⟨n2, mem2, x2, hrun2, hm2, h22, h102, hfr⟩ :=
    prime_count_spec _ hN x1 mem1 hm1 _ "" h21 h11 hv1
  have hra2 : readBytes mem2 0x3ffffc 4 = some 8 := by
    rw [← h1, ← hra1]
    exact readBytes_congr fun a h _ => hfr a (by omega)
  obtain ⟨n3, hst, hout⟩ := print_all (primeCount (digitsValue ds) % 2 ^ 32) (Nat.mod_lt _ (by decide))
    x2 mem2 hm2 _ "" h22 (by rw [h102]; apply BitVec.eq_of_toNat_eq; simp) hra2
  refine ⟨2 + n1 + n2 + n3, ?_, ?_⟩
  · rw [run_add, run_add, run_add, hrun0, hrun1, hrun2, hst]
  · rw [run_add, run_add, run_add, hrun0, hrun1, hrun2, hout, String.empty_append]

/-- The same with the printed number equal to `π(N)` itself, given `primeCount_lt`. -/
theorem correct' (pre ds post : List Char) (hpre : ∀ c ∈ pre, c.isDigit = false)
    (hds : ds ≠ []) (hds' : ∀ c ∈ ds, c.isDigit) (hpost : ∀ c ∈ post.head?, c.isDigit = false)
    (hN : digitsValue ds ≤ 10 ^ 11) :
    ∃ n, (run n (load 32 prog memSize (pre ++ ds ++ post))).status = .exited 0 ∧
      (run n (load 32 prog memSize (pre ++ ds ++ post))).output =
        toString (primeCount (digitsValue ds)) ++ "\n" := by
  have := correct pre ds post hpre hds hds' hpost hN
  rwa [Nat.mod_eq_of_lt (primeCount_lt _ hN)] at this

end TinyFive.CountingPrimesLpha
