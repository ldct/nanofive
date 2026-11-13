import TinyFive.Machine

/-!
# Correctness of `abc101_a.py`

`abc101_a.py` solves AtCoder ABC101 A: start from 0, add 1 for each `+` read and subtract 1 for
each `-`, and print the result. This file proves that its 20 words of machine code do that on the
machine model of `TinyFive.Machine`.

## What is proven

`correct`: for every input, the machine loaded with `prog` reaches, after some number `n` of
steps, a state that has exited with code 0 and has printed `tally input` followed by a newline.
Since the machine is deterministic and `run` stops at the first state that is not running, this
says both that the program terminates and what it has printed when it does.

`correct_of_length_lt`: the same with the printed number equal to `tally input` exactly, for
inputs shorter than `2 ^ 31` characters. `correct` itself prints the tally wrapped to a signed
`w`-bit number, because that is what the register holding it does.

Both hold at register width `w = 32`, which is the `machine` that `abc101_a.py` runs on, and at
`w = 64`.

## What input is valid

Every input is: the theorems have no hypothesis on it. The program reads until the first
character that is neither `+` nor `-`, or until the input ends, and leaves the rest unread.
`tally` is defined to match, as the count of `+` minus the count of `-` over the leading run of
those two characters. On an input as AtCoder gives it, four signs and a newline, that is the
answer to the problem.

## How input and output are represented

They are fields of the machine state, not a separate trace. `Machine.input : List Char` is what
remains of standard input and `Machine.output : String` is everything printed so far. The system
calls act on them (`TinyFive.ecall`):

* `read_char` (`a7 = 12`) removes the first character and puts its code point in `a0`, or puts
  `-1` there if no input remains;
* `print_int` (`a7 = 1`) appends `a0` as a signed decimal number;
* `print_char` (`a7 = 11`) appends the character whose code is the low byte of `a0`;
* `exit` (`a7 = 10`) sets `Machine.status` to `exited 0`.

Both are text, not bytes, because `machine.py` reads and prints text.

## How `prog` and `code` are related

`prog` is the machine code and `code` is a readable list of instructions. That `prog` decodes to
`code` is proven, not assumed: `fetch32` and `fetch64` state that reading four bytes of `image`
at any address `n < 80` divisible by 4 and decoding them gives entry `n / 4` of `code`. The
kernel checks this by evaluating all 20 cases. `image` is the memory that `load` builds from
`prog`.

What is not proven here is that `prog` is the list of the same name in `abc101_a.py`. That is
checked by `abc101_a_lean_test.py`, which also compares the model with `machine.py` on sample
inputs.

## Proof strategy

1. `step_image` turns `fetch32` and `fetch64` into a rewrite rule: one step of a machine whose
   memory is `image` executes the entry of `code` at its `pc`.
2. The tactic `sym_exec` runs a machine forward by simplification. It needs the state written
   out with a literal `pc`, and unfolds a fixed number of steps into the state they produce.
3. Four lemmas describe every path from the head of the loop (address 4), each proved by
   `sym_exec`: `loop_plus` and `loop_minus` return to address 4 with one character consumed and
   `t0` changed by 1; `done_nil` and `done_cons` leave the loop, print `t0` and exit. The program
   never stores to memory, so the memory stays equal to `image` throughout.
4. `loop_correct` is an induction on the input: from the head of the loop the program prints
   `t0` plus the tally of the remaining input. This is where termination comes from, since each
   trip round the loop consumes a character.
5. `correct` executes the one instruction before the loop, which sets `t0` to 0, and applies
   `loop_correct`.
-/

namespace TinyFive

theorem run_add {w : Nat} (a b : Nat) (m : Machine w) : run (a + b) m = run b (run a m) := by
  induction a generalizing m with
  | zero => simp [run]
  | succ a ih =>
    rw [Nat.add_right_comm, run, run]
    split
    · exact ih _
    · cases b <;> simp [run, *]

namespace Abc101a

/-- The machine code of `abc101_a.py`, as produced by its `prog` list. -/
def prog : List (BitVec 32) := [
  0x00000293, 0x00c00893, 0x00000073, 0x02b00313, 0x00650863,
  0x02d00313, 0x00650863, 0x0140006f, 0x00128293, 0xfe1ff06f,
  0xfff28293, 0xfd9ff06f, 0x00028513, 0x00100893, 0x00000073,
  0x00a00513, 0x00b00893, 0x00000073, 0x00a00893, 0x00000073]

/-- The memory of the loaded machine. -/
def image : Array (BitVec 8) := (load 32 prog 256 []).mem

/-- What `prog` decodes to. -/
def code : List Instr := [
  .opImm .add 5 0 0,       --  0:        li   t0, 0
  .opImm .add 17 0 12,     --  4: loop:  li   a7, 12
  .ecall,                  --  8:        ecall            (read_char)
  .opImm .add 6 0 43,      -- 12:        li   t1, '+'
  .branch .beq 10 6 16,    -- 16:        beq  a0, t1, plus
  .opImm .add 6 0 45,      -- 20:        li   t1, '-'
  .branch .beq 10 6 16,    -- 24:        beq  a0, t1, minus
  .jal 0 20,               -- 28:        j    done
  .opImm .add 5 5 1,       -- 32: plus:  addi t0, t0, 1
  .jal 0 (-32),            -- 36:        j    loop
  .opImm .add 5 5 (-1),    -- 40: minus: addi t0, t0, -1
  .jal 0 (-40),            -- 44:        j    loop
  .opImm .add 10 5 0,      -- 48: done:  mv   a0, t0
  .opImm .add 17 0 1,      -- 52:        li   a7, 1
  .ecall,                  -- 56:        ecall            (print_int)
  .opImm .add 10 0 10,     -- 60:        li   a0, '\n'
  .opImm .add 17 0 11,     -- 64:        li   a7, 11
  .ecall,                  -- 68:        ecall            (print_char)
  .opImm .add 17 0 10,     -- 72:        li   a7, 10
  .ecall]                  -- 76:        ecall            (exit)

theorem fetch32 : ∀ n, n < 80 → n % 4 = 0 →
    (readBytes image n 4).bind (decode 32) = some (code.getD (n / 4) .ecall) := by
  decide +kernel

theorem fetch64 : ∀ n, n < 80 → n % 4 = 0 →
    (readBytes image n 4).bind (decode 64) = some (code.getD (n / 4) .ecall) := by
  decide +kernel

variable {w : Nat}

theorem step_image (hw : w = 32 ∨ w = 64) (x : Regs w) (pc : BitVec w)
    (inp : List Char) (out : String) (st : Status) (h : pc.toNat < 80) (h4 : pc.toNat % 4 = 0) :
    step ⟨x, pc, image, inp, out, st⟩ =
      exec (code.getD (pc.toNat / 4) .ecall) ⟨x, pc, image, inp, out, st⟩ := by
  obtain rfl | rfl := hw
  · simp only [step, fetch32 _ h h4]
  · simp only [step, fetch64 _ h h4]

/-- Symbolic execution: run a machine whose state is given explicitly, with concrete `pc`. -/
macro "sym_exec" : tactic =>
  `(tactic| simp [run, step_image, code, exec, Machine.setReg, Machine.advance, Machine.fail, alu,
      ecall, Regs.get_set, BranchOp.taken, *])

theorem ofNat_toNat_ne (hw : w = 32 ∨ w = 64) {c d : Char} (h : c ≠ d) :
    BitVec.ofNat w c.toNat ≠ BitVec.ofNat w d.toNat := by
  intro h'
  apply h
  have h' := congrArg BitVec.toNat h'
  have hc : c.toNat < 2 ^ 32 := c.val.toNat_lt
  have hd : d.toNat < 2 ^ 32 := d.val.toNat_lt
  have : c.toNat = d.toNat := by
    obtain rfl | rfl := hw <;> simp only [BitVec.toNat_ofNat] at h' <;> omega
  rw [← Char.ofNat_toNat c, this, Char.ofNat_toNat]

theorem push_newline (s : String) : s.push (Char.ofNat 10) = s ++ "\n" := by
  rfl

/-- One trip round the loop on reading `+`. -/
theorem loop_plus (hw : w = 32 ∨ w = 64) (x : Regs w) (rest : List Char) (out : String) :
    ∃ x' : Regs w, x'.get 5 = x.get 5 + 1 ∧
      run 6 ⟨x, 4, image, '+' :: rest, out, .running⟩ = ⟨x', 4, image, rest, out, .running⟩ := by
  obtain rfl | rfl := hw <;> sym_exec

/-- One trip round the loop on reading `-`. -/
theorem loop_minus (hw : w = 32 ∨ w = 64) (x : Regs w) (rest : List Char) (out : String) :
    ∃ x' : Regs w, x'.get 5 = x.get 5 - 1 ∧
      run 8 ⟨x, 4, image, '-' :: rest, out, .running⟩ = ⟨x', 4, image, rest, out, .running⟩ := by
  obtain rfl | rfl := hw <;> sym_exec <;> bv_omega

/-- Leaving the loop at the end of the input. -/
theorem done_nil (hw : w = 32 ∨ w = 64) (x : Regs w) (out : String) :
    (run 15 ⟨x, 4, image, [], out, .running⟩).status = .exited 0 ∧
      (run 15 ⟨x, 4, image, [], out, .running⟩).output =
        out ++ toString (x.get 5).toInt ++ "\n" := by
  obtain rfl | rfl := hw <;> sym_exec <;> exact push_newline _

/-- Leaving the loop on reading anything other than `+` or `-`. -/
theorem done_cons (hw : w = 32 ∨ w = 64) (x : Regs w) (c : Char) (rest : List Char) (out : String)
    (hp : c ≠ '+') (hm : c ≠ '-') :
    (run 15 ⟨x, 4, image, c :: rest, out, .running⟩).status = .exited 0 ∧
      (run 15 ⟨x, 4, image, c :: rest, out, .running⟩).output =
        out ++ toString (x.get 5).toInt ++ "\n" := by
  have hp : BitVec.ofNat w c.toNat ≠ 43#w := ofNat_toNat_ne hw hp
  have hm : BitVec.ofNat w c.toNat ≠ 45#w := ofNat_toNat_ne hw hm
  obtain rfl | rfl := hw <;> sym_exec <;> exact push_newline _

/-- The number the program should print: over the leading run of `+` and `-` characters, the
count of `+` minus the count of `-`. -/
def tally (input : List Char) : Int :=
  let signs := input.takeWhile fun c => c = '+' ∨ c = '-'
  signs.count '+' - signs.count '-'

theorem tally_plus (rest : List Char) : tally ('+' :: rest) = tally rest + 1 := by
  simp [tally]; omega

theorem tally_minus (rest : List Char) : tally ('-' :: rest) = tally rest - 1 := by
  simp [tally]; omega

theorem tally_other (c : Char) (rest : List Char) (hp : c ≠ '+') (hm : c ≠ '-') :
    tally (c :: rest) = 0 := by
  simp [tally, hp, hm]

theorem tally_bounds (input : List Char) :
    -(input.length : Int) ≤ tally input ∧ tally input ≤ input.length := by
  have hlen := (List.takeWhile_sublist (l := input) fun c => decide (c = '+' ∨ c = '-')).length_le
  have hplus := List.count_le_length (a := '+')
    (l := input.takeWhile fun c => decide (c = '+' ∨ c = '-'))
  have hminus := List.count_le_length (a := '-')
    (l := input.takeWhile fun c => decide (c = '+' ∨ c = '-'))
  simp only [tally]
  omega

/-- From the head of the loop with `t0 = t`, the program prints `t` plus the tally of the
remaining input, then exits. -/
theorem loop_correct (hw : w = 32 ∨ w = 64) (inp : List Char) (x : Regs w) (out : String) :
    ∃ n, (run n ⟨x, 4, image, inp, out, .running⟩).status = .exited 0 ∧
      (run n ⟨x, 4, image, inp, out, .running⟩).output =
        out ++ toString (x.get 5 + BitVec.ofInt w (tally inp)).toInt ++ "\n" := by
  induction inp generalizing x with
  | nil => exact ⟨15, by simpa [tally] using done_nil hw x out⟩
  | cons c rest ih =>
    by_cases hp : c = '+'
    · subst hp
      obtain ⟨x', hx', hrun⟩ := loop_plus hw x rest out
      obtain ⟨n, hn⟩ := ih x'
      refine ⟨6 + n, ?_⟩
      have e : x.get 5 + 1 + BitVec.ofInt w (tally rest) =
          x.get 5 + BitVec.ofInt w (tally rest + 1) := by
        obtain rfl | rfl := hw <;> simp [BitVec.ofInt_add] <;> ac_rfl
      rwa [run_add, hrun, tally_plus, ← e, ← hx']
    by_cases hm : c = '-'
    · subst hm
      obtain ⟨x', hx', hrun⟩ := loop_minus hw x rest out
      obtain ⟨n, hn⟩ := ih x'
      refine ⟨8 + n, ?_⟩
      have e : x.get 5 - 1 + BitVec.ofInt w (tally rest) =
          x.get 5 + BitVec.ofInt w (tally rest - 1) := by
        obtain rfl | rfl := hw <;> simp [Int.sub_eq_add_neg, BitVec.ofInt_add] <;> bv_omega
      rwa [run_add, hrun, tally_minus, ← e, ← hx']
    · exact ⟨15, by simpa [tally_other c rest hp hm] using done_cons hw x c rest out hp hm⟩

/-- **Correctness of `abc101_a.py`.** Loaded into a 256-byte machine and run from address 0, the
program exits with code 0 having printed the tally of its input as a signed `w`-bit number,
followed by a newline. -/
theorem correct (hw : w = 32 ∨ w = 64) (input : List Char) :
    ∃ n, (run n (load w prog 256 input)).status = .exited 0 ∧
      (run n (load w prog 256 input)).output =
        toString (BitVec.ofInt w (tally input)).toInt ++ "\n" := by
  have first : ∃ x' : Regs w, x'.get 5 = 0 ∧
      run 1 (load w prog 256 input) = ⟨x', 4, image, input, "", .running⟩ := by
    have : load w prog 256 input = ⟨⟨Vector.replicate 32 0⟩, 0, image, input, "", .running⟩ := rfl
    rw [this]
    obtain rfl | rfl := hw <;> sym_exec
  obtain ⟨x', hx', hrun⟩ := first
  obtain ⟨n, hn⟩ := loop_correct hw input x' ""
  refine ⟨1 + n, ?_⟩
  rw [run_add, hrun]
  simpa [hx'] using hn

/-- When the input is too short for the tally to overflow, the program prints the tally itself. -/
theorem correct_of_length_lt (hw : w = 32 ∨ w = 64) (input : List Char)
    (h : input.length < 2 ^ 31) :
    ∃ n, (run n (load w prog 256 input)).status = .exited 0 ∧
      (run n (load w prog 256 input)).output = toString (tally input) ++ "\n" := by
  have hb := tally_bounds input
  have e : (BitVec.ofInt w (tally input)).toInt = tally input := by
    rw [BitVec.toInt_ofInt]
    apply Int.bmod_eq_of_le <;> obtain rfl | rfl := hw <;> simp <;> omega
  simpa [e] using correct hw input

end Abc101a

end TinyFive
