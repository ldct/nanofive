import TinyFive.Machine
import TinyFive.SieveMemory

/-!
# Correctness of `decode_percent` from jwerle/url.h

`decode_percent` (url.c) decodes `%XX` escapes of a NUL-terminated string in place and returns
the string, or NULL if a `%` is not followed by two hex digits. url.h uses it on the path, the
fragment and each query key and value. This file proves its 56 words of RV32IM machine code, as
gcc -O2 compiled them into `urlh/url_inspect.elf` at `0x374`, correct on the machine model of
`TinyFive.Machine`. `urlh_test.py` checks that the words in `prog` are the ones in the ELF, and
runs them on nanofive against a Python copy of `decodePercent`.

## What is proven

`decode_percent_correct`: called with `a0 = A` pointing at a NUL-terminated string `s`, the code
returns to `ra` after some number of steps, with:
* every register other than `t1` and `a0`–`a7` unchanged (so `sp`, `ra` and the callee-saved
  registers are preserved, as the calling convention requires);
* memory unchanged outside `s` and its terminator;
* if `decodePercent s = some d`, `a0 = A` and memory at `A` holding `d` and a NUL;
* if `decodePercent s = none`, `a0 = 0`.

`decodePercent` is the specification, a recursive function on byte lists. About it:
* `decodePercent_length`: the output is never longer than the input, which is why decoding in
  place cannot overrun the buffer;
* `decodePercent_of_no_pct`: a string without `%` decodes to itself;
* `decodePercent_encodeAll`: decoding inverts percent-encoding every byte;
* `decodePercent_nul`: `%00` decodes to a NUL byte, so a C caller sees the result cut short
  there (`"%00A"` reads as `""`);
* `decodePercent_bad`: `%` without two hex digits after it gives NULL.

## Hypotheses

The string has no NUL before its terminator (it is a C string), the string and its terminator
lie in memory, memory has at most `2 ^ 32` bytes (so addresses do not wrap), and the string does
not overlap the code (the function writes into it). There is no bound on the length.

## How

`fetch_*` give the effect of each instruction. `dp_run` executes a path symbolically with them;
the lemmas `lit`, `put_cont`, `put_end`, `hi_ok`, `hi_bad`, `lo_ok` and `lo_bad` cover the
straight-line pieces between `loop` and `put`, and `loop` puts them together by induction on the
length of the remaining input. The proofs use no `sorry`, `native_decide` or `bv_decide`
(whose proofs would add axioms): `#print axioms decode_percent_correct` lists only `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace TinyFive.UrlDecode

open SieveMemory

/-- The address of `decode_percent` in `urlh/url_inspect.elf`. -/
def base : Nat := 0x374

/-- The 56 words of `decode_percent` at `base`, as gcc emitted them. -/
def prog : List (BitVec 32) := [
  0x00054783, 0x0c078a63, 0x00150713, 0x00050693, 0x02500813, 0x00900313, 0x00500893,
  0x03078263, 0x00168693, 0x00070613, 0xfef70fa3, 0x0006c783, 0x00170713, 0xfe0794e3,
  0x00060023, 0x00008067, 0x0016c603, 0xfd060793, 0x0ff7f593, 0x06b37463, 0xfbf60793,
  0x0ff7f793, 0x06f8f263, 0xf9f60793, 0x0ff7f793, 0x06f8e663, 0xfa960613, 0x0026c583,
  0xfd058793, 0x0ff7f793, 0x02f37263, 0xfbf58793, 0x0ff7f793, 0x04f8f063, 0xf9f58793,
  0x0ff7f793, 0x04f8e063, 0xfa958593, 0x0ff5f793, 0x00461613, 0x00c787b3, 0x0ff7f793,
  0x00070613, 0x00368693, 0xf79ff06f, 0x00078613, 0xfb5ff06f, 0xfc960613, 0xfadff06f,
  0xfc958593, 0x0ff5f793, 0xfd1ff06f, 0x00000513, 0x00008067, 0x00050613, 0xf5dff06f]

/-- What `prog` decodes to; entry `k` is at address `base + 4 * k`. -/
def code : List Instr := [
  .load .byte false 15 10 0,       -- 374:        lbu  a5, 0(a0)
  .branch .beq 15 0 212,           -- 378:        beqz a5, empty
  .opImm .add 14 10 1,             -- 37c:        addi a4, a0, 1      a4 = out + 1
  .opImm .add 13 10 0,             -- 380:        mv   a3, a0         a3 = in
  .opImm .add 16 0 37,             -- 384:        li   a6, '%'
  .opImm .add 6 0 9,               -- 388:        li   t1, 9
  .opImm .add 17 0 5,              -- 38c:        li   a7, 5
  .branch .beq 15 16 36,           -- 390: loop:  beq  a5, a6, pct
  .opImm .add 13 13 1,             -- 394:        addi a3, a3, 1
  .opImm .add 12 14 0,             -- 398:        mv   a2, a4
  .store .byte 15 14 (-1),         -- 39c: put:   sb   a5, -1(a4)     *out = a5
  .load .byte false 15 13 0,       -- 3a0:        lbu  a5, 0(a3)
  .opImm .add 14 14 1,             -- 3a4:        addi a4, a4, 1
  .branch .bne 15 0 (-24),         -- 3a8:        bnez a5, loop
  .store .byte 0 12 0,             -- 3ac: end:   sb   zero, 0(a2)
  .jalr 0 1 0,                     -- 3b0:        ret                 (a0 = s)
  .load .byte false 12 13 1,       -- 3b4: pct:   lbu  a2, 1(a3)      high digit
  .opImm .add 15 12 (-48),         -- 3b8:        addi a5, a2, -'0'
  .opImm .and 11 15 255,           -- 3bc:        zext.b a1, a5
  .branch .bgeu 6 11 104,          -- 3c0:        bgeu t1, a1, hi09
  .opImm .add 15 12 (-65),         -- 3c4:        addi a5, a2, -'A'
  .opImm .and 15 15 255,           -- 3c8:        zext.b a5, a5
  .branch .bgeu 17 15 100,         -- 3cc:        bgeu a7, a5, hiAF
  .opImm .add 15 12 (-97),         -- 3d0:        addi a5, a2, -'a'
  .opImm .and 15 15 255,           -- 3d4:        zext.b a5, a5
  .branch .bltu 17 15 108,         -- 3d8:        bltu a7, a5, fail
  .opImm .add 12 12 (-87),         -- 3dc:        addi a2, a2, -('a' - 10)
  .load .byte false 11 13 2,       -- 3e0: lo:    lbu  a1, 2(a3)      low digit
  .opImm .add 15 11 (-48),         -- 3e4:        addi a5, a1, -'0'
  .opImm .and 15 15 255,           -- 3e8:        zext.b a5, a5
  .branch .bgeu 6 15 36,           -- 3ec:        bgeu t1, a5, comb
  .opImm .add 15 11 (-65),         -- 3f0:        addi a5, a1, -'A'
  .opImm .and 15 15 255,           -- 3f4:        zext.b a5, a5
  .branch .bgeu 17 15 64,          -- 3f8:        bgeu a7, a5, loAF
  .opImm .add 15 11 (-97),         -- 3fc:        addi a5, a1, -'a'
  .opImm .and 15 15 255,           -- 400:        zext.b a5, a5
  .branch .bltu 17 15 64,          -- 404:        bltu a7, a5, fail
  .opImm .add 11 11 (-87),         -- 408:        addi a1, a1, -('a' - 10)
  .opImm .and 15 11 255,           -- 40c:        zext.b a5, a1
  .opImm .sll 12 12 4,             -- 410: comb:  slli a2, a2, 4
  .op .add 15 15 12,               -- 414:        add  a5, a5, a2
  .opImm .and 15 15 255,           -- 418:        zext.b a5, a5
  .opImm .add 12 14 0,             -- 41c:        mv   a2, a4
  .opImm .add 13 13 3,             -- 420:        addi a3, a3, 3
  .jal 0 (-136),                   -- 424:        j    put
  .opImm .add 12 15 0,             -- 428: hi09:  mv   a2, a5
  .jal 0 (-76),                    -- 42c:        j    lo
  .opImm .add 12 12 (-55),         -- 430: hiAF:  addi a2, a2, -('A' - 10)
  .jal 0 (-84),                    -- 434:        j    lo
  .opImm .add 11 11 (-55),         -- 438: loAF:  addi a1, a1, -('A' - 10)
  .opImm .and 15 11 255,           -- 43c:        zext.b a5, a1
  .jal 0 (-48),                    -- 440:        j    comb
  .opImm .add 10 0 0,              -- 444: fail:  li   a0, 0
  .jalr 0 1 0,                     -- 448:        ret                 (NULL)
  .opImm .add 12 10 0,             -- 44c: empty: mv   a2, a0
  .jal 0 (-164)]                   -- 450:        j    end

theorem decode_prog : ∀ k, k < 56 → decode 32 (prog.getD k 0) = some (code.getD k .ecall) := by
  decide +kernel

/-- `decode_percent`'s code is at `base` in `mem`. -/
def CodeAt (mem : Array (BitVec 8)) : Prop :=
  ∀ k, k < 56 → readBytes mem (base + 4 * k) 4 = some (prog.getD k 0)

theorem CodeAt.set {mem : Array (BitVec 8)} (h : CodeAt mem) {q : Nat} (v : BitVec 8)
    (hq : q < base ∨ base + 224 ≤ q) : CodeAt (mem.setIfInBounds q v) := by
  intro k hk
  rw [readBytes_update_disjoint _ _ _ _ _ (by omega)]
  exact h k hk

theorem step_code (x : Regs 32) (pc : BitVec 32) (mem : Array (BitVec 8)) (inp : List Char)
    (out : String) (st : Status) (hc : CodeAt mem)
    (h1 : base ≤ pc.toNat) (h2 : pc.toNat < base + 224) (h3 : pc.toNat % 4 = 0) :
    step ⟨x, pc, mem, inp, out, st⟩ =
      exec (code.getD ((pc.toNat - base) / 4) .ecall) ⟨x, pc, mem, inp, out, st⟩ := by
  have e : base + 4 * ((pc.toNat - base) / 4) = pc.toNat := by unfold base at *; omega
  have hr := hc ((pc.toNat - base) / 4) (by unfold base at *; omega)
  rw [e] at hr
  have hk : (pc.toNat - base) / 4 < 56 := by unfold base at *; omega
  simp only [step, hr, Option.bind_some, decode_prog _ hk]


/-! ## One step lemma per instruction address

Each states the effect of the instruction at that address with its immediate already sign-extended
and its branch target computed. They are proved from the generic lemmas below, whose immediates
are variables: unfolding `exec` on an instruction with a concrete negative immediate makes the
kernel check expensive. -/

theorem step_code' {x : Regs 32} {pc : BitVec 32} {mem : Array (BitVec 8)} {inp : List Char}
    {out : String} {st : Status} (hc : CodeAt mem)
    (h : base ≤ pc.toNat ∧ pc.toNat < base + 224 ∧ pc.toNat % 4 = 0) :
    step ⟨x, pc, mem, inp, out, st⟩ =
      exec (code.getD ((pc.toNat - base) / 4) .ecall) ⟨x, pc, mem, inp, out, st⟩ :=
  step_code x pc mem inp out st hc h.1 h.2.1 h.2.2

section
variable (x : Regs 32) (pc : BitVec 32) (mem : Array (BitVec 8)) (i : List Char) (o : String)

theorem exec_opImm (op : AluOp) (rd rs1 : Reg) (imm : BitVec 12) :
    exec (.opImm op rd rs1 imm) ⟨x, pc, mem, i, o, .running⟩ =
      ⟨x.set rd (alu op (x.get rs1) (imm.signExtend 32)), pc + 4, mem, i, o, .running⟩ := rfl

theorem exec_op (rd rs1 rs2 : Reg) :
    exec (.op .add rd rs1 rs2) ⟨x, pc, mem, i, o, .running⟩ =
      ⟨x.set rd (x.get rs1 + x.get rs2), pc + 4, mem, i, o, .running⟩ := rfl

theorem exec_lbu (rd rs1 : Reg) (imm : BitVec 12) :
    exec (.load .byte false rd rs1 imm) ⟨x, pc, mem, i, o, .running⟩ =
      match readBytes mem (x.get rs1 + imm.signExtend 32).toNat 1 with
      | some v => ⟨x.set rd (v.setWidth 32), pc + 4, mem, i, o, .running⟩
      | none => ⟨x, pc, mem, i, o, .fault⟩ := by
  simp only [exec, Width.bytes, Machine.setReg, Machine.advance, Machine.fail]
  split <;> simp_all

theorem exec_sb (rs2 rs1 : Reg) (imm : BitVec 12) :
    exec (.store .byte rs2 rs1 imm) ⟨x, pc, mem, i, o, .running⟩ =
      match writeBytes mem (x.get rs1 + imm.signExtend 32).toNat (x.get rs2) 1 with
      | some mem' => ⟨x, pc + 4, mem', i, o, .running⟩
      | none => ⟨x, pc, mem, i, o, .fault⟩ := rfl

theorem exec_branch (op : BranchOp) (rs1 rs2 : Reg) (imm : BitVec 13) :
    exec (.branch op rs1 rs2 imm) ⟨x, pc, mem, i, o, .running⟩ =
      if op.taken (x.get rs1) (x.get rs2) then ⟨x, pc + imm.signExtend 32, mem, i, o, .running⟩
      else ⟨x, pc + 4, mem, i, o, .running⟩ := rfl

theorem exec_jal (rd : Reg) (imm : BitVec 21) :
    exec (.jal rd imm) ⟨x, pc, mem, i, o, .running⟩ =
      ⟨x.set rd (pc + 4), pc + imm.signExtend 32, mem, i, o, .running⟩ := rfl

theorem exec_jalr (rd rs1 : Reg) (imm : BitVec 12) :
    exec (.jalr rd rs1 imm) ⟨x, pc, mem, i, o, .running⟩ =
      ⟨x.set rd (pc + 4), (x.get rs1 + imm.signExtend 32) &&& ~~~1, mem, i, o, .running⟩ := rfl

end

theorem fetch_374 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 884#32, mem, inp, out, .running⟩ =
      match readBytes mem (x.get 10 + 0#32).toNat 1 with
      | some v => ⟨x.set 15 (v.setWidth 32), 888#32, mem, inp, out, .running⟩
      | none => ⟨x, 884#32, mem, inp, out, .fault⟩ := by
  rw [step_code' hc (by decide), show (((884#32 : BitVec 32)).toNat - base) / 4 = 0 by decide,
    show code.getD 0 .ecall = (.load .byte false 15 10 0) by decide, exec_lbu, show BitVec.signExtend 32 (0 : BitVec 12) = 0#32 by decide,
    show (884#32 : BitVec 32) + 4 = 888#32 by decide]
  all_goals rfl

theorem fetch_378 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 888#32, mem, inp, out, .running⟩ =
      if BranchOp.taken .beq (x.get 15) (x.get 0) then ⟨x, 1100#32, mem, inp, out, .running⟩
      else ⟨x, 892#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((888#32 : BitVec 32)).toNat - base) / 4 = 1 by decide,
    show code.getD 1 .ecall = (.branch .beq 15 0 212) by decide, exec_branch, show (888#32 : BitVec 32) + BitVec.signExtend 32 (212 : BitVec 13) = 1100#32 by decide,
    show (888#32 : BitVec 32) + 4 = 892#32 by decide]
  all_goals rfl

theorem fetch_37c {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 892#32, mem, inp, out, .running⟩ =
      ⟨x.set 14 (x.get 10 + 1#32), 896#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((892#32 : BitVec 32)).toNat - base) / 4 = 2 by decide,
    show code.getD 2 .ecall = (.opImm .add 14 10 1) by decide, exec_opImm, show BitVec.signExtend 32 (1 : BitVec 12) = 1#32 by decide,
    show (892#32 : BitVec 32) + 4 = 896#32 by decide]
  all_goals rfl

theorem fetch_380 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 896#32, mem, inp, out, .running⟩ =
      ⟨x.set 13 (x.get 10 + 0#32), 900#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((896#32 : BitVec 32)).toNat - base) / 4 = 3 by decide,
    show code.getD 3 .ecall = (.opImm .add 13 10 0) by decide, exec_opImm, show BitVec.signExtend 32 (0 : BitVec 12) = 0#32 by decide,
    show (896#32 : BitVec 32) + 4 = 900#32 by decide]
  all_goals rfl

theorem fetch_384 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 900#32, mem, inp, out, .running⟩ =
      ⟨x.set 16 (x.get 0 + 37#32), 904#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((900#32 : BitVec 32)).toNat - base) / 4 = 4 by decide,
    show code.getD 4 .ecall = (.opImm .add 16 0 37) by decide, exec_opImm, show BitVec.signExtend 32 (37 : BitVec 12) = 37#32 by decide,
    show (900#32 : BitVec 32) + 4 = 904#32 by decide]
  all_goals rfl

theorem fetch_388 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 904#32, mem, inp, out, .running⟩ =
      ⟨x.set 6 (x.get 0 + 9#32), 908#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((904#32 : BitVec 32)).toNat - base) / 4 = 5 by decide,
    show code.getD 5 .ecall = (.opImm .add 6 0 9) by decide, exec_opImm, show BitVec.signExtend 32 (9 : BitVec 12) = 9#32 by decide,
    show (904#32 : BitVec 32) + 4 = 908#32 by decide]
  all_goals rfl

theorem fetch_38c {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 908#32, mem, inp, out, .running⟩ =
      ⟨x.set 17 (x.get 0 + 5#32), 912#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((908#32 : BitVec 32)).toNat - base) / 4 = 6 by decide,
    show code.getD 6 .ecall = (.opImm .add 17 0 5) by decide, exec_opImm, show BitVec.signExtend 32 (5 : BitVec 12) = 5#32 by decide,
    show (908#32 : BitVec 32) + 4 = 912#32 by decide]
  all_goals rfl

theorem fetch_390 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 912#32, mem, inp, out, .running⟩ =
      if BranchOp.taken .beq (x.get 15) (x.get 16) then ⟨x, 948#32, mem, inp, out, .running⟩
      else ⟨x, 916#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((912#32 : BitVec 32)).toNat - base) / 4 = 7 by decide,
    show code.getD 7 .ecall = (.branch .beq 15 16 36) by decide, exec_branch, show (912#32 : BitVec 32) + BitVec.signExtend 32 (36 : BitVec 13) = 948#32 by decide,
    show (912#32 : BitVec 32) + 4 = 916#32 by decide]
  all_goals rfl

theorem fetch_394 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 916#32, mem, inp, out, .running⟩ =
      ⟨x.set 13 (x.get 13 + 1#32), 920#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((916#32 : BitVec 32)).toNat - base) / 4 = 8 by decide,
    show code.getD 8 .ecall = (.opImm .add 13 13 1) by decide, exec_opImm, show BitVec.signExtend 32 (1 : BitVec 12) = 1#32 by decide,
    show (916#32 : BitVec 32) + 4 = 920#32 by decide]
  all_goals rfl

theorem fetch_398 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 920#32, mem, inp, out, .running⟩ =
      ⟨x.set 12 (x.get 14 + 0#32), 924#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((920#32 : BitVec 32)).toNat - base) / 4 = 9 by decide,
    show code.getD 9 .ecall = (.opImm .add 12 14 0) by decide, exec_opImm, show BitVec.signExtend 32 (0 : BitVec 12) = 0#32 by decide,
    show (920#32 : BitVec 32) + 4 = 924#32 by decide]
  all_goals rfl

theorem fetch_39c {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 924#32, mem, inp, out, .running⟩ =
      match writeBytes mem (x.get 14 + 4294967295#32).toNat (x.get 15) 1 with
      | some mem' => ⟨x, 928#32, mem', inp, out, .running⟩
      | none => ⟨x, 924#32, mem, inp, out, .fault⟩ := by
  rw [step_code' hc (by decide), show (((924#32 : BitVec 32)).toNat - base) / 4 = 10 by decide,
    show code.getD 10 .ecall = (.store .byte 15 14 (-1)) by decide, exec_sb, show BitVec.signExtend 32 ((-1) : BitVec 12) = 4294967295#32 by decide,
    show (924#32 : BitVec 32) + 4 = 928#32 by decide]
  all_goals rfl

theorem fetch_3a0 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 928#32, mem, inp, out, .running⟩ =
      match readBytes mem (x.get 13 + 0#32).toNat 1 with
      | some v => ⟨x.set 15 (v.setWidth 32), 932#32, mem, inp, out, .running⟩
      | none => ⟨x, 928#32, mem, inp, out, .fault⟩ := by
  rw [step_code' hc (by decide), show (((928#32 : BitVec 32)).toNat - base) / 4 = 11 by decide,
    show code.getD 11 .ecall = (.load .byte false 15 13 0) by decide, exec_lbu, show BitVec.signExtend 32 (0 : BitVec 12) = 0#32 by decide,
    show (928#32 : BitVec 32) + 4 = 932#32 by decide]
  all_goals rfl

theorem fetch_3a4 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 932#32, mem, inp, out, .running⟩ =
      ⟨x.set 14 (x.get 14 + 1#32), 936#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((932#32 : BitVec 32)).toNat - base) / 4 = 12 by decide,
    show code.getD 12 .ecall = (.opImm .add 14 14 1) by decide, exec_opImm, show BitVec.signExtend 32 (1 : BitVec 12) = 1#32 by decide,
    show (932#32 : BitVec 32) + 4 = 936#32 by decide]
  all_goals rfl

theorem fetch_3a8 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 936#32, mem, inp, out, .running⟩ =
      if BranchOp.taken .bne (x.get 15) (x.get 0) then ⟨x, 912#32, mem, inp, out, .running⟩
      else ⟨x, 940#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((936#32 : BitVec 32)).toNat - base) / 4 = 13 by decide,
    show code.getD 13 .ecall = (.branch .bne 15 0 (-24)) by decide, exec_branch, show (936#32 : BitVec 32) + BitVec.signExtend 32 ((-24) : BitVec 13) = 912#32 by decide,
    show (936#32 : BitVec 32) + 4 = 940#32 by decide]
  all_goals rfl

theorem fetch_3ac {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 940#32, mem, inp, out, .running⟩ =
      match writeBytes mem (x.get 12 + 0#32).toNat (x.get 0) 1 with
      | some mem' => ⟨x, 944#32, mem', inp, out, .running⟩
      | none => ⟨x, 940#32, mem, inp, out, .fault⟩ := by
  rw [step_code' hc (by decide), show (((940#32 : BitVec 32)).toNat - base) / 4 = 14 by decide,
    show code.getD 14 .ecall = (.store .byte 0 12 0) by decide, exec_sb, show BitVec.signExtend 32 (0 : BitVec 12) = 0#32 by decide,
    show (940#32 : BitVec 32) + 4 = 944#32 by decide]
  all_goals rfl

theorem fetch_3b0 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 944#32, mem, inp, out, .running⟩ =
      ⟨x.set 0 948#32, x.get 1 &&& 4294967294#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((944#32 : BitVec 32)).toNat - base) / 4 = 15 by decide,
    show code.getD 15 .ecall = (.jalr 0 1 0) by decide, exec_jalr, show (944#32 : BitVec 32) + 4 = 948#32 by decide,
    show (x.get 1 + BitVec.signExtend 32 (0 : BitVec 12)) &&& ~~~1 = x.get 1 &&& 4294967294#32 by rw [show BitVec.signExtend 32 (0 : BitVec 12) = 0#32 by decide, BitVec.add_zero]; rfl]
  all_goals rfl

theorem fetch_3b4 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 948#32, mem, inp, out, .running⟩ =
      match readBytes mem (x.get 13 + 1#32).toNat 1 with
      | some v => ⟨x.set 12 (v.setWidth 32), 952#32, mem, inp, out, .running⟩
      | none => ⟨x, 948#32, mem, inp, out, .fault⟩ := by
  rw [step_code' hc (by decide), show (((948#32 : BitVec 32)).toNat - base) / 4 = 16 by decide,
    show code.getD 16 .ecall = (.load .byte false 12 13 1) by decide, exec_lbu, show BitVec.signExtend 32 (1 : BitVec 12) = 1#32 by decide,
    show (948#32 : BitVec 32) + 4 = 952#32 by decide]
  all_goals rfl

theorem fetch_3b8 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 952#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 12 + 4294967248#32), 956#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((952#32 : BitVec 32)).toNat - base) / 4 = 17 by decide,
    show code.getD 17 .ecall = (.opImm .add 15 12 (-48)) by decide, exec_opImm, show BitVec.signExtend 32 ((-48) : BitVec 12) = 4294967248#32 by decide,
    show (952#32 : BitVec 32) + 4 = 956#32 by decide]
  all_goals rfl

theorem fetch_3bc {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 956#32, mem, inp, out, .running⟩ =
      ⟨x.set 11 (x.get 15 &&& 255#32), 960#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((956#32 : BitVec 32)).toNat - base) / 4 = 18 by decide,
    show code.getD 18 .ecall = (.opImm .and 11 15 255) by decide, exec_opImm, show BitVec.signExtend 32 (255 : BitVec 12) = 255#32 by decide,
    show (956#32 : BitVec 32) + 4 = 960#32 by decide]
  all_goals rfl

theorem fetch_3c0 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 960#32, mem, inp, out, .running⟩ =
      if BranchOp.taken .bgeu (x.get 6) (x.get 11) then ⟨x, 1064#32, mem, inp, out, .running⟩
      else ⟨x, 964#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((960#32 : BitVec 32)).toNat - base) / 4 = 19 by decide,
    show code.getD 19 .ecall = (.branch .bgeu 6 11 104) by decide, exec_branch, show (960#32 : BitVec 32) + BitVec.signExtend 32 (104 : BitVec 13) = 1064#32 by decide,
    show (960#32 : BitVec 32) + 4 = 964#32 by decide]
  all_goals rfl

theorem fetch_3c4 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 964#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 12 + 4294967231#32), 968#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((964#32 : BitVec 32)).toNat - base) / 4 = 20 by decide,
    show code.getD 20 .ecall = (.opImm .add 15 12 (-65)) by decide, exec_opImm, show BitVec.signExtend 32 ((-65) : BitVec 12) = 4294967231#32 by decide,
    show (964#32 : BitVec 32) + 4 = 968#32 by decide]
  all_goals rfl

theorem fetch_3c8 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 968#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 15 &&& 255#32), 972#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((968#32 : BitVec 32)).toNat - base) / 4 = 21 by decide,
    show code.getD 21 .ecall = (.opImm .and 15 15 255) by decide, exec_opImm, show BitVec.signExtend 32 (255 : BitVec 12) = 255#32 by decide,
    show (968#32 : BitVec 32) + 4 = 972#32 by decide]
  all_goals rfl

theorem fetch_3cc {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 972#32, mem, inp, out, .running⟩ =
      if BranchOp.taken .bgeu (x.get 17) (x.get 15) then ⟨x, 1072#32, mem, inp, out, .running⟩
      else ⟨x, 976#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((972#32 : BitVec 32)).toNat - base) / 4 = 22 by decide,
    show code.getD 22 .ecall = (.branch .bgeu 17 15 100) by decide, exec_branch, show (972#32 : BitVec 32) + BitVec.signExtend 32 (100 : BitVec 13) = 1072#32 by decide,
    show (972#32 : BitVec 32) + 4 = 976#32 by decide]
  all_goals rfl

theorem fetch_3d0 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 976#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 12 + 4294967199#32), 980#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((976#32 : BitVec 32)).toNat - base) / 4 = 23 by decide,
    show code.getD 23 .ecall = (.opImm .add 15 12 (-97)) by decide, exec_opImm, show BitVec.signExtend 32 ((-97) : BitVec 12) = 4294967199#32 by decide,
    show (976#32 : BitVec 32) + 4 = 980#32 by decide]
  all_goals rfl

theorem fetch_3d4 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 980#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 15 &&& 255#32), 984#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((980#32 : BitVec 32)).toNat - base) / 4 = 24 by decide,
    show code.getD 24 .ecall = (.opImm .and 15 15 255) by decide, exec_opImm, show BitVec.signExtend 32 (255 : BitVec 12) = 255#32 by decide,
    show (980#32 : BitVec 32) + 4 = 984#32 by decide]
  all_goals rfl

theorem fetch_3d8 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 984#32, mem, inp, out, .running⟩ =
      if BranchOp.taken .bltu (x.get 17) (x.get 15) then ⟨x, 1092#32, mem, inp, out, .running⟩
      else ⟨x, 988#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((984#32 : BitVec 32)).toNat - base) / 4 = 25 by decide,
    show code.getD 25 .ecall = (.branch .bltu 17 15 108) by decide, exec_branch, show (984#32 : BitVec 32) + BitVec.signExtend 32 (108 : BitVec 13) = 1092#32 by decide,
    show (984#32 : BitVec 32) + 4 = 988#32 by decide]
  all_goals rfl

theorem fetch_3dc {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 988#32, mem, inp, out, .running⟩ =
      ⟨x.set 12 (x.get 12 + 4294967209#32), 992#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((988#32 : BitVec 32)).toNat - base) / 4 = 26 by decide,
    show code.getD 26 .ecall = (.opImm .add 12 12 (-87)) by decide, exec_opImm, show BitVec.signExtend 32 ((-87) : BitVec 12) = 4294967209#32 by decide,
    show (988#32 : BitVec 32) + 4 = 992#32 by decide]
  all_goals rfl

theorem fetch_3e0 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 992#32, mem, inp, out, .running⟩ =
      match readBytes mem (x.get 13 + 2#32).toNat 1 with
      | some v => ⟨x.set 11 (v.setWidth 32), 996#32, mem, inp, out, .running⟩
      | none => ⟨x, 992#32, mem, inp, out, .fault⟩ := by
  rw [step_code' hc (by decide), show (((992#32 : BitVec 32)).toNat - base) / 4 = 27 by decide,
    show code.getD 27 .ecall = (.load .byte false 11 13 2) by decide, exec_lbu, show BitVec.signExtend 32 (2 : BitVec 12) = 2#32 by decide,
    show (992#32 : BitVec 32) + 4 = 996#32 by decide]
  all_goals rfl

theorem fetch_3e4 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 996#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 11 + 4294967248#32), 1000#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((996#32 : BitVec 32)).toNat - base) / 4 = 28 by decide,
    show code.getD 28 .ecall = (.opImm .add 15 11 (-48)) by decide, exec_opImm, show BitVec.signExtend 32 ((-48) : BitVec 12) = 4294967248#32 by decide,
    show (996#32 : BitVec 32) + 4 = 1000#32 by decide]
  all_goals rfl

theorem fetch_3e8 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1000#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 15 &&& 255#32), 1004#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1000#32 : BitVec 32)).toNat - base) / 4 = 29 by decide,
    show code.getD 29 .ecall = (.opImm .and 15 15 255) by decide, exec_opImm, show BitVec.signExtend 32 (255 : BitVec 12) = 255#32 by decide,
    show (1000#32 : BitVec 32) + 4 = 1004#32 by decide]
  all_goals rfl

theorem fetch_3ec {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1004#32, mem, inp, out, .running⟩ =
      if BranchOp.taken .bgeu (x.get 6) (x.get 15) then ⟨x, 1040#32, mem, inp, out, .running⟩
      else ⟨x, 1008#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1004#32 : BitVec 32)).toNat - base) / 4 = 30 by decide,
    show code.getD 30 .ecall = (.branch .bgeu 6 15 36) by decide, exec_branch, show (1004#32 : BitVec 32) + BitVec.signExtend 32 (36 : BitVec 13) = 1040#32 by decide,
    show (1004#32 : BitVec 32) + 4 = 1008#32 by decide]
  all_goals rfl

theorem fetch_3f0 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1008#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 11 + 4294967231#32), 1012#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1008#32 : BitVec 32)).toNat - base) / 4 = 31 by decide,
    show code.getD 31 .ecall = (.opImm .add 15 11 (-65)) by decide, exec_opImm, show BitVec.signExtend 32 ((-65) : BitVec 12) = 4294967231#32 by decide,
    show (1008#32 : BitVec 32) + 4 = 1012#32 by decide]
  all_goals rfl

theorem fetch_3f4 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1012#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 15 &&& 255#32), 1016#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1012#32 : BitVec 32)).toNat - base) / 4 = 32 by decide,
    show code.getD 32 .ecall = (.opImm .and 15 15 255) by decide, exec_opImm, show BitVec.signExtend 32 (255 : BitVec 12) = 255#32 by decide,
    show (1012#32 : BitVec 32) + 4 = 1016#32 by decide]
  all_goals rfl

theorem fetch_3f8 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1016#32, mem, inp, out, .running⟩ =
      if BranchOp.taken .bgeu (x.get 17) (x.get 15) then ⟨x, 1080#32, mem, inp, out, .running⟩
      else ⟨x, 1020#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1016#32 : BitVec 32)).toNat - base) / 4 = 33 by decide,
    show code.getD 33 .ecall = (.branch .bgeu 17 15 64) by decide, exec_branch, show (1016#32 : BitVec 32) + BitVec.signExtend 32 (64 : BitVec 13) = 1080#32 by decide,
    show (1016#32 : BitVec 32) + 4 = 1020#32 by decide]
  all_goals rfl

theorem fetch_3fc {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1020#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 11 + 4294967199#32), 1024#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1020#32 : BitVec 32)).toNat - base) / 4 = 34 by decide,
    show code.getD 34 .ecall = (.opImm .add 15 11 (-97)) by decide, exec_opImm, show BitVec.signExtend 32 ((-97) : BitVec 12) = 4294967199#32 by decide,
    show (1020#32 : BitVec 32) + 4 = 1024#32 by decide]
  all_goals rfl

theorem fetch_400 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1024#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 15 &&& 255#32), 1028#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1024#32 : BitVec 32)).toNat - base) / 4 = 35 by decide,
    show code.getD 35 .ecall = (.opImm .and 15 15 255) by decide, exec_opImm, show BitVec.signExtend 32 (255 : BitVec 12) = 255#32 by decide,
    show (1024#32 : BitVec 32) + 4 = 1028#32 by decide]
  all_goals rfl

theorem fetch_404 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1028#32, mem, inp, out, .running⟩ =
      if BranchOp.taken .bltu (x.get 17) (x.get 15) then ⟨x, 1092#32, mem, inp, out, .running⟩
      else ⟨x, 1032#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1028#32 : BitVec 32)).toNat - base) / 4 = 36 by decide,
    show code.getD 36 .ecall = (.branch .bltu 17 15 64) by decide, exec_branch, show (1028#32 : BitVec 32) + BitVec.signExtend 32 (64 : BitVec 13) = 1092#32 by decide,
    show (1028#32 : BitVec 32) + 4 = 1032#32 by decide]
  all_goals rfl

theorem fetch_408 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1032#32, mem, inp, out, .running⟩ =
      ⟨x.set 11 (x.get 11 + 4294967209#32), 1036#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1032#32 : BitVec 32)).toNat - base) / 4 = 37 by decide,
    show code.getD 37 .ecall = (.opImm .add 11 11 (-87)) by decide, exec_opImm, show BitVec.signExtend 32 ((-87) : BitVec 12) = 4294967209#32 by decide,
    show (1032#32 : BitVec 32) + 4 = 1036#32 by decide]
  all_goals rfl

theorem fetch_40c {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1036#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 11 &&& 255#32), 1040#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1036#32 : BitVec 32)).toNat - base) / 4 = 38 by decide,
    show code.getD 38 .ecall = (.opImm .and 15 11 255) by decide, exec_opImm, show BitVec.signExtend 32 (255 : BitVec 12) = 255#32 by decide,
    show (1036#32 : BitVec 32) + 4 = 1040#32 by decide]
  all_goals rfl

theorem fetch_410 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1040#32, mem, inp, out, .running⟩ =
      ⟨x.set 12 (x.get 12 <<< 4), 1044#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1040#32 : BitVec 32)).toNat - base) / 4 = 39 by decide,
    show code.getD 39 .ecall = (.opImm .sll 12 12 4) by decide, exec_opImm,
    show BitVec.signExtend 32 (4 : BitVec 12) = 4#32 by decide, show (1040#32 : BitVec 32) + 4 = 1044#32 by decide]
  all_goals rfl

theorem fetch_414 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1044#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 15 + x.get 12), 1048#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1044#32 : BitVec 32)).toNat - base) / 4 = 40 by decide,
    show code.getD 40 .ecall = (.op .add 15 15 12) by decide, exec_op, show (1044#32 : BitVec 32) + 4 = 1048#32 by decide]
  all_goals rfl

theorem fetch_418 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1048#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 15 &&& 255#32), 1052#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1048#32 : BitVec 32)).toNat - base) / 4 = 41 by decide,
    show code.getD 41 .ecall = (.opImm .and 15 15 255) by decide, exec_opImm, show BitVec.signExtend 32 (255 : BitVec 12) = 255#32 by decide,
    show (1048#32 : BitVec 32) + 4 = 1052#32 by decide]
  all_goals rfl

theorem fetch_41c {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1052#32, mem, inp, out, .running⟩ =
      ⟨x.set 12 (x.get 14 + 0#32), 1056#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1052#32 : BitVec 32)).toNat - base) / 4 = 42 by decide,
    show code.getD 42 .ecall = (.opImm .add 12 14 0) by decide, exec_opImm, show BitVec.signExtend 32 (0 : BitVec 12) = 0#32 by decide,
    show (1052#32 : BitVec 32) + 4 = 1056#32 by decide]
  all_goals rfl

theorem fetch_420 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1056#32, mem, inp, out, .running⟩ =
      ⟨x.set 13 (x.get 13 + 3#32), 1060#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1056#32 : BitVec 32)).toNat - base) / 4 = 43 by decide,
    show code.getD 43 .ecall = (.opImm .add 13 13 3) by decide, exec_opImm, show BitVec.signExtend 32 (3 : BitVec 12) = 3#32 by decide,
    show (1056#32 : BitVec 32) + 4 = 1060#32 by decide]
  all_goals rfl

theorem fetch_424 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1060#32, mem, inp, out, .running⟩ =
      ⟨x.set 0 1064#32, 924#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1060#32 : BitVec 32)).toNat - base) / 4 = 44 by decide,
    show code.getD 44 .ecall = (.jal 0 (-136)) by decide, exec_jal, show (1060#32 : BitVec 32) + BitVec.signExtend 32 ((-136) : BitVec 21) = 924#32 by decide,
    show (1060#32 : BitVec 32) + 4 = 1064#32 by decide]
  all_goals rfl

theorem fetch_428 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1064#32, mem, inp, out, .running⟩ =
      ⟨x.set 12 (x.get 15 + 0#32), 1068#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1064#32 : BitVec 32)).toNat - base) / 4 = 45 by decide,
    show code.getD 45 .ecall = (.opImm .add 12 15 0) by decide, exec_opImm, show BitVec.signExtend 32 (0 : BitVec 12) = 0#32 by decide,
    show (1064#32 : BitVec 32) + 4 = 1068#32 by decide]
  all_goals rfl

theorem fetch_42c {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1068#32, mem, inp, out, .running⟩ =
      ⟨x.set 0 1072#32, 992#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1068#32 : BitVec 32)).toNat - base) / 4 = 46 by decide,
    show code.getD 46 .ecall = (.jal 0 (-76)) by decide, exec_jal, show (1068#32 : BitVec 32) + BitVec.signExtend 32 ((-76) : BitVec 21) = 992#32 by decide,
    show (1068#32 : BitVec 32) + 4 = 1072#32 by decide]
  all_goals rfl

theorem fetch_430 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1072#32, mem, inp, out, .running⟩ =
      ⟨x.set 12 (x.get 12 + 4294967241#32), 1076#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1072#32 : BitVec 32)).toNat - base) / 4 = 47 by decide,
    show code.getD 47 .ecall = (.opImm .add 12 12 (-55)) by decide, exec_opImm, show BitVec.signExtend 32 ((-55) : BitVec 12) = 4294967241#32 by decide,
    show (1072#32 : BitVec 32) + 4 = 1076#32 by decide]
  all_goals rfl

theorem fetch_434 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1076#32, mem, inp, out, .running⟩ =
      ⟨x.set 0 1080#32, 992#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1076#32 : BitVec 32)).toNat - base) / 4 = 48 by decide,
    show code.getD 48 .ecall = (.jal 0 (-84)) by decide, exec_jal, show (1076#32 : BitVec 32) + BitVec.signExtend 32 ((-84) : BitVec 21) = 992#32 by decide,
    show (1076#32 : BitVec 32) + 4 = 1080#32 by decide]
  all_goals rfl

theorem fetch_438 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1080#32, mem, inp, out, .running⟩ =
      ⟨x.set 11 (x.get 11 + 4294967241#32), 1084#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1080#32 : BitVec 32)).toNat - base) / 4 = 49 by decide,
    show code.getD 49 .ecall = (.opImm .add 11 11 (-55)) by decide, exec_opImm, show BitVec.signExtend 32 ((-55) : BitVec 12) = 4294967241#32 by decide,
    show (1080#32 : BitVec 32) + 4 = 1084#32 by decide]
  all_goals rfl

theorem fetch_43c {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1084#32, mem, inp, out, .running⟩ =
      ⟨x.set 15 (x.get 11 &&& 255#32), 1088#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1084#32 : BitVec 32)).toNat - base) / 4 = 50 by decide,
    show code.getD 50 .ecall = (.opImm .and 15 11 255) by decide, exec_opImm, show BitVec.signExtend 32 (255 : BitVec 12) = 255#32 by decide,
    show (1084#32 : BitVec 32) + 4 = 1088#32 by decide]
  all_goals rfl

theorem fetch_440 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1088#32, mem, inp, out, .running⟩ =
      ⟨x.set 0 1092#32, 1040#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1088#32 : BitVec 32)).toNat - base) / 4 = 51 by decide,
    show code.getD 51 .ecall = (.jal 0 (-48)) by decide, exec_jal, show (1088#32 : BitVec 32) + BitVec.signExtend 32 ((-48) : BitVec 21) = 1040#32 by decide,
    show (1088#32 : BitVec 32) + 4 = 1092#32 by decide]
  all_goals rfl

theorem fetch_444 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1092#32, mem, inp, out, .running⟩ =
      ⟨x.set 10 (x.get 0 + 0#32), 1096#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1092#32 : BitVec 32)).toNat - base) / 4 = 52 by decide,
    show code.getD 52 .ecall = (.opImm .add 10 0 0) by decide, exec_opImm, show BitVec.signExtend 32 (0 : BitVec 12) = 0#32 by decide,
    show (1092#32 : BitVec 32) + 4 = 1096#32 by decide]
  all_goals rfl

theorem fetch_448 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1096#32, mem, inp, out, .running⟩ =
      ⟨x.set 0 1100#32, x.get 1 &&& 4294967294#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1096#32 : BitVec 32)).toNat - base) / 4 = 53 by decide,
    show code.getD 53 .ecall = (.jalr 0 1 0) by decide, exec_jalr, show (1096#32 : BitVec 32) + 4 = 1100#32 by decide,
    show (x.get 1 + BitVec.signExtend 32 (0 : BitVec 12)) &&& ~~~1 = x.get 1 &&& 4294967294#32 by rw [show BitVec.signExtend 32 (0 : BitVec 12) = 0#32 by decide, BitVec.add_zero]; rfl]
  all_goals rfl

theorem fetch_44c {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1100#32, mem, inp, out, .running⟩ =
      ⟨x.set 12 (x.get 10 + 0#32), 1104#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1100#32 : BitVec 32)).toNat - base) / 4 = 54 by decide,
    show code.getD 54 .ecall = (.opImm .add 12 10 0) by decide, exec_opImm, show BitVec.signExtend 32 (0 : BitVec 12) = 0#32 by decide,
    show (1100#32 : BitVec 32) + 4 = 1104#32 by decide]
  all_goals rfl

theorem fetch_450 {x : Regs 32} {mem : Array (BitVec 8)} {inp : List Char} {out : String}
    (hc : CodeAt mem) : step ⟨x, 1104#32, mem, inp, out, .running⟩ =
      ⟨x.set 0 1108#32, 940#32, mem, inp, out, .running⟩ := by
  rw [step_code' hc (by decide), show (((1104#32 : BitVec 32)).toNat - base) / 4 = 55 by decide,
    show code.getD 55 .ecall = (.jal 0 (-164)) by decide, exec_jal, show (1104#32 : BitVec 32) + BitVec.signExtend 32 ((-164) : BitVec 21) = 940#32 by decide,
    show (1104#32 : BitVec 32) + 4 = 1108#32 by decide]
  all_goals rfl

/-! ## Symbolic execution -/

theorem run_succ {n : Nat} {x : Regs 32} {pc : BitVec 32} {mem : Array (BitVec 8)}
    {inp : List Char} {out : String} : run (n + 1) ⟨x, pc, mem, inp, out, .running⟩ =
      run n (step ⟨x, pc, mem, inp, out, .running⟩) := by
  simp [run]

theorem run_zero (m : Machine 32) : run 0 m = m := rfl

theorem getElem_of_some {mem : Array (BitVec 8)} {i : Nat} {v : BitVec 8} (h : mem[i]? = some v)
    (hi : i < mem.size) : mem[i] = v := by
  simpa [hi] using h

/-- Lets `bv_omega` see the byte masks the compiler emits as `andi rd, rs, 255`. -/
theorem and_255 (y : BitVec 32) : y &&& 255#32 = (y.setWidth 8).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
  exact Nat.and_two_pow_sub_one_eq_mod y.toNat 8

theorem and_255_8 (y : BitVec 8) : y &&& 255#8 = y := BitVec.and_allOnes

/-- Side conditions of `dp_step`: the code is intact after stores outside it, stores and loads are
in bounds. -/
macro "dp_disch" : tactic => `(tactic| first
  | assumption
  | (simp only [Array.size_setIfInBounds]; assumption))

set_option hygiene false in
/-- Execute one instruction of `decode_percent` in the hypothesis `hS : run (n + 1) m = S`, by
simplification. `m` must have a literal `pc`. Side conditions (the code is still in place after a
store, addresses in range) go to the hypotheses and `omega`. -/
macro "dp_step" : tactic =>
  `(tactic| (rw [run_succ] at hS; simp (disch := dp_disch)
      [fetch_374, fetch_378, fetch_37c, fetch_380, fetch_384, fetch_388, fetch_38c, fetch_390, fetch_394, fetch_398, fetch_39c, fetch_3a0, fetch_3a4, fetch_3a8, fetch_3ac, fetch_3b0, fetch_3b4, fetch_3b8, fetch_3bc, fetch_3c0, fetch_3c4, fetch_3c8, fetch_3cc, fetch_3d0, fetch_3d4, fetch_3d8, fetch_3dc, fetch_3e0, fetch_3e4, fetch_3e8, fetch_3ec, fetch_3f0, fetch_3f4, fetch_3f8, fetch_3fc, fetch_400, fetch_404, fetch_408, fetch_40c, fetch_410, fetch_414, fetch_418, fetch_41c, fetch_420, fetch_424, fetch_428, fetch_42c, fetch_430, fetch_434, fetch_438, fetch_43c, fetch_440, fetch_444, fetch_448, fetch_44c, fetch_450,
       alu, Regs.get_set, BranchOp.taken,
       Width.bytes, writeBytes_byte, readBytes_byte, BitVec.add_assoc, run_zero, -BitVec.toNat_add,
       -BitVec.toNat_add_of_not_uaddOverflow, *] at hS))

set_option hygiene false in
/-- Resolve an `if` or `match` in `hS` when the hypotheses decide it: split, and close the
impossible side by `bv_omega`. -/
macro "dp_if" : tactic => `(tactic| (split at hS <;> try (exfalso; (try simp only [and_255, and_255_8, BitVec.ult, BitVec.slt, decide_eq_false_iff_not, Bool.not_eq_false, decide_eq_true_eq] at *); bv_omega)))

/-- Symbolic execution to the end of `hS`. -/
macro "dp_run" : tactic => `(tactic| repeat (first | dp_step | dp_if))

/-- Registers `decode_percent` may change: `t1` and `a0`–`a7`. -/
def clobbered : List Reg := [6, 10, 11, 12, 13, 14, 15, 16, 17]

set_option hygiene false in
/-- Close `∃ x', S = ⟨x', ...⟩ ∧ facts about x'` once `hS` has been run to the end. -/
macro "dp_done" : tactic => `(tactic| (
  subst hS; refine ⟨_, rfl, ?_⟩
  and_intros
  all_goals try simp (config := {contextual := true}) [Regs.get_set, clobbered, *]
  all_goals first | (intro r; intros; grind [Regs.get_zero]) | ((try simp only [and_255, and_255_8, BitVec.ult, BitVec.slt, decide_eq_false_iff_not, Bool.not_eq_false, decide_eq_true_eq] at *); bv_omega)))

/-! ## Paths through `decode_percent`

Labels as in `code`. `P` is the input pointer (`a3`) and `Q` the output pointer (`a4 - 1`). -/

/-- `loop` with a byte other than `%`: on to `put` with `a3` advanced. -/
theorem lit (x : Regs 32) (mem : Array (BitVec 8)) (inp : List Char) (out : String)
    (P Q : BitVec 32) (c : BitVec 8) (hc : CodeAt mem)
    (h13 : x.get 13 = P) (h14 : x.get 14 = Q + 1) (h15 : x.get 15 = c.setWidth 32)
    (h16 : x.get 16 = 37) (hpct : c ≠ 37) :
    ∃ x', run 3 ⟨x, 0x390#32, mem, inp, out, .running⟩ = ⟨x', 0x39c#32, mem, inp, out, .running⟩ ∧
      x'.get 13 = P + 1 ∧ x'.get 14 = Q + 1 ∧ x'.get 12 = Q + 1 ∧ x'.get 15 = c.setWidth 32 ∧
      x'.get 10 = x.get 10 ∧ x'.get 16 = x.get 16 ∧ x'.get 6 = x.get 6 ∧ x'.get 17 = x.get 17 ∧
      ∀ r, r ∉ clobbered → x'.get r = x.get r := by
  obtain ⟨S, hS⟩ : ∃ S, run 3 ⟨x, 0x390#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
  rw [hS]
  dp_run
  dp_done

/-- `put`: store the low byte of `a5` at `a4 - 1`, load the next input byte, and go back to
`loop` if it is not 0. -/
theorem put_cont (x : Regs 32) (mem : Array (BitVec 8)) (inp : List Char) (out : String)
    (P Q : BitVec 32) (v c : BitVec 8) (hc : CodeAt mem)
    (h13 : x.get 13 = P) (h14 : x.get 14 = Q + 1) (h15 : (x.get 15).setWidth 8 = v)
    (hQ : Q.toNat < mem.size) (hQc : Q.toNat < base ∨ base + 224 ≤ Q.toNat)
    (hPQ : Q.toNat ≠ P.toNat) (hP : P.toNat < mem.size) (hmem : mem[P.toNat]? = some c)
    (hnz : c ≠ 0) :
    ∃ x', run 4 ⟨x, 0x39c#32, mem, inp, out, .running⟩ =
        ⟨x', 0x390#32, mem.setIfInBounds Q.toNat v, inp, out, .running⟩ ∧
      x'.get 13 = P ∧ x'.get 14 = Q + 2 ∧ x'.get 15 = c.setWidth 32 ∧
      x'.get 10 = x.get 10 ∧ x'.get 16 = x.get 16 ∧ x'.get 6 = x.get 6 ∧ x'.get 17 = x.get 17 ∧
      ∀ r, r ∉ clobbered → x'.get r = x.get r := by
  have hm := getElem_of_some hmem hP
  have hc1 := hc.set v hQc
  obtain ⟨S, hS⟩ : ∃ S, run 4 ⟨x, 0x39c#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
  rw [hS]
  dp_run
  dp_done


/-- `put` when the next input byte is 0: store, write the terminator, return `a0`. -/
theorem put_end (x : Regs 32) (mem : Array (BitVec 8)) (inp : List Char) (out : String)
    (P Q : BitVec 32) (v : BitVec 8) (hc : CodeAt mem)
    (h13 : x.get 13 = P) (h14 : x.get 14 = Q + 1) (h12 : x.get 12 = Q + 1)
    (h15 : (x.get 15).setWidth 8 = v)
    (hQ : Q.toNat < mem.size) (hQc : Q.toNat < base ∨ base + 224 ≤ Q.toNat)
    (hQ1 : (Q + 1#32).toNat < mem.size) (hQ1c : (Q + 1#32).toNat < base ∨ base + 224 ≤ (Q + 1#32).toNat)
    (hPQ : Q.toNat ≠ P.toNat) (hP : P.toNat < mem.size) (hmem : mem[P.toNat]? = some 0) :
    ∃ x', run 6 ⟨x, 0x39c#32, mem, inp, out, .running⟩ =
        ⟨x', x.get 1 &&& 4294967294#32, (mem.setIfInBounds Q.toNat v).setIfInBounds (Q + 1#32).toNat 0#8, inp, out, .running⟩ ∧
      x'.get 10 = x.get 10 ∧ ∀ r, r ∉ clobbered → x'.get r = x.get r := by
  have hm := getElem_of_some hmem hP
  have hc1 := hc.set v hQc
  have hc2 := hc1.set 0#8 hQ1c
  obtain ⟨S, hS⟩ : ∃ S, run 6 ⟨x, 0x39c#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
  rw [hS]
  dp_run
  dp_done

/-- The empty string: write the terminator and return. -/
theorem entry_empty (x : Regs 32) (mem : Array (BitVec 8)) (inp : List Char) (out : String)
    (A : BitVec 32) (hc : CodeAt mem) (h10 : x.get 10 = A)
    (hA : A.toNat < mem.size) (hAc : A.toNat < base ∨ base + 224 ≤ A.toNat)
    (hmem : mem[A.toNat]? = some 0) :
    ∃ x', run 6 ⟨x, 0x374#32, mem, inp, out, .running⟩ =
        ⟨x', x.get 1 &&& 4294967294#32, mem.setIfInBounds A.toNat 0#8, inp, out, .running⟩ ∧
      x'.get 10 = A ∧ ∀ r, r ∉ clobbered → x'.get r = x.get r := by
  have hm := getElem_of_some hmem hA
  have hc1 := hc.set 0#8 hAc
  obtain ⟨S, hS⟩ : ∃ S, run 6 ⟨x, 0x374#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
  rw [hS]
  dp_run
  dp_done

/-- A nonempty string: set up the loop. -/
theorem entry (x : Regs 32) (mem : Array (BitVec 8)) (inp : List Char) (out : String)
    (A : BitVec 32) (c : BitVec 8) (hc : CodeAt mem) (h10 : x.get 10 = A)
    (hmem : mem[A.toNat]? = some c) (hnz : c ≠ 0) :
    ∃ x', run 7 ⟨x, 0x374#32, mem, inp, out, .running⟩ = ⟨x', 0x390#32, mem, inp, out, .running⟩ ∧
      x'.get 13 = A ∧ x'.get 14 = A + 1 ∧ x'.get 15 = c.setWidth 32 ∧ x'.get 10 = A ∧
      x'.get 16 = 37 ∧ x'.get 6 = 9 ∧ x'.get 17 = 5 ∧
      ∀ r, r ∉ clobbered → x'.get r = x.get r := by
  obtain ⟨S, hS⟩ : ∃ S, run 7 ⟨x, 0x374#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
  rw [hS]
  dp_run
  dp_done

/-- `unhex` of url.c: the value of a hex digit. -/
def hexVal (b : BitVec 8) : Option (BitVec 8) :=
  if 48#8 ≤ b ∧ b ≤ 57#8 then some (b - 48#8)
  else if 65#8 ≤ b ∧ b ≤ 70#8 then some (b - 55#8)
  else if 97#8 ≤ b ∧ b ≤ 102#8 then some (b - 87#8)
  else none

/-- `loop` at a `%` whose next byte is a hex digit: on to `lo` with its value in `a2`. -/
theorem hi_ok (x : Regs 32) (mem : Array (BitVec 8)) (inp : List Char) (out : String)
    (P : BitVec 32) (h v : BitVec 8) (hc : CodeAt mem)
    (h13 : x.get 13 = P) (h15 : x.get 15 = 37#32) (h16 : x.get 16 = 37#32)
    (h6 : x.get 6 = 9#32) (h17 : x.get 17 = 5#32)
    (hP : (P + 1#32).toNat < mem.size) (hmem : mem[(P + 1#32).toNat]? = some h)
    (hv : hexVal h = some v) :
    ∃ n x', run n ⟨x, 0x390#32, mem, inp, out, .running⟩ = ⟨x', 0x3e0#32, mem, inp, out, .running⟩ ∧
      x'.get 12 = v.setWidth 32 ∧ x'.get 13 = P ∧ x'.get 14 = x.get 14 ∧ x'.get 10 = x.get 10 ∧
      x'.get 16 = 37#32 ∧ x'.get 6 = 9#32 ∧ x'.get 17 = 5#32 ∧
      ∀ r, r ∉ clobbered → x'.get r = x.get r := by
  have hm := getElem_of_some hmem hP
  unfold hexVal at hv
  split at hv
  · cases hv
    refine ⟨7, ?_⟩
    obtain ⟨S, hS⟩ : ∃ S, run 7 ⟨x, 0x390#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
    rw [hS]; dp_run; dp_done
  split at hv
  · cases hv
    refine ⟨10, ?_⟩
    obtain ⟨S, hS⟩ : ∃ S, run 10 ⟨x, 0x390#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
    rw [hS]; dp_run; dp_done
  split at hv
  · cases hv
    refine ⟨12, ?_⟩
    obtain ⟨S, hS⟩ : ∃ S, run 12 ⟨x, 0x390#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
    rw [hS]; dp_run; dp_done
  · cases hv

/-- `loop` at a `%` whose next byte is not a hex digit: return NULL. -/
theorem hi_bad (x : Regs 32) (mem : Array (BitVec 8)) (inp : List Char) (out : String)
    (P : BitVec 32) (h : BitVec 8) (hc : CodeAt mem)
    (h13 : x.get 13 = P) (h15 : x.get 15 = 37#32) (h16 : x.get 16 = 37#32)
    (h6 : x.get 6 = 9#32) (h17 : x.get 17 = 5#32)
    (hP : (P + 1#32).toNat < mem.size) (hmem : mem[(P + 1#32).toNat]? = some h)
    (hv : hexVal h = none) :
    ∃ x', run 13 ⟨x, 0x390#32, mem, inp, out, .running⟩ =
        ⟨x', x.get 1 &&& 4294967294#32, mem, inp, out, .running⟩ ∧
      x'.get 10 = 0#32 ∧ ∀ r, r ∉ clobbered → x'.get r = x.get r := by
  have hm := getElem_of_some hmem hP
  unfold hexVal at hv
  split at hv; · cases hv
  split at hv; · cases hv
  split at hv; · cases hv
  obtain ⟨S, hS⟩ : ∃ S, run 13 ⟨x, 0x390#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
  rw [hS]; dp_run; dp_done


/-- `lo` with a hex digit: combine the two digits and go to `put`. -/
theorem lo_ok (x : Regs 32) (mem : Array (BitVec 8)) (inp : List Char) (out : String)
    (P : BitVec 32) (hv l v : BitVec 8) (hc : CodeAt mem)
    (h12 : x.get 12 = hv.setWidth 32) (h13 : x.get 13 = P)
    (h6 : x.get 6 = 9#32) (h17 : x.get 17 = 5#32)
    (hP : (P + 2#32).toNat < mem.size) (hmem : mem[(P + 2#32).toNat]? = some l)
    (hv' : hexVal l = some v) :
    ∃ n x', run n ⟨x, 0x3e0#32, mem, inp, out, .running⟩ = ⟨x', 0x39c#32, mem, inp, out, .running⟩ ∧
      (x'.get 15).setWidth 8 = hv * 16 + v ∧ x'.get 13 = P + 3#32 ∧ x'.get 14 = x.get 14 ∧
      x'.get 12 = x.get 14 ∧ x'.get 10 = x.get 10 ∧ x'.get 16 = x.get 16 ∧
      x'.get 6 = 9#32 ∧ x'.get 17 = 5#32 ∧ ∀ r, r ∉ clobbered → x'.get r = x.get r := by
  have hm := getElem_of_some hmem hP
  unfold hexVal at hv'
  split at hv'
  · cases hv'
    refine ⟨10, ?_⟩
    obtain ⟨S, hS⟩ : ∃ S, run 10 ⟨x, 0x3e0#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
    rw [hS]; dp_run; dp_done
  split at hv'
  · cases hv'
    refine ⟨16, ?_⟩
    obtain ⟨S, hS⟩ : ∃ S, run 16 ⟨x, 0x3e0#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
    rw [hS]; dp_run; dp_done
  split at hv'
  · cases hv'
    refine ⟨18, ?_⟩
    obtain ⟨S, hS⟩ : ∃ S, run 18 ⟨x, 0x3e0#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
    rw [hS]; dp_run; dp_done
  · cases hv'

/-- `lo` with a byte that is not a hex digit: return NULL. -/
theorem lo_bad (x : Regs 32) (mem : Array (BitVec 8)) (inp : List Char) (out : String)
    (P : BitVec 32) (l : BitVec 8) (hc : CodeAt mem) (h13 : x.get 13 = P)
    (h6 : x.get 6 = 9#32) (h17 : x.get 17 = 5#32)
    (hP : (P + 2#32).toNat < mem.size) (hmem : mem[(P + 2#32).toNat]? = some l)
    (hv' : hexVal l = none) :
    ∃ x', run 12 ⟨x, 0x3e0#32, mem, inp, out, .running⟩ =
        ⟨x', x.get 1 &&& 4294967294#32, mem, inp, out, .running⟩ ∧
      x'.get 10 = 0#32 ∧ ∀ r, r ∉ clobbered → x'.get r = x.get r := by
  have hm := getElem_of_some hmem hP
  unfold hexVal at hv'
  split at hv'; · cases hv'
  split at hv'; · cases hv'
  split at hv'; · cases hv'
  obtain ⟨S, hS⟩ : ∃ S, run 12 ⟨x, 0x3e0#32, mem, inp, out, .running⟩ = S := ⟨_, rfl⟩
  rw [hS]; dp_run; dp_done

/-! ## Correctness of the whole function -/

/-- What `decode_percent` computes, on the bytes of a string without its terminator: `none`
where the C function returns NULL. -/
def decodePercent : List (BitVec 8) → Option (List (BitVec 8))
  | [] => some []
  | c :: rest =>
    if c = 37 then
      match rest with
      | h :: l :: rest' =>
        match hexVal h, hexVal l with
        | some hv, some lv => ((hv * 16 + lv) :: ·) <$> decodePercent rest'
        | _, _ => none
      | _ => none
    else (c :: ·) <$> decodePercent rest

theorem decodePercent_nil : decodePercent [] = some [] := by unfold decodePercent; rfl

theorem decodePercent_lit {c : BitVec 8} (rest : List (BitVec 8)) (h : c ≠ 37) :
    decodePercent (c :: rest) = (c :: ·) <$> decodePercent rest := by
  conv => lhs; unfold decodePercent
  simp only [h, ↓reduceIte]

theorem decodePercent_pct (h l : BitVec 8) (rest : List (BitVec 8)) :
    decodePercent (37 :: h :: l :: rest) =
      match hexVal h, hexVal l with
      | some hv, some lv => ((hv * 16 + lv) :: ·) <$> decodePercent rest
      | _, _ => none := by
  conv => lhs; unfold decodePercent
  simp

theorem decodePercent_pct_short (rest : List (BitVec 8)) (h : rest.length < 2) :
    decodePercent (37 :: rest) = none := by
  match rest, h with
  | [], _ => unfold decodePercent; simp
  | [_], _ => unfold decodePercent; simp

/-- The bytes `t` followed by a 0 terminator, at address `p`. -/
def StrAt (mem : Array (BitVec 8)) (p : Nat) (t : List (BitVec 8)) : Prop :=
  (∀ i (h : i < t.length), mem[p + i]? = some t[i]) ∧ mem[p + t.length]? = some 0

theorem StrAt.head {mem : Array (BitVec 8)} {p : Nat} {t : List (BitVec 8)} (h : StrAt mem p t) :
    mem[p]? = some (t.head?.getD 0) := by
  cases t with
  | nil => simpa using h.2
  | cons c rest => exact h.1 0 (by simp)

theorem StrAt.tail {mem : Array (BitVec 8)} {p : Nat} {c : BitVec 8} {t : List (BitVec 8)}
    (h : StrAt mem p (c :: t)) : StrAt mem (p + 1) t := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have := h.1 (i + 1) (by simp; omega)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
  · have := h.2
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem StrAt.set {mem : Array (BitVec 8)} {p q : Nat} {t : List (BitVec 8)} (h : StrAt mem p t)
    (hq : q < p) (v : BitVec 8) : StrAt (mem.setIfInBounds q v) p t := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [Array.getElem?_setIfInBounds_ne (by omega)]; exact h.1 i hi
  · rw [Array.getElem?_setIfInBounds_ne (by omega)]; exact h.2

theorem StrAt.lt_size {mem : Array (BitVec 8)} {p : Nat} {t : List (BitVec 8)} (h : StrAt mem p t) :
    p + t.length < mem.size := by
  have := h.2
  by_cases hc : p + t.length < mem.size
  · exact hc
  · simp [Array.getElem?_eq_none (show mem.size ≤ p + t.length by omega)] at this

theorem toNat_add_k (P : BitVec 32) (k : Nat) (hk : k < 2 ^ 32) (h : P.toNat + k < 2 ^ 32) :
    (P + BitVec.ofNat 32 k).toNat = P.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt h]

theorem hexVal_zero : hexVal 0 = none := by decide


/-- `x` and `y` agree on the registers `decode_percent` does not clobber. -/
def Agree (x y : Regs 32) : Prop := ∀ r, r ∉ clobbered → x.get r = y.get r

theorem Agree.trans {x y z : Regs 32} (h1 : Agree x y) (h2 : Agree y z) : Agree x z :=
  fun r hr => (h1 r hr).trans (h2 r hr)

theorem Agree.ra {x y : Regs 32} (h : Agree x y) : x.get 1 = y.get 1 := h 1 (by decide)

theorem set_ne {mem : Array (BitVec 8)} {q i : Nat} {v : BitVec 8} (h : q ≠ i) :
    (mem.setIfInBounds q v)[i]? = mem[i]? := Array.getElem?_setIfInBounds_ne h

theorem set_eq {mem : Array (BitVec 8)} {q : Nat} {v : BitVec 8} (h : q < mem.size) :
    (mem.setIfInBounds q v)[q]? = some v := Array.getElem?_setIfInBounds_self_of_lt h

/-- The result of running `decode_percent` from `loop` on the input `t` at `P`, writing at `Q`. -/
def LoopPost (x x' : Regs 32) (mem mem' : Array (BitVec 8)) (P Q : BitVec 32)
    (t : List (BitVec 8)) : Prop :=
  Agree x' x ∧ (∀ i, i < Q.toNat ∨ P.toNat + t.length < i → mem'[i]? = mem[i]?) ∧
    match decodePercent t with
    | some d => x'.get 10 = x.get 10 ∧ ∀ i, i < d.length + 1 → mem'[Q.toNat + i]? = (d ++ [0])[i]?
    | none => x'.get 10 = 0#32

/-- `decode_percent` is correct from `loop` on inputs of at most `N` bytes. -/
def LoopSpec (N : Nat) : Prop :=
  ∀ (c : BitVec 8) (rest : List (BitVec 8)) (x : Regs 32) (mem : Array (BitVec 8))
    (inp : List Char) (out : String) (P Q : BitVec 32),
    (c :: rest).length ≤ N → CodeAt mem →
    x.get 13 = P → x.get 14 = Q + 1 → x.get 15 = c.setWidth 32 → x.get 16 = 37#32 →
    x.get 6 = 9#32 → x.get 17 = 5#32 →
    StrAt mem P.toNat (c :: rest) → (∀ b ∈ c :: rest, b ≠ 0) → Q.toNat ≤ P.toNat →
    mem.size ≤ 2 ^ 32 → (P.toNat + (c :: rest).length < base ∨ base + 224 ≤ Q.toNat) →
    ∃ n x' mem', run n ⟨x, 0x390#32, mem, inp, out, .running⟩ =
        ⟨x', x.get 1 &&& 4294967294#32, mem', inp, out, .running⟩ ∧
      LoopPost x x' mem mem' P Q (c :: rest)

/-- From `put` with the byte `v` to write at `Q` and the rest of the input `t` at `P`: write `v`
and decode `t` after it. -/
theorem from_put (N : Nat) (ih : LoopSpec N) (v : BitVec 8) (t : List (BitVec 8)) (x : Regs 32)
    (mem : Array (BitVec 8)) (inp : List Char) (out : String) (P Q : BitVec 32)
    (ht : t.length ≤ N) (hc : CodeAt mem)
    (h13 : x.get 13 = P) (h14 : x.get 14 = Q + 1) (h12 : x.get 12 = Q + 1)
    (h15 : (x.get 15).setWidth 8 = v) (h16 : x.get 16 = 37#32) (h6 : x.get 6 = 9#32)
    (h17 : x.get 17 = 5#32) (hs : StrAt mem P.toNat t) (hnz : ∀ b ∈ t, b ≠ 0)
    (hQP : Q.toNat < P.toNat) (hsize : mem.size ≤ 2 ^ 32)
    (hcode : P.toNat + t.length < base ∨ base + 224 ≤ Q.toNat) :
    ∃ n x' mem', run n ⟨x, 0x39c#32, mem, inp, out, .running⟩ =
        ⟨x', x.get 1 &&& 4294967294#32, mem', inp, out, .running⟩ ∧
      Agree x' x ∧ (∀ i, i < Q.toNat ∨ P.toNat + t.length < i → mem'[i]? = mem[i]?) ∧
      match (v :: ·) <$> decodePercent t with
      | some d => x'.get 10 = x.get 10 ∧
          ∀ i, i < d.length + 1 → mem'[Q.toNat + i]? = (d ++ [0])[i]?
      | none => x'.get 10 = 0#32 := by
  have hlt := hs.lt_size
  have eQ1 : (Q + 1#32).toNat = Q.toNat + 1 := toNat_add_k Q 1 (by decide) (by omega)
  have hQ : Q.toNat < mem.size := by omega
  have hQc : Q.toNat < base ∨ base + 224 ≤ Q.toNat := by omega
  cases t with
  | nil =>
    have hm : mem[P.toNat]? = some 0 := by simpa using hs.2
    have hQ1 : (Q + 1#32).toNat < mem.size := by simp at hlt; omega
    have hQ1c : (Q + 1#32).toNat < base ∨ base + 224 ≤ (Q + 1#32).toNat := by simp at hcode; omega
    obtain ⟨x2, e2, b10, ag2⟩ := put_end x mem inp out P Q v hc h13 h14 h12 h15 hQ hQc hQ1
      hQ1c (by omega) (by simp at hlt; omega) hm
    refine ⟨6, x2, (mem.setIfInBounds Q.toNat v).setIfInBounds (Q + 1#32).toNat 0#8, e2, ag2,
      fun i hi => ?_, ?_⟩
    · simp only [List.length_nil] at hi
      rw [set_ne (by omega), set_ne (by omega)]
    · rw [decodePercent_nil]
      refine ⟨b10, fun i hi => ?_⟩
      simp only [List.length_cons, List.length_nil] at hi
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · rw [Nat.add_zero, set_ne (by omega), set_eq hQ]; rfl
      · rw [← eQ1, set_eq (by simpa using hQ1)]; rfl
  | cons c' rest' =>
    simp only [List.length_cons] at hlt hcode ht
    have hc' : c' ≠ 0 := hnz c' (by simp)
    have hm : mem[P.toNat]? = some c' := by simpa using hs.head
    obtain ⟨x2, e2, b13, b14, b15, b10, b16, b6, b17, ag2⟩ := put_cont x mem inp out P Q v c'
      hc h13 h14 h15 hQ hQc (by omega) (by omega) hm hc'
    have hs2 : StrAt (mem.setIfInBounds Q.toNat v) P.toNat (c' :: rest') := hs.set hQP v
    obtain ⟨n, x3, mem3, e3, ag3, hout3, hres3⟩ := ih c' rest' x2 _ inp out P (Q + 1#32)
      (by simp; omega) (hc.set v hQc) b13 (by rw [b14]; bv_omega) b15
      (by rw [b16, h16]) (by rw [b6, h6]) (by rw [b17, h17]) hs2 hnz (by omega)
      (by simpa using hsize) (by simp only [List.length_cons]; omega)
    refine ⟨4 + n, x3, mem3, by rw [run_add, e2, e3, Agree.ra ag2], Agree.trans ag3 ag2,
      fun i hi => ?_, ?_⟩
    · simp only [List.length_cons] at hi
      rw [hout3 i (by simp only [List.length_cons]; omega), set_ne (by omega)]
    · revert hres3
      cases decodePercent (c' :: rest') with
      | none => intro h; simpa [b10] using h
      | some d =>
        intro ⟨h10', hb⟩
        refine ⟨by rw [h10', b10], fun i hi => ?_⟩
        cases i with
        | zero => rw [Nat.add_zero, hout3 Q.toNat (by omega), set_eq hQ]; rfl
        | succ j =>
          have := hb j (by simp at hi; omega)
          rw [eQ1] at this
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem loop (N : Nat) : LoopSpec N := by
  induction N with
  | zero => intro c rest; simp
  | succ N ih =>
  intro c rest x mem inp out P Q hlen hc h13 h14 h15 h16 h6 h17 hs hnz hQP hsize hcode
  have hlt := hs.lt_size
  simp only [List.length_cons] at hlt hcode hlen
  have eP1 : (P + 1).toNat = P.toNat + 1 := toNat_add_k P 1 (by decide) (by omega)
  by_cases hpct : c = 37
  · subst hpct
    have h15' : x.get 15 = 37#32 := by rw [h15]; decide
    have eP1' : (P + 1#32).toNat = P.toNat + 1 := toNat_add_k P 1 (by decide) (by omega)
    have hP1 : (P + 1#32).toNat < mem.size := by omega
    have hm1 : mem[(P + 1#32).toNat]? = some (rest.head?.getD 0) := by
      rw [eP1']; exact hs.tail.head
    match hh : hexVal (rest.head?.getD 0) with
    | none =>
      obtain ⟨x1, e1, b10, ag1⟩ := hi_bad x mem inp out P _ hc h13 h15' h16 h6 h17 hP1 hm1 hh
      refine ⟨13, x1, mem, e1, ag1, fun _ _ => rfl, ?_⟩
      have : decodePercent (37 :: rest) = none := by
        match rest, hh with
        | [], _ => exact decodePercent_pct_short [] (by simp)
        | [_], _ => exact decodePercent_pct_short _ (by simp)
        | h :: l :: r, hh => rw [decodePercent_pct]; simp at hh; simp [hh]
      rw [this]; exact b10
    | some hv =>
      cases rest with
      | nil => (try simp only [List.head?_nil, Option.getD_none] at hh); rw [hexVal_zero] at hh; cases hh
      | cons h rest1 =>
      simp only [List.head?_cons, Option.getD_some] at hh hm1
      simp only [List.length_cons] at hlt hcode hlen
      obtain ⟨n1, x1, e1, a12, a13, a14, a10, a16, a6, a17, ag1⟩ :=
        hi_ok x mem inp out P h hv hc h13 h15' h16 h6 h17 hP1 hm1 hh
      have eP2 : (P + 2#32).toNat = P.toNat + 2 := toNat_add_k P 2 (by decide) (by omega)
      have hm2 : mem[(P + 2#32).toNat]? = some (rest1.head?.getD 0) := by
        rw [eP2]; have := hs.tail.tail.head; simpa [Nat.add_assoc] using this
      match hl : hexVal (rest1.head?.getD 0) with
      | none =>
        obtain ⟨x2, e2, b10, ag2⟩ := lo_bad x1 mem inp out P _ hc a13 a6 a17 (by omega) hm2 hl
        refine ⟨n1 + 12, x2, mem, by rw [run_add, e1, e2, Agree.ra ag1],
          Agree.trans ag2 ag1, fun _ _ => rfl, ?_⟩
        have : decodePercent (37 :: h :: rest1) = none := by
          cases rest1 with
          | nil => exact decodePercent_pct_short _ (by simp)
          | cons l r => rw [decodePercent_pct, hh]; simp at hl; simp [hl]
        rw [this]; exact b10
      | some lv =>
        cases rest1 with
        | nil => (try simp only [List.head?_nil, Option.getD_none] at hl); rw [hexVal_zero] at hl; cases hl
        | cons l rest2 =>
        simp only [List.head?_cons, Option.getD_some] at hl hm2
        simp only [List.length_cons] at hlt hcode hlen
        obtain ⟨n2, x2, e2, c15, c13, c14, c12, c10, c16, c6, c17, ag2⟩ :=
          lo_ok x1 mem inp out P hv l lv hc a12 a13 a6 a17 (by omega) hm2 hl
        have eP3 : (P + 3#32).toNat = P.toNat + 3 := toNat_add_k P 3 (by decide) (by omega)
        obtain ⟨n3, x3, mem3, e3, ag3, hout3, hres3⟩ := from_put N ih (hv * 16 + lv) rest2 x2 mem
          inp out (P + 3#32) Q (by omega) hc c13 (by rw [c14, a14, h14]) (by rw [c12, a14, h14])
          c15 (by rw [c16, a16]) c6 c17
          (by rw [eP3]; have := hs.tail.tail.tail; simpa [Nat.add_assoc] using this)
          (fun b hb => hnz b (by simp [hb])) (by omega) hsize (by rw [eP3]; omega)
        refine ⟨n1 + n2 + n3, x3, mem3,
          by rw [run_add, run_add, e1, e2, e3, Agree.ra ag2, Agree.ra ag1],
          Agree.trans ag3 (Agree.trans ag2 ag1),
          fun i hi => hout3 i (by rw [eP3]; simp only [List.length_cons] at hi; omega), ?_⟩
        rw [decodePercent_pct, hh, hl]
        revert hres3
        cases decodePercent rest2 with
        | none => intro h; simpa [c10, a10] using h
        | some d => intro ⟨h10', hb⟩; exact ⟨by rw [h10', c10, a10], hb⟩
  obtain ⟨x1, e1, a13, a14, a12, a15, a10, a16, a6, a17, ag1⟩ :=
    lit x mem inp out P Q c hc h13 h14 h15 (by simpa using h16) hpct
  obtain ⟨n, x2, mem2, e2, ag2, hout2, hres2⟩ := from_put N ih c rest x1 mem inp out (P + 1) Q
    (by omega) hc a13 a14 a12 (by rw [a15]; bv_omega) (by rw [a16, h16]) (by rw [a6, h6])
    (by rw [a17, h17]) (by rw [eP1]; exact hs.tail) (fun b hb => hnz b (by simp [hb]))
    (by omega) hsize (by omega)
  refine ⟨3 + n, x2, mem2, by rw [run_add, e1, e2, Agree.ra ag1], Agree.trans ag2 ag1,
    fun i hi => hout2 i (by simp only [List.length_cons] at hi; omega), ?_⟩
  rw [decodePercent_lit rest hpct]
  revert hres2
  cases decodePercent rest with
  | none => intro h; simpa [a10] using h
  | some d => intro ⟨h10', hb⟩; exact ⟨by rw [h10', a10], hb⟩

/-- **`decode_percent` is correct.** Called with `a0 = A` pointing at the NUL-terminated string
`s` (no NUL inside, not overlapping the code), it returns to `ra` with the callee-saved and other
non-temporary registers unchanged and touches memory only within `s` and its terminator. If
`decodePercent s` succeeds with `d`, it returns `A` and leaves `d` NUL-terminated at `A`;
otherwise it returns NULL. -/
theorem decode_percent_correct (x : Regs 32) (mem : Array (BitVec 8)) (inp : List Char)
    (out : String) (A : BitVec 32) (s : List (BitVec 8)) (hc : CodeAt mem) (h10 : x.get 10 = A)
    (hs : StrAt mem A.toNat s) (hnz : ∀ b ∈ s, b ≠ 0) (hsize : mem.size ≤ 2 ^ 32)
    (hcode : A.toNat + s.length < base ∨ base + 224 ≤ A.toNat) :
    ∃ n x' mem', run n ⟨x, 0x374#32, mem, inp, out, .running⟩ =
        ⟨x', x.get 1 &&& 4294967294#32, mem', inp, out, .running⟩ ∧
      Agree x' x ∧ (∀ i, i < A.toNat ∨ A.toNat + s.length < i → mem'[i]? = mem[i]?) ∧
      match decodePercent s with
      | some d => x'.get 10 = A ∧ ∀ i, i < d.length + 1 → mem'[A.toNat + i]? = (d ++ [0])[i]?
      | none => x'.get 10 = 0#32 := by
  have hlt := hs.lt_size
  cases s with
  | nil =>
    simp only [List.length_nil, Nat.add_zero] at hlt hcode
    have hm : mem[A.toNat]? = some 0 := by simpa using hs.2
    obtain ⟨x1, e1, b10, ag1⟩ := entry_empty x mem inp out A hc h10 hlt hcode hm
    refine ⟨6, x1, _, e1, ag1, fun i hi => set_ne (by simp at hi; omega), ?_⟩
    rw [decodePercent_nil]
    refine ⟨b10, fun i hi => ?_⟩
    simp only [List.length_nil] at hi
    rcases (show i = 0 by omega) with rfl
    rw [Nat.add_zero, set_eq hlt]; rfl
  | cons c rest =>
    obtain ⟨x1, e1, a13, a14, a15, a10, a16, a6, a17, ag1⟩ :=
      entry x mem inp out A c hc h10 (by simpa using hs.head) (hnz c (by simp))
    obtain ⟨n, x2, mem2, e2, ag2, hout2, hres2⟩ := loop (c :: rest).length c rest x1 mem inp out A A
      (Nat.le_refl _) hc a13 a14 a15 (by rw [a16]; rfl) (by rw [a6]; rfl) (by rw [a17]; rfl) hs hnz
      (Nat.le_refl _) hsize hcode
    refine ⟨7 + n, x2, mem2, by rw [run_add, e1, e2, Agree.ra ag1], Agree.trans ag2 ag1, hout2, ?_⟩
    revert hres2
    cases decodePercent (c :: rest) with
    | none => exact id
    | some d => intro ⟨h10', hb⟩; exact ⟨h10'.trans a10, hb⟩

/-! ## Properties of `decodePercent` -/

/-- Decoding never makes a string longer, so decoding in place is safe. -/
theorem decodePercent_length : ∀ (s d : List (BitVec 8)), decodePercent s = some d →
    d.length ≤ s.length
  | [], d, h => by rw [decodePercent_nil] at h; cases h; simp
  | c :: rest, d, h => by
    by_cases hc : c = 37
    · subst hc
      match rest, h with
      | [], h => rw [decodePercent_pct_short [] (by simp)] at h; cases h
      | [_], h => rw [decodePercent_pct_short _ (by simp)] at h; cases h
      | a :: b :: r, h =>
        rw [decodePercent_pct] at h
        split at h
        · cases e : decodePercent r with
          | none => rw [e] at h; cases h
          | some d' =>
            rw [e] at h; cases h
            have := decodePercent_length r d' e
            simp; omega
        · cases h
    · rw [decodePercent_lit rest hc] at h
      cases e : decodePercent rest with
      | none => rw [e] at h; cases h
      | some d' =>
        rw [e] at h; cases h
        have := decodePercent_length rest d' e
        simp; omega

/-- A string with no `%` decodes to itself. -/
theorem decodePercent_of_no_pct : ∀ s : List (BitVec 8), 37 ∉ s → decodePercent s = some s
  | [], _ => decodePercent_nil
  | c :: rest, h => by
    have hc : c ≠ 37 := fun e => h (by simp [e])
    rw [decodePercent_lit rest hc, decodePercent_of_no_pct rest (fun e => h (List.mem_cons_of_mem _ e))]
    rfl

/-- The uppercase hex digit for a value below 16. -/
def hexDigit (v : BitVec 8) : BitVec 8 := if v < 10 then v + 48 else v + 55

/-- Percent-encode every byte, as `%XX`. -/
def encodeAll : List (BitVec 8) → List (BitVec 8)
  | [] => []
  | b :: rest => 37 :: hexDigit (b >>> 4) :: hexDigit (b &&& 15) :: encodeAll rest

theorem hexVal_hexDigit_hi (b : BitVec 8) : hexVal (hexDigit (b >>> 4)) = some (b >>> 4) := by
  revert b; decide

theorem hexVal_hexDigit_lo (b : BitVec 8) : hexVal (hexDigit (b &&& 15)) = some (b &&& 15) := by
  revert b; decide

theorem hi_lo (b : BitVec 8) : (b >>> 4) * 16 + (b &&& 15) = b := by revert b; decide

/-- Decoding inverts percent-encoding: `decodePercent (encodeAll s) = some s` for every byte
string, including ones with NUL bytes. -/
theorem decodePercent_encodeAll : ∀ s : List (BitVec 8), decodePercent (encodeAll s) = some s
  | [] => decodePercent_nil
  | b :: rest => by
    rw [encodeAll, decodePercent_pct, hexVal_hexDigit_hi, hexVal_hexDigit_lo,
      decodePercent_encodeAll rest]
    show some ((((b >>> 4) * 16 + (b &&& 15)) : BitVec 8) :: rest) = _
    rw [hi_lo]

/-- `"%00"` decodes to a NUL byte, so the C result, read as a C string, is cut short:
`"%00A"` becomes the bytes `0, 'A'`, which C sees as the empty string. -/
theorem decodePercent_nul : decodePercent [37, 48, 48, 65] = some [0, 65] := by decide

/-- A `%` without two hex digits after it makes `decode_percent` fail (return NULL). -/
theorem decodePercent_bad : decodePercent [37, 71, 48] = none ∧ decodePercent [65, 37] = none := by
  decide

end TinyFive.UrlDecode
