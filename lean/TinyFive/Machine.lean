/-!
# A small RISC-V machine model

A Lean counterpart of `machine.py`: RV32IM and RV64IM integer instructions as used by the
emulator, and a subset of its RARS-style system calls.

Differences from `machine.py`:

* system calls 4, 5 and 8 (print string, read integer, read line) are absent;
* an address is an unsigned `w`-bit number and an access outside memory is a fault, whereas Python
  lets a negative index wrap to the end of `mem`;
* an unsupported instruction or system call sets `Status.fault` instead of raising an exception.
-/

namespace TinyFive

abbrev Reg := Fin 32

inductive AluOp where
  | add | sub | sll | slt | sltu | xor | srl | sra | or | and
  | mul | mulh | mulhsu | mulhu | div | divu | rem | remu
  deriving DecidableEq, Repr

inductive BranchOp where
  | beq | bne | blt | bge | bltu | bgeu
  deriving DecidableEq, Repr

inductive Width where
  | byte | half | word | dword
  deriving DecidableEq, Repr

inductive Instr where
  | lui (rd : Reg) (imm : BitVec 20)
  | auipc (rd : Reg) (imm : BitVec 20)
  | jal (rd : Reg) (imm : BitVec 21)
  | jalr (rd rs1 : Reg) (imm : BitVec 12)
  | branch (op : BranchOp) (rs1 rs2 : Reg) (imm : BitVec 13)
  | load (width : Width) (signed : Bool) (rd rs1 : Reg) (imm : BitVec 12)
  | store (width : Width) (rs2 rs1 : Reg) (imm : BitVec 12)
  | opImm (op : AluOp) (rd rs1 : Reg) (imm : BitVec 12)
  | op (op : AluOp) (rd rs1 rs2 : Reg)
  | opImmWord (op : AluOp) (rd rs1 : Reg) (imm : BitVec 12)
  | opWord (op : AluOp) (rd rs1 rs2 : Reg)
  | ecall
  deriving DecidableEq, Repr

/-- Decode a 32-bit instruction word for a machine of register width `w`. The width matters for
the XLEN-wide shift-immediates, whose shift amount has 6 bits when `w = 64` and 5 bits otherwise,
and for RV64-only instructions. -/
def decode (w : Nat) (i : BitVec 32) : Option Instr :=
  let opcode := i.extractLsb' 0 7
  let rd : Reg := (i.extractLsb' 7 5).toFin
  let f3 := i.extractLsb' 12 3
  let rs1 : Reg := (i.extractLsb' 15 5).toFin
  let rs2 : Reg := (i.extractLsb' 20 5).toFin
  let f7 := i.extractLsb' 25 7
  let immI := i.extractLsb' 20 12
  let immS := f7 ++ i.extractLsb' 7 5
  let immB : BitVec 13 :=
    i.extractLsb' 31 1 ++ i.extractLsb' 7 1 ++ i.extractLsb' 25 6 ++ i.extractLsb' 8 4 ++ 0#1
  let immU := i.extractLsb' 12 20
  let immJ : BitVec 21 :=
    i.extractLsb' 31 1 ++ i.extractLsb' 12 8 ++ i.extractLsb' 20 1 ++ i.extractLsb' 21 10 ++ 0#1
  match opcode with
  | 0x37 => some (.lui rd immU)
  | 0x17 => some (.auipc rd immU)
  | 0x6f => some (.jal rd immJ)
  | 0x67 => if f3 = 0 then some (.jalr rd rs1 immI) else none
  | 0x63 =>
    match f3 with
    | 0 => some (.branch .beq rs1 rs2 immB)
    | 1 => some (.branch .bne rs1 rs2 immB)
    | 4 => some (.branch .blt rs1 rs2 immB)
    | 5 => some (.branch .bge rs1 rs2 immB)
    | 6 => some (.branch .bltu rs1 rs2 immB)
    | 7 => some (.branch .bgeu rs1 rs2 immB)
    | _ => none
  | 0x03 =>
    match f3 with
    | 0 => some (.load .byte true rd rs1 immI)
    | 1 => some (.load .half true rd rs1 immI)
    | 2 => some (.load .word true rd rs1 immI)
    | 3 => if w = 64 then some (.load .dword true rd rs1 immI) else none
    | 4 => some (.load .byte false rd rs1 immI)
    | 5 => some (.load .half false rd rs1 immI)
    | 6 => if w = 64 then some (.load .word false rd rs1 immI) else none
    | _ => none
  | 0x23 =>
    match f3 with
    | 0 => some (.store .byte rs2 rs1 immS)
    | 1 => some (.store .half rs2 rs1 immS)
    | 2 => some (.store .word rs2 rs1 immS)
    | 3 => if w = 64 then some (.store .dword rs2 rs1 immS) else none
    | _ => none
  | 0x13 =>
    -- For a shift, the bits of `immI` above the shift amount select the kind of shift.
    let shamtBits := if w = 64 then 6 else 5
    let shamt : BitVec 12 := immI &&& (BitVec.ofNat 12 (2 ^ shamtBits - 1))
    let kind := immI >>> shamtBits
    let arith : BitVec 12 := BitVec.ofNat 12 (2 ^ (10 - shamtBits))
    match f3 with
    | 0 => some (.opImm .add rd rs1 immI)
    | 2 => some (.opImm .slt rd rs1 immI)
    | 3 => some (.opImm .sltu rd rs1 immI)
    | 4 => some (.opImm .xor rd rs1 immI)
    | 6 => some (.opImm .or rd rs1 immI)
    | 7 => some (.opImm .and rd rs1 immI)
    | 1 => if kind = 0 then some (.opImm .sll rd rs1 shamt) else none
    | 5 =>
      if kind = 0 then some (.opImm .srl rd rs1 shamt)
      else if kind = arith then some (.opImm .sra rd rs1 shamt)
      else none
    | _ => none
  | 0x1b =>
    if w = 64 then
      let shamt := (i.extractLsb' 20 5).setWidth 12
      match f3, f7 with
      | 0, _    => some (.opImmWord .add rd rs1 immI)
      | 1, 0x00 => some (.opImmWord .sll rd rs1 shamt)
      | 5, 0x00 => some (.opImmWord .srl rd rs1 shamt)
      | 5, 0x20 => some (.opImmWord .sra rd rs1 shamt)
      | _, _ => none
    else none
  | 0x33 =>
    match f3, f7 with
    | 0, 0x00 => some (.op .add rd rs1 rs2)
    | 0, 0x20 => some (.op .sub rd rs1 rs2)
    | 1, 0x00 => some (.op .sll rd rs1 rs2)
    | 2, 0x00 => some (.op .slt rd rs1 rs2)
    | 3, 0x00 => some (.op .sltu rd rs1 rs2)
    | 4, 0x00 => some (.op .xor rd rs1 rs2)
    | 5, 0x00 => some (.op .srl rd rs1 rs2)
    | 5, 0x20 => some (.op .sra rd rs1 rs2)
    | 6, 0x00 => some (.op .or rd rs1 rs2)
    | 7, 0x00 => some (.op .and rd rs1 rs2)
    | 0, 0x01 => some (.op .mul rd rs1 rs2)
    | 1, 0x01 => some (.op .mulh rd rs1 rs2)
    | 2, 0x01 => some (.op .mulhsu rd rs1 rs2)
    | 3, 0x01 => some (.op .mulhu rd rs1 rs2)
    | 4, 0x01 => some (.op .div rd rs1 rs2)
    | 5, 0x01 => some (.op .divu rd rs1 rs2)
    | 6, 0x01 => some (.op .rem rd rs1 rs2)
    | 7, 0x01 => some (.op .remu rd rs1 rs2)
    | _, _ => none
  | 0x3b =>
    if w = 64 then
      match f3, f7 with
      | 0, 0x00 => some (.opWord .add rd rs1 rs2)
      | 0, 0x20 => some (.opWord .sub rd rs1 rs2)
      | 1, 0x00 => some (.opWord .sll rd rs1 rs2)
      | 5, 0x00 => some (.opWord .srl rd rs1 rs2)
      | 5, 0x20 => some (.opWord .sra rd rs1 rs2)
      | 0, 0x01 => some (.opWord .mul rd rs1 rs2)
      | 4, 0x01 => some (.opWord .div rd rs1 rs2)
      | 5, 0x01 => some (.opWord .divu rd rs1 rs2)
      | 6, 0x01 => some (.opWord .rem rd rs1 rs2)
      | 7, 0x01 => some (.opWord .remu rd rs1 rs2)
      | _, _ => none
    else none
  | _ => if i = 0x00000073 then some .ecall else none

/-- The register file. Register 0 reads as zero whatever is stored in it. -/
structure Regs (w : Nat) where
  vec : Vector (BitVec w) 32

namespace Regs

variable {w : Nat}

def get (x : Regs w) (r : Reg) : BitVec w := if r = 0 then 0 else x.vec[r]

def set (x : Regs w) (r : Reg) (v : BitVec w) : Regs w := ⟨x.vec.set r v⟩

@[simp] theorem get_zero (x : Regs w) : x.get 0 = 0 := rfl

theorem get_set (x : Regs w) (i j : Reg) (v : BitVec w) :
    (x.set i v).get j = if j = 0 then 0 else if i = j then v else x.get j := by
  grind [get, set, Fin.val_inj]

end Regs

inductive Status where
  | running
  | exited (code : Int)
  | fault
  deriving DecidableEq, Repr

/-- The machine state. `input` is what remains of standard input and `output` is everything
printed so far; both are text, as they are for `machine.py`. -/
structure Machine (w : Nat) where
  x : Regs w
  pc : BitVec w
  mem : Array (BitVec 8)
  input : List Char
  output : String
  status : Status

namespace Machine

variable {w : Nat}

def setReg (m : Machine w) (rd : Reg) (v : BitVec w) : Machine w :=
  { m with x := m.x.set rd v }

def advance (m : Machine w) : Machine w := { m with pc := m.pc + 4 }

def fail (m : Machine w) : Machine w := { m with status := .fault }

end Machine

/-- `mul` keeps the low `w` bits of the product; `mulh*` read the high half of a widened
product. Division truncates toward zero; a zero divisor gives all ones for the quotient
and the dividend for the remainder. Signed overflow wraps at the operation width. -/
def alu {w : Nat} (op : AluOp) (a b : BitVec w) : BitVec w :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .sll => a <<< (b.toNat % w)
  | .slt => if a.slt b then 1 else 0
  | .sltu => if a.ult b then 1 else 0
  | .xor => a ^^^ b
  | .srl => a >>> (b.toNat % w)
  | .sra => a.sshiftRight (b.toNat % w)
  | .or => a ||| b
  | .and => a &&& b
  | .mul => a * b
  | .mulh => (a.signExtend (w + w) * b.signExtend (w + w)).extractLsb' w w
  | .mulhsu => (a.signExtend (w + w) * b.setWidth (w + w)).extractLsb' w w
  | .mulhu => (a.setWidth (w + w) * b.setWidth (w + w)).extractLsb' w w
  | .div => if b = 0 then BitVec.allOnes w else a.sdiv b
  | .divu => if b = 0 then BitVec.allOnes w else a / b
  | .rem => a.srem b
  | .remu => a % b

def BranchOp.taken {w : Nat} (op : BranchOp) (a b : BitVec w) : Bool :=
  match op with
  | .beq => a == b
  | .bne => a != b
  | .blt => a.slt b
  | .bge => !a.slt b
  | .bltu => a.ult b
  | .bgeu => !a.ult b

def Width.bytes : Width → Nat
  | .byte => 1
  | .half => 2
  | .word => 4
  | .dword => 8

/-- The little-endian value of the `n` bytes at `addr`, or `none` if any lies outside memory. -/
def readBytes (mem : Array (BitVec 8)) (addr : Nat) : (n : Nat) → Option (BitVec (8 * n))
  | 0 => some 0#0
  | n + 1 => do
    let lo ← mem[addr]?
    let hi ← readBytes mem (addr + 1) n
    some ((hi ++ lo).cast (by omega))

/-- Store the low `n` bytes of `v` at `addr`, little-endian, or `none` if any lies outside
memory. -/
def writeBytes {k : Nat} (mem : Array (BitVec 8)) (addr : Nat) (v : BitVec k) :
    Nat → Option (Array (BitVec 8))
  | 0 => some mem
  | n + 1 =>
    if addr < mem.size then
      writeBytes (mem.setIfInBounds addr (v.setWidth 8)) (addr + 1) (v >>> 8) n
    else none

/-- The system calls of `machine.ECALL`: `a7` selects the service and `a0` carries the argument
and the result. -/
def ecall {w : Nat} (m : Machine w) : Machine w :=
  let a0 := m.x.get 10
  match (m.x.get 17).toNat with
  | 1 => { m with output := m.output ++ toString a0.toInt }.advance
  | 10 => { m with status := .exited 0 }.advance
  | 11 => { m with output := m.output.push (Char.ofNat (a0.toNat % 256)) }.advance
  | 12 =>
    match m.input with
    | [] => (m.setReg 10 (-1)).advance
    | c :: rest => ({ m with input := rest }.setReg 10 (BitVec.ofNat w c.toNat)).advance
  | 93 => { m with status := .exited a0.toInt }.advance
  | _ => m.fail

def exec {w : Nat} (i : Instr) (m : Machine w) : Machine w :=
  match i with
  | .lui rd imm => (m.setReg rd ((imm ++ 0#12).signExtend w)).advance
  | .auipc rd imm => (m.setReg rd (m.pc + (imm ++ 0#12).signExtend w)).advance
  | .jal rd imm => { m.setReg rd (m.pc + 4) with pc := m.pc + imm.signExtend w }
  | .jalr rd rs1 imm =>
    { m.setReg rd (m.pc + 4) with pc := (m.x.get rs1 + imm.signExtend w) &&& ~~~1 }
  | .branch op rs1 rs2 imm =>
    if op.taken (m.x.get rs1) (m.x.get rs2) then { m with pc := m.pc + imm.signExtend w }
    else m.advance
  | .load width signed rd rs1 imm =>
    match readBytes m.mem (m.x.get rs1 + imm.signExtend w).toNat width.bytes with
    | some v => (m.setReg rd (if signed then v.signExtend w else v.setWidth w)).advance
    | none => m.fail
  | .store width rs2 rs1 imm =>
    match writeBytes m.mem (m.x.get rs1 + imm.signExtend w).toNat (m.x.get rs2) width.bytes with
    | some mem => { m with mem := mem }.advance
    | none => m.fail
  | .opImm op rd rs1 imm => (m.setReg rd (alu op (m.x.get rs1) (imm.signExtend w))).advance
  | .op op rd rs1 rs2 => (m.setReg rd (alu op (m.x.get rs1) (m.x.get rs2))).advance
  | .opImmWord op rd rs1 imm =>
    (m.setReg rd ((alu op ((m.x.get rs1).setWidth 32) (imm.signExtend 32)).signExtend w)).advance
  | .opWord op rd rs1 rs2 =>
    (m.setReg rd ((alu op ((m.x.get rs1).setWidth 32) ((m.x.get rs2).setWidth 32)).signExtend w)).advance
  | .ecall => ecall m

/-- Execute the instruction at `pc`. -/
def step {w : Nat} (m : Machine w) : Machine w :=
  match (readBytes m.mem m.pc.toNat 4).bind (decode w) with
  | some i => exec i m
  | none => m.fail

/-- Execute up to `n` instructions, stopping early once the machine is no longer running. -/
def run {w : Nat} : Nat → Machine w → Machine w
  | 0, m => m
  | n + 1, m => if m.status = .running then run n (step m) else m

/-- A machine with `words` loaded at address 0 of a zeroed memory of `memSize` bytes, about to
execute from address 0. Corresponds to `machine(mem_size)`, `write_i32_vec(words, 0)` and
`run(start=0)`. -/
def load (w : Nat) (words : List (BitVec 32)) (memSize : Nat) (input : List Char) : Machine w :=
  let bytes := words.flatMap fun (x : BitVec 32) => (List.range 4).map fun k => (x >>> (8 * k)).setWidth 8
  { x := ⟨Vector.replicate 32 0⟩
    pc := 0
    mem := (bytes ++ List.replicate (memSize - bytes.length) 0).toArray
    input := input
    output := ""
    status := .running }

/-- Running `a + b` steps is running `a` steps and then `b` more. -/
theorem run_add {w : Nat} (a b : Nat) (m : Machine w) : run (a + b) m = run b (run a m) := by
  induction a generalizing m with
  | zero => simp [run]
  | succ a ih =>
    rw [Nat.add_right_comm, run, run]
    split
    · exact ih _
    · cases b <;> simp [run, *]

/-- Once a machine has stopped (exited or faulted), more fuel leaves it unchanged. -/
theorem run_stopped {w : Nat} (fuel : Nat) (m : Machine w) (h : m.status ≠ .running) :
    run fuel m = m := by
  cases fuel <;> simp [run, h]

/-- The machine has exited with code zero after printing exactly `output`. -/
abbrev is_exited_with_output {w : Nat} (m : Machine w) (output : String) : Prop :=
  m.status = .exited 0 ∧ m.output = output

/-- Extra fuel does not change a run that has already exited with code zero. -/
theorem is_exited_with_output_mono {w : Nat} {a b : Nat} {m : Machine w} {output : String}
    (hab : a ≤ b) (h : is_exited_with_output (run a m) output) :
    is_exited_with_output (run b m) output := by
  rw [show b = a + (b-a) by omega, run_add, run_stopped _ _ (by rw [h.1]; decide)]
  exact h

end TinyFive
