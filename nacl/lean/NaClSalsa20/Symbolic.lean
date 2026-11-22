import NaClSalsa20.Wire
import TweetNaCl.Salsa20Replay
import Std.Data.TreeMap

/-!
# Symbolic dataflow over a checked schedule

The replay certificate fixes every instruction, branch decision and memory address. This pass
follows the data: it tracks the low 32 bits of each register, and each memory byte, as wires.
A register missing from `regs` is unknown. A byte missing from `mem` still holds its initial
value, an atom `leaf`; a byte mapped to `none` is unknown.
-/
namespace NaClSalsa20.Symbolic
open TinyFive Wire
open TweetNaCl.Salsa20Replay (Event Effect)

structure State where
  regs : Std.TreeMap Nat Wire := {}
  mem : Std.TreeMap Nat (Option Wire) := {}

def State.get (s : State) (r : Reg) : Option Wire :=
  if r = 0 then some (const 0) else s.regs[r.val]?

def State.set (s : State) (r : Reg) : Option Wire → State
  | some w => { s with regs := s.regs.insert r.val w }
  | none => { s with regs := s.regs.erase r.val }

/-- The byte at `addr`, introducing a leaf atom for an initial byte. -/
def getByte [Monad m] (emit : Emit m) (s : State) (addr : Nat) : m (Option Wire) :=
  match s.mem[addr]? with
  | some b => pure b
  | none => return some (atom 8 (← emit (.leaf addr)))

/-- The low 32 bits of a load of `n` bytes at `addr`. -/
def load [Monad m] (emit : Emit m) (s : State) (addr n : Nat) (signed : Bool) :
    m (Option Wire) := do
  let bytes ← (List.range (min n 4)).mapM fun k => getByte emit s (addr + k)
  return (bytes.mapM id).map fun bs =>
    gen fun i =>
      if i < 8 * n then bit (bs.getD (i / 8) []) (i % 8)
      else if signed then bit (bs.getD (n - 1) []) 7 else Bit.zero

def store (s : State) (addr n : Nat) (v : Option Wire) : State :=
  { s with mem := (List.range n).foldl (fun mem k =>
      mem.insert (addr + k) (if k < 4 then v.map (byte · k) else none)) s.mem }

def imm32 (imm : BitVec 12) : Wire := const (imm.signExtend 32)

def optOp [Monad m] (f : Wire → Wire → m (Option Wire)) : Option Wire → Option Wire → m (Option Wire)
  | some a, some b => f a b
  | _, _ => pure none

def step [Monad m] (emit : Emit m) (s : State) (e : Event) : m State :=
  match e.instr, e.effect with
  | .load w signed rd _ _, .load addr _ => return s.set rd (← load emit s addr w.bytes signed)
  | .store w src _ _, .store addr _ => return store s addr w.bytes (s.get src)
  | .lui rd imm, _ => return s.set rd (some (const ((imm ++ 0#12).signExtend 32)))
  | .opImm op rd r imm, _ => return s.set rd (← optOp (op64 emit op) (s.get r) (some (imm32 imm)))
  | .op op rd r t, _ => return s.set rd (← optOp (op64 emit op) (s.get r) (s.get t))
  | .opImmWord op rd r imm, _ =>
    return s.set rd (← optOp (op32 emit op) (s.get r) (some (imm32 imm)))
  | .opWord op rd r t, _ => return s.set rd (← optOp (op32 emit op) (s.get r) (s.get t))
  | .jal rd _, _ | .jalr rd _ _, _ | .auipc rd _, _ => return s.set rd none
  | _, _ => return s

def run [Monad m] (emit : Emit m) (es : List Event) (s : State) : m State := es.foldlM (step emit) s

/-- The events this pass supports: matching instruction and effect, accesses in memory. -/
def Event.Ok (capacity : Nat) (e : Event) : Bool :=
  match e.instr, e.effect with
  | .load w _ _ _ _, .load addr n | .store w _ _ _, .store addr n =>
    n == w.bytes && addr + w.bytes ≤ capacity
  | .jal _ _, .jump _ | .jalr _ _ _, .jump _ | .branch _ _ _ _, .branch _ => true
  | .lui .., .plain | .auipc .., .plain | .opImm .., .plain | .op .., .plain
  | .opImmWord .., .plain | .opWord .., .plain => true
  | _, _ => false

end NaClSalsa20.Symbolic
