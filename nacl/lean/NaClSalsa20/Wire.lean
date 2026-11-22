import TinyFive.Machine
import Std.Data.HashMap

/-!
# Bit-level normal forms for 32-bit dataflow

A `Wire` describes a 32-bit value (or an 8-bit byte) bit by bit. Each bit is a constant XOR
a set of bits of *atoms*. An atom is an initial memory byte or the sum of two wires, recorded
in an `Arena`. Shifts, rotations, XOR and ORs of values with disjoint bits are therefore pure
rewiring, and two computations that differ only in how they order or associate those
operations get the same wire. Sums are shared through the arena, with their operands ordered.

`Arena.mk` only looks rows up and checks them, so a soundness proof need not trust the
builder `Arena.intern` or the hash index.
-/
namespace NaClSalsa20.Wire

abbrev Id := Nat

/-- Bit `j` of atom `a`. -/
abbrev Term := Id × Nat

/-- A bit: `flip` XOR the listed atom bits. Lists are kept strictly sorted, so equal sets of
terms are equal lists. -/
structure Bit where
  flip : Bool
  terms : List Term
  deriving DecidableEq, Hashable, Repr, Inhabited

def Bit.zero : Bit := ⟨false, []⟩

/-- Bit `i` of a wire is `w.getD i Bit.zero`. -/
abbrev Wire := List Bit

def termLt (a b : Term) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- The symmetric difference of two sorted term lists. -/
def merge : List Term → List Term → List Term
  | [], l => l
  | l, [] => l
  | a :: as, b :: bs =>
    if a = b then merge as bs
    else if termLt a b then a :: merge as (b :: bs)
    else b :: merge (a :: as) bs
termination_by l r => l.length + r.length

def Bit.xor (a b : Bit) : Bit := ⟨a.flip ^^ b.flip, merge a.terms b.terms⟩

/-- The OR of two bits, if one of them is constant. -/
def Bit.or (a b : Bit) : Option Bit :=
  if a.terms = [] then some (if a.flip then ⟨true, []⟩ else b)
  else if b.terms = [] then some (if b.flip then ⟨true, []⟩ else a)
  else none

/-- The AND of two bits, if one of them is constant. -/
def Bit.and (a b : Bit) : Option Bit :=
  if a.terms = [] then some (if a.flip then b else Bit.zero)
  else if b.terms = [] then some (if b.flip then a else Bit.zero)
  else none

def gen (f : Nat → Bit) : Wire := (List.range 32).map f

def genM (f : Nat → Option Bit) : Option Wire := (List.range 32).mapM f

def bit (w : Wire) (i : Nat) : Bit := w.getD i Bit.zero

def const (v : BitVec 32) : Wire := gen fun i => ⟨v.getLsbD i, []⟩

def toConst (w : Wire) : Option (BitVec 32) :=
  if (List.range 32).all (fun i => (bit w i).terms = []) then
    some (BitVec.ofBoolListLE ((List.range 32).map fun i => (bit w i).flip) |>.cast (by simp))
  else none

def xor (a b : Wire) : Wire := gen fun i => (bit a i).xor (bit b i)
def or (a b : Wire) : Option Wire := genM fun i => (bit a i).or (bit b i)
def and (a b : Wire) : Option Wire := genM fun i => (bit a i).and (bit b i)
def shl (k : Nat) (a : Wire) : Wire := gen fun i => if i < k then Bit.zero else bit a (i - k)
def shr (k : Nat) (a : Wire) : Wire := gen fun i => if i + k < 32 then bit a (i + k) else Bit.zero
def sar (k : Nat) (a : Wire) : Wire := gen fun i => if i + k < 32 then bit a (i + k) else bit a 31
def rotl (a : Wire) (k : Nat) : Wire := gen fun i => bit a ((i + 32 - k % 32) % 32)

/-- The wire of atom `id`'s low `n` bits. -/
def atom (n : Nat) (id : Id) : Wire := (List.range n).map fun i => ⟨false, [(id, i)]⟩

/-- Bits `8k` to `8k + 7` of a wire, as a byte. -/
def byte (w : Wire) (k : Nat) : Wire := (List.range 8).map fun j => bit w (8 * k + j)

/-- Four bytes, least significant first, as a word. -/
def pack (b0 b1 b2 b3 : Wire) : Wire :=
  gen fun i => bit (#[b0, b1, b2, b3].getD (i / 8) []) (i % 8)

inductive Node where
  /-- The initial byte at an address, zero-extended. -/
  | leaf (addr : Nat)
  | add (a b : Wire)
  deriving DecidableEq, Hashable, Repr

structure Arena where
  ofFields ::
  nodes : Array Node
  index : Std.HashMap Node Id

namespace Arena

def empty : Arena := ⟨#[], {}⟩

def intern (arena : Arena) (node : Node) : Id × Arena :=
  match arena.index[node]? with
  | some id => (id, arena)
  | none => (arena.nodes.size, ⟨arena.nodes.push node, arena.index.insert node arena.nodes.size⟩)

/-- Every atom a wire refers to precedes `id`. -/
def Below (id : Id) (w : Wire) : Bool := w.all fun b => b.terms.all fun t => t.1 < id

def Node.Before (id : Id) : Node → Bool
  | .leaf _ => true
  | .add a b => Below id a && Below id b

/-- Look a row up, and check it and the order of its operands. -/
def mk (arena : Arena) (node : Node) : Option Id := do
  let id ← arena.index[node]?
  if arena.nodes[id]? = some node ∧ Node.Before id node = true then some id else none

end Arena

/-- The emission interface for atoms: the builder interns, the checker looks up. -/
abbrev Emit (m : Type → Type) := Node → m Id

/-- Sums, with constant folding and ordered operands. -/
def add [Monad m] (emit : Emit m) (a b : Wire) : m Wire := do
  match toConst a, toConst b with
  | some x, some y => return const (x + y)
  | some 0, _ => return b
  | _, some 0 => return a
  | _, _ =>
    let node := if hash b < hash a then Node.add b a else Node.add a b
    return atom 32 (← emit node)

/-- The low 32 bits of a 32-bit ALU operation, where the normal form can express it. -/
def op32 [Monad m] (emit : Emit m) (op : TinyFive.AluOp) (a b : Wire) : m (Option Wire) :=
  match op with
  | .add => return some (← add emit a b)
  | .xor => return some (xor a b)
  | .or => return or a b
  | .and => return and a b
  | .sll => return (toConst b).map fun k => shl (k.toNat % 32) a
  | .srl => return (toConst b).map fun k => shr (k.toNat % 32) a
  | .sra => return (toConst b).map fun k => sar (k.toNat % 32) a
  | _ => return none

/-- The low 32 bits of a 64-bit ALU operation, given the low 32 bits of its operands. -/
def op64 [Monad m] (emit : Emit m) (op : TinyFive.AluOp) (a b : Wire) : m (Option Wire) :=
  match op with
  | .add | .xor | .or | .and => op32 emit op a b
  | .sll => return (toConst b).map fun k => shl (k.toNat % 64) a
  | _ => return none

end NaClSalsa20.Wire
