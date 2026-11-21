import TinyFive.Machine
import Std.Data.TreeMap

/-! A shared expression arena for comparing two symbolic Salsa20 executions.
`intern` builds the candidate arena; `mk` checks membership in a fixed arena.
The index is just a hint: the checking theorem does not trust the builder
or require a global invariant on the index. -/

namespace TweetNaCl.Salsa20Circuit
open TinyFive

abbrev Id := Nat
abbrev Word := BitVec 64

inductive Node where
  | constant (v : Word)
  | savedReg (reg : Reg)
  | argByte (addr : Nat)
  | bytes (addr : Nat) (width : Width)
  | apply (op : AluOp) (a b : Id)
  | applyWord (op : AluOp) (a b : Id)
  | truncByte (a : Id)
  deriving DecidableEq, Repr


private def aluTag : AluOp → Nat
  | .add => 0 | .sub => 1 | .sll => 2 | .slt => 3 | .sltu => 4
  | .xor => 5 | .srl => 6 | .sra => 7 | .or => 8 | .and => 9
  | .mul => 10 | .mulh => 11 | .mulhsu => 12 | .mulhu => 13
  | .div => 14 | .divu => 15 | .rem => 16 | .remu => 17

private def widthTag : Width → Nat
  | .byte => 0 | .half => 1 | .word => 2 | .dword => 3

private def Node.key : Node → Nat × Nat × Nat × Nat
  | .constant v => (0, v.toNat, 0, 0)
  | .savedReg r => (1, r.val, 0, 0)
  | .argByte addr => (2, addr, 0, 0)
  | .bytes addr w => (3, addr, widthTag w, 0)
  | .apply op a b => (4, aluTag op, a, b)
  | .applyWord op a b => (5, aluTag op, a, b)
  | .truncByte a => (6, a, 0, 0)

/-- Lexicographic order on fixed-size node keys, using kernel-reducible operations. -/
def Node.compare (x y : Node) : Ordering :=
  let (t, a, b, c) := x.key
  let (t', a', b', c') := y.key
  (Ord.compare t t').then <| (Ord.compare a a').then <| (Ord.compare b b').then (Ord.compare c c')

/-- Initial data leaves, interpreted independently of the builder and its index. -/
structure Leaves where
  savedReg : Reg → Word
  argByte : Nat → BitVec 8

/-- A little-endian load from byte leaves. -/
def Leaves.read (env : Leaves) (addr : Nat) : (n : Nat) → BitVec (8 * n)
  | 0 => 0#0
  | n + 1 => (env.read (addr + 1) n ++ env.argByte addr).cast (by omega)

def Node.eval (env : Leaves) (value : Id → Word) : Node → Word
  | .constant v => v
  | .savedReg r => env.savedReg r
  | .argByte addr => (env.argByte addr).zeroExtend 64
  | .bytes addr w => (env.read addr w.bytes).zeroExtend 64
  | .apply op a b => alu op (value a) (value b)
  | .applyWord op a b => (alu op ((value a).setWidth 32) ((value b).setWidth 32)).signExtend 64
  | .truncByte a => ((value a).setWidth 8).zeroExtend 64

/-- All operand IDs precede the row that uses them. -/
def Node.Before (id : Id) : Node → Prop
  | .apply _ a b | .applyWord _ a b => a < id ∧ b < id
  | .truncByte a => a < id
  | _ => True

instance (id : Id) (node : Node) : Decidable (node.Before id) := by
  cases node <;> unfold Node.Before <;> infer_instance

structure Arena where
  ofFields ::
  nodes : Array Node
  index : Std.TreeMap Node Id Node.compare

namespace Arena

def empty : Arena := ⟨#[], ∅⟩

/-- Build a candidate arena in topological order, sharing identical nodes. The
verifier below checks its result, so no builder invariant is needed in proofs. -/
def intern (arena : Arena) (node : Node) : Id × Arena :=
  match arena.index[node]? with
  | some id => (id, arena)
  | none =>
    let id := arena.nodes.size
    (id, ⟨arena.nodes.push node, arena.index.insert node id⟩)

/-- Look up a row by expression and check both the hint and its operand bounds. -/
def mk (arena : Arena) (node : Node) : Option Id := do
  let id ← arena.index[node]?
  if arena.nodes[id]? = some node ∧ node.Before id then some id else none

theorem mk_get {arena : Arena} {node : Node} {id : Id}
    (h : arena.mk node = some id) :
    arena.nodes[id]? = some node ∧ node.Before id := by
  unfold mk at h
  cases hh : arena.index[node]? with
  | none => simp [hh] at h
  | some i =>
    simp only [hh, bind, Option.bind] at h
    split at h
    next checked =>
      cases h
      exact checked
    next => contradiction

/-- Total interpretation of an ID. Unchecked missing or non-topological rows
are assigned zero; `mk_sound` proves this default is not used at a checked row. -/
def eval (arena : Arena) (env : Leaves) (id : Id) : Word :=
  match arena.nodes[id]? with
  | none => 0
  | some (.apply op a b) =>
    if _h : a < id ∧ b < id then alu op (eval arena env a) (eval arena env b) else 0
  | some (.applyWord op a b) =>
    if _h : a < id ∧ b < id then
      (alu op ((eval arena env a).setWidth 32) ((eval arena env b).setWidth 32)).signExtend 64
    else 0
  | some (.truncByte a) =>
    if _h : a < id then ((eval arena env a).setWidth 8).zeroExtend 64 else 0
  | some (.constant v) => v
  | some (.savedReg r) => env.savedReg r
  | some (.argByte addr) => (env.argByte addr).zeroExtend 64
  | some (.bytes addr w) => (env.read addr w.bytes).zeroExtend 64
termination_by id
decreasing_by all_goals first | exact _h.1 | exact _h.2 | exact _h

theorem eval_eq_of_get {arena : Arena} {node : Node} {id : Id} (env : Leaves)
    (h : arena.nodes[id]? = some node) (hb : node.Before id) :
    arena.eval env id = node.eval env (arena.eval env) := by
  rw [eval, h]
  cases node <;> simp_all [Node.Before, Node.eval]

/-- Certificate-checking is sound for every choice of initial registers/bytes. -/
theorem mk_sound {arena : Arena} {node : Node} {id : Id} (env : Leaves)
    (h : arena.mk node = some id) :
    arena.eval env id = node.eval env (arena.eval env) :=
  eval_eq_of_get env (mk_get h).1 (mk_get h).2

/-- Even a corrupt hint cannot cause different expressions to share a checked ID. -/
theorem mk_same_id {arena : Arena} {a b : Node} {id : Id}
    (ha : arena.mk a = some id) (hb : arena.mk b = some id) : a = b :=
  Option.some.inj ((mk_get ha).1.symm.trans (mk_get hb).1)

end Arena
end TweetNaCl.Salsa20Circuit
