import TweetNaCl.Salsa20Slots
import TweetNaCl.Salsa20Circuit

/-! Fold the checked slot actions into a circuit. Public constants are folded,
while input bytes and caller registers remain uninterpreted. The arena builder
is only a hint: the second pass checks every row against its indexed node. -/
namespace TweetNaCl.Salsa20Symbolic
open TinyFive Salsa20Circuit

inductive Value where
  | literal (v : BitVec 64)
  | ref (id : Id)
  deriving Inhabited, DecidableEq

def Value.eval (a : Arena) (e : Leaves) : Value → BitVec 64
  | .literal v => v
  | .ref id => a.eval e id

abbrev Emit (m : Type → Type) := Node → m Id

def toRef [Monad m] (emit : Emit m) : Value → m Id
  | .literal v => emit (.constant v)
  | .ref id => pure id

def wordAlu (op : AluOp) (a b : BitVec 64) : BitVec 64 :=
  (alu op (a.setWidth 32) (b.setWidth 32)).signExtend 64

def apply [Monad m] (emit : Emit m) (narrow : Bool) (op : AluOp) (a b : Value) : m Value := do
  match a, b with
  | .literal a, .literal b => pure (.literal (if narrow then wordAlu op a b else alu op a b))
  | _, _ =>
    let x ← toRef emit a
    let y ← toRef emit b
    return .ref (← emit (if narrow then .applyWord op x y else .apply op x y))

def trunc [Monad m] (emit : Emit m) : Value → m Value
  | .literal v => pure (.literal ((v.setWidth 8).setWidth 64))
  | .ref id => return .ref (← emit (.truncByte id))

def readArg [Monad m] (emit : Emit m) (a : Nat) : m Value := do
  return .ref (← emit (.argByte a))

structure State where
  regs : Std.TreeMap Nat Value := {}
  mem : Std.TreeMap Nat Value := {}
  pc : BitVec 64

def getReg [Monad m] (emit : Emit m) (s : State) (r : Reg) : m Value := do
  if r = 0 then return .literal 0
  if let some v := s.regs[r.val]? then return v
  return .ref (← emit (.savedReg r))

def getMem [Monad m] (emit : Emit m) (s : State) (w : Width) (a : Nat) : m Value := do
  if let some v := s.mem[a]? then return v
  if w = .byte then readArg emit a else return .ref (← emit (.bytes a w))

def expr [Monad m] (emit : Emit m) (s : State) : Salsa20Slots.Expr → m Value
  | .literal v => pure (.literal v)
  | .pcAdd offset => pure (.literal (s.pc + offset))
  | .load w _ rd => getMem emit s w rd
  | .opImm op r imm => do apply emit false op (← getReg emit s r) (.literal (imm.signExtend 64))
  | .op op r t => do apply emit false op (← getReg emit s r) (← getReg emit s t)
  | .opImmWord op r imm => do
    apply emit true op (← getReg emit s r) (.literal (imm.signExtend 64))
  | .opWord op r t => do apply emit true op (← getReg emit s r) (← getReg emit s t)

def step [Monad m] (emit : Emit m) (s : State) : Salsa20Slots.Action → m State
  | .setReg rd e => do
    let value ← expr emit s e
    return { s with regs := s.regs.insert rd.val value, pc := s.pc + 4 }
  | .store w a src => do
    let v ← getReg emit s src
    let v ← if w = .byte then trunc emit v else pure v
    return { s with mem := s.mem.insert a v, pc := s.pc + 4 }
  | .jump rd target => pure { s with regs := s.regs.insert rd.val (.literal (s.pc + 4)), pc := target }
  | .advance offset => pure { s with pc := s.pc + offset }

def run [Monad m] (emit : Emit m) (as : List Salsa20Slots.Action) (s : State) : m State :=
  as.foldlM (step emit) s

/-- Initial circuit value of a slot before the first symbolic write. -/
def initialMem (env : Leaves) (w : Width) (addr : Nat) : Word :=
  if w = .byte then (env.argByte addr).zeroExtend 64 else (env.read addr w.bytes).zeroExtend 64

/-- Missing symbolic entries denote arbitrary initial register and byte leaves. -/
def State.Related (arena : Arena) (env : Leaves) (l : Salsa20Slots.Layout)
    (s : State) (t : Salsa20Slots.State) : Prop :=
  s.pc = t.pc ∧
  (∀ (r : Reg), r ≠ 0 →
    (s.regs[r.val]?.map (Value.eval arena env)).getD (env.savedReg r) = t.x.get r) ∧
  (∀ w a, l.Allows w a →
    (s.mem[a]?.map (Value.eval arena env)).getD (initialMem env w a) = t.mem.get a)

/-- The circuit format does not encode byte sign-extension. Full-width
signed loads are fine, since sign-extension at the same width is identity. -/
def Supported (l : Salsa20Slots.Layout) : Salsa20Slots.Action → Prop
  | .setReg _ (.load w signed a) => l.Allows w a ∧ (signed = false ∨ w = .dword)
  | .store w a _ => l.Allows w a
  | _ => True

instance (l : Salsa20Slots.Layout) (a : Salsa20Slots.Action) : Decidable (Supported l a) := by
  cases a with
  | setReg rd e => cases e <;> unfold Supported <;> infer_instance
  | _ => unfold Supported; infer_instance

private theorem toRef_sound {arena : Arena} (env : Leaves) {v : Value} {i : Id}
    (h : toRef arena.mk v = some i) : arena.eval env i = v.eval arena env := by
  cases v with
  | literal v => exact arena.mk_sound env h
  | ref id => cases h; rfl

theorem apply_sound {arena : Arena} (env : Leaves) {narrow : Bool} {op : AluOp}
    {x y v : Value} (h : apply arena.mk narrow op x y = some v) :
    v.eval arena env = if narrow then wordAlu op (x.eval arena env) (y.eval arena env)
      else alu op (x.eval arena env) (y.eval arena env) := by
  cases x <;> cases y
  · cases h; rfl
  all_goals
    simp only [apply, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := h
    have he := arena.mk_sound env hk
    cases narrow <;> simpa [Value.eval, Node.eval, wordAlu, toRef_sound env hi, toRef_sound env hj] using he

theorem trunc_sound {arena : Arena} (env : Leaves) {x v : Value}
    (h : trunc arena.mk x = some v) :
    v.eval arena env = ((x.eval arena env).setWidth 8).setWidth 64 := by
  cases x with
  | literal x => cases h; rfl
  | ref i =>
    simp only [trunc, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨k, hk, rfl⟩ := h
    exact arena.mk_sound env hk

private theorem getReg_sound {arena : Arena} {env : Leaves} {l : Salsa20Slots.Layout}
    {s : State} {t : Salsa20Slots.State} {r : Reg} {v : Value}
    (h : s.Related arena env l t) (hr : getReg arena.mk s r = some v) :
    v.eval arena env = t.x.get r := by
  by_cases hz : r = 0
  · subst r
    simp [getReg, pure] at hr
    subst v
    rfl
  · have hrel := h.2.1 r hz
    cases hs : s.regs[r.val]? with
    | some a =>
      simp [getReg, hz, hs, pure] at hr
      subst v
      simpa [hs, Option.getD] using hrel
    | none =>
      simp only [getReg, hz, ite_false, hs, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr
      obtain ⟨i, hi, rfl⟩ := hr
      exact (arena.mk_sound env hi).trans (by simpa [hs, Node.eval, Option.getD] using hrel)

private theorem getMem_sound {arena : Arena} {env : Leaves} {l : Salsa20Slots.Layout}
    {s : State} {t : Salsa20Slots.State} {w : Width} {a : Nat} {v : Value}
    (h : s.Related arena env l t) (ha : l.Allows w a) (hr : getMem arena.mk s w a = some v) :
    v.eval arena env = t.mem.get a := by
  have hrel := h.2.2 w a ha
  cases hs : s.mem[a]? with
  | some x =>
    simp [getMem, hs, pure] at hr
    subst v
    simpa [hs, Option.getD] using hrel
  | none =>
    by_cases hw : w = .byte
    · simp only [getMem, hs, hw, ite_true, readArg, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr
      obtain ⟨i, hi, rfl⟩ := hr
      exact (arena.mk_sound env hi).trans (by simpa [hs, initialMem, hw, Node.eval, Option.getD] using hrel)
    · simp only [getMem, hs, hw, ite_false, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr
      obtain ⟨i, hi, rfl⟩ := hr
      exact (arena.mk_sound env hi).trans (by simpa [hs, initialMem, hw, Node.eval, Option.getD] using hrel)

private theorem imm_narrow (imm : BitVec 12) : (imm.signExtend 64).setWidth 32 = imm.signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h64 : i < 64 := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi, h64,
    decide_true, Bool.true_and]

private theorem expr_sound {arena : Arena} {env : Leaves} {l : Salsa20Slots.Layout}
    {s : State} {t : Salsa20Slots.State} {rd : Reg} {e : Salsa20Slots.Expr} {v : Value}
    (h : s.Related arena env l t) (hs : Supported l (.setReg rd e))
    (he : expr arena.mk s e = some v) : v.eval arena env = e.eval t := by
  cases e with
  | literal v => cases he; rfl
  | pcAdd off => cases he; exact congrArg (· + off) h.1
  | load w signed a =>
    have hv := getMem_sound h hs.1 he
    rcases hs.2 with hf | hd
    · simpa [Salsa20Slots.Expr.eval, hf] using hv
    · subst w
      simpa [Salsa20Slots.Expr.eval, Width.bytes] using hv
  | opImm op r imm =>
    simp only [expr, bind, Option.bind_eq_some_iff] at he
    obtain ⟨x, hx, he⟩ := he
    have hv := apply_sound env he
    rw [getReg_sound h hx] at hv
    exact hv
  | op op r q =>
    simp only [expr, bind, Option.bind_eq_some_iff] at he
    obtain ⟨x, hx, y, hy, he⟩ := he
    simpa [Salsa20Slots.Expr.eval, getReg_sound h hx, getReg_sound h hy] using apply_sound env he
  | opImmWord op r imm =>
    simp only [expr, bind, Option.bind_eq_some_iff] at he
    obtain ⟨x, hx, he⟩ := he
    have hv := apply_sound env he
    rw [getReg_sound h hx] at hv
    simpa [Salsa20Slots.Expr.eval, Value.eval, wordAlu, imm_narrow] using hv
  | opWord op r q =>
    simp only [expr, bind, Option.bind_eq_some_iff] at he
    obtain ⟨x, hx, y, hy, he⟩ := he
    simpa [Salsa20Slots.Expr.eval, wordAlu, getReg_sound h hx, getReg_sound h hy] using apply_sound env he

private theorem regs_insert_sound {arena : Arena} {env : Leaves} {l : Salsa20Slots.Layout}
    {s : State} {t : Salsa20Slots.State} {rd : Reg} {v : Value} {value : Word}
    (h : s.Related arena env l t) (hv : v.eval arena env = value) (r : Reg) (hr : r ≠ 0) :
    ((s.regs.insert rd.val v)[r.val]?.map (Value.eval arena env)).getD (env.savedReg r) =
      (t.x.set rd value).get r := by
  by_cases he : rd = r
  · subst rd
    simp [Regs.get_set, hr, hv, Option.getD]
  · have hval : rd.val ≠ r.val := fun hh => he (Fin.ext hh)
    simpa [Std.TreeMap.getElem?_insert, Regs.get_set, hr, he, hval] using h.2.1 r hr

private theorem mem_insert_sound {arena : Arena} {env : Leaves} {l : Salsa20Slots.Layout}
    {s : State} {t : Salsa20Slots.State} {w : Width} {a : Nat} {v : Value} {value : Word}
    (h : s.Related arena env l t) (hv : v.eval arena env = (value.setWidth (8 * w.bytes)).setWidth 64)
    (q : Width) (b : Nat) (hb : l.Allows q b) :
    ((s.mem.insert a v)[b]?.map (Value.eval arena env)).getD (initialMem env q b) =
      (t.mem.set w a value).get b := by
  by_cases he : a = b
  · subst b
    simp [hv, Option.getD]
  · simpa [Std.TreeMap.getElem?_insert, he] using h.2.2 q b hb

theorem step_sound {arena : Arena} {env : Leaves} {l : Salsa20Slots.Layout}
    {s s' : State} {t : Salsa20Slots.State} {a : Salsa20Slots.Action}
    (h : s.Related arena env l t) (hs : Supported l a)
    (he : step arena.mk s a = some s') : s'.Related arena env l (a.eval t) := by
  cases a with
  | setReg rd expr =>
    simp only [step, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at he
    obtain ⟨v, hv, rfl⟩ := he
    exact ⟨congrArg (· + 4) h.1, regs_insert_sound h (expr_sound h hs hv), h.2.2⟩
  | store w a src =>
    rcases hs.2 with ⟨rfl, _⟩ | ⟨rfl, _, _⟩
    · simp only [step, ite_true, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at he
      obtain ⟨x, hx, v, hv, rfl⟩ := he
      have hreg := getReg_sound h hx
      exact ⟨congrArg (· + 4) h.1, h.2.1, mem_insert_sound h
        (by simpa [Width.bytes, hreg] using trunc_sound env hv)⟩
    · simp only [step, show Width.dword ≠ .byte by decide, ite_false, pure, bind,
        Option.bind_eq_some_iff, Option.some.injEq, exists_eq_left'] at he
      obtain ⟨x, hx, rfl⟩ := he
      exact ⟨congrArg (· + 4) h.1, h.2.1, mem_insert_sound h
        (by simpa [Width.bytes] using getReg_sound h hx)⟩
  | jump rd target =>
    cases he
    exact ⟨rfl, regs_insert_sound h (congrArg (· + 4) h.1), h.2.2⟩
  | advance off =>
    cases he
    exact ⟨congrArg (· + off) h.1, h.2⟩

/-- A successful check with the fixed arena preserves the concrete semantics of
all registers, PC, and legal memory slots for every environment. -/
theorem run_sound {arena : Arena} {env : Leaves} {l : Salsa20Slots.Layout}
    {as : List Salsa20Slots.Action} {s s' : State} {t : Salsa20Slots.State}
    (hs : ∀ a ∈ as, Supported l a) (h : s.Related arena env l t)
    (he : run arena.mk as s = some s') : s'.Related arena env l (Salsa20Slots.run as t) := by
  induction as generalizing s t with
  | nil => cases he; exact h
  | cons a as ih =>
    simp only [run, List.foldlM_cons, bind, Option.bind_eq_some_iff] at he
    obtain ⟨mid, hm, hf⟩ := he
    exact ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))
      (step_sound h (hs a (List.mem_cons_self ..)) hm) hf

end TweetNaCl.Salsa20Symbolic
