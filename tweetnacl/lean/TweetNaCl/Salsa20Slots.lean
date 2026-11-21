import TweetNaCl.Salsa20Replay
import TinyFive.SieveMemory

/-!
# Straight-line RV64 replay over disjoint memory slots

Only schedule addresses, widths, and control effects are fixed. The register file
and initial slot contents are ordinary parameters, including secret data. A slot
is either one byte in a byte block, or the whole aligned eight-byte word in a
word block. Layout membership checks suffice to rule out partially overlapping
accesses, even between different steps of a schedule.
-/
namespace TweetNaCl.Salsa20Slots

open TinyFive
open Salsa20Replay (Word Byte Event)

structure Layout where
  capacity : Nat
  /-- Classify each eight-byte block, indexed by `address / 8`. -/
  wordBlock : Nat → Bool

def Layout.Allows (l : Layout) (w : Width) (a : Nat) : Prop :=
  a + w.bytes ≤ l.capacity ∧
    ((w = .byte ∧ l.wordBlock (a / 8) = false) ∨
     (w = .dword ∧ l.wordBlock (a / 8) = true ∧ a % 8 = 0))

instance (l : Layout) (w : Width) (a : Nat) : Decidable (l.Allows w a) :=
  inferInstanceAs (Decidable (_ ∧ ((_ ∧ _) ∨ (_ ∧ _ ∧ _))))

/-- Two allowed accesses are either to the very same slot or disjoint. -/
theorem Layout.same_or_disjoint {l : Layout} {w q : Width} {a b : Nat}
    (ha : l.Allows w a) (hb : l.Allows q b) :
    (a = b ∧ w = q) ∨ a + w.bytes ≤ b ∨ b + q.bytes ≤ a := by
  rcases ha.2 with ⟨rfl, hla⟩ | ⟨rfl, hla, ha8⟩ <;>
    rcases hb.2 with ⟨rfl, hlb⟩ | ⟨rfl, hlb, hb8⟩ <;>
    simp only [Width.bytes, eq_self, and_true]
  · omega
  · by_cases he : a / 8 = b / 8
    · rw [he, hlb] at hla
      contradiction
    · omega
  · by_cases he : a / 8 = b / 8
    · rw [he, hlb] at hla
      contradiction
    · omega
  · omega

/-- Separate immutable initial contents from the finite set of writes. -/
structure Memory where
  initial : Nat → Word
  writes : Std.TreeMap Nat Word := {}

def Memory.get (s : Memory) (addr : Nat) : Word := s.writes[addr]?.getD (s.initial addr)

/-- Byte slots hold a zero-extended byte; dword slots hold a full word. -/
def Memory.set (s : Memory) (w : Width) (addr : Nat) (v : Word) : Memory :=
  { s with writes := s.writes.insert addr (v.setWidth (8 * w.bytes) |>.setWidth 64) }

@[simp] theorem Memory.get_set (s : Memory) (w : Width) (a b : Nat) (v : Word) :
    (s.set w a v).get b = if a = b then (v.setWidth (8 * w.bytes)).setWidth 64 else s.get b := by
  by_cases h : a = b <;> simp [get, set, Std.TreeMap.getElem?_insert, h]

/-- Every legal slot agrees exactly with the little-endian concrete read (zero
extended to a register width). No assumption is made on the underlying bytes. -/
def Memory.Related (l : Layout) (s : Memory) (mem : Array Byte) : Prop :=
  mem.size = l.capacity ∧
    ∀ w a, l.Allows w a → readBytes mem a w.bytes = some ((s.get a).setWidth (8 * w.bytes)) ∧
      ((s.get a).setWidth (8 * w.bytes)).setWidth 64 = s.get a

private theorem read_inBounds {mem : Array Byte} {a n : Nat} (h : a + n ≤ mem.size) :
    ∃ v, readBytes mem a n = some v := by
  induction n generalizing a with
  | zero => exact ⟨_, rfl⟩
  | succ n ih =>
    have ha : a < mem.size := by omega
    obtain ⟨hi, hhi⟩ := ih (a := a + 1) (by omega)
    simp [readBytes, Array.getElem?_eq_getElem ha, hhi]

private theorem append_setWidth {k : Nat} (v : BitVec k) (n : Nat) :
    (((v >>> 8).setWidth (8 * n) ++ v.setWidth 8).cast (by omega) : BitVec (8 * (n + 1))) =
      v.setWidth (8 * (n + 1)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  by_cases h : i < 8
  · simp [h, hi]
  · simp [h, hi, show i - 8 < 8 * n by omega, show 8 + (i - 8) = i by omega]

private theorem writeBytes_spec (n : Nat) (mem : Array Byte) (addr : Nat) (v : Word)
    (h : addr + n ≤ mem.size) :
    ∃ mem', writeBytes mem addr v n = some mem' ∧ mem'.size = mem.size ∧
      (∀ i, i < addr ∨ addr + n ≤ i → mem'[i]? = mem[i]?) ∧
      readBytes mem' addr n = some (v.setWidth (8 * n)) := by
  induction n generalizing mem addr v with
  | zero =>
    refine ⟨mem, rfl, rfl, fun _ _ => rfl, ?_⟩
    simp only [readBytes]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_one]
  | succ n ih =>
    have hlt : addr < mem.size := by omega
    obtain ⟨mem', hw, hs, hf, hr⟩ := ih (mem.setIfInBounds addr (v.setWidth 8)) (addr + 1)
      (v >>> 8) (by rw [Array.size_setIfInBounds]; omega)
    refine ⟨mem', ?_, ?_, ?_, ?_⟩
    · simpa only [writeBytes, hlt, ite_true] using hw
    · rw [hs, Array.size_setIfInBounds]
    · intro i hi
      rw [hf i (by omega), Array.getElem?_setIfInBounds_ne (by omega)]
    · have hlo : mem'[addr]? = some (v.setWidth 8) := by
        rw [hf addr (by omega), Array.getElem?_setIfInBounds_self_of_lt hlt]
      simp only [readBytes, hlo, hr, bind, Option.bind]
      congr 1
      exact append_setWidth v n

private theorem Width.bits_le (w : Width) : 8 * w.bytes ≤ 64 := by cases w <;> decide

/-- Abstract a concrete array lazily: words are packed only when read. -/
def Memory.ofBytes (l : Layout) (mem : Array Byte) : Memory :=
  { initial := fun a =>
      if l.wordBlock (a / 8) then (readBytes mem a 8).getD 0
      else ((readBytes mem a 1).getD 0).setWidth 64 }

theorem Memory.ofBytes_related (l : Layout) (mem : Array Byte) (h : mem.size = l.capacity) :
    (Memory.ofBytes l mem).Related l mem := by
  refine ⟨h, fun w a ha => ?_⟩
  obtain ⟨v, hv⟩ := read_inBounds (mem := mem) (h ▸ ha.1)
  rcases ha.2 with ⟨rfl, hbyte⟩ | ⟨rfl, hword, _⟩
  · change BitVec 8 at v
    change readBytes mem a 1 = some v at hv
    rw [SieveMemory.readBytes_byte] at hv
    simp [Memory.get, Memory.ofBytes, Width.bytes, hbyte, hv, Option.getD]
  · change BitVec 64 at v
    change readBytes mem a 8 = some v at hv
    simp [Memory.get, Memory.ofBytes, Width.bytes, hword, hv, Option.getD]

/-- Updating a slot simulates the byte-array update, preserving all disjoint slots. -/
theorem Memory.Related.store {l : Layout} {s : Memory} {mem : Array Byte}
    (h : s.Related l mem) {w : Width} {a : Nat} (ha : l.Allows w a) (v : Word) :
    ∃ mem', writeBytes mem a v w.bytes = some mem' ∧ (s.set w a v).Related l mem' := by
  obtain ⟨mem', hw, hs, hf, hr⟩ := writeBytes_spec w.bytes mem a v (h.1 ▸ ha.1)
  refine ⟨mem', hw, hs.trans h.1, fun q b hb => ?_⟩
  rcases Layout.same_or_disjoint ha hb with ⟨rfl, rfl⟩ | hd
  · simp [hr, BitVec.setWidth_setWidth_of_le, Width.bits_le]
  · have hne : a ≠ b := by
      have hp (q : Width) : 0 < q.bytes := by cases q <;> decide
      have hpa := hp w
      have hpb := hp q
      omega
    have hrd : readBytes mem' b q.bytes = readBytes mem b q.bytes := by
      apply SieveMemory.readBytes_congr
      intro i hlo hhi
      exact hf i (by omega)
    simpa [hrd, hne] using h.2 q b hb

/-- The dataflow evaluator keeps the actual registers and slot contents. -/
structure State where
  x : Regs 64
  pc : Word
  mem : Memory

def State.ofMachine (l : Layout) (m : Machine 64) : State :=
  ⟨m.x, m.pc, Memory.ofBytes l m.mem⟩

def State.Related (l : Layout) (s : State) (m : Machine 64) : Prop :=
  s.x = m.x ∧ s.pc = m.pc ∧ s.mem.Related l m.mem

theorem State.ofMachine_related (l : Layout) (m : Machine 64) (h : m.mem.size = l.capacity) :
    (State.ofMachine l m).Related l m := ⟨rfl, rfl, Memory.ofBytes_related l m.mem h⟩

/-- Data inputs to a register assignment. A load has no dynamic address. -/
inductive Expr where
  | literal (value : Word)
  | pcAdd (offset : Word)
  | load (width : Width) (signed : Bool) (address : Nat)
  | opImm (op : AluOp) (src : Reg) (imm : BitVec 12)
  | op (op : AluOp) (lhs rhs : Reg)
  | opImmWord (op : AluOp) (src : Reg) (imm : BitVec 12)
  | opWord (op : AluOp) (lhs rhs : Reg)
  deriving Inhabited

def Expr.eval (s : State) : Expr → Word
  | .literal v => v
  | .pcAdd offset => s.pc + offset
  | .load w signed a =>
    if signed then ((s.mem.get a).setWidth (8 * w.bytes)).signExtend 64 else s.mem.get a
  | .opImm f r imm => alu f (s.x.get r) (imm.signExtend 64)
  | .op f r t => alu f (s.x.get r) (s.x.get t)
  | .opImmWord f r imm => (alu f ((s.x.get r).setWidth 32) (imm.signExtend 32)).signExtend 64
  | .opWord f r t => (alu f ((s.x.get r).setWidth 32) ((s.x.get t).setWidth 32)).signExtend 64

/-- Fixed control flow only changes PC/link; no action branches on its data. -/
inductive Action where
  | setReg (rd : Reg) (value : Expr)
  | store (width : Width) (address : Nat) (src : Reg)
  | jump (link : Reg) (target : Word)
  | advance (offset : Word)
  deriving Inhabited

def Action.eval (s : State) : Action → State
  | .setReg rd e => { s with x := s.x.set rd (e.eval s), pc := s.pc + 4 }
  | .store w a src => { s with mem := s.mem.set w a (s.x.get src), pc := s.pc + 4 }
  | .jump rd target => { s with x := s.x.set rd (s.pc + 4), pc := target }
  | .advance offset => { s with pc := s.pc + offset }

/-- Lower a scheduled instruction, rejecting unsupported operations, mismatched
recorded effects, out-of-bounds accesses, and illegal slot widths/alignments. -/
def lower (l : Layout) (e : Event) : Option Action :=
  match e.instr, e.effect with
  | .lui rd imm, .plain => some (.setReg rd (.literal ((imm ++ 0#12).signExtend 64)))
  | .auipc rd imm, .plain => some (.setReg rd (.pcAdd ((imm ++ 0#12).signExtend 64)))
  | .jal rd _, .jump dest | .jalr rd _ _, .jump dest => some (.jump rd dest)
  | .branch _ _ _ imm, .branch taken => some (.advance (if taken then imm.signExtend 64 else 4))
  | .load w signed rd _ _, .load a n =>
    if n = w.bytes ∧ l.Allows w a then some (.setReg rd (.load w signed a)) else none
  | .store w src _ _, .store a n =>
    if n = w.bytes ∧ l.Allows w a then some (.store w a src) else none
  | .opImm op rd r imm, .plain => some (.setReg rd (.opImm op r imm))
  | .op op rd r t, .plain => some (.setReg rd (.op op r t))
  | .opImmWord op rd r imm, .plain => some (.setReg rd (.opImmWord op r imm))
  | .opWord op rd r t, .plain => some (.setReg rd (.opWord op r t))
  | _, _ => none

theorem lower_sound {l : Layout} {s : State} {m : Machine 64} {e : Event} {a : Action}
    (h : s.Related l m) (he : lower l e = some a) :
    (a.eval s).Related l (Salsa20Replay.fixedStep m e) := by
  obtain ⟨hx, hp, hm⟩ := h
  rcases e with ⟨pc, i, ef⟩
  cases i <;> cases ef <;> simp [lower] at he
  all_goals try (subst a; exact ⟨by simp [Action.eval, Expr.eval, Salsa20Replay.fixedStep, exec,
      Machine.setReg, Machine.advance, hx, hp],
    by simp [Action.eval, Salsa20Replay.fixedStep, exec, Machine.setReg, Machine.advance, hp], hm⟩)
  case branch.branch op r t imm taken =>
    subst a
    cases taken <;> exact ⟨rfl.trans hx, by simp [Action.eval, Salsa20Replay.fixedStep, hp, Machine.advance], hm⟩
  case load.load w signed rd r imm addr n =>
    obtain ⟨⟨_, ha⟩, rfl⟩ := he
    obtain ⟨hr, hz⟩ := hm.2 w addr ha
    simp only [Action.eval, Expr.eval, Salsa20Replay.fixedStep, hr, hz, Machine.setReg, Machine.advance, State.Related]
    exact ⟨by rw [hx], congrArg (· + 4) hp, hm⟩
  case store.store w src r imm addr n =>
    obtain ⟨⟨_, ha⟩, rfl⟩ := he
    obtain ⟨mem', hw, hmem⟩ := hm.store ha (m.x.get src)
    simp only [Salsa20Replay.fixedStep, hw, Machine.advance, Action.eval, State.Related]
    exact ⟨hx, congrArg (· + 4) hp, by simpa only [hx] using hmem⟩

/-- Compile the complete schedule. Exact order is retained; compilation makes
all layout checks independently of the input data. -/
def compile (l : Layout) (es : List Event) : Option (List Action) := es.mapM (lower l)

def run (as : List Action) (s : State) : State := as.foldl Action.eval s

theorem compile_sound {l : Layout} {es : List Event} {as : List Action} {s : State} {m : Machine 64}
    (hc : compile l es = some as) (h : s.Related l m) :
    (run as s).Related l (Salsa20Replay.runFixed es m) := by
  induction es generalizing as s m with
  | nil =>
    have : as = [] := by simpa [compile] using hc.symm
    subst as
    exact h
  | cons e es ih =>
    cases he : lower l e with
    | none => simp [compile, List.mapM_cons, he] at hc
    | some a =>
      cases ht : compile l es with
      | none => simp [compile, List.mapM_cons, he, show es.mapM (lower l) = none from ht] at hc
      | some as' =>
        have hh : a :: as' = as := by
          simpa [compile, List.mapM_cons, he, show es.mapM (lower l) = some as' from ht] using hc
        subst as
        change (run as' (a.eval s)).Related l (Salsa20Replay.runFixed es (Salsa20Replay.fixedStep m e))
        exact ih ht (lower_sound h he)

theorem compile_sound_of_trace {l : Layout} {es : List Event} {as : List Action}
    {s : State} {m : Machine 64} (hc : compile l es = some as) (h : s.Related l m)
    (ht : Salsa20Replay.Trace es m) : (run as s).Related l (TinyFive.run es.length m) := by
  rw [← ht.runFixed_eq]
  exact compile_sound hc h

namespace Wrapper

open Salsa20Replay.Wrapper (capacity schedule steps)

/-- The linked wrapper uses full word slots in the stack frame and byte slots
elsewhere, notably for input, key, constant, and output. -/
def layout : Layout := ⟨capacity, fun block => decide ((capacity - 528) / 8 ≤ block)⟩

private def checked : Option (List Action) := compile layout schedule

def program : List Action := checked.getD []

-- The public-only certificate checks every address, width, and alignment;
-- the generic soundness proof does not rely on native computation.
private theorem checked_length : checked.map List.length = some steps := by
  native_decide

theorem program_checked : compile layout schedule = some program := by
  have h := checked_length
  change checked = some program
  cases hc : checked with
  | none => rw [hc] at h; contradiction
  | some as => simp [program, hc]

/-- The wrapper's slot program is sound for arbitrary concrete data under the
same public initial-state assumptions as the replay certificate. -/
theorem program_sound {m : Machine 64} (h : Salsa20Replay.Related Salsa20Replay.Wrapper.initial m)
    (hc : m.mem.size = capacity) :
    (run program (State.ofMachine layout m)).Related layout (TinyFive.run steps m) := by
  rw [← (Salsa20Replay.Wrapper.verified h hc).2.1]
  exact compile_sound program_checked (State.ofMachine_related layout m hc)

end Wrapper

end TweetNaCl.Salsa20Slots
