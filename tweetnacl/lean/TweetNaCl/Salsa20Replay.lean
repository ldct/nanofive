import DecNumber.Replay
import TweetNaCl.Salsa20Program
import Std.Data.TreeMap.Lemmas

/-! A public-value abstract interpreter for the TinyFive RV64 model. `none` denotes
arbitrary data, not zero. Control decisions and memory addresses must be known;
unknown data may be loaded, transformed, and stored without becoming public. -/

namespace TweetNaCl.Salsa20Replay
open TinyFive

abbrev Byte := BitVec 8
abbrev Word := BitVec 64
abbrev KnownBytes := Std.TreeMap Nat Byte
abbrev Frame := DecNumber.Replay.Frame

/-- The concrete value need only match if the checker knows it. -/
def Known {α : Type} (a : Option α) (v : α) : Prop := ∀ k, a = some k → v = k

private theorem known_some {v : α} : Known (some v) v := by simp [Known]

private theorem Known.map {a : Option α} {v : α} {f : α → β} (h : Known a v) :
    Known (a.map f) (f v) := by
  cases a <;> simp_all [Known]

private def map₂ (f : α → β → γ) (a : Option α) (b : Option β) : Option γ := do
  let x ← a
  let y ← b
  pure (f x y)

private theorem known_map₂ {a : Option α} {b : Option β} {v : α} {w : β}
    (f : α → β → γ) (ha : Known a v) (hb : Known b w) :
    Known (map₂ f a b) (f v w) := by
  cases a <;> cases b <;> simp_all [Known, map₂]

def Agrees (bytes : KnownBytes) (mem : Array Byte) : Prop :=
  DecNumber.Replay.Agrees (fun a => bytes[a]?) mem

def read (bytes : KnownBytes) (addr n : Nat) : Option (BitVec (8 * n)) :=
  DecNumber.Replay.read (fun a => bytes[a]?) addr n

private def put (bytes : KnownBytes) (addr : Nat) : Option Byte → KnownBytes
  | some b => bytes.insert addr b
  | none => bytes.erase addr

private theorem lookup_put (bytes : KnownBytes) (addr i : Nat) (v : Option Byte) :
    (put bytes addr v)[i]? = if addr = i then v else bytes[i]? := by
  cases v <;> simp [put, Std.TreeMap.getElem?_insert, Std.TreeMap.getElem?_erase]

/-- An unknown store must erase, not preserve, knowledge of every overwritten byte. -/
def write (bytes : KnownBytes) (addr : Nat) (v : Option Word) : Nat → KnownBytes
  | 0 => bytes
  | n + 1 => write (put bytes addr (v.map (·.setWidth 8))) (addr + 1) (v.map (fun x : Word => x >>> 8)) n

private theorem read_inBounds {mem : Array Byte} {a n : Nat} (h : a + n ≤ mem.size) :
    ∃ v, readBytes mem a n = some v := by
  induction n generalizing a with
  | zero => exact ⟨_, rfl⟩
  | succ n ih =>
    have ha : a < mem.size := by omega
    obtain ⟨hi, hhi⟩ := ih (a := a + 1) (by omega)
    simp [readBytes, Array.getElem?_eq_getElem ha, hhi]

private theorem write_sound {bytes : KnownBytes} {mem : Array Byte} (h : Agrees bytes mem)
    {addr n : Nat} {v : Option Word} {value : Word} (hv : Known v value)
    (hf : addr + n ≤ mem.size) :
    ∃ mem', writeBytes mem addr value n = some mem' ∧ Agrees (write bytes addr v n) mem' ∧
      mem'.size = mem.size ∧ ∀ i, (i < addr ∨ addr + n ≤ i) → mem'[i]? = mem[i]? := by
  induction n generalizing addr mem bytes v value with
  | zero => exact ⟨mem, rfl, h, rfl, fun _ _ => rfl⟩
  | succ n ih =>
    let mid := mem.setIfInBounds addr (value.setWidth 8)
    have ha : addr < mem.size := by omega
    have hs : mid.size = mem.size := Array.size_setIfInBounds
    have hm : Agrees (put bytes addr (v.map (·.setWidth 8))) mid := by
      intro i val hi
      change (put bytes addr (v.map (·.setWidth 8)))[i]? = some val at hi
      rw [lookup_put] at hi
      by_cases he : addr = i
      · subst i
        simp only [ite_true] at hi
        rw [Array.getElem?_setIfInBounds_self_of_lt ha, (hv.map (f := fun x : Word => x.setWidth 8)) val hi]
      · rw [Array.getElem?_setIfInBounds_ne he]
        exact h i val (by simpa [he] using hi)
    obtain ⟨mem', hw, hag, hs', hstay⟩ := ih hm (hv.map (f := fun x : Word => x >>> 8)) (addr := addr + 1) (by omega)
    refine ⟨mem', by simpa [writeBytes, ha, mid] using hw, hag, hs'.trans hs, ?_⟩
    intro i hi
    exact (hstay i (by omega)).trans (Array.getElem?_setIfInBounds_ne (by omega))

structure State where
  x : Vector (Option Word) 32
  pc : Word
  bytes : KnownBytes

/-- As on the machine, reading register zero always produces zero. -/
def State.get (s : State) (r : Reg) : Option Word := if r = 0 then some 0 else s.x[r.val]

def State.setReg (s : State) (r : Reg) (v : Option Word) : State :=
  { s with x := s.x.set r.val v r.isLt }

def State.advance (s : State) : State := { s with pc := s.pc + 4 }

def Related (s : State) (m : Machine 64) : Prop :=
  m.pc = s.pc ∧ m.status = .running ∧ (∀ r, Known (s.get r) (m.x.get r)) ∧ Agrees s.bytes m.mem

private theorem Related.setReg {s : State} {m : Machine 64} (h : Related s m)
    {r : Reg} {v : Option Word} {value : Word} (hv : Known v value) :
    Related (s.setReg r v) (m.setReg r value) := by
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  intro i
  simp only [State.get, State.setReg, Machine.setReg, Regs.get_set, Vector.getElem_set, Fin.val_inj]
  by_cases hz : i = 0
  · simp [hz, known_some]
  · by_cases he : r = i
    · simp [hz, he, hv]
    · simpa [State.get, hz, he, Ne.symm he] using h.2.2.1 i

private theorem Related.advance {s : State} {m : Machine 64} (h : Related s m) :
    Related s.advance m.advance := ⟨congrArg (· + 4) h.1, h.2⟩

private theorem Related.setPC {s : State} {m : Machine 64} (h : Related s m) (pc : Word) :
    Related { s with pc := pc } { m with pc := pc } := ⟨rfl, h.2⟩

/-- The observed part of a single instruction, excluding data values. -/
inductive Effect where
  | plain
  | jump (target : Word)
  | branch (taken : Bool)
  | load (address bytes : Nat)
  | store (address bytes : Nat)
  deriving DecidableEq, Repr

structure Event where
  pc : Word
  instr : Instr
  effect : Effect
  deriving DecidableEq, Repr

private def address (base : Word) (imm : BitVec 12) : Nat := (base + imm.signExtend 64).toNat

private def indirect (base : Word) (imm : BitVec 12) : Word :=
  (base + imm.signExtend 64) &&& ~~~1

/-- The observable event for a decoded instruction in a concrete machine. -/
def observe (m : Machine 64) (i : Instr) : Event := ⟨m.pc, i, match i with
  | .jal _ imm => .jump (m.pc + imm.signExtend 64)
  | .jalr _ r imm => .jump (indirect (m.x.get r) imm)
  | .branch op r t _ => .branch (op.taken (m.x.get r) (m.x.get t))
  | .load w _ _ r imm => .load (address (m.x.get r) imm) w.bytes
  | .store w _ r imm => .store (address (m.x.get r) imm) w.bytes
  | _ => .plain⟩

private def abstractExec (writable : Nat → Bool) (capacity : Nat) (s : State) (i : Instr) :
    Option (Event × State) :=
  let emit := fun eff t => some (⟨s.pc, i, eff⟩, t)
  let reg := fun rd v => emit .plain (s.setReg rd v).advance
  match i with
  | .lui rd imm => reg rd (some ((imm ++ 0#12).signExtend 64))
  | .auipc rd imm => reg rd (some (s.pc + (imm ++ 0#12).signExtend 64))
  | .jal rd imm =>
    let dest := s.pc + imm.signExtend 64
    emit (.jump dest) { s.setReg rd (some (s.pc + 4)) with pc := dest }
  | .jalr rd r imm => do
    let base ← s.get r
    let dest := indirect base imm
    emit (.jump dest) { s.setReg rd (some (s.pc + 4)) with pc := dest }
  | .branch op r t imm => do
    let a ← s.get r
    let b ← s.get t
    let taken := op.taken a b
    emit (.branch taken) (if taken then { s with pc := s.pc + imm.signExtend 64 } else s.advance)
  | .load w signed rd r imm => do
    let base ← s.get r
    let addr := address base imm
    if addr + w.bytes ≤ capacity then
      let v := (read s.bytes addr w.bytes).map fun v => if signed then v.signExtend 64 else v.setWidth 64
      emit (.load addr w.bytes) (s.setReg rd v).advance
    else none
  | .store w src r imm => do
    let base ← s.get r
    let addr := address base imm
    if addr + w.bytes ≤ capacity ∧ (List.range w.bytes).all (fun k => writable (addr + k)) then
      emit (.store addr w.bytes) { s.advance with bytes := write s.bytes addr (s.get src) w.bytes }
    else none
  | .opImm op rd r imm => reg rd ((s.get r).map fun v => alu op v (imm.signExtend 64))
  | .op op rd r t => reg rd (map₂ (alu op) (s.get r) (s.get t))
  | .opImmWord op rd r imm =>
    reg rd ((s.get r).map fun v => (alu op (v.setWidth 32) (imm.signExtend 32)).signExtend 64)
  | .opWord op rd r t =>
    reg rd (map₂ (fun v w => (alu op (v.setWidth 32) (w.setWidth 32)).signExtend 64) (s.get r) (s.get t))
  | .ecall => none

/-- Fetch and decode a known word, then check its public effects. -/
def next (writable : Nat → Bool) (capacity : Nat) (s : State) : Option (Event × State) := do
  let word ← read s.bytes s.pc.toNat 4
  let insn ← decode 64 word
  abstractExec writable capacity s insn

private theorem read_sound {bytes : KnownBytes} {mem : Array Byte} (h : Agrees bytes mem)
    {addr n : Nat} {v : BitVec (8 * n)} (hv : readBytes mem addr n = some v) :
    Known (read bytes addr n) v := by
  intro k hk
  exact Option.some.inj (hv.symm.trans (DecNumber.Replay.read_agrees h hk))

private theorem abstractExec_sound {writable : Nat → Bool} {capacity : Nat} {s t : State}
    {m : Machine 64} {i : Instr} {e : Event} (h : Related s m) (hc : m.mem.size = capacity)
    (hn : abstractExec writable capacity s i = some (e, t)) :
    e = observe m i ∧ Related t (exec i m) ∧ Frame writable m (exec i m) := by
  have hp := h.1
  have hreg := h.2.2.1
  cases i with
  | ecall => contradiction
  | jal rd imm =>
    simp [abstractExec] at hn
    obtain ⟨rfl, rfl⟩ := hn
    refine ⟨by simp [observe, hp], ?_, by simp [DecNumber.Replay.Frame, exec, Machine.setReg]⟩
    simpa [exec, hp] using (h.setReg (r := rd) (v := some (s.pc + 4)) known_some).setPC
      (s.pc + imm.signExtend 64)
  | jalr rd r imm =>
    cases hb : s.get r with
    | none => simp [abstractExec, hb] at hn
    | some base =>
      simp [abstractExec, hb] at hn
      obtain ⟨rfl, rfl⟩ := hn
      have hr := hreg r base hb
      refine ⟨by simp [observe, hp, hr], ?_, by simp [DecNumber.Replay.Frame, exec, Machine.setReg]⟩
      simpa [exec, hp, hr, indirect] using
        (h.setReg (r := rd) (v := some (s.pc + 4)) known_some).setPC (indirect base imm)
  | branch op r t imm =>
    cases ha : s.get r with
    | none => simp [abstractExec, ha] at hn
    | some a =>
      cases hb : s.get t with
      | none => simp [abstractExec, ha, hb] at hn
      | some b =>
        have hra := hreg r a ha
        have hrb := hreg t b hb
        cases ht : op.taken a b <;> simp [abstractExec, ha, hb, ht] at hn <;> obtain ⟨rfl, rfl⟩ := hn
        · exact ⟨by simp [observe, hp, hra, hrb, ht],
            by simpa [exec, hra, hrb, ht] using h.advance,
            by simp [DecNumber.Replay.Frame, exec, hra, hrb, ht, Machine.advance]⟩
        · exact ⟨by simp [observe, hp, hra, hrb, ht],
            by simpa [exec, hp, hra, hrb, ht] using h.setPC (s.pc + imm.signExtend 64),
            by simp [DecNumber.Replay.Frame, exec, hra, hrb, ht]⟩
  | load w signed rd r imm =>
    cases hb : s.get r with
    | none => simp [abstractExec, hb] at hn
    | some base =>
      by_cases hbnd : address base imm + w.bytes ≤ capacity
      · simp [abstractExec, hb, hbnd] at hn
        obtain ⟨rfl, rfl⟩ := hn
        have hr := hreg r base hb
        obtain ⟨v, hv⟩ := read_inBounds (mem := m.mem) (hc ▸ hbnd)
        have hv' := (read_sound h.2.2.2 hv).map
          (f := fun v => if signed then v.signExtend 64 else v.setWidth 64)
        rw [show exec (.load w signed rd r imm) m =
          (m.setReg rd (if signed then v.signExtend 64 else v.setWidth 64)).advance by
            simp only [exec, hr, show (base + imm.signExtend 64).toNat = address base imm from rfl, hv]]
        exact ⟨by simp [observe, hp, hr], (h.setReg hv').advance,
          by simp [DecNumber.Replay.Frame, Machine.setReg, Machine.advance]⟩
      · simp [abstractExec, hb, hbnd] at hn
  | store w src r imm =>
    cases hb : s.get r with
    | none => simp [abstractExec, hb] at hn
    | some base =>
      let addr := address base imm
      by_cases hf : address base imm + w.bytes ≤ capacity ∧ (List.range w.bytes).all (fun k => writable (address base imm + k)) = true
      · simp only [abstractExec, hb, bind, Option.bind, ite_eq_left hf, Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        have hr := hreg r base hb
        obtain ⟨mem', hw, hm, hs, hstay⟩ := write_sound h.2.2.2 (hreg src) (hc ▸ hf.1)
        have hex : exec (.store w src r imm) m = { m with mem := mem' }.advance := by
          simp only [exec, hr, show (base + imm.signExtend 64).toNat = address base imm from rfl, hw]
        rw [hex]
        refine ⟨by simp [observe, hp, hr],
          ⟨h.advance.1, h.2.1, hreg, hm⟩, hs, rfl, rfl, fun j hj => hstay j ?_⟩
        by_cases hin : j < addr ∨ addr + w.bytes ≤ j
        · exact hin
        exfalso
        have hwj := List.all_eq_true.mp hf.2 (j - addr) (List.mem_range.mpr (by omega))
        rw [show addr + (j - addr) = j by omega, hj] at hwj
        contradiction
      · simp only [abstractExec, hb, bind, Option.bind, ite_eq_right hf, reduceCtorEq] at hn
  | lui rd imm =>
    simp [abstractExec] at hn
    obtain ⟨rfl, rfl⟩ := hn
    exact ⟨by simp [observe, hp], (h.setReg known_some).advance,
      by simp [DecNumber.Replay.Frame, exec, Machine.setReg, Machine.advance]⟩
  | auipc rd imm =>
    simp [abstractExec] at hn
    obtain ⟨rfl, rfl⟩ := hn
    refine ⟨by simp [observe, hp], ?_, by simp [DecNumber.Replay.Frame, exec, Machine.setReg, Machine.advance]⟩
    simpa [exec, hp] using (h.setReg (r := rd) (v := some (s.pc + (imm ++ 0#12).signExtend 64)) known_some).advance
  | opImm op rd r imm =>
    simp [abstractExec] at hn
    obtain ⟨rfl, rfl⟩ := hn
    exact ⟨by simp [observe, hp], (h.setReg (hreg r).map).advance,
      by simp [DecNumber.Replay.Frame, exec, Machine.setReg, Machine.advance]⟩
  | op op rd r t =>
    simp [abstractExec] at hn
    obtain ⟨rfl, rfl⟩ := hn
    exact ⟨by simp [observe, hp], (h.setReg (known_map₂ (alu op) (hreg r) (hreg t))).advance,
      by simp [DecNumber.Replay.Frame, exec, Machine.setReg, Machine.advance]⟩
  | opImmWord op rd r imm =>
    simp [abstractExec] at hn
    obtain ⟨rfl, rfl⟩ := hn
    exact ⟨by simp [observe, hp], (h.setReg (hreg r).map).advance,
      by simp [DecNumber.Replay.Frame, exec, Machine.setReg, Machine.advance]⟩
  | opWord op rd r t =>
    simp [abstractExec] at hn
    obtain ⟨rfl, rfl⟩ := hn
    exact ⟨by simp [observe, hp], (h.setReg (known_map₂ _ (hreg r) (hreg t))).advance,
      by simp [DecNumber.Replay.Frame, exec, Machine.setReg, Machine.advance]⟩

/-- The word at the concrete PC actually decodes to the recorded instruction, and
    the concrete step has precisely the recorded observable effect. -/
def Event.Matches (e : Event) (m : Machine 64) : Prop :=
  (readBytes m.mem m.pc.toNat 4).bind (decode 64) = some e.instr ∧ e = observe m e.instr

theorem Event.Matches.step_eq {e : Event} {m : Machine 64} (h : e.Matches m) :
    step m = exec e.instr m := by simp only [step, h.1]

theorem next_sound {writable : Nat → Bool} {capacity : Nat} {s t : State} {m : Machine 64}
    {e : Event} (h : Related s m) (hc : m.mem.size = capacity)
    (hn : next writable capacity s = some (e, t)) :
    e.Matches m ∧ Related t (step m) ∧ Frame writable m (step m) := by
  cases hf : read s.bytes s.pc.toNat 4 with
  | none => simp [next, hf] at hn
  | some word =>
    cases hd : decode 64 word with
    | none => simp [next, hf, hd] at hn
    | some instr =>
      simp [next, hf, hd] at hn
      obtain ⟨he, hrel, hframe⟩ := abstractExec_sound h hc hn
      have hi : e.instr = instr := congrArg Event.instr he
      have hf' := DecNumber.Replay.read_agrees h.2.2.2 hf
      have hmatch : e.Matches m := ⟨by simp [h.1, hf', hd, hi], hi.symm ▸ he⟩
      rw [hmatch.step_eq, hi]
      exact ⟨hmatch, hrel, hframe⟩

/-- A chronological schedule, matched against each actual instruction fetch and
    event, with the machine running before every step. -/
inductive Trace : List Event → Machine 64 → Prop
  | nil (m) : Trace [] m
  | cons {e es m} (running : m.status = .running) (event : e.Matches m)
      (rest : Trace es (step m)) : Trace (e :: es) m

/-- Any schedule entry describes the actual event at that instruction index. -/
theorem Trace.eventAt {es : List Event} {m : Machine 64} (h : Trace es m)
    {i : Nat} (hi : i < es.length) : es[i].Matches (run i m) := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons e es m hs he _ ih =>
    cases i with
    | zero => exact he
    | succ i =>
      rw [run, ite_eq_left hs]
      exact ih (by simpa using hi)

/-- Collect events until the first arrival at `returnPC`, without executing it.
    Failure means an unsupported step, unknown control/address/fetch, an
    out-of-bounds access, a forbidden store, or insufficient fuel. -/
def untilReturn (writable : Nat → Bool) (capacity : Nat) (returnPC : Word) :
    Nat → State → Option (List Event × State)
  | 0, s => if s.pc = returnPC then some ([], s) else none
  | n + 1, s => if s.pc = returnPC then some ([], s) else do
    let (e, t) ← next writable capacity s
    let (es, result) ← untilReturn writable capacity returnPC n t
    pure (e :: es, result)

theorem untilReturn_sound {writable : Nat → Bool} {capacity : Nat} {returnPC : Word}
    {fuel : Nat} {es : List Event} {s result : State} {m : Machine 64} (h : Related s m)
    (hc : m.mem.size = capacity) (hr : untilReturn writable capacity returnPC fuel s = some (es, result)) :
    Trace es m ∧ Related result (run es.length m) ∧ Frame writable m (run es.length m) ∧
      result.pc = returnPC ∧ es.length ≤ fuel := by
  induction fuel generalizing es s result m with
  | zero =>
    simp only [untilReturn] at hr
    split at hr
    next he =>
      cases hr
      exact ⟨.nil _, h, .refl .., he, Nat.le_refl _⟩
    next => contradiction
  | succ fuel ih =>
    simp only [untilReturn] at hr
    split at hr
    next he =>
      cases hr
      exact ⟨.nil _, h, .refl .., he, Nat.zero_le _⟩
    next =>
      cases hn : next writable capacity s with
      | none => simp [hn] at hr
      | some p =>
        rcases p with ⟨e, t⟩
        cases ha : untilReturn writable capacity returnPC fuel t with
        | none => simp [hn, ha] at hr
        | some p =>
          rcases p with ⟨rest, final⟩
          simp [hn, ha] at hr
          obtain ⟨rfl, rfl⟩ := hr
          obtain ⟨hm, ht, hfr⟩ := next_sound h hc hn
          obtain ⟨trace, rel, frame, ret, bound⟩ := ih ht (hfr.1.trans hc) ha
          rw [List.length_cons, run, ite_eq_left h.2.1]
          exact ⟨.cons h.2.1 hm trace, rel, hfr.trans frame, ret, Nat.succ_le_succ bound⟩

/-- Replay one scheduled instruction using recorded branch decisions and
    addresses, and actual data. For an uncertified event this is not intended
    to emulate an instruction; use `Trace.runFixed_eq` for the correspondence. -/
def fixedStep (m : Machine 64) (e : Event) : Machine 64 :=
  match e.instr, e.effect with
  | .jal rd _, .jump dest | .jalr rd _ _, .jump dest => { m.setReg rd (m.pc + 4) with pc := dest }
  | .branch _ _ _ imm, .branch taken =>
    if taken then { m with pc := m.pc + imm.signExtend 64 } else m.advance
  | .load w signed rd _ _, .load addr _ =>
    match readBytes m.mem addr w.bytes with
    | some v => (m.setReg rd (if signed then v.signExtend 64 else v.setWidth 64)).advance
    | none => m.fail
  | .store w src _ _, .store addr _ =>
    match writeBytes m.mem addr (m.x.get src) w.bytes with
    | some mem => { m with mem := mem }.advance
    | none => m.fail
  | i, _ => exec i m

private theorem fixedStep_eq (m : Machine 64) (i : Instr) : fixedStep m (observe m i) = exec i m := by
  cases i <;> rfl

def runFixed (es : List Event) (m : Machine 64) : Machine 64 := es.foldl fixedStep m

theorem Trace.runFixed_eq {es : List Event} {m : Machine 64} (h : Trace es m) :
    runFixed es m = run es.length m := by
  induction h with
  | nil => rfl
  | @cons e es m hs he _ ih =>
    have hstep : fixedStep m e = step m :=
      calc
        fixedStep m e = fixedStep m (observe m e.instr) := congrArg (fixedStep m) he.2
        _ = exec e.instr m := fixedStep_eq ..
        _ = step m := he.step_eq.symm
    simpa [runFixed, run, hs, hstep] using ih

end TweetNaCl.Salsa20Replay

namespace TweetNaCl.Salsa20Replay.Wrapper
open TinyFive

abbrev capacity : Nat := 0x100000
abbrev out : Nat := 0x80000
abbrev inp : Nat := 0x80100
abbrev key : Nat := 0x80200
abbrev constant : Nat := 0x80300
abbrev returnPC : Word := 0x11bc
abbrev steps : Nat := 11550

/-- The wrapper's writable regions: 64 output bytes and the combined 528-byte stack frame. -/
def writable (a : Nat) : Bool :=
  decide ((out ≤ a ∧ a < out + 64) ∨ (capacity - 528 ≤ a ∧ a < capacity))

private def addWords (base : Nat) (words : List (BitVec 32)) (bytes : KnownBytes) : KnownBytes :=
  (words.zipIdx).foldl (fun b (w, i) => write b (base + 4 * i) (some (w.setWidth 64)) 4) bytes

/-- Known initial bytes are just the linked instructions. In particular the inputs,
    output and stack have arbitrary contents. -/
def image : KnownBytes :=
  addWords Salsa20Program.entry Salsa20Program.wrapperWords
    (addWords Salsa20Program.coreEntry Salsa20Program.coreWords {})

/-- Only argument registers, the stack pointer, and return address are public initially. -/
def initial : State :=
  let regs := Vector.replicate 32 (α := Option Word) none
  let regs := regs.set 1 (some returnPC) (by decide)
  let regs := regs.set 2 (some (BitVec.ofNat 64 capacity)) (by decide)
  let regs := regs.set 10 (some (BitVec.ofNat 64 out)) (by decide)
  let regs := regs.set 11 (some (BitVec.ofNat 64 inp)) (by decide)
  let regs := regs.set 12 (some (BitVec.ofNat 64 key)) (by decide)
  let regs := regs.set 13 (some (BitVec.ofNat 64 constant)) (by decide)
  ⟨regs, BitVec.ofNat 64 Salsa20Program.entry, image⟩

/-- Sufficient explicit ABI and byte-image assumptions for the checker. No other
    register or memory contents are restricted. -/
theorem initial_related {m : Machine 64}
    (hpc : m.pc = BitVec.ofNat 64 Salsa20Program.entry) (hrun : m.status = .running)
    (hra : m.x.get 1 = returnPC) (hsp : m.x.get 2 = BitVec.ofNat 64 capacity)
    (ho : m.x.get 10 = BitVec.ofNat 64 out) (hi : m.x.get 11 = BitVec.ofNat 64 inp)
    (hk : m.x.get 12 = BitVec.ofNat 64 key) (hc : m.x.get 13 = BitVec.ofNat 64 constant)
    (hmem : Agrees image m.mem) : Related initial m := by
  refine ⟨hpc, hrun, ?_, hmem⟩
  intro r
  by_cases h0 : r = 0
  · subst r
    exact known_some
  simp only [State.get, initial, ite_eq_right h0, Vector.getElem_set, Vector.getElem_replicate]
  split
  next he => simpa [Known, show r = 13 from Fin.ext he.symm] using hc
  split
  next he => simpa [Known, show r = 12 from Fin.ext he.symm] using hk
  split
  next he => simpa [Known, show r = 11 from Fin.ext he.symm] using hi
  split
  next he => simpa [Known, show r = 10 from Fin.ext he.symm] using ho
  split
  next he => simpa [Known, show r = 2 from Fin.ext he.symm] using hsp
  split
  next he => simpa [Known, show r = 1 from Fin.ext he.symm] using hra
  simp [Known]

/-- The instruction words `words` are stored little-endian from `base`: byte `j`
    of word `i` is at address `base + 4 * i + j`. -/
def WordsAt (m : Machine 64) (base : Nat) (words : List (BitVec 32)) : Prop :=
  ∀ i (hi : i < words.length) j, j < 4 →
    m.mem[base + 4 * i + j]? = some (words[i].extractLsb' (8 * j) 8)

private theorem write_agrees {bytes : KnownBytes} {mem : Array Byte} (h : Agrees bytes mem)
    {addr n : Nat} {x : Word}
    (hx : ∀ j, j < n → mem[addr + j]? = some ((x >>> (8 * j)).setWidth 8)) :
    Agrees (write bytes addr (some x) n) mem := by
  induction n generalizing bytes addr x with
  | zero => exact h
  | succ n ih =>
    simp only [write, Option.map_some]
    refine ih ?_ ?_
    · intro i b hb
      change (put bytes addr (some (x.setWidth 8)))[i]? = some b at hb
      rw [lookup_put] at hb
      split at hb
      · subst i
        cases hb
        simpa using hx 0 (by omega)
      · exact h i b hb
    · intro j hj
      have hs : (x >>> 8) >>> (8 * j) = x >>> (8 * (j + 1)) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ushiftRight, ← Nat.shiftRight_add]
        congr 1
        omega
      rw [hs, show addr + 1 + j = addr + (j + 1) by omega]
      exact hx (j + 1) (by omega)

private theorem byte_of_word (w : BitVec 32) {j : Nat} (hj : j < 4) :
    ((w.setWidth 64 >>> (8 * j)).setWidth 8) = w.extractLsb' (8 * j) 8 := by
  ext k hk
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getElem_extractLsb',
    BitVec.getLsbD_setWidth]
  have : 8 * j + k < 64 := by omega
  simp [this]

private theorem addWords_agrees {bytes : KnownBytes} {mem : Array Byte} (h : Agrees bytes mem)
    {base : Nat} {words : List (BitVec 32)}
    (hw : ∀ i (hi : i < words.length) j, j < 4 →
      mem[base + 4 * i + j]? = some (words[i].extractLsb' (8 * j) 8)) :
    Agrees (addWords base words bytes) mem := by
  unfold addWords
  suffices ∀ (l : List (BitVec 32 × Nat)) (b : KnownBytes), (∀ p ∈ l, p ∈ words.zipIdx) →
      Agrees b mem →
      Agrees (l.foldl (fun b (w, i) => write b (base + 4 * i) (some (w.setWidth 64)) 4) b) mem from
    this _ _ (fun _ hp => hp) h
  intro l
  induction l with
  | nil => intro b _ hb; exact hb
  | cons p l ih =>
    intro b hl hb
    refine ih _ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) ?_
    obtain ⟨w, i⟩ := p
    obtain ⟨hi, he⟩ := List.mem_zipIdx' (hl _ List.mem_cons_self)
    refine write_agrees hb fun j hj => ?_
    rw [byte_of_word _ hj, he]
    exact hw i hi j hj

/-- Plain memory assumptions for the checker's code image. -/
theorem image_agrees {m : Machine 64}
    (hcore : WordsAt m Salsa20Program.coreEntry Salsa20Program.coreWords)
    (hwrap : WordsAt m Salsa20Program.entry Salsa20Program.wrapperWords) :
    Agrees image m.mem :=
  addWords_agrees (addWords_agrees (fun _ _ h => by simp at h) hcore) hwrap

-- Abstract the evaluated option so that kernel conversion does not unfold the
-- 11,550-step execution when checking a proof about its projections.
private opaque checkedResult :
    { v : Option (List Event × State) // untilReturn writable capacity returnPC steps initial = v } :=
  ⟨untilReturn writable capacity returnPC steps initial, rfl⟩

private def cert : Option (List Event × State) := checkedResult.val

/-- Fully checked decoded schedule for the linked `crypto_core_salsa20_tweet` wrapper. -/
def schedule : List Event := (cert.getD ([], initial)).1

private def final : State := (cert.getD ([], initial)).2

-- Only the public certificate is evaluated natively. The correspondence to every
-- agreeing concrete machine is proved by the generic theorems above.
private theorem cert_checked :
    cert.map (fun (es, s) => (es.length, s.get 10, s.get 2, s.get 1)) =
      some (steps, some 0, some (BitVec.ofNat 64 capacity), some returnPC) := by
  native_decide

private theorem unpack (v : Option (List Event × State)) (f : State)
    (h : v.map (fun (es, s) => (es.length, s.get 10, s.get 2, s.get 1)) =
      some (steps, some 0, some (BitVec.ofNat 64 capacity), some returnPC)) :
    v = some ((v.getD ([], f)).1, (v.getD ([], f)).2) ∧
      (v.getD ([], f)).1.length = steps ∧ (v.getD ([], f)).2.get 10 = some 0 ∧
      (v.getD ([], f)).2.get 2 = some (BitVec.ofNat 64 capacity) ∧
      (v.getD ([], f)).2.get 1 = some returnPC := by
  cases v with
  | none => contradiction
  | some p => rcases p with ⟨es, s⟩; simp_all only [Option.map_some, Option.getD, Option.some.injEq, Prod.mk.injEq, true_and]

private theorem cert_success : cert = some (schedule, final) :=
  (unpack cert initial cert_checked).1

private theorem cert_summary : schedule.length = steps ∧ final.get 10 = some 0 ∧
    final.get 2 = some (BitVec.ofNat 64 capacity) ∧ final.get 1 = some returnPC :=
  (unpack cert initial cert_checked).2

theorem schedule_length : schedule.length = steps := cert_summary.1

/-- For every concrete completion, the wrapper returns along the same decoded
    path with the same branch decisions and memory addresses (including widths).
    This is a control-flow and memory-effect theorem, not a claim about the
    output bytes or instruction timing on physical hardware. -/
theorem verified {m : Machine 64} (h : Related initial m) (hc : m.mem.size = capacity) :
    Trace schedule m ∧ runFixed schedule m = run steps m ∧ Frame writable m (run steps m) ∧
    (run steps m).pc = returnPC ∧ (run steps m).status = .running ∧
    (run steps m).x.get 10 = 0 ∧ (run steps m).x.get 2 = BitVec.ofNat 64 capacity ∧
    (run steps m).x.get 1 = returnPC := by
  obtain ⟨trace, rel, frame, ret, _⟩ := untilReturn_sound h hc (checkedResult.property.trans cert_success)
  obtain ⟨hlen, h0, hsp, hra⟩ := cert_summary
  have hfixed := trace.runFixed_eq
  rw [hlen] at hfixed rel frame
  exact ⟨trace, hfixed, frame, rel.1.trans ret, rel.2.1, rel.2.2.1 10 0 h0,
    rel.2.2.1 2 _ hsp, rel.2.2.1 1 _ hra⟩

end TweetNaCl.Salsa20Replay.Wrapper
