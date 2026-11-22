import NaClSalsa20.Symbolic
import NaClSalsa20.WireSound

/-!
# Soundness of the symbolic dataflow pass

`Rel` relates a symbolic state to a machine: known registers and bytes are described by their
wires, and bytes never written still hold their initial values `env`. Each supported event of
the schedule preserves `Rel` under `fixedStep`, the replay of an event with its recorded
addresses and branch decisions.
-/
namespace NaClSalsa20.Symbolic
open TinyFive Wire
open TweetNaCl.Salsa20Replay (Event Effect fixedStep runFixed)

attribute [-simp] BitVec.getLsbD_eq_getElem

section
variable (val : Id → BitVec 32) (env : Nat → BitVec 8)

def ByteRel (a : Nat) : Option (Option Wire) → BitVec 8 → Prop
  | none, b => b = env a
  | some none, _ => True
  | some (some w), b => Describes val 8 w b

structure Rel (capacity : Nat) (s : State) (m : Machine 64) : Prop where
  regs : ∀ r w, s.get r = some w → Describes val 32 w (m.x.get r)
  size : m.mem.size = capacity
  mem : ∀ a, a < capacity → ∃ b, m.mem[a]? = some b ∧ ByteRel val env a s.mem[a]? b
end

variable {val : Id → BitVec 32} {env : Nat → BitVec 8} {capacity : Nat}

theorem Rel.congr {s : State} {m m' : Machine 64} (h : Rel val env capacity s m)
    (hx : m'.x = m.x) (hm : m'.mem = m.mem) : Rel val env capacity s m' :=
  ⟨hx ▸ h.regs, hm ▸ h.size, hm ▸ h.mem⟩

theorem State.get_set (s : State) (rd r : Reg) (v : Option Wire) :
    (s.set rd v).get r = if r = 0 then some (const 0) else if rd = r then v else s.get r := by
  have hne : rd ≠ r → rd.val ≠ r.val := fun h e => h (Fin.ext e)
  cases v <;> by_cases h0 : r = 0 <;> by_cases he : rd = r <;>
    simp_all [State.get, State.set, Std.TreeMap.getElem?_insert, Std.TreeMap.getElem?_erase]

theorem Rel.set {s : State} {m : Machine 64} (h : Rel val env capacity s m) (rd : Reg)
    {v : Option Wire} {X : BitVec 64} (hv : ∀ w, v = some w → Describes val 32 w X) :
    Rel val env capacity (s.set rd v) (m.setReg rd X) := by
  refine ⟨fun r w hw => ?_, h.size, by cases v <;> exact h.mem⟩
  rw [State.get_set] at hw
  simp only [Machine.setReg, Regs.get_set]
  by_cases h0 : r = 0
  · simp only [h0, ite_true, Option.some.injEq] at hw ⊢
    subst hw
    exact const_sound 0
  · simp only [h0, ite_false] at hw ⊢
    by_cases he : rd = r
    · simp only [he, ite_true] at hw ⊢
      exact hv w hw
    · simp only [he, ite_false] at hw ⊢
      exact h.regs r w hw

/-! ## Memory -/

theorem readBytes_some {mem : Array (BitVec 8)} {a : Nat} :
    ∀ {n : Nat}, a + n ≤ mem.size → ∃ v, readBytes mem a n = some v
  | 0, _ => ⟨_, rfl⟩
  | n + 1, h => by
    obtain ⟨v, hv⟩ := readBytes_some (mem := mem) (a := a + 1) (n := n) (by omega)
    simp [readBytes, Array.getElem?_eq_getElem (show a < mem.size by omega), hv]

theorem readBytes_bits {mem : Array (BitVec 8)} :
    ∀ {a n : Nat} {v : BitVec (8 * n)}, readBytes mem a n = some v →
      ∀ i, i < 8 * n → v.getLsbD i = (mem[a + i / 8]?.getD 0).getLsbD (i % 8)
  | _, 0, _, _, i, hi => by omega
  | a, n + 1, v, h, i, hi => by
    simp only [readBytes, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨lo, hlo, hi', hhi, rfl⟩ := h
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · simp [h8, hlo, Nat.div_eq_of_lt h8, Nat.mod_eq_of_lt h8]
    · simp only [h8, ite_false]
      rw [readBytes_bits hhi (i - 8) (by omega), show a + 1 + (i - 8) / 8 = a + i / 8 by omega,
        show (i - 8) % 8 = i % 8 by omega]

theorem writeBytes_spec {mem : Array (BitVec 8)} {v : BitVec 64} :
    ∀ {a n : Nat}, a + n ≤ mem.size → ∃ mem', writeBytes mem a v n = some mem' ∧
      mem'.size = mem.size ∧ ∀ i, mem'[i]? =
        if a ≤ i ∧ i < a + n then some ((v >>> (8 * (i - a))).setWidth 8) else mem[i]?
  | a, 0, _ => ⟨mem, rfl, rfl, fun i => by simp; omega⟩
  | a, n + 1, h => by
    have ha : a < mem.size := by omega
    obtain ⟨mem', hw, hs, hi⟩ := writeBytes_spec (mem := mem.setIfInBounds a (v.setWidth 8))
      (v := v >>> 8) (a := a + 1) (n := n) (by simp; omega)
    refine ⟨mem', by simpa [writeBytes, ha] using hw, by simp [hs], fun i => ?_⟩
    rw [hi i]
    by_cases hia : i = a
    · subst hia
      simp [show ¬ (i + 1 ≤ i) by omega, Array.getElem?_setIfInBounds_self_of_lt ha]
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hia)]
      by_cases hr : a + 1 ≤ i ∧ i < a + 1 + n
      · rw [ite_eq_left hr, ite_eq_left (by omega), ← BitVec.shiftRight_add]
        congr 3
        omega
      · rw [ite_eq_right hr, ite_eq_right (by omega)]

theorem store_mem (s : State) (addr n a : Nat) (v : Option Wire) :
    (store s addr n v).mem[a]? = if addr ≤ a ∧ a < addr + n then
      some (if a - addr < 4 then v.map (byte · (a - addr)) else none) else s.mem[a]? := by
  simp only [store]
  induction n with
  | zero => simp; omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.TreeMap.getElem?_insert, ih]
    by_cases he : addr + n = a
    · subst he; simp
    · have : compare (addr + n) a ≠ .eq := by simpa [Nat.compare_eq_eq] using he
      simp only [this, ite_false]
      have hc : (addr ≤ a ∧ a < addr + (n + 1)) ↔ (addr ≤ a ∧ a < addr + n) := by omega
      simp only [hc]

/-! ## Steps -/

section Steps
variable {arena : Arena} {s : State} {m : Machine 64}

theorem getByte_sound (h : Rel (arena.eval env) env capacity s m) {a : Nat} (ha : a < capacity)
    {ob : Option Wire} (hg : getByte arena.mk s a = some ob) {w : Wire} (hw : ob = some w)
    {b : BitVec 8} (hb : m.mem[a]? = some b) : Describes (arena.eval env) 8 w b := by
  obtain ⟨b', hb', hr⟩ := h.mem a ha
  rw [hb] at hb'
  cases hb'
  unfold getByte at hg
  split at hg
  next o hs =>
    cases hg
    subst hw
    simpa [hs, ByteRel] using hr
  next hs =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hg
    obtain ⟨id, hid, rfl⟩ := hg
    cases hw
    simp only [hs, ByteRel] at hr
    subst hr
    refine (atom_sound id).of_bits fun i hi => ?_
    rw [Arena.mk_sound env hid]
    simp [Node.eval, show i < 32 by omega]

theorem load_sound (h : Rel (arena.eval env) env capacity s m) {addr n : Nat} {signed : Bool}
    (hn : 0 < n) (hc : addr + n ≤ capacity) {v : BitVec (8 * n)}
    (hv : readBytes m.mem addr n = some v) {r : Option Wire}
    (hl : load arena.mk s addr n signed = some r) {w : Wire} (hw : r = some w) :
    Describes (arena.eval env) 32 w (if signed then v.signExtend 64 else v.setWidth 64) := by
  unfold load at hl
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨bytes, hbytes, rfl⟩ := hl
  simp only [Option.map_eq_some_iff] at hw
  obtain ⟨bs, hbs, rfl⟩ := hw
  obtain ⟨hl1, he1⟩ := mapM_some hbytes
  obtain ⟨hl2, he2⟩ := mapM_some hbs
  simp only [List.length_range] at hl1 he1
  -- Every needed byte is described.
  have hbyte : ∀ k, k < min n 4 → ∀ j, j < 8 →
      (m.mem[addr + k]?.getD 0).getLsbD j = (bit (bs.getD k []) j).eval (arena.eval env) := by
    intro k hk j hj
    obtain ⟨b, hb, -⟩ := h.mem (addr + k) (by omega)
    have hg := he1 k hk
    have hk2 : k < bytes.length := by omega
    have hid := he2 k hk2
    simp only [List.getElem_range, id] at hg hid
    rw [List.getElem?_eq_getElem hk2] at hg
    rw [hid] at hg
    have hkb : k < bs.length := by omega
    rw [List.getElem?_eq_getElem hkb] at hg
    rw [hb, Option.getD_some, getByte_sound h (by omega) hg rfl hb j hj,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkb, Option.getD_some]
  have hbits := readBytes_bits hv
  intro i hi
  rw [bit_gen hi]
  by_cases hin : i < 8 * n
  · simp only [hin, ite_true]
    have hv' : v.getLsbD i = (bit (bs.getD (i / 8) []) (i % 8)).eval (arena.eval env) := by
      rw [hbits i hin, hbyte (i / 8) (by omega) (i % 8) (by omega)]
    cases signed <;> simp [BitVec.getLsbD_signExtend, hin, hv', show i < 64 by omega]
  · simp only [hin, ite_false]
    cases signed
    · simp [BitVec.getLsbD_of_ge v i (by omega)]
    · have hm : v.msb = (bit (bs.getD (n - 1) []) 7).eval (arena.eval env) := by
        rw [BitVec.msb_eq_getLsbD_last, hbits _ (by omega)]
        rw [show (8 * n - 1) / 8 = n - 1 by omega, show (8 * n - 1) % 8 = 7 by omega]
        exact hbyte (n - 1) (by omega) 7 (by omega)
      simp [BitVec.getLsbD_signExtend, hin, hm, show i < 64 by omega]

theorem store_sound (h : Rel (arena.eval env) env capacity s m) {addr n : Nat}
    (hc : addr + n ≤ capacity) (src : Reg) {mem' : Array (BitVec 8)}
    (hw : writeBytes m.mem addr (m.x.get src) n = some mem') :
    Rel (arena.eval env) env capacity (store s addr n (s.get src)) { m with mem := mem' } := by
  obtain ⟨mem'', hw', hs, hi⟩ := writeBytes_spec (v := m.x.get src) (h.size ▸ hc)
  rw [hw] at hw'
  cases hw'
  refine ⟨h.regs, hs.trans h.size, fun a ha => ?_⟩
  change ∃ b, mem'[a]? = some b ∧ _
  rw [hi a, store_mem]
  split
  next hr =>
    refine ⟨_, rfl, ?_⟩
    split
    next hk =>
      cases hsrc : s.get src with
      | none => trivial
      | some w =>
        exact byte_sound hk (h.regs src w hsrc) fun j hj => by
          simp [hj]
    next => trivial
  next => exact h.mem a ha

theorem imm32_sound (imm : BitVec 12) :
    Describes (arena.eval env) 32 (imm32 imm) (imm.signExtend 64) :=
  (const_sound _).of_bits fun i hi => by
    simp [BitVec.getLsbD_signExtend, hi, show i < 64 by omega]

theorem step_sound {s' : State} {e : Event} (hok : Event.Ok capacity e = true)
    (h : Rel (arena.eval env) env capacity s m) (hs : step arena.mk s e = some s') :
    Rel (arena.eval env) env capacity s' (fixedStep m e) := by
  obtain ⟨pc, i, ef⟩ := e
  have none_ok : ∀ (X : BitVec 64) w, (none : Option Wire) = some w →
      Describes (arena.eval env) 32 w X := fun _ _ h => by cases h
  cases i <;> cases ef <;> simp only [Event.Ok, Bool.false_eq_true] at hok
  case lui.plain rd imm =>
    simp only [step, pure, Option.some.injEq] at hs
    subst hs
    refine (h.set rd (X := (imm ++ 0#12).signExtend 64) fun w hw => ?_).congr rfl rfl
    cases hw
    exact (const_sound _).of_bits fun i hi => by
      simp [BitVec.getLsbD_signExtend, hi, show i < 64 by omega]
  case auipc.plain rd imm =>
    simp only [step, pure, Option.some.injEq] at hs
    subst hs
    exact (h.set rd (none_ok (m.pc + (imm ++ 0#12).signExtend 64))).congr rfl rfl
  case jal.jump rd imm dest =>
    simp only [step, pure, Option.some.injEq] at hs
    subst hs
    exact (h.set rd (none_ok (m.pc + 4))).congr rfl rfl
  case jalr.jump rd r imm dest =>
    simp only [step, pure, Option.some.injEq] at hs
    subst hs
    exact (h.set rd (none_ok (m.pc + 4))).congr rfl rfl
  case branch.branch op r t imm taken =>
    simp only [step, pure, Option.some.injEq] at hs
    subst hs
    simp only [fixedStep]
    split <;> exact h.congr rfl rfl
  case load.load w signed rd r imm addr n =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨-, hc⟩ := hok
    obtain ⟨v, hv⟩ := readBytes_some (mem := m.mem) (a := addr) (n := w.bytes) (h.size ▸ hc)
    simp only [step, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hs
    obtain ⟨r', hr', rfl⟩ := hs
    simp only [fixedStep, hv]
    refine (h.set rd fun x hx => ?_).congr rfl rfl
    exact load_sound h (by cases w <;> decide) hc hv hr' hx
  case store.store w src r imm addr n =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨-, hc⟩ := hok
    obtain ⟨mem', hw, -⟩ := writeBytes_spec (v := m.x.get src) (h.size ▸ hc)
    simp only [step, pure, Option.some.injEq] at hs
    subst hs
    simp only [fixedStep, hw]
    exact (store_sound h hc src hw).congr rfl rfl
  case opImm.plain op rd r imm =>
    simp only [step, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hs
    obtain ⟨r', hr', rfl⟩ := hs
    refine (h.set rd (X := alu op (m.x.get r) (imm.signExtend 64)) fun w hw => ?_).congr rfl rfl
    subst hw
    cases ha : s.get r with
    | none => simp [optOp, ha, pure] at hr'
    | some a =>
      simp only [optOp, ha] at hr'
      exact op64_sound hr' (h.regs r a ha) (imm32_sound imm)
  case op.plain op rd r t =>
    simp only [step, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hs
    obtain ⟨r', hr', rfl⟩ := hs
    refine (h.set rd (X := alu op (m.x.get r) (m.x.get t)) fun w hw => ?_).congr rfl rfl
    subst hw
    cases ha : s.get r with
    | none => simp [optOp, ha, pure] at hr'
    | some a =>
      cases hb : s.get t with
      | none => simp [optOp, ha, hb, pure] at hr'
      | some b =>
        simp only [optOp, ha, hb] at hr'
        exact op64_sound hr' (h.regs r a ha) (h.regs t b hb)
  case opImmWord.plain op rd r imm =>
    simp only [step, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hs
    obtain ⟨r', hr', rfl⟩ := hs
    refine (h.set rd (X := (alu op ((m.x.get r).setWidth 32) (imm.signExtend 32)).signExtend 64)
      fun w hw => ?_).congr rfl rfl
    subst hw
    cases ha : s.get r with
    | none => simp [optOp, ha, pure] at hr'
    | some a =>
      simp only [optOp, ha] at hr'
      exact describes_signExtend.mpr (op32_sound hr'
        (describes_setWidth.mpr (h.regs r a ha)) (const_sound _))
  case opWord.plain op rd r t =>
    simp only [step, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hs
    obtain ⟨r', hr', rfl⟩ := hs
    refine (h.set rd (X := (alu op ((m.x.get r).setWidth 32) ((m.x.get t).setWidth 32)).signExtend 64)
      fun w hw => ?_).congr rfl rfl
    subst hw
    cases ha : s.get r with
    | none => simp [optOp, ha, pure] at hr'
    | some a =>
      cases hb : s.get t with
      | none => simp [optOp, ha, hb, pure] at hr'
      | some b =>
        simp only [optOp, ha, hb] at hr'
        exact describes_signExtend.mpr (op32_sound hr'
          (describes_setWidth.mpr (h.regs r a ha))
          (describes_setWidth.mpr (h.regs t b hb)))

theorem run_sound {es : List Event} (hok : es.all (Event.Ok capacity) = true) {s' : State}
    (h : Rel (arena.eval env) env capacity s m) (hs : run arena.mk es s = some s') :
    Rel (arena.eval env) env capacity s' (runFixed es m) := by
  induction es generalizing s m with
  | nil => cases hs; exact h
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [run, List.foldlM_cons, bind, Option.bind_eq_some_iff] at hs
    obtain ⟨mid, hm, hf⟩ := hs
    exact ih hok.2 (step_sound hok.1 h hm) hf

end Steps

end NaClSalsa20.Symbolic
