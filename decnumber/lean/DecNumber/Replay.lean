import TinyFive.Machine

/-! A sound sparse replay of TinyFive RV64 code. `none` denotes unknown memory,
not a zero byte. A successful replay needs every fetched/loaded byte to be
known; stores establish knowledge of the bytes they overwrite. The checked
write predicate is a byte-level frame, not an emulator instrumentation result. -/
namespace DecNumber.Replay
open TinyFive

abbrev Bytes := Nat → Option (BitVec 8)

def Agrees (known : Bytes) (mem : Array (BitVec 8)) : Prop :=
  ∀ a b, known a = some b → mem[a]? = some b

def put (known : Bytes) (addr : Nat) (b : BitVec 8) : Bytes :=
  fun i => if i = addr then some b else known i

def read (known : Bytes) (addr : Nat) : (n : Nat) → Option (BitVec (8 * n))
  | 0 => some 0#0
  | n + 1 => do
    let lo ← known addr
    let hi ← read known (addr + 1) n
    some ((hi ++ lo).cast (by omega))

def write {k : Nat} (known : Bytes) (addr : Nat) (v : BitVec k) : Nat → Bytes
  | 0 => known
  | n + 1 => write (put known addr (v.setWidth 8)) (addr + 1) (v >>> 8) n

theorem read_agrees {known : Bytes} {mem : Array (BitVec 8)} (h : Agrees known mem)
    {addr n : Nat} {v : BitVec (8 * n)} (hr : read known addr n = some v) :
    readBytes mem addr n = some v := by
  induction n generalizing addr with
  | zero => exact hr
  | succ n ih =>
    cases hb : known addr with
    | none => simp [read, hb] at hr
    | some b =>
      cases hv : read known (addr + 1) n with
      | none => simp [read, hb, hv] at hr
      | some hi => simpa only [read, hb, hv, readBytes, h addr b hb, ih hv] using hr

/-- All stores are in bounds, establish the replay's new knowledge, and leave
    every byte outside their interval unchanged. -/
private theorem write_agrees {k : Nat} {known : Bytes} {mem : Array (BitVec 8)}
    (h : Agrees known mem) {addr n : Nat} (v : BitVec k) (hf : addr + n ≤ mem.size) :
    ∃ mem', writeBytes mem addr v n = some mem' ∧ Agrees (write known addr v n) mem' ∧
      mem'.size = mem.size ∧
      ∀ i, (i < addr ∨ addr + n ≤ i) → mem'[i]? = mem[i]? := by
  induction n generalizing addr mem known v with
  | zero => exact ⟨mem, rfl, h, rfl, fun _ _ => rfl⟩
  | succ n ih =>
    let b := v.setWidth 8
    let mid := mem.setIfInBounds addr b
    have ha : addr < mem.size := by omega
    have hs : mid.size = mem.size := Array.size_setIfInBounds
    have hm : Agrees (put known addr b) mid := by
      intro i val hi
      by_cases he : i = addr
      · subst i
        simp [put] at hi
        simpa [mid, Array.getElem?_setIfInBounds_self_of_lt ha] using hi
      · rw [Array.getElem?_setIfInBounds_ne (Ne.symm he)]
        exact h i val (by simpa [put, he] using hi)
    obtain ⟨mem', hw, hag, hs', hstay⟩ := ih hm (v >>> 8) (addr := addr + 1) (by omega)
    refine ⟨mem', by simpa [writeBytes, ha, mid, b] using hw, hag, hs'.trans hs, ?_⟩
    intro i hi
    calc
      mem'[i]? = mid[i]? := hstay i (by omega)
      _ = mem[i]? := Array.getElem?_setIfInBounds_ne (by omega)

structure State where
  x : Regs 64
  pc : BitVec 64
  bytes : Bytes

def Related (s : State) (m : Machine 64) : Prop :=
  m.x = s.x ∧ m.pc = s.pc ∧ m.status = .running ∧ Agrees s.bytes m.mem

def Frame (writable : Nat → Bool) (m m' : Machine 64) : Prop :=
  m'.mem.size = m.mem.size ∧ m'.input = m.input ∧ m'.output = m.output ∧
    ∀ i, writable i = false → m'.mem[i]? = m.mem[i]?

theorem Frame.refl (writable : Nat → Bool) (m : Machine 64) : Frame writable m m :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Frame.trans {writable : Nat → Bool} {a b c : Machine 64}
    (ab : Frame writable a b) (bc : Frame writable b c) : Frame writable a c :=
  ⟨bc.1.trans ab.1, bc.2.1.trans ab.2.1, bc.2.2.1.trans ab.2.2.1,
    fun i h => (bc.2.2.2 i h).trans (ab.2.2.2 i h)⟩

private def State.bare (s : State) : Machine 64 := ⟨s.x, s.pc, #[], [], "", .running⟩

/-- The caller's return PC is a stopping boundary, never an instruction executed here. -/
def next (writable : Nat → Bool) (capacity : Nat) (s : State) : Option State := do
  let word ← read s.bytes s.pc.toNat 4
  let insn ← decode 64 word
  match insn with
  | .load width signed rd rs1 imm =>
    let v ← read s.bytes (s.x.get rs1 + imm.signExtend 64).toNat width.bytes
    some { s with x := s.x.set rd (if signed then v.signExtend 64 else v.setWidth 64), pc := s.pc + 4 }
  | .store width rs2 rs1 imm =>
    let addr := (s.x.get rs1 + imm.signExtend 64).toNat
    let n := width.bytes
    if addr + n ≤ capacity ∧ (List.range n).all (fun i => writable (addr + i)) then
      some { s with bytes := write s.bytes addr (s.x.get rs2) n, pc := s.pc + 4 }
    else none
  | .ecall => none
  | _ =>
    let c := exec insn s.bare
    some { s with x := c.x, pc := c.pc }

private theorem next_sound {writable : Nat → Bool} {capacity : Nat} {s s' : State} {m : Machine 64}
    (h : Related s m) (hc : m.mem.size = capacity) (hn : next writable capacity s = some s') :
    Related s' (step m) ∧ Frame writable m (step m) := by
  obtain ⟨hx, hp, hstatus, ha⟩ := h
  unfold next at hn
  cases hw : read s.bytes s.pc.toNat 4 with
  | none => simp [hw] at hn
  | some word =>
    cases hd : decode 64 word with
    | none => simp [hw, hd] at hn
    | some i =>
      have he : step m = exec i m := by simp [step, hp, read_agrees ha hw, hd]
      rw [he]
      rw [hw] at hn
      simp only [bind, Option.bind] at hn
      rw [hd] at hn
      cases i <;> dsimp only at hn
      case load width signed rd rs1 imm =>
        cases hread : read s.bytes (s.x.get rs1 + imm.signExtend 64).toNat width.bytes with
        | none =>
          rw [hread] at hn
          contradiction
        | some value =>
          rw [hread] at hn
          simp only [Option.some.injEq] at hn
          subst s'
          simp only [exec, hx, hp, read_agrees ha hread, Related, Frame, Machine.advance, Machine.setReg]
          simp [hstatus, ha]
      case store width rs2 rs1 imm =>
        split at hn
        next fit =>
          simp only [Option.some.injEq] at hn
          subst s'
          let addr := (s.x.get rs1 + imm.signExtend 64).toNat
          obtain ⟨mem', hwrite, hag, hsize, hstay⟩ :=
            write_agrees ha (s.x.get rs2) (addr := addr) (n := width.bytes) (hc ▸ fit.1)
          simp only [exec, hx, hp, show (s.x.get rs1 + imm.signExtend 64).toNat = addr from rfl,
            hwrite, Machine.advance]
          unfold Related Frame
          refine ⟨⟨rfl, rfl, hstatus, hag⟩, hsize, rfl, rfl, fun j hj => hstay j ?_⟩
          by_cases hin : j < addr ∨ addr + width.bytes ≤ j
          · exact hin
          exfalso
          have hv : writable (addr + (j - addr)) = true :=
            List.all_eq_true.mp fit.2 _ (List.mem_range.mpr (by omega))
          rw [show addr + (j - addr) = j by omega, hj] at hv
          contradiction
        next => contradiction
      case ecall => contradiction
      all_goals
        simp only [Option.some.injEq] at hn
        subst s'
        simp [Related, Frame, exec, State.bare, Machine.setReg, Machine.advance, hx, hp, hstatus, ha]
        <;> split <;> simp_all

/-- Return `none` on an unknown read, out-of-frame store, or insufficient fuel. -/
def untilReturn (writable : Nat → Bool) (capacity : Nat) (returnPC : BitVec 64) :
    Nat → State → Option (Nat × State)
  | 0, s => if s.pc = returnPC then some (0, s) else none
  | n + 1, s => if s.pc = returnPC then some (0, s) else do
    let s' ← next writable capacity s
    let (steps, result) ← untilReturn writable capacity returnPC n s'
    some (steps + 1, result)

theorem untilReturn_sound {writable : Nat → Bool} {capacity : Nat} {returnPC : BitVec 64}
    {fuel steps : Nat} {s result : State} {m : Machine 64} (h : Related s m)
    (hc : m.mem.size = capacity) (hr : untilReturn writable capacity returnPC fuel s = some (steps, result)) :
    Related result (run steps m) ∧ Frame writable m (run steps m) ∧ result.pc = returnPC ∧ steps ≤ fuel := by
  induction fuel generalizing steps s result m with
  | zero =>
    simp only [untilReturn] at hr
    split at hr
    next he =>
      cases hr
      exact ⟨h, .refl .., he, Nat.le_refl _⟩
    next => contradiction
  | succ fuel ih =>
    simp only [untilReturn] at hr
    split at hr
    next he =>
      cases hr
      exact ⟨h, .refl .., he, Nat.zero_le _⟩
    next =>
      cases hn : next writable capacity s with
      | none => simp [hn] at hr
      | some s' =>
        rcases hrec : untilReturn writable capacity returnPC fuel s' with _ | ⟨k, final⟩
        · simp [hn, hrec] at hr
        · rw [hn] at hr
          simp only [bind, Option.bind] at hr
          rw [hrec] at hr
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          obtain ⟨h', frame⟩ := next_sound h hc hn
          obtain ⟨hout, fr, heq, hb⟩ := ih h' (frame.1.trans hc) hrec
          rw [run]
          simp only [h.2.2.1, ite_true]
          exact ⟨hout, frame.trans fr, heq, Nat.succ_le_succ hb⟩

end DecNumber.Replay
