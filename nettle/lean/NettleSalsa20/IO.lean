import NettleSalsa20.Call
import TweetNaCl.ForHumans.Salsa20IOSpec

/-!
# Correctness of the stand-alone Nettle Salsa20 program

This follows `NaClSalsa20.IO`. The driver of `start.S` reads standard input in seven pieces,
to where `Salsa20Spec.initialState` holds them in the state (`Call.statePos`), by `readn_loop`;
the straight-line segments are proved by `simp`. The call itself is `Call.salsa20_correct`,
whose `Frame` keeps the driver code and the input and output streams unchanged. `correct`
composes the pieces with `run_add` into one run of 2,931 instructions.
-/

namespace NettleSalsa20.IO
open TinyFive Call
open TweetNaCl

attribute [local irreducible] prog

/-- `prog` is stored little-endian from address 0. -/
def CodeAt (mem : Array (BitVec 8)) : Prop :=
  ∀ i (hi : i < prog.length) j, j < 4 → mem[4 * i + j]? = some (prog[i].extractLsb' (8 * j) 8)

theorem byte_eq (w : BitVec 32) (j : Nat) :
    (w >>> (8 * j)).setWidth 8 = w.extractLsb' (8 * j) 8 := by
  ext k hk
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getElem_extractLsb']

theorem flatMap_getElem? (ws : List (BitVec 32)) (i : Nat) (hi : i < ws.length) (j : Nat)
    (hj : j < 4) :
    (ws.flatMap fun (x : BitVec 32) => (List.range 4).map fun k => (x >>> (8 * k)).setWidth 8)[4 * i + j]? =
      some ((ws[i] >>> (8 * j)).setWidth 8) := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    rw [List.flatMap_cons]
    cases i with
    | zero => simp [List.getElem?_append_left, hj]
    | succ i =>
      rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_range]
      rw [show 4 * (i + 1) + j - 4 = 4 * i + j by omega]
      exact ih i (by simpa using hi)

theorem prog_length : prog.length = 368 := by decide +kernel

theorem length_flatMap_bytes (ws : List (BitVec 32)) :
    (ws.flatMap fun (x : BitVec 32) => (List.range 4).map fun k => (x >>> (8 * k)).setWidth 8).length =
      4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.flatMap_cons, List.length_append, ih]; simp; omega

theorem codeAt_initial : CodeAt initial.mem := by
  intro i hi j hj
  simp only [initial, load]
  rw [List.getElem?_toArray, List.getElem?_append_left (by rw [length_flatMap_bytes]; omega),
    flatMap_getElem? _ _ hi _ hj, byte_eq]

theorem initial_size : initial.mem.size = memSize := by
  simp only [initial, load, List.size_toArray, List.length_append, List.length_replicate,
    length_flatMap_bytes, prog_length, memSize]

theorem wordsAt_of_drop {m : Machine 64} (h : CodeAt m.mem) (k : Nat) {ws : List (BitVec 32)}
    (hw : (prog.drop k).take ws.length = ws) : WordsAt m (4 * k) ws := by
  intro i hi j hj
  have he : prog[k + i]? = some ws[i] := by
    rw [← List.getElem?_eq_getElem hi]
    have := congrArg (·[i]?) hw
    simp only [List.getElem?_take, hi, ite_true, List.getElem?_drop] at this
    exact this
  obtain ⟨hk, he'⟩ := List.getElem?_eq_some_iff.mp he
  rw [show 4 * k + 4 * i + j = 4 * (k + i) + j by omega, h (k + i) hk j hj, he']

theorem codeAt_core {m : Machine 64} (h : CodeAt m.mem) : WordsAt m coreEntry coreWords := by
  refine wordsAt_of_drop h 48 ?_
  rw [show prog = driverWords ++ coreWords by with_unfolding_all rfl,
    List.drop_left' (show driverWords.length = 48 by decide), List.take_length]

theorem readBytes_word {mem : Array (BitVec 8)} {a : Nat} {w : BitVec 32}
    (h : ∀ j, j < 4 → mem[a + j]? = some (w.extractLsb' (8 * j) 8)) :
    readBytes mem a 4 = some w := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [readBytes, h0, show a + 1 + 1 = a + 2 by omega, show a + 1 + 1 + 1 = a + 3 by omega,
    h1, h2, h3]
  simp only [bind, Option.bind, Option.some.injEq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with
    h | h | h | h
  · simp [h]
  · simp [show ¬ i < 8 by omega, show i - 8 < 8 by omega, show 8 + (i - 8) = i by omega]
  · simp [show ¬ i < 8 by omega, show ¬ i - 8 < 8 by omega, show i - 8 - 8 < 8 by omega,
      show 16 + (i - 8 - 8) = i by omega]
  · simp [show ¬ i < 8 by omega, show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega,
      show i - 8 - 8 - 8 < 8 by omega, show 24 + (i - 8 - 8 - 8) = i by omega]

theorem fetch {mem : Array (BitVec 8)} (h : CodeAt mem) (k : Nat) (hk : k < prog.length) :
    readBytes mem (4 * k) 4 = some (prog.getD k 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact readBytes_word fun j hj => h k hk j hj

theorem step_of {m : Machine 64} {w : BitVec 32} {i : Instr}
    (hf : readBytes m.mem m.pc.toNat 4 = some w) (hd : decode 64 w = some i) :
    step m = exec i m := by
  simp only [step, hf, Option.bind_some, hd]

/-- The driver words decoded, from `driverEntry`. -/
def code : List Instr := [
  .lui 2 0x100, .opImm .add 17 0 12,
  .lui 5 0x80, .opImm .add 5 5 0x118, .opImm .add 6 5 16, .jal 7 0x98,
  .lui 5 0x80, .opImm .add 5 5 0x104, .opImm .add 6 5 16, .jal 7 0x88,
  .lui 5 0x80, .opImm .add 5 5 0x12c, .opImm .add 6 5 16, .jal 7 0x78,
  .lui 5 0x80, .opImm .add 5 5 0x100, .opImm .add 6 5 4, .jal 7 0x68,
  .lui 5 0x80, .opImm .add 5 5 0x114, .opImm .add 6 5 4, .jal 7 0x58,
  .lui 5 0x80, .opImm .add 5 5 0x128, .opImm .add 6 5 4, .jal 7 0x48,
  .lui 5 0x80, .opImm .add 5 5 0x13c, .opImm .add 6 5 4, .jal 7 0x38,
  .lui 10 0x80, .opImm .add 11 10 0x100, .opImm .add 12 0 20, .jal 1 0x3c,
  .lui 5 0x80, .opImm .add 6 5 64, .opImm .add 17 0 11,
  .load .byte false 10 5 0, .ecall, .opImm .add 5 5 1, .branch .bne 5 6 (-12),
  .opImm .add 17 0 10, .ecall,
  .ecall, .store .byte 10 5 0, .opImm .add 5 5 1, .branch .bne 5 6 (-12), .jalr 0 7 0]

theorem decode_driver : ∀ k, k < 48 →
    decode 64 (prog.getD k 0) = some (code.getD k .ecall) := by decide +kernel

theorem step_driver {mem : Array (BitVec 8)} (h : CodeAt mem) (x : Regs 64) (pc : BitVec 64)
    (inp : List Char) (out : String) (st : Status)
    (h2 : pc.toNat < 0xc0) (h4 : pc.toNat % 4 = 0) :
    step ⟨x, pc, mem, inp, out, st⟩ =
      exec (code.getD (pc.toNat / 4) .ecall) ⟨x, pc, mem, inp, out, st⟩ := by
  have hp : pc.toNat = 4 * (pc.toNat / 4) := by omega
  have hl : pc.toNat / 4 < prog.length := by rw [prog_length]; omega
  refine step_of (w := prog.getD (pc.toNat / 4) 0) ?_ (decode_driver _ (by omega))
  change readBytes mem pc.toNat 4 = _
  rw [← fetch h _ hl, ← hp]

theorem codeAt_set {mem : Array (BitVec 8)} (h : CodeAt mem) {a : Nat} (ha : 0x5c0 ≤ a)
    (v : BitVec 8) : CodeAt (mem.setIfInBounds a v) := by
  intro i hi j hj
  rw [Array.getElem?_setIfInBounds_ne (by rw [prog_length] at hi; omega)]
  exact h i hi j hj

theorem run_succ {m : Machine 64} (n : Nat) (h : m.status = .running) :
    run (n + 1) m = run n (step m) := by
  simp [run, h]

theorem char_toNat (b : BitVec 8) : (Char.ofNat b.toNat).toNat = b.toNat := by
  have := b.isLt
  simp only [Char.ofNat, Nat.isValidChar, show b.toNat < 0xd800 by omega, true_or, ↓reduceDIte]
  rfl

theorem writeBytes_one {k : Nat} {mem : Array (BitVec 8)} {a : Nat} (v : BitVec k)
    (h : a < mem.size) : writeBytes mem a v 1 = some (mem.setIfInBounds a (v.setWidth 8)) := by
  simp [writeBytes, h]

theorem readn_body (b : BitVec 8) (rest : List Char) (x : Regs 64) (mem : Array (BitVec 8))
    (out : String) (a : Nat) (hcode : CodeAt mem) (hsize : mem.size = memSize)
    (ha : 0x5c0 ≤ a) (ha' : a < memSize)
    (h5 : x.get 5 = BitVec.ofNat 64 a) (h17 : x.get 17 = 12) :
    run 3 ⟨x, 0xac, mem, Char.ofNat b.toNat :: rest, out, .running⟩ =
      ⟨(x.set 10 (b.setWidth 64)).set 5 (BitVec.ofNat 64 (a + 1)), 0xb8,
        mem.setIfInBounds a b, rest, out, .running⟩ := by
  have ha64 : a < 2 ^ 64 := by unfold memSize at ha'; omega
  rw [run_succ _ rfl, step_driver hcode _ _ _ _ _ (by decide) (by decide)]
  simp [code, exec, ecall, h17, Machine.setReg, Machine.advance, char_toNat]
  rw [run_succ _ rfl, step_driver hcode _ _ _ _ _ (by decide) (by decide)]
  simp [code, exec, Regs.get_set, h5, Width.bytes, writeBytes_one _ (show a < mem.size by omega),
    Nat.mod_eq_of_lt ha64, Machine.advance]
  rw [run_succ _ rfl, step_driver (codeAt_set hcode ha _) _ _ _ _ _ (by decide) (by decide)]
  simp [code, exec, Regs.get_set, h5, Machine.setReg, Machine.advance, run]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [alu]

theorem ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro he
  have := congrArg BitVec.toNat he
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact h this

/-- `readn` stores the bytes `bs` from `a` and returns to `t2`. -/
theorem readn_loop (bs : List (BitVec 8)) : ∀ (_ : bs ≠ []) (rest : List Char) (x : Regs 64)
    (mem : Array (BitVec 8)) (out : String) (a : Nat) (_ : CodeAt mem) (_ : mem.size = memSize)
    (_ : 0x5c0 ≤ a) (_ : a + bs.length ≤ memSize)
    (_ : x.get 5 = BitVec.ofNat 64 a) (_ : x.get 6 = BitVec.ofNat 64 (a + bs.length))
    (_ : x.get 17 = 12),
    ∃ x' mem', run (4 * bs.length + 1) ⟨x, 0xac, mem, Salsa20Spec.toChars bs ++ rest, out, .running⟩ =
        ⟨x', x.get 7 &&& ~~~1, mem', rest, out, .running⟩ ∧
      x'.get 2 = x.get 2 ∧ x'.get 7 = x.get 7 ∧ x'.get 17 = 12 ∧
      CodeAt mem' ∧ mem'.size = memSize ∧
      (∀ i (hi : i < bs.length), mem'[a + i]? = some bs[i]) ∧
      (∀ c, (c < a ∨ a + bs.length ≤ c) → mem'[c]? = mem[c]?) := by
  induction bs with
  | nil => intro h; contradiction
  | cons b bs ih =>
    intro _ rest x mem out a hcode hsize ha hb h5 h6 h17
    simp only [List.length_cons] at hb h6
    have ha64 : a + bs.length + 1 < 2 ^ 64 := by unfold memSize at hb; omega
    have hbody := readn_body b (Salsa20Spec.toChars bs ++ rest) x mem out a hcode hsize ha
      (by omega) h5 h17
    have hcode1 := codeAt_set hcode ha b
    have hsize1 : (mem.setIfInBounds a b).size = memSize := by simp [hsize]
    have hinp : Salsa20Spec.toChars (b :: bs) ++ rest =
        Char.ofNat b.toNat :: (Salsa20Spec.toChars bs ++ rest) := rfl
    simp only [List.length_cons]
    rw [hinp, show 4 * (bs.length + 1) + 1 = 3 + (4 * bs.length + 1 + 1) by omega, run_add,
      hbody, run_succ _ rfl,
      step_driver hcode1 _ _ _ _ _ (by decide) (by decide)]
    let x1 := (x.set 10 (b.setWidth 64)).set 5 (BitVec.ofNat 64 (a + 1))
    have g5 : x1.get 5 = BitVec.ofNat 64 (a + 1) := by simp [x1, Regs.get_set]
    have g6 : x1.get 6 = x.get 6 := by simp [x1, Regs.get_set]
    have g2 : x1.get 2 = x.get 2 := by simp [x1, Regs.get_set]
    have g7 : x1.get 7 = x.get 7 := by simp [x1, Regs.get_set]
    have g17 : x1.get 17 = 12 := by simp [x1, Regs.get_set, h17]
    have hset (c : Nat) : (mem.setIfInBounds a b)[c]? = if a = c then some b else mem[c]? := by
      rw [Array.getElem?_setIfInBounds]
      split <;> simp_all; omega
    cases bs with
    | nil =>
      simp [code, exec, BranchOp.taken, Regs.get_set, h6, Machine.advance, Salsa20Spec.toChars]
      rw [run_succ _ rfl, step_driver hcode1 _ _ _ _ _ (by decide) (by decide)]
      simp [code, exec, Regs.get_set, Machine.setReg, run]
      refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
      simp only [Regs.get_set, h17, hcode1, hsize1, hset]
      exact ⟨by simp, by simp, by simp, trivial, trivial, by simp,
        fun c hc => by simp [show a ≠ c by omega]⟩
    | cons b' bs' =>
      simp only [List.length_cons] at ha64 hb h6 ⊢
      have hne : BitVec.ofNat 64 (a + 1) ≠ BitVec.ofNat 64 (a + (bs'.length + 1 + 1)) :=
        ofNat_ne (by omega) (by omega) (by omega)
      simp [code, exec, BranchOp.taken, Regs.get_set, h6, hne]
      obtain ⟨x', mem', hrun, h2', h7', h17', hc', hs', hw', hf'⟩ :=
        ih (by simp) rest x1 (mem.setIfInBounds a b) out (a + 1) hcode1 hsize1 (by omega)
          (by simp only [List.length_cons]; omega) g5 (by rw [g6, h6]; congr 1; simp only [List.length_cons]; omega) g17
      simp only [List.length_cons] at hrun hw' hf'
      refine ⟨x', mem', ?_, by rw [h2', g2], by rw [h7', g7], h17', hc', hs', ?_, ?_⟩
      · rw [← g7]; exact hrun
      · intro i hi
        cases i with
        | zero =>
          rw [Nat.add_zero, hf' a (by omega), hset]
          simp
        | succ i =>
          rw [show a + (i + 1) = a + 1 + i by omega, hw' i (by omega)]
          simp
      · intro c hc
        rw [hf' c (by omega), hset]
        simp [show a ≠ c by omega]

theorem readBytes_one (mem : Array (BitVec 8)) (a : Nat) (b : BitVec 8) (h : mem[a]? = some b) :
    readBytes mem a 1 = some (b.cast (by omega)) := by
  simp only [readBytes, h, bind, Option.bind, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cast, BitVec.toNat_cast, BitVec.toNat_append]
  simp

/-- The print loop prints the bytes `bs` stored from `a`. -/
theorem print_loop (bs : List (BitVec 8)) : ∀ (_ : bs ≠ []) (x : Regs 64)
    (mem : Array (BitVec 8)) (inp : List Char) (cs : List Char) (a : Nat) (_ : CodeAt mem)
    (_ : a + bs.length ≤ memSize)
    (_ : ∀ i (hi : i < bs.length), mem[a + i]? = some bs[i])
    (_ : x.get 5 = BitVec.ofNat 64 a) (_ : x.get 6 = BitVec.ofNat 64 (a + bs.length))
    (_ : x.get 17 = 11),
    ∃ x', run (4 * bs.length) ⟨x, 0x94, mem, inp, String.ofList cs, .running⟩ =
        ⟨x', 0xa4, mem, inp, String.ofList (cs ++ Salsa20Spec.toChars bs), .running⟩ ∧
      x'.get 17 = 11 := by
  induction bs with
  | nil => intro h; contradiction
  | cons b bs ih =>
    intro _ x mem inp cs a hcode hb hm h5 h6 h17
    simp only [List.length_cons] at hb h6 ⊢
    have ha64 : a + bs.length + 1 < 2 ^ 64 := by unfold memSize at hb; omega
    have hr := readBytes_one mem a b (by rw [← Nat.add_zero a]; exact hm 0 (by simp))
    rw [show 4 * (bs.length + 1) = 4 * bs.length + 1 + 1 + 1 + 1 by omega, run_succ _ rfl,
      step_driver hcode _ _ _ _ _ (by decide) (by decide)]
    simp [code, exec, h5, Width.bytes, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega),
      hr, Machine.setReg, Machine.advance]
    rw [run_succ _ rfl, step_driver hcode _ _ _ _ _ (by decide) (by decide)]
    simp [code, exec, ecall, Regs.get_set, h17, Machine.advance]
    rw [run_succ _ rfl, step_driver hcode _ _ _ _ _ (by decide) (by decide)]
    simp [code, exec, Regs.get_set, h5, Machine.setReg, Machine.advance, alu]
    rw [run_succ _ rfl, step_driver hcode _ _ _ _ _ (by decide) (by decide)]
    have hb8 : b.toNat % 256 = b.toNat := Nat.mod_eq_of_lt b.isLt
    have hadd : BitVec.ofNat 64 a + 1#64 = BitVec.ofNat 64 (a + 1) := by
      apply BitVec.eq_of_toNat_eq; simp
    have hout : (String.ofList cs).push (Char.ofNat b.toNat) =
        String.ofList (cs ++ [Char.ofNat b.toNat]) := by simp
    simp only [hb8, hadd, hout]
    cases bs with
    | nil =>
      simp [code, exec, BranchOp.taken, Regs.get_set, h6, Machine.advance, run,
        Salsa20Spec.toChars, h17]
    | cons b' bs' =>
      simp only [List.length_cons] at ha64 hb h6 ⊢
      have hne : BitVec.ofNat 64 (a + 1) ≠ BitVec.ofNat 64 (a + (bs'.length + 1 + 1)) :=
        ofNat_ne (by omega) (by omega) (by omega)
      simp [code, exec, BranchOp.taken, Regs.get_set, h6, hne]
      obtain ⟨x', hrun, h17'⟩ := ih (by simp) ((x.set 10 (b.setWidth 64)).set 5 (BitVec.ofNat 64 (a + 1))) mem inp (cs ++ [Char.ofNat b.toNat]) (a + 1) hcode
        (by simp only [List.length_cons]; omega)
        (fun i hi => by rw [show a + 1 + i = a + (i + 1) by omega]; exact hm (i + 1) (by simp at hi ⊢; omega))
        (by simp [Regs.get_set]) (by rw [show a + 1 + (b' :: bs').length = a + (bs'.length + 1 + 1) by simp; omega]; simp [Regs.get_set, h6]) (by simp [Regs.get_set, h17])
      refine ⟨x', ?_, h17'⟩
      rw [hout]
      refine hrun.trans ?_
      simp [Salsa20Spec.toChars]

macro "drv" h:term : tactic =>
  `(tactic| simp [run, step_driver $h, code, exec, ecall, Machine.setReg,
      Machine.advance, alu, Regs.get_set])

theorem seg_start {mem : Array (BitVec 8)} (h : CodeAt mem) (x : Regs 64) (inp : List Char)
    (out : String) :
    ∃ x', run 6 ⟨x, 0, mem, inp, out, .running⟩ = ⟨x', 0xac, mem, inp, out, .running⟩ ∧
      x'.get 2 = BitVec.ofNat 64 memSize ∧ x'.get 17 = 12 ∧ x'.get 5 = BitVec.ofNat 64 0x80118 ∧
      x'.get 6 = BitVec.ofNat 64 (0x80118 + 16) ∧ x'.get 7 = 0x18 := by
  drv h
  rfl

/-- The six later reads: `t0` and `t1` bound the bytes, `t2` is the return address. -/
macro "seg_read" pc:term:max a:term:max n:term:max ret:term:max : command =>
  `(theorem $(Lean.mkIdent (.mkSimple s!"seg_{pc.raw.isNatLit?.getD 0}")) {mem : Array (BitVec 8)}
      (h : CodeAt mem) (x : Regs 64) (inp : List Char) (out : String) :
      ∃ x', run 4 ⟨x, $pc, mem, inp, out, .running⟩ = ⟨x', 0xac, mem, inp, out, .running⟩ ∧
        x'.get 2 = x.get 2 ∧ x'.get 17 = x.get 17 ∧ x'.get 5 = BitVec.ofNat 64 $a ∧
        x'.get 6 = BitVec.ofNat 64 ($a + $n) ∧ x'.get 7 = $ret := by
    drv h)

seg_read 0x18 0x80104 16 0x28
seg_read 0x28 0x8012c 16 0x38
seg_read 0x38 0x80100 4 0x48
seg_read 0x48 0x80114 4 0x58
seg_read 0x58 0x80128 4 0x68
seg_read 0x68 0x8013c 4 0x78

theorem seg_call {mem : Array (BitVec 8)} (h : CodeAt mem) (x : Regs 64) (inp : List Char)
    (out : String) :
    ∃ x', run 4 ⟨x, 0x78, mem, inp, out, .running⟩ = ⟨x', 0xc0, mem, inp, out, .running⟩ ∧
      x'.get 2 = x.get 2 ∧ x'.get 1 = 0x88 ∧ x'.get 10 = BitVec.ofNat 64 0x80000 ∧
      x'.get 11 = BitVec.ofNat 64 0x80100 ∧ x'.get 12 = BitVec.ofNat 64 20 := by
  drv h

theorem seg_print {mem : Array (BitVec 8)} (h : CodeAt mem) (x : Regs 64) (inp : List Char)
    (out : String) :
    ∃ x', run 3 ⟨x, 0x88, mem, inp, out, .running⟩ = ⟨x', 0x94, mem, inp, out, .running⟩ ∧
      x'.get 17 = 11 ∧ x'.get 5 = BitVec.ofNat 64 0x80000 ∧
      x'.get 6 = BitVec.ofNat 64 (0x80000 + 64) := by
  drv h

theorem seg_exit {mem : Array (BitVec 8)} (h : CodeAt mem) (x : Regs 64) (inp : List Char)
    (out : String) :
    is_exited_with_output (run 2 ⟨x, 0xa4, mem, inp, out, .running⟩) out := by
  drv h
  exact ⟨rfl, rfl⟩

theorem and_not_one (r : BitVec 64) (h : r ∈ [0x18, 0x28, 0x38, 0x48, 0x58, 0x68, 0x78]) :
    r &&& ~~~1 = r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem statePos_eq (k : Nat) : Call.statePos k =
    if k < 16 then k + 24 else if k < 32 then k - 12 else if k < 48 then k + 12
    else if k < 52 then k - 48 else if k < 56 then k - 32 else if k < 60 then k - 16 else k := rfl

open Salsa20Spec in
/-- The program exits after printing the Salsa20 core of the 64 input bytes. -/
theorem correct (input : Bytes 16) (key : Bytes 32) (constant : Bytes 16) :
    is_exited_with_output
      (run 2931 { initial with input := toChars (input.toList ++ key.toList ++ constant.toList) })
      (String.ofList (toChars (core input key constant).toList)) := by
  have hc0 := codeAt_initial
  have hs0 := initial_size
  -- The seven pieces of standard input.
  have l0 : input.toList.length = 16 := by simp
  have l1 : (key.toList.take 16).length = 16 := by simp
  have l2 : (key.toList.drop 16).length = 16 := by simp
  have l3 : (constant.toList.take 4).length = 4 := by simp
  have l4 : ((constant.toList.drop 4).take 4).length = 4 := by simp
  have l5 : ((constant.toList.drop 8).take 4).length = 4 := by simp
  have l6 : (constant.toList.drop 12).length = 4 := by simp
  have hkey : key.toList = key.toList.take 16 ++ key.toList.drop 16 := (List.take_append_drop _ _).symm
  have hcon : constant.toList = constant.toList.take 4 ++ ((constant.toList.drop 4).take 4 ++
      ((constant.toList.drop 8).take 4 ++ constant.toList.drop 12)) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [Vector.length_toList] at h1
    simp only [List.getElem_append, List.getElem_take, List.getElem_drop, List.length_take,
      List.length_drop, Vector.length_toList]
    split
    · rfl
    · split
      · congr 1; omega
      · split
        · congr 1; omega
        · congr 1; omega
  have hm0 : { initial with input := toChars (input.toList ++ key.toList ++ constant.toList) } =
      ⟨⟨Vector.replicate 32 0⟩, 0, initial.mem,
        toChars input.toList ++ (toChars (key.toList.take 16) ++ (toChars (key.toList.drop 16) ++
        (toChars (constant.toList.take 4) ++ (toChars ((constant.toList.drop 4).take 4) ++
        (toChars ((constant.toList.drop 8).take 4) ++ (toChars (constant.toList.drop 12) ++ [])))))),
        "", .running⟩ := by
    conv => lhs; rw [hkey, hcon]
    simp only [toChars, List.map_append, List.append_assoc, List.append_nil]; rfl
  rw [hm0, show 2931 = 6 + ((4 * input.toList.length + 1) +
      (4 + ((4 * (key.toList.take 16).length + 1) +
      (4 + ((4 * (key.toList.drop 16).length + 1) +
      (4 + ((4 * (constant.toList.take 4).length + 1) +
      (4 + ((4 * ((constant.toList.drop 4).take 4).length + 1) +
      (4 + ((4 * ((constant.toList.drop 8).take 4).length + 1) +
      (4 + ((4 * (constant.toList.drop 12).length + 1) +
      (4 + (2373 + (3 + (4 * (core input key constant).toList.length + 2))))))))))))))))) by
      simp only [l0, l1, l2, l3, l4, l5, l6]; simp]
  -- The input, to state bytes 24–39.
  obtain ⟨x1, e1, x1_2, x1_17, x1_5, x1_6, x1_7⟩ := seg_start hc0 ⟨Vector.replicate 32 0⟩ _ ""
  rw [run_add, e1, run_add]
  obtain ⟨y1, mem1, r1, y1_2, y1_7, y1_17, hc1, hs1, hw1, hf1⟩ :=
    readn_loop input.toList (by simp) _ x1 initial.mem "" 0x80118 hc0 hs0 (by decide)
      (by simp [memSize]) x1_5 (by simpa using x1_6) x1_17
  rw [r1, x1_7, and_not_one 0x18 (by decide), run_add]
  -- The key, to state bytes 4–19 and 44–59.
  obtain ⟨x2, e2, x2_2, x2_17, x2_5, x2_6, x2_7⟩ := seg_24 hc1 y1 _ ""
  rw [e2, run_add]
  obtain ⟨y2, mem2, r2, y2_2, y2_7, y2_17, hc2, hs2, hw2, hf2⟩ :=
    readn_loop (key.toList.take 16) (by simp) _ x2 mem1 "" 0x80104 hc1 hs1 (by decide)
      (by simp [memSize]) x2_5 (by simpa using x2_6) (by rw [x2_17, y1_17])
  rw [r2, x2_7, and_not_one 0x28 (by decide), run_add]
  obtain ⟨x3, e3, x3_2, x3_17, x3_5, x3_6, x3_7⟩ := seg_40 hc2 y2 _ ""
  rw [e3, run_add]
  obtain ⟨y3, mem3, r3, y3_2, y3_7, y3_17, hc3, hs3, hw3, hf3⟩ :=
    readn_loop (key.toList.drop 16) (by simp) _ x3 mem2 "" 0x8012c hc2 hs2 (by decide)
      (by simp [memSize]) x3_5 (by simpa using x3_6) (by rw [x3_17, y2_17])
  rw [r3, x3_7, and_not_one 0x38 (by decide), run_add]
  -- The constant, to state bytes 0–3, 20–23, 40–43 and 60–63.
  obtain ⟨x4, e4, x4_2, x4_17, x4_5, x4_6, x4_7⟩ := seg_56 hc3 y3 _ ""
  rw [e4, run_add]
  obtain ⟨y4, mem4, r4, y4_2, y4_7, y4_17, hc4, hs4, hw4, hf4⟩ :=
    readn_loop (constant.toList.take 4) (by simp) _ x4 mem3 "" 0x80100 hc3 hs3 (by decide)
      (by simp [memSize]) x4_5 (by simpa using x4_6) (by rw [x4_17, y3_17])
  rw [r4, x4_7, and_not_one 0x48 (by decide), run_add]
  obtain ⟨x5, e5, x5_2, x5_17, x5_5, x5_6, x5_7⟩ := seg_72 hc4 y4 _ ""
  rw [e5, run_add]
  obtain ⟨y5, mem5, r5, y5_2, y5_7, y5_17, hc5, hs5, hw5, hf5⟩ :=
    readn_loop ((constant.toList.drop 4).take 4) (by simp) _ x5 mem4 "" 0x80114 hc4 hs4
      (by decide) (by simp [memSize]) x5_5 (by simpa using x5_6) (by rw [x5_17, y4_17])
  rw [r5, x5_7, and_not_one 0x58 (by decide), run_add]
  obtain ⟨x6, e6, x6_2, x6_17, x6_5, x6_6, x6_7⟩ := seg_88 hc5 y5 _ ""
  rw [e6, run_add]
  obtain ⟨y6, mem6, r6, y6_2, y6_7, y6_17, hc6, hs6, hw6, hf6⟩ :=
    readn_loop ((constant.toList.drop 8).take 4) (by simp) _ x6 mem5 "" 0x80128 hc5 hs5
      (by decide) (by simp [memSize]) x6_5 (by simpa using x6_6) (by rw [x6_17, y5_17])
  rw [r6, x6_7, and_not_one 0x68 (by decide), run_add]
  obtain ⟨x7, e7, x7_2, x7_17, x7_5, x7_6, x7_7⟩ := seg_104 hc6 y6 _ ""
  rw [e7, run_add]
  obtain ⟨y7, mem7, r7, y7_2, y7_7, -, hc7, hs7, hw7, hf7⟩ :=
    readn_loop (constant.toList.drop 12) (by simp) [] x7 mem6 "" 0x8013c hc6 hs6
      (by decide) (by simp [memSize]) x7_5 (by simpa using x7_6) (by rw [x7_17, y6_17])
  rw [r7, x7_7, and_not_one 0x78 (by decide), run_add]
  simp only [l0, l1, l2, l3, l4, l5, l6] at hf1 hf2 hf3 hf4 hf5 hf6 hf7
  -- Call `_nettle_salsa20_core`.
  obtain ⟨x8, e8, x8_2, x8_1, x8_10, x8_11, x8_12⟩ := seg_call hc7 y7 [] ""
  rw [e8, run_add]
  have hst : Call.StateAt ⟨x8, 0xc0, mem7, [], "", .running⟩ Call.src input key constant := by
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;> have := i.isLt
    · change mem7[0x80100 + Call.statePos i.val]? = _
      rw [statePos_eq, ite_eq_left (by omega),
        show 0x80100 + (i.val + 24) = 0x80118 + i.val by omega,
        hf7 _ (by omega), hf6 _ (by omega), hf5 _ (by omega), hf4 _ (by omega),
        hf3 _ (by omega), hf2 _ (by omega), hw1 i.val (by simp)]
      simp
    · change mem7[0x80100 + Call.statePos (16 + i.val)]? = _
      rw [statePos_eq, ite_eq_right (by omega)]
      by_cases hk : i.val < 16
      · rw [ite_eq_left (by omega), show 0x80100 + (16 + i.val - 12) = 0x80104 + i.val by omega,
          hf7 _ (by omega), hf6 _ (by omega), hf5 _ (by omega), hf4 _ (by omega),
          hf3 _ (by omega), hw2 i.val (by simp; omega)]
        simp
      · rw [ite_eq_right (by omega), ite_eq_left (by omega),
          show 0x80100 + (16 + i.val + 12) = 0x8012c + (i.val - 16) by omega,
          hf7 _ (by omega), hf6 _ (by omega), hf5 _ (by omega), hf4 _ (by omega),
          hw3 (i.val - 16) (by simp; omega)]
        simp [show 16 + (i.val - 16) = i.val by omega]
    · change mem7[0x80100 + Call.statePos (48 + i.val)]? = _
      rw [statePos_eq, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      by_cases h1 : i.val < 4
      · rw [ite_eq_left (by omega), show 0x80100 + (48 + i.val - 48) = 0x80100 + i.val by omega,
          hf7 _ (by omega), hf6 _ (by omega), hf5 _ (by omega), hw4 i.val (by simp; omega)]
        simp
      rw [ite_eq_right (by omega)]
      by_cases h2 : i.val < 8
      · rw [ite_eq_left (by omega), show 0x80100 + (48 + i.val - 32) = 0x80114 + (i.val - 4) by omega,
          hf7 _ (by omega), hf6 _ (by omega), hw5 (i.val - 4) (by simp; omega)]
        simp [show 4 + (i.val - 4) = i.val by omega]
      rw [ite_eq_right (by omega)]
      by_cases h3 : i.val < 12
      · rw [ite_eq_left (by omega), show 0x80100 + (48 + i.val - 16) = 0x80128 + (i.val - 8) by omega,
          hf7 _ (by omega), hw6 (i.val - 8) (by simp; omega)]
        simp [show 8 + (i.val - 8) = i.val by omega]
      · rw [ite_eq_right (by omega), show 0x80100 + (48 + i.val) = 0x8013c + (i.val - 12) by omega,
          hw7 (i.val - 12) (by simp; omega)]
        simp [show 12 + (i.val - 12) = i.val by omega]
  obtain ⟨hout, hpc, hrun, -, -, hframe, -⟩ := salsa20_correct (m := ⟨x8, 0xc0, mem7, [], "", .running⟩)
    hs7 (codeAt_core hc7) rfl rfl x8_1
    (by rw [x8_2, y7_2, x7_2, y6_2, x6_2, y5_2, x5_2, y4_2, x4_2, y3_2, x3_2, y2_2, x2_2, y1_2,
      x1_2]; rfl)
    x8_10 x8_11 x8_12 input key constant hst
  change BytesAt (run 2373 _) _ _ at hout
  change (run 2373 _).pc = _ at hpc
  change (run 2373 _).status = _ at hrun
  change TweetNaCl.Salsa20Replay.Frame _ _ (run 2373 _) at hframe
  generalize run 2373 ⟨x8, 0xc0, mem7, [], "", .running⟩ = R at hout hpc hrun hframe ⊢
  obtain ⟨xR, pcR, memR, inpR, outR, stR⟩ := R
  obtain ⟨hsR, hiR, hoR, hfR⟩ := hframe
  simp only at hpc hrun hsR hiR hoR hfR hout
  subst hpc hrun hiR hoR
  have hcR : CodeAt memR := by
    intro i hi j hj
    rw [hfR _ (by simp [writable, Call.out, capacity, frameBytes]; rw [prog_length] at hi; omega)]
    exact hc7 i hi j hj
  -- Print the output and exit.
  obtain ⟨x9, e9, x9_17, x9_5, x9_6⟩ := seg_print hcR xR [] ""
  rw [run_add, e9, run_add]
  obtain ⟨x10, r10, -⟩ := print_loop (core input key constant).toList (by simp) x9 memR [] []
    0x80000 hcR (by simp [memSize]) (fun i hi => by simpa using hout ⟨i, by simpa using hi⟩)
    x9_5 (by simpa using x9_6) x9_17
  rw [show ("" : String) = String.ofList [] from rfl, r10]
  simpa using seg_exit hcR x10 [] _

theorem isCorrect : Salsa20Spec.IsCorrect initial := ⟨2931, correct⟩

end NettleSalsa20.IO
