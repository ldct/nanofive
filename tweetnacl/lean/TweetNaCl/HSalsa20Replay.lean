import TweetNaCl.Salsa20Replay
import TweetNaCl.HSalsa20Program

/-!
# The public replay of `crypto_core_hsalsa20_tweet`

`Salsa20Replay.Wrapper` for the HSalsa20 wrapper: the generic replay of `Salsa20Replay` from
the wrapper entry to its return, with only the code bytes, `sp`, `ra` and the argument
registers known, fixes the instruction, branch and address schedule. The helper `core` takes
its `h = 1` branch.
-/
namespace TweetNaCl.HSalsa20Replay
open TinyFive Salsa20Replay

abbrev capacity : Nat := 0x100000
abbrev out : Nat := 0x80000
abbrev inp : Nat := 0x80100
abbrev key : Nat := 0x80200
abbrev constant : Nat := 0x80300
/-- The return address: the instruction after the call in `HSalsa20IOProgram`'s driver. -/
abbrev returnPC : Word := 0x11e0
abbrev steps : Nat := 11514

/-- The wrapper's writable regions: 32 output bytes and the combined 528-byte stack frame. -/
def writable (a : Nat) : Bool :=
  decide ((out ≤ a ∧ a < out + 32) ∨ (capacity - 528 ≤ a ∧ a < capacity))

private def addWords (base : Nat) (words : List (BitVec 32)) (bytes : KnownBytes) : KnownBytes :=
  (words.zipIdx).foldl (fun b (w, i) => write b (base + 4 * i) (some (w.setWidth 64)) 4) bytes

/-- Known initial bytes are just the linked instructions. In particular the inputs,
    output and stack have arbitrary contents. -/
def image : KnownBytes :=
  addWords HSalsa20Program.entry HSalsa20Program.wrapperWords
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
  ⟨regs, BitVec.ofNat 64 HSalsa20Program.entry, image⟩

/-- Sufficient explicit ABI and byte-image assumptions for the checker. No other
    register or memory contents are restricted. -/
theorem initial_related {m : Machine 64}
    (hpc : m.pc = BitVec.ofNat 64 HSalsa20Program.entry) (hrun : m.status = .running)
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
    (hwrap : WordsAt m HSalsa20Program.entry HSalsa20Program.wrapperWords) :
    Agrees image m.mem :=
  addWords_agrees (addWords_agrees (fun _ _ h => by simp at h) hcore) hwrap

-- Abstract the evaluated option so that kernel conversion does not unfold the
-- 11,514-step execution when checking a proof about its projections.
private opaque checkedResult :
    { v : Option (List Event × State) // untilReturn writable capacity returnPC steps initial = v } :=
  ⟨untilReturn writable capacity returnPC steps initial, rfl⟩

private def cert : Option (List Event × State) := checkedResult.val

/-- Fully checked decoded schedule for the linked `crypto_core_hsalsa20_tweet` wrapper. -/
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

end TweetNaCl.HSalsa20Replay
