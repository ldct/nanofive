import NettleSalsa20.Program
import NaClSalsa20.SymbolicSound
import NaClSalsa20.Reference

/-!
# `_nettle_salsa20_core` as a call

`_nettle_salsa20_core(dst, src, rounds)` maps the 16 little-endian words of the Salsa20 state at
`src` to the core's output at `dst`. Here `rounds` is 20. The proof is that of
`NaClSalsa20.Call`, with the input, key and constant bytes placed where the specification's
initial state holds them (`statePos`). Two certificates, both checked with `native_decide`:

* `Replay`: the public replay of `TweetNaCl.Salsa20Replay` from the function entry to its
  return, with only the code bytes, `sp`, `ra` and the argument registers known. It fixes the
  instruction, branch and address schedule, which therefore does not depend on the data. It
  includes `memcpy` and decides Nettle's `assert` on the known `rounds`.
* `Output`: the symbolic dataflow pass over that schedule gives each output byte a wire, and
  `Reference.core` over wires gives each byte of the Salsa20 core the same wire.

The soundness of both passes is proved in the kernel (`untilReturn_sound`, `run_sound`,
`core_rel`), so the certificates hold for every input.
-/
namespace NettleSalsa20.Call
open TinyFive NaClSalsa20 Wire
open TweetNaCl.Salsa20Replay (Word KnownBytes State Related Agrees Known Event Trace Frame
  untilReturn untilReturn_sound runFixed)

abbrev capacity : Nat := 0x100000
/-- `dst`, the output. -/
abbrev out : Nat := 0x80000
/-- `src`, the state. -/
abbrev src : Nat := 0x80100
abbrev rounds : Nat := 20
/-- The driver's return address. -/
abbrev returnPC : Word := 0x88
abbrev steps : Nat := 2373
abbrev frameBytes : Nat := 192

/-- The offset in the state of byte `k` of `input ++ key ++ constant`: `Salsa20Spec.initialState`
holds the constant in words 0, 5, 10 and 15, the key in words 1–4 and 11–14, and the input in
words 6–9. -/
def statePos (k : Nat) : Nat :=
  if k < 16 then k + 24 else if k < 32 then k - 12 else if k < 48 then k + 12
  else if k < 52 then k - 48 else if k < 56 then k - 32 else if k < 60 then k - 16 else k

theorem statePos_lt {k : Nat} (h : k < 64) : statePos k < 64 := by
  unfold statePos; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> omega

/-- The call's writable regions: the 64 output bytes and the 192-byte stack frame. -/
def writable (a : Nat) : Bool :=
  decide ((out ≤ a ∧ a < out + 64) ∨ (capacity - frameBytes ≤ a ∧ a < capacity))

/-! ## The replay certificate -/

/-- The only known initial bytes are `coreWords`: the code from `_nettle_salsa20_core` on. -/
@[irreducible] def image : KnownBytes :=
  coreWords.zipIdx.foldl (fun bytes (w, i) =>
    (List.range 4).foldl (fun bytes j => bytes.insert (coreEntry + 4 * i + j) (w.extractLsb' (8 * j) 8))
      bytes) {}

/-- Only the argument registers, the stack pointer and the return address are known. -/
def initial : State :=
  let regs := Vector.replicate 32 (α := Option Word) none
  let regs := regs.set 1 (some returnPC) (by decide)
  let regs := regs.set 2 (some (BitVec.ofNat 64 capacity)) (by decide)
  let regs := regs.set 10 (some (BitVec.ofNat 64 out)) (by decide)
  let regs := regs.set 11 (some (BitVec.ofNat 64 src)) (by decide)
  let regs := regs.set 12 (some (BitVec.ofNat 64 rounds)) (by decide)
  ⟨regs, BitVec.ofNat 64 coreEntry, image⟩

theorem initial_related {m : Machine 64}
    (hpc : m.pc = BitVec.ofNat 64 coreEntry) (hrun : m.status = .running)
    (hra : m.x.get 1 = returnPC) (hsp : m.x.get 2 = BitVec.ofNat 64 capacity)
    (ho : m.x.get 10 = BitVec.ofNat 64 out) (hs : m.x.get 11 = BitVec.ofNat 64 src)
    (hr : m.x.get 12 = BitVec.ofNat 64 rounds)
    (hmem : Agrees image m.mem) : Related initial m := by
  refine ⟨hpc, hrun, ?_, show Agrees image m.mem from hmem⟩
  intro r
  by_cases h0 : r = 0
  · subst r
    intro k hk
    rw [TweetNaCl.Salsa20Replay.State.get, ite_eq_left rfl] at hk
    cases hk
    exact Regs.get_zero _
  simp only [TweetNaCl.Salsa20Replay.State.get, initial, ite_eq_right h0, Vector.getElem_set,
    Vector.getElem_replicate]
  split
  next he => simpa [Known, show r = 12 from Fin.ext he.symm] using hr
  split
  next he => simpa [Known, show r = 11 from Fin.ext he.symm] using hs
  split
  next he => simpa [Known, show r = 10 from Fin.ext he.symm] using ho
  split
  next he => simpa [Known, show r = 2 from Fin.ext he.symm] using hsp
  split
  next he => simpa [Known, show r = 1 from Fin.ext he.symm] using hra
  simp [Known]

/-- The instruction words `words` are stored little-endian from `base`. -/
def WordsAt (m : Machine 64) (base : Nat) (words : List (BitVec 32)) : Prop :=
  ∀ i (hi : i < words.length) j, j < 4 →
    m.mem[base + 4 * i + j]? = some (words[i].extractLsb' (8 * j) 8)

theorem image_agrees {m : Machine 64} (hcore : WordsAt m coreEntry coreWords) :
    Agrees image m.mem := by
  have hins : ∀ (bytes : KnownBytes) (addr : Nat) (v : BitVec 8), Agrees bytes m.mem →
      m.mem[addr]? = some v → Agrees (bytes.insert addr v) m.mem := by
    intro bytes addr v hb hv a b hab
    change (bytes.insert addr v)[a]? = some b at hab
    rw [Std.TreeMap.getElem?_insert] at hab
    split at hab
    next he =>
      cases hab
      rw [← show addr = a from Nat.compare_eq_eq.mp he]
      exact hv
    next => exact hb a b hab
  unfold image
  suffices ∀ (l : List (BitVec 32 × Nat)) (b : KnownBytes), (∀ p ∈ l, p ∈ coreWords.zipIdx) →
      Agrees b m.mem →
      Agrees (l.foldl (fun bytes (w, i) => (List.range 4).foldl (fun bytes j =>
        bytes.insert (coreEntry + 4 * i + j) (w.extractLsb' (8 * j) 8)) bytes) b) m.mem from
    this _ _ (fun _ hp => hp) (fun _ _ h => by simp at h)
  intro l
  induction l with
  | nil => intro b _ hb; exact hb
  | cons p l ih =>
    intro b hl hb
    refine ih _ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) ?_
    obtain ⟨w, i⟩ := p
    obtain ⟨hi, he⟩ := List.mem_zipIdx' (hl _ List.mem_cons_self)
    simp only
    suffices ∀ (js : List Nat) (b : KnownBytes), (∀ j ∈ js, j < 4) → Agrees b m.mem →
        Agrees (js.foldl (fun bytes j =>
          bytes.insert (coreEntry + 4 * i + j) (w.extractLsb' (8 * j) 8)) b) m.mem from
      this _ _ (fun j hj => List.mem_range.mp hj) hb
    intro js
    induction js with
    | nil => intro b _ hb; exact hb
    | cons j js ih' =>
      intro b hj hb
      refine ih' _ (fun k hk => hj k (List.mem_cons_of_mem _ hk)) (hins _ _ _ hb ?_)
      rw [he]
      exact hcore i hi j (hj j List.mem_cons_self)

-- Keep the kernel from unfolding the replay when checking facts about its projections.
private opaque checkedResult :
    { v : Option (List Event × State) // untilReturn writable capacity returnPC steps initial = v } :=
  ⟨untilReturn writable capacity returnPC steps initial, rfl⟩

private def cert : Option (List Event × State) := checkedResult.val

/-- The checked schedule of `_nettle_salsa20_core`. -/
def schedule : List Event := (cert.getD ([], initial)).1

private def final : State := (cert.getD ([], initial)).2

private theorem cert_checked :
    cert.map (fun (es, s) => (es.length, s.get 2, s.get 1)) =
      some (steps, some (BitVec.ofNat 64 capacity), some returnPC) := by
  native_decide

private theorem unpack (v : Option (List Event × State)) (f : State)
    (h : v.map (fun (es, s) => (es.length, s.get 2, s.get 1)) =
      some (steps, some (BitVec.ofNat 64 capacity), some returnPC)) :
    v = some ((v.getD ([], f)).1, (v.getD ([], f)).2) ∧
      (v.getD ([], f)).1.length = steps ∧
      (v.getD ([], f)).2.get 2 = some (BitVec.ofNat 64 capacity) ∧
      (v.getD ([], f)).2.get 1 = some returnPC := by
  cases v with
  | none => contradiction
  | some p =>
    rcases p with ⟨es, s⟩
    simp_all only [Option.map_some, Option.getD, Option.some.injEq, Prod.mk.injEq, true_and]

private theorem cert_success : cert = some (schedule, final) :=
  (unpack cert initial cert_checked).1

private theorem cert_summary : schedule.length = steps ∧
    final.get 2 = some (BitVec.ofNat 64 capacity) ∧ final.get 1 = some returnPC :=
  (unpack cert initial cert_checked).2

/-- Every machine that agrees with `initial` returns along the checked schedule. -/
theorem verified {m : Machine 64} (h : Related initial m) (hc : m.mem.size = capacity) :
    Trace schedule m ∧ runFixed schedule m = run steps m ∧ Frame writable m (run steps m) ∧
    (run steps m).pc = returnPC ∧ (run steps m).status = .running ∧
    (run steps m).x.get 2 = BitVec.ofNat 64 capacity ∧
    (run steps m).x.get 1 = returnPC := by
  obtain ⟨trace, rel, frame, ret, _⟩ :=
    untilReturn_sound h hc (checkedResult.property.trans cert_success)
  obtain ⟨hlen, hsp, hra⟩ := cert_summary
  have hfixed := trace.runFixed_eq
  rw [hlen] at hfixed rel frame
  exact ⟨trace, hfixed, frame, rel.1.trans ret, rel.2.1, rel.2.2.1 2 _ hsp, rel.2.2.1 1 _ hra⟩

/-! ## The output certificate -/

/-- `Reference.core` over wires: sums are atoms looked up in `a`. -/
def symOps (a : Arena) : Reference.Ops (Option Wire) (Option Wire) where
  add x y := do Wire.add a.mk (← x) (← y)
  xor x y := do pure (Wire.xor (← x) (← y))
  rotl x k := x.map (Wire.rotl · k)
  pack b0 b1 b2 b3 := do pure (Wire.pack (← b0) (← b1) (← b2) (← b3))
  byte x k := x.map (Wire.byte · k.val)

/-- The initial bytes at `src + statePos (first + i)`, as leaf atoms. -/
def leaves (a : Arena) (first n : Nat) : Vector (Option Wire) n :=
  Vector.ofFn fun i => (a.mk (.leaf (src + statePos (first + i)))).map (atom 8)

def expected (a : Arena) : Vector (Option Wire) 64 :=
  Reference.core (symOps a) (leaves a 0 16) (leaves a 16 32) (leaves a 48 16)

private def buildEmit (n : Node) : StateM Arena Id := fun a => a.intern n

/-- The arena the checker uses; a hint, since every row is checked where it is used. -/
private def candidate : Arena := ((Symbolic.run buildEmit schedule {}).run Arena.empty).2

private def matchAt (a : Arena) (s : Symbolic.State) (i : Fin 64) : Bool :=
  match s.mem[out + i.val]?, (expected a)[i] with
  | some (some x), some y => decide (x = y)
  | _, _ => false

private def check : Bool :=
  match Symbolic.run candidate.mk schedule {} with
  | some s => (List.finRange 64).all (matchAt candidate s)
  | none => false

private theorem checked : check = true := by native_decide

private theorem schedule_ok : schedule.all (Symbolic.Event.Ok capacity) = true := by native_decide

/-- The bytes at a buffer in machine memory. -/
def BytesAt (m : Machine 64) (address : Nat) {n : Nat} (b : TweetNaCl.Salsa20Spec.Bytes n) : Prop :=
  ∀ i : Fin n, m.mem[address + i.val]? = some b[i]

attribute [-simp] BitVec.getLsbD_eq_getElem

section Output
variable (a : Arena) (env : Nat → BitVec 8)

/-- Wires relate to the values they describe. -/
private def rel : Reference.Rel (symOps a) Reference.concrete where
  word x v := ∀ w, x = some w → Describes (a.eval env) 32 w v
  byte x b := ∀ w, x = some w → Describes (a.eval env) 8 w b
  add := by
    intro x v y u hx hy w hw
    simp only [symOps, bind, Option.bind_eq_some_iff] at hw
    obtain ⟨x', hx', y', hy', hw⟩ := hw
    exact add_sound hw (hx x' hx') (hy y' hy')
  xor := by
    intro x v y u hx hy w hw
    simp only [symOps, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨x', hx', y', hy', rfl⟩ := hw
    exact xor_sound (hx x' hx') (hy y' hy')
  rotl := by
    intro x v k hx w hw
    simp only [symOps, Option.map_eq_some_iff] at hw
    obtain ⟨x', hx', rfl⟩ := hw
    exact rotl_sound k (hx x' hx')
  pack := by
    intro b0 c0 b1 c1 b2 c2 b3 c3 h0 h1 h2 h3 w hw
    simp only [symOps, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨x0, e0, x1, e1, x2, e2, x3, e3, rfl⟩ := hw
    exact pack_sound (h0 x0 e0) (h1 x1 e1) (h2 x2 e2) (h3 x3 e3)
  toByte := by
    intro x v k hx w hw
    simp only [symOps, Option.map_eq_some_iff] at hw
    obtain ⟨x', hx', rfl⟩ := hw
    exact byte_sound k.isLt (hx x' hx') fun j hj => by simp [Reference.concrete, hj]

private theorem leaves_rel {first n : Nat} {b : TweetNaCl.Salsa20Spec.Bytes n}
    (h : ∀ i (hi : i < n), env (src + statePos (first + i)) = b[i]) :
    Reference.Pointwise (rel a env).byte (leaves a first n) b := by
  intro i hi w hw
  simp only [leaves, Vector.getElem_ofFn, Option.map_eq_some_iff] at hw
  obtain ⟨id, hid, rfl⟩ := hw
  refine (atom_sound id).of_bits fun j hj => ?_
  rw [Arena.mk_sound env hid]
  simp [Node.eval, h i hi, show j < 32 by omega]

end Output

private theorem eq_of_describes {val : Id → BitVec 32} {w : Wire} {b c : BitVec 8}
    (hb : Describes val 8 w b) (hc : Describes val 8 w c) : b = c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [hb i hi, hc i hi]

/-- The state at `base` holds `input`, `key` and `constant` where `Salsa20Spec.initialState`
puts them. -/
def StateAt (m : Machine 64) (base : Nat) (input : TweetNaCl.Salsa20Spec.Bytes 16)
    (key : TweetNaCl.Salsa20Spec.Bytes 32) (constant : TweetNaCl.Salsa20Spec.Bytes 16) : Prop :=
  (∀ i : Fin 16, m.mem[base + statePos i.val]? = some input[i]) ∧
  (∀ i : Fin 32, m.mem[base + statePos (16 + i.val)]? = some key[i]) ∧
  (∀ i : Fin 16, m.mem[base + statePos (48 + i.val)]? = some constant[i])

/-- Every input, key and constant in the state produces the Salsa20 core. -/
theorem output_correct {m : Machine 64} (h : Related initial m) (hc : m.mem.size = capacity)
    (inputBytes : TweetNaCl.Salsa20Spec.Bytes 16) (keyBytes : TweetNaCl.Salsa20Spec.Bytes 32)
    (constantBytes : TweetNaCl.Salsa20Spec.Bytes 16)
    (hst : StateAt m src inputBytes keyBytes constantBytes) :
    BytesAt (run steps m) out (TweetNaCl.Salsa20Spec.core inputBytes keyBytes constantBytes) := by
  let env : Nat → BitVec 8 := fun a => m.mem[a]?.getD 0
  have hstart : Symbolic.Rel (candidate.eval env) env capacity {} m := by
    refine ⟨fun r w hw => ?_, hc, fun a ha => ⟨env a, ?_, rfl⟩⟩
    · simp only [Symbolic.State.get] at hw
      split at hw
      next h0 =>
        cases hw
        subst h0
        exact const_sound 0
      next => simp at hw
    · simp [env, Array.getElem?_eq_getElem (show a < m.mem.size by omega)]
  have hcheck := checked
  unfold check at hcheck
  split at hcheck
  next s hs =>
    have hrun := Symbolic.run_sound schedule_ok hstart hs
    rw [(verified h hc).2.1] at hrun
    have href := Reference.core_rel (rel candidate env)
      (leaves_rel candidate env (first := 0) (b := inputBytes) fun j hj => by
        simp [env, hst.1 ⟨j, hj⟩])
      (leaves_rel candidate env (first := 16) (b := keyBytes) fun j hj => by
        simp [env, hst.2.1 ⟨j, hj⟩])
      (leaves_rel candidate env (first := 48) (b := constantBytes) fun j hj => by
        simp [env, hst.2.2 ⟨j, hj⟩])
    rw [Reference.core_concrete] at href
    intro i
    have hmi := List.all_eq_true.mp hcheck i (List.mem_finRange i)
    unfold matchAt at hmi
    split at hmi
    next x y hx hy =>
      obtain rfl := of_decide_eq_true hmi
      obtain ⟨b, hb, hr⟩ := hrun.mem (out + i.val) (by have := i.isLt; simp only [out, capacity]; omega)
      rw [hx] at hr
      have hs := href i.val i.isLt x hy
      rw [hb, eq_of_describes hr hs]
      rfl
    next => contradiction
  next => contradiction

/-- The call writes the Salsa20 core of the input, key and constant in the state. The
instruction, branch and address trace does not depend on them.

Assumptions: memory is `capacity` bytes and holds `coreWords` at `coreEntry`; execution starts
there; `ra`, `sp` and `a0`–`a2` hold the return address, the top of memory, `dst`, `src` and 20.
Nothing else about the registers or memory is assumed. -/
theorem salsa20_correct {m : Machine 64}
    (hc : m.mem.size = capacity) (hcore : WordsAt m coreEntry coreWords)
    (hpc : m.pc = BitVec.ofNat 64 coreEntry) (hrun : m.status = .running)
    (hra : m.x.get 1 = returnPC) (hsp : m.x.get 2 = BitVec.ofNat 64 capacity)
    (ha0 : m.x.get 10 = BitVec.ofNat 64 out) (ha1 : m.x.get 11 = BitVec.ofNat 64 src)
    (ha2 : m.x.get 12 = BitVec.ofNat 64 rounds)
    (inputBytes : TweetNaCl.Salsa20Spec.Bytes 16) (keyBytes : TweetNaCl.Salsa20Spec.Bytes 32)
    (constantBytes : TweetNaCl.Salsa20Spec.Bytes 16)
    (hst : StateAt m src inputBytes keyBytes constantBytes) :
    let r := run steps m
    BytesAt r out (TweetNaCl.Salsa20Spec.core inputBytes keyBytes constantBytes) ∧
    r.pc = returnPC ∧ r.status = .running ∧
    r.x.get 2 = BitVec.ofNat 64 capacity ∧ r.x.get 1 = returnPC ∧
    Frame writable m r ∧ Trace schedule m := by
  have h := initial_related hpc hrun hra hsp ha0 ha1 ha2 (image_agrees hcore)
  obtain ⟨trace, _, frame, hp, hr, hsp', hra'⟩ := verified h hc
  exact ⟨output_correct h hc inputBytes keyBytes constantBytes hst,
    hp, hr, hsp', hra', frame, trace⟩

/-! ## The state as 64 bytes -/

open TweetNaCl.Salsa20Spec in
/-- The input, key and constant bytes of a state. -/
def split (b : Bytes 64) : Bytes 16 × Bytes 32 × Bytes 16 :=
  (Vector.ofFn fun i => b[statePos i.val]'(statePos_lt (by omega)),
   Vector.ofFn fun i => b[statePos (16 + i.val)]'(statePos_lt (by omega)),
   Vector.ofFn fun i => b[statePos (48 + i.val)]'(statePos_lt (by omega)))

open TweetNaCl.Salsa20Spec in
theorem decode_split (b : Bytes 64) :
    TweetNaCl.Salsa20Spec.decode b = initialState (split b).1 (split b).2.1 (split b).2.2 := by
  apply Vector.ext
  intro i hi
  simp only [TweetNaCl.Salsa20Spec.decode, decodeWords, initialState, split, Vector.getElem_ofFn]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _
  | 12, _ | 13, _ | 14, _ | 15, _ => simp [statePos]
  | _ + 16, h => exact absurd h (by omega)

open TweetNaCl.Salsa20Spec in
/-- The core of a whole state is the core of its input, key and constant. -/
theorem coreBytes_split (b : Bytes 64) :
    coreBytes b = core (split b).1 (split b).2.1 (split b).2.2 := by
  rw [coreBytes, core, decode_split]

theorem stateAt_of_bytesAt {m : Machine 64} {b : TweetNaCl.Salsa20Spec.Bytes 64}
    (h : BytesAt m src b) : StateAt m src (split b).1 (split b).2.1 (split b).2.2 :=
  ⟨fun i => by simpa [split] using h ⟨_, statePos_lt (k := i.val) (by omega)⟩,
   fun i => by simpa [split] using h ⟨_, statePos_lt (k := 16 + i.val) (by omega)⟩,
   fun i => by simpa [split] using h ⟨_, statePos_lt (k := 48 + i.val) (by omega)⟩⟩

/-- The call writes the Salsa20 core of the 64-byte state, `Salsa20Spec.coreBytes`. -/
theorem salsa20_correct_bytes {m : Machine 64}
    (hc : m.mem.size = capacity) (hcore : WordsAt m coreEntry coreWords)
    (hpc : m.pc = BitVec.ofNat 64 coreEntry) (hrun : m.status = .running)
    (hra : m.x.get 1 = returnPC) (hsp : m.x.get 2 = BitVec.ofNat 64 capacity)
    (ha0 : m.x.get 10 = BitVec.ofNat 64 out) (ha1 : m.x.get 11 = BitVec.ofNat 64 src)
    (ha2 : m.x.get 12 = BitVec.ofNat 64 rounds)
    (state : TweetNaCl.Salsa20Spec.Bytes 64) (hs : BytesAt m src state) :
    let r := run steps m
    BytesAt r out (TweetNaCl.Salsa20Spec.coreBytes state) ∧
    r.pc = returnPC ∧ r.status = .running ∧
    r.x.get 2 = BitVec.ofNat 64 capacity ∧ r.x.get 1 = returnPC ∧
    Frame writable m r ∧ Trace schedule m := by
  rw [coreBytes_split]
  exact salsa20_correct hc hcore hpc hrun hra hsp ha0 ha1 ha2 _ _ _ (stateAt_of_bytesAt hs)

end NettleSalsa20.Call
