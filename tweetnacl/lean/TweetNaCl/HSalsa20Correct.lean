import TweetNaCl.HSalsa20Replay
import TweetNaCl.HSalsa20Reference
import TweetNaCl.Salsa20Correct

/-!
# `crypto_core_hsalsa20_tweet` is HSalsa20

This follows `Salsa20Slots.Wrapper`, `Salsa20RefCert` and `Salsa20Correct` for the HSalsa20
wrapper. The checked schedule of `HSalsa20Replay` is lowered to slot actions over the same
layout, folded into a circuit, and every output byte is compared with the reference
`HSalsa20Reference.hcore`, whose concrete bytes are `HSalsa20Spec.hsalsa20`.
-/
namespace TweetNaCl.HSalsa20Correct
open TinyFive Salsa20Circuit Salsa20Symbolic Salsa20Reference Salsa20RefCert
open HSalsa20Reference (hcore map_hcore)
open HSalsa20Replay (capacity out inp key constant returnPC steps writable schedule initial
  initial_related image_agrees verified WordsAt)
open Salsa20Correct (BytesAt)

/-! ## The slot program -/

private def slotsChecked : Option (List Salsa20Slots.Action) :=
  Salsa20Slots.compile Salsa20Slots.Wrapper.layout schedule

def program : List Salsa20Slots.Action := slotsChecked.getD []

private theorem slots_length : slotsChecked.map List.length = some steps := by
  native_decide

theorem program_checked : Salsa20Slots.compile Salsa20Slots.Wrapper.layout schedule = some program := by
  have h := slots_length
  change slotsChecked = some program
  cases hc : slotsChecked with
  | none => rw [hc] at h; contradiction
  | some as => simp [program, hc]

theorem program_sound {m : Machine 64} (h : Salsa20Replay.Related initial m)
    (hc : m.mem.size = capacity) :
    (Salsa20Slots.run program (Salsa20Slots.State.ofMachine Salsa20Slots.Wrapper.layout m)).Related
      Salsa20Slots.Wrapper.layout (TinyFive.run steps m) := by
  rw [← (verified h hc).2.1]
  exact Salsa20Slots.compile_sound program_checked
    (Salsa20Slots.State.ofMachine_related Salsa20Slots.Wrapper.layout m hc)

/-! ## The reference over the circuit -/

def href (a : Arena) (inp key constant : Nat) : Vector (Option Value) 32 :=
  hcore (algebra a) (readArg a.mk) inp key constant

theorem href_sound (a : Arena) (env : Leaves) (inp key constant : Nat) (i : Fin 32)
    {v : Value} (h : (href a inp key constant)[i.val] = some v) :
    v.eval a env = (hcore concreteOps (fun addr => (env.argByte addr).setWidth 64)
      inp key constant)[i.val] := by
  let paired := hcore (pairOps a env) (pairInput a env) inp key constant
  have hs : paired[i.val].1.1 = (href a inp key constant)[i.val] := by
    have he := map_hcore (symbolicProjection a env) (fun addr => show
      (symbolicProjection a env).toFun (pairInput a env addr) = readArg a.mk addr from rfl)
      inp key constant
    have hi := congrArg (fun xs : Vector (Option Value) 32 => xs[i.val]) he
    change ((hcore (pairOps a env) (pairInput a env) inp key constant).map
      (symbolicProjection a env).toFun)[i.val] = (href a inp key constant)[i.val] at hi
    rw [Vector.getElem_map] at hi
    exact hi
  have hc : paired[i.val].1.2 = (hcore concreteOps (input env) inp key constant)[i.val] := by
    have he := map_hcore (concreteProjection a env) (fun addr => show
      (concreteProjection a env).toFun (pairInput a env addr) = input env addr from rfl)
      inp key constant
    have hi := congrArg (fun xs : Vector Word 32 => xs[i.val]) he
    change ((hcore (pairOps a env) (pairInput a env) inp key constant).map
      (concreteProjection a env).toFun)[i.val] =
        (hcore concreteOps (input env) inp key constant)[i.val] at hi
    rw [Vector.getElem_map] at hi
    exact hi
  exact (paired[i.val].2 v (hs.trans h)).trans hc


/-! ## The output certificate -/

def start : Salsa20Symbolic.State :=
  let regs := ([(1, returnPC), (2, BitVec.ofNat 64 capacity), (10, BitVec.ofNat 64 out),
    (11, BitVec.ofNat 64 inp), (12, BitVec.ofNat 64 key), (13, BitVec.ofNat 64 constant)] :
      List (Nat × BitVec 64)).foldl (fun r (i, v) => r.insert i (.literal v)) ({} : Std.TreeMap Nat Value)
  { regs, pc := BitVec.ofNat 64 HSalsa20Program.entry }

private def buildEmit (n : Node) : StateM Arena Id := fun a => a.intern n

private def candidate : Arena :=
  ((Salsa20Symbolic.run buildEmit program start).run Arena.empty).2

private def expected (a : Arena) : Vector (Option Value) 32 :=
  href a inp key constant

private def matchAt (a : Arena) (s : Salsa20Symbolic.State) (i : Fin 32) : Bool :=
  match s.mem[out + i.val]?, (expected a)[i] with
  | some x, some y => decide (x = y)
  | _, _ => false

/-- Check every output position separately; missing rows cannot compare equal. -/
private def outputsMatch (a : Arena) (s : Salsa20Symbolic.State) : Bool :=
  (List.finRange 32).all (matchAt a s)

private def check : Bool :=
  match Salsa20Symbolic.run candidate.mk program start with
  | some s => outputsMatch candidate s
  | none => false

private theorem checked : check = true := by native_decide

private theorem match_at {a : Arena} {s : Salsa20Symbolic.State} (h : outputsMatch a s = true) (i : Fin 32) :
    ∃ v, s.mem[out + i.val]? = some v ∧ (expected a)[i] = some v := by
  have hi : matchAt a s i = true := List.all_eq_true.mp h i (List.mem_finRange i)
  unfold matchAt at hi
  split at hi
  next x y hx hy =>
    obtain rfl := of_decide_eq_true hi
    exact ⟨x, hx, hy⟩
  next => contradiction

private def leaves (m : Machine 64) : Leaves :=
  ⟨m.x.get, fun addr => m.mem[addr]?.getD 0⟩

private theorem read_leaves (m : Machine 64) (a n : Nat) (hb : a + n ≤ m.mem.size) :
    readBytes m.mem a n = some ((leaves m).read a n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp [readBytes, Leaves.read, leaves, Array.getElem?_eq_getElem (show a < m.mem.size by omega),
      ih (a + 1) (by omega)]

private theorem register_start {m : Machine 64} (h : Salsa20Replay.Related HSalsa20Replay.initial m)
    (a : Arena) (r : TinyFive.Reg) :
    (start.regs[r.val]?.map (Value.eval a (leaves m))).getD ((leaves m).savedReg r) = m.x.get r := by
  have ha (q : TinyFive.Reg) (v : BitVec 64)
      (hq : HSalsa20Replay.initial.get q = some v) := (h.2.2.1 q v hq).symm
  simp only [start, List.foldl_cons, List.foldl_nil, Std.TreeMap.getElem?_insert,
    Nat.compare_eq_eq]
  split
  next he =>
    have hr : r = 13 := Fin.ext (by omega)
    subst r
    exact ha 13 (BitVec.ofNat 64 constant) (by decide)
  split
  next he =>
    have hr : r = 12 := Fin.ext (by omega)
    subst r
    exact ha 12 (BitVec.ofNat 64 key) (by decide)
  split
  next he =>
    have hr : r = 11 := Fin.ext (by omega)
    subst r
    exact ha 11 (BitVec.ofNat 64 inp) (by decide)
  split
  next he =>
    have hr : r = 10 := Fin.ext (by omega)
    subst r
    exact ha 10 (BitVec.ofNat 64 out) (by decide)
  split
  next he =>
    have hr : r = 2 := Fin.ext (by omega)
    subst r
    exact ha 2 (BitVec.ofNat 64 capacity) (by decide)
  split
  next he =>
    have hr : r = 1 := Fin.ext (by omega)
    subst r
    exact ha 1 returnPC (by decide)
  rfl

private theorem bytesAt_region {m : Machine 64} {base n : Nat} {b : Salsa20Spec.Bytes n}
    (h : BytesAt m base b) :
    Salsa20Reference.ByteRegion (fun a => ((leaves m).argByte a).setWidth 64) base b := by
  intro i hi
  have h' : m.mem[base + i]? = some b[i] := h ⟨i, hi⟩
  simp [leaves, h']

private theorem start_related {m : Machine 64} (h : Salsa20Replay.Related HSalsa20Replay.initial m)
    (hc : m.mem.size = capacity) (a : Arena) :
    start.Related a (leaves m) Salsa20Slots.Wrapper.layout
      (Salsa20Slots.State.ofMachine Salsa20Slots.Wrapper.layout m) := by
  refine ⟨h.1.symm, fun r _ => register_start h a r, ?_⟩
  intro w addr hw
  have hb : addr + w.bytes ≤ m.mem.size := hc ▸ hw.1
  change initialMem (leaves m) w addr =
    (Salsa20Slots.Memory.ofBytes Salsa20Slots.Wrapper.layout m.mem).get addr
  rcases hw.2 with ⟨rfl, hbyte⟩ | ⟨rfl, hword, _⟩
  · simp [initialMem, Salsa20Slots.Memory.get, Salsa20Slots.Memory.ofBytes, hbyte, leaves]
  · simp [initialMem, Salsa20Slots.Memory.get, Salsa20Slots.Memory.ofBytes, hword,
      read_leaves m addr 8 (by simpa [Width.bytes] using hb), Width.bytes]

private theorem checked_supported :
    program.all
      (fun a => decide (Supported Salsa20Slots.Wrapper.layout a)) = true := by native_decide

private theorem checked_output_slots :
    (List.finRange 32).all (fun i => decide
      (Salsa20Slots.Wrapper.layout.Allows .byte (out + i.val))) = true := by native_decide

private theorem read_one (mem : Array (BitVec 8)) (addr : Nat) :
    readBytes mem addr 1 = mem[addr]? := by
  unfold readBytes
  cases mem[addr]? with
  | none => rfl
  | some b =>
    simp [readBytes]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    change (0#0 ++ b).getLsbD i = b.getLsbD i
    simp only [BitVec.getLsbD_append, ite_eq_left hi]

private theorem some_check (a : Arena) (r : Option Salsa20Symbolic.State)
    (h : (match r with | some s => outputsMatch a s | none => false) = true) :
    ∃ s, r = some s ∧ outputsMatch a s = true := by
  cases r with
  | none => contradiction
  | some s => exact ⟨s, rfl, h⟩

/-- Every input/key/constant triple at the fixed ABI layout produces the 32
    specified HSalsa20 bytes, in exactly `steps` model instructions. -/
theorem output_correct {m : Machine 64} (h : Salsa20Replay.Related HSalsa20Replay.initial m)
    (hc : m.mem.size = capacity)
    (inputBytes : Salsa20Spec.Bytes 16) (keyBytes : Salsa20Spec.Bytes 32)
    (constantBytes : Salsa20Spec.Bytes 16)
    (hi : BytesAt m inp inputBytes) (hk : BytesAt m key keyBytes)
    (ht : BytesAt m constant constantBytes) :
    BytesAt (TinyFive.run steps m) out
      (HSalsa20Spec.hsalsa20 inputBytes keyBytes constantBytes) := by
  obtain ⟨s, hs, hm⟩ := some_check candidate _ checked
  have hsupp (a) (ha : a ∈ program) : Supported Salsa20Slots.Wrapper.layout a :=
    of_decide_eq_true (List.all_eq_true.mp checked_supported a ha)
  have hrun := Salsa20Symbolic.run_sound hsupp (start_related h hc candidate) hs
  have hslots := program_sound h hc
  have hspec := HSalsa20Reference.hcore_concrete_eq_hsalsa20 _ inp key constant inputBytes
    keyBytes constantBytes (bytesAt_region hi) (bytesAt_region hk) (bytesAt_region ht)
  intro i
  obtain ⟨v, hv, he⟩ := match_at hm i
  have ha : Salsa20Slots.Wrapper.layout.Allows .byte (out + i.val) :=
    of_decide_eq_true (List.all_eq_true.mp checked_output_slots i (List.mem_finRange i))
  have hr := hrun.2.2 .byte _ ha
  simp only [hv, Option.map_some, Option.getD_some] at hr
  have hb := (hslots.2.2.2 .byte _ ha).1
  change readBytes (TinyFive.run steps m).mem (out + i.val) 1 = some _ at hb
  have href := href_sound candidate (leaves m) inp key constant i he
  have hbyte := congrArg (fun xs : Salsa20Spec.Bytes 32 => xs[i.val]) hspec
  rw [read_one, ← hr, href] at hb
  simp only [Vector.getElem_map] at hbyte
  exact hb.trans (congrArg some hbyte)

/-- `crypto_core_hsalsa20_tweet` writes HSalsa20 and returns zero, for every input, key and
constant at the fixed buffers. The instruction, branch and address trace does not depend on
them.

Assumptions: memory is `capacity` bytes and holds the linked helper and wrapper words;
execution starts at the wrapper entry; `ra`, `sp` and `a0`–`a3` hold the return address, the
top of memory, and the output, input, key and constant addresses. Nothing else about the
registers or memory is assumed. -/
theorem hsalsa20_correct {m : Machine 64}
    (hc : m.mem.size = capacity)
    (hcore : WordsAt m Salsa20Program.coreEntry Salsa20Program.coreWords)
    (hwrap : WordsAt m HSalsa20Program.entry HSalsa20Program.wrapperWords)
    (hpc : m.pc = BitVec.ofNat 64 HSalsa20Program.entry) (hrun : m.status = .running)
    (hra : m.x.get 1 = returnPC) (hsp : m.x.get 2 = BitVec.ofNat 64 capacity)
    (ha0 : m.x.get 10 = BitVec.ofNat 64 out) (ha1 : m.x.get 11 = BitVec.ofNat 64 inp)
    (ha2 : m.x.get 12 = BitVec.ofNat 64 key) (ha3 : m.x.get 13 = BitVec.ofNat 64 constant)
    (inputBytes : Salsa20Spec.Bytes 16) (keyBytes : Salsa20Spec.Bytes 32)
    (constantBytes : Salsa20Spec.Bytes 16)
    (hi : BytesAt m inp inputBytes) (hk : BytesAt m key keyBytes)
    (ht : BytesAt m constant constantBytes) :
    let r := TinyFive.run steps m
    BytesAt r out (HSalsa20Spec.hsalsa20 inputBytes keyBytes constantBytes) ∧
    r.pc = returnPC ∧ r.status = .running ∧ r.x.get 10 = 0 ∧
    r.x.get 2 = BitVec.ofNat 64 capacity ∧ r.x.get 1 = returnPC ∧
    Salsa20Replay.Frame writable m r ∧ Salsa20Replay.Trace schedule m := by
  have h := initial_related hpc hrun hra hsp ha0 ha1 ha2 ha3 (image_agrees hcore hwrap)
  obtain ⟨trace, _, frame, hp, hr, h0, hsp', hra'⟩ := verified h hc
  exact ⟨output_correct h hc inputBytes keyBytes constantBytes hi hk ht,
    hp, hr, h0, hsp', hra', frame, trace⟩

end TweetNaCl.HSalsa20Correct
