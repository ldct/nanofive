import TweetNaCl.Salsa20Symbolic
import TweetNaCl.Salsa20Reference
import TweetNaCl.Salsa20RefCert

/-! The output certificate compares the linked RV64 slot program with an
independently constructed Salsa20 word program by symbolic dataflow. -/
namespace TweetNaCl.Salsa20Correct
open TinyFive Salsa20Circuit Salsa20Symbolic
open Salsa20Replay.Wrapper (capacity out inp key constant returnPC steps)

def start : Salsa20Symbolic.State :=
  let regs := ([(1, returnPC), (2, BitVec.ofNat 64 capacity), (10, BitVec.ofNat 64 out),
    (11, BitVec.ofNat 64 inp), (12, BitVec.ofNat 64 key), (13, BitVec.ofNat 64 constant)] :
      List (Nat × BitVec 64)).foldl (fun r (i, v) => r.insert i (.literal v)) ({} : Std.TreeMap Nat Value)
  { regs, pc := BitVec.ofNat 64 Salsa20Program.entry }

private def buildEmit (n : Node) : StateM Arena Id := fun a => a.intern n

private def candidate : Arena :=
  ((Salsa20Symbolic.run buildEmit Salsa20Slots.Wrapper.program start).run Arena.empty).2

private def expected (a : Arena) : Vector (Option Value) 64 :=
  Salsa20RefCert.ref a inp key constant

private def matchAt (a : Arena) (s : Salsa20Symbolic.State) (i : Fin 64) : Bool :=
  match s.mem[out + i.val]?, (expected a)[i] with
  | some x, some y => decide (x = y)
  | _, _ => false

/-- Check every output position separately; missing rows cannot compare equal. -/
private def outputsMatch (a : Arena) (s : Salsa20Symbolic.State) : Bool :=
  (List.finRange 64).all (matchAt a s)

private def check : Bool :=
  match Salsa20Symbolic.run candidate.mk Salsa20Slots.Wrapper.program start with
  | some s => outputsMatch candidate s
  | none => false

private theorem checked : check = true := by native_decide

private theorem match_at {a : Arena} {s : Salsa20Symbolic.State} (h : outputsMatch a s = true) (i : Fin 64) :
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

private theorem register_start {m : Machine 64} (h : Salsa20Replay.Related Salsa20Replay.Wrapper.initial m)
    (a : Arena) (r : TinyFive.Reg) :
    (start.regs[r.val]?.map (Value.eval a (leaves m))).getD ((leaves m).savedReg r) = m.x.get r := by
  have ha (q : TinyFive.Reg) (v : BitVec 64)
      (hq : Salsa20Replay.Wrapper.initial.get q = some v) := (h.2.2.1 q v hq).symm
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

/-- The bytes at a contiguous (possibly unaligned) buffer in machine memory. -/
def BytesAt (m : Machine 64) (address : Nat) {n : Nat} (b : Salsa20Spec.Bytes n) : Prop :=
  ∀ i : Fin n, m.mem[address + i.val]? = some b[i]

private theorem bytesAt_region {m : Machine 64} {base n : Nat} {b : Salsa20Spec.Bytes n}
    (h : BytesAt m base b) :
    Salsa20Reference.ByteRegion (fun a => ((leaves m).argByte a).setWidth 64) base b := by
  intro i hi
  have h' : m.mem[base + i]? = some b[i] := h ⟨i, hi⟩
  simp [leaves, h']

private theorem start_related {m : Machine 64} (h : Salsa20Replay.Related Salsa20Replay.Wrapper.initial m)
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
    Salsa20Slots.Wrapper.program.all
      (fun a => decide (Supported Salsa20Slots.Wrapper.layout a)) = true := by native_decide

private theorem checked_output_slots :
    (List.finRange 64).all (fun i => decide
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

/-- Every input/key/constant triple at the fixed ABI layout produces the 64
    specified Salsa20 bytes, in exactly `steps` model instructions. -/
theorem output_correct {m : Machine 64} (h : Salsa20Replay.Related Salsa20Replay.Wrapper.initial m)
    (hc : m.mem.size = capacity)
    (inputBytes : Salsa20Spec.Bytes 16) (keyBytes : Salsa20Spec.Bytes 32)
    (constantBytes : Salsa20Spec.Bytes 16)
    (hi : BytesAt m inp inputBytes) (hk : BytesAt m key keyBytes)
    (ht : BytesAt m constant constantBytes) :
    BytesAt (TinyFive.run steps m) out (Salsa20Spec.core inputBytes keyBytes constantBytes) := by
  obtain ⟨s, hs, hm⟩ := some_check candidate _ checked
  have hsupp (a) (ha : a ∈ Salsa20Slots.Wrapper.program) :
      Supported Salsa20Slots.Wrapper.layout a :=
    of_decide_eq_true (List.all_eq_true.mp checked_supported a ha)
  have hrun := Salsa20Symbolic.run_sound hsupp (start_related h hc candidate) hs
  have hslots := Salsa20Slots.Wrapper.program_sound h hc
  have hspec := (Salsa20Reference.core_concrete_eq_core64 _ inp key constant inputBytes keyBytes
    constantBytes (bytesAt_region hi) (bytesAt_region hk) (bytesAt_region ht)).trans
      (Salsa20WideIO.core64_eq_core ..)
  intro i
  obtain ⟨v, hv, he⟩ := match_at hm i
  have ha : Salsa20Slots.Wrapper.layout.Allows .byte (out + i.val) :=
    of_decide_eq_true (List.all_eq_true.mp checked_output_slots i (List.mem_finRange i))
  have hr := hrun.2.2 .byte _ ha
  simp only [hv, Option.map_some, Option.getD_some] at hr
  have hb := (hslots.2.2.2 .byte _ ha).1
  change readBytes (TinyFive.run steps m).mem (out + i.val) 1 = some _ at hb
  have href := Salsa20RefCert.ref_sound candidate (leaves m) inp key constant i he
  have hbyte := congrArg (fun xs : Salsa20Spec.Bytes 64 => xs[i.val]) hspec
  rw [read_one, ← hr, href] at hb
  simp only [Vector.getElem_map] at hbyte
  exact hb.trans (congrArg some hbyte)

end TweetNaCl.Salsa20Correct
