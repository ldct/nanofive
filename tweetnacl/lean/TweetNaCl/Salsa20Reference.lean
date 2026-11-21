import TweetNaCl.Salsa20WideIO
import TinyFive.Machine

/-! Straight-line, word-oriented Salsa20 program in a small value algebra.
Independent of the instruction trace: loops run over the prescribed Salsa20
state layout, not over machine code. -/
namespace TweetNaCl.Salsa20Reference
open TinyFive

structure Ops (α : Type) where
  literal : BitVec 64 → α
  alu : AluOp → α → α → α
  aluWord : AluOp → α → α → α
  byte : α → α

abbrev Quad (α : Type) := α × α × α × α

def word (o : Ops α) (a b c d : α) : α :=
  let shift x n := o.alu .sll x (o.literal n)
  o.alu .or (shift d 24) (o.alu .or (shift c 16) (o.alu .or (shift b 8) a))

def loadWords (o : Ops α) (b : Nat → α) (base : Nat) (n : Nat) : Vector α n :=
  Vector.ofFn fun i =>
    let p := base + 4 * i.val
    word o (b p) (b (p+1)) (b (p+2)) (b (p+3))

def arrange (inp : Vector α 4) (key : Vector α 8) (constant : Vector α 4) : Vector α 16 :=
  #v[constant[0], key[0], key[1], key[2],
     key[3], constant[1], inp[0], inp[1],
     inp[2], inp[3], constant[2], key[4],
     key[5], key[6], key[7], constant[3]]

def quarter (o : Ops α) (a b c d : α) : Quad α :=
  let xor := o.alu .xor
  let add := o.alu .add
  let or := o.alu .or
  let left x n := o.alu .sll x (o.literal n)
  let rightWord x n := o.aluWord .srl x (o.literal n)
  let rightMask x n mask := o.alu .and (o.alu .srl x (o.literal n)) (o.literal mask)
  let s := add a d
  let b' := xor (or (rightWord s 25) (left s 7)) b
  let s := add a b'
  let c' := xor (or (rightWord s 23) (left s 9)) c
  let s := add b' c'
  let d' := xor (or (rightMask s 19 0x1fff) (left s 13)) d
  let s := add c' d'
  let a' := xor (or (rightMask s 14 0x3ffff) (left s 18)) a
  (a', b', c', d')

def round (o : Ops α) (s : Vector α 16) : Vector α 16 :=
  let q0 := quarter o s[0] s[4] s[8] s[12]
  let q1 := quarter o s[5] s[9] s[13] s[1]
  let q2 := quarter o s[10] s[14] s[2] s[6]
  let q3 := quarter o s[15] s[3] s[7] s[11]
  #v[q0.1, q0.2.1, q0.2.2.1, q0.2.2.2,
     q1.2.2.2, q1.1, q1.2.1, q1.2.2.1,
     q2.2.2.1, q2.2.2.2, q2.1, q2.2.1,
     q3.2.1, q3.2.2.1, q3.2.2.2, q3.1]

def rounds (o : Ops α) (n : Nat) (s : Vector α 16) : Vector α 16 :=
  match n with
  | 0 => s
  | n + 1 => round o (rounds o n s)

def split (o : Ops α) (w : α) : Vector α 4 :=
  let shift (x : α) := o.alu .srl x (o.literal 8)
  let w1 := shift w
  let w2 := shift w1
  let w3 := shift w2
  #v[o.byte w, o.byte w1, o.byte w2, o.byte w3]

def core (o : Ops α) (b : Nat → α) (inp key constant : Nat) : Vector α 64 :=
  let s := arrange (loadWords o b inp 4) (loadWords o b key 8) (loadWords o b constant 4)
  ((rounds o 20 s).zipWith (o.alu .add) s |>.map (split o)).flatten

/-- A value interpretation that preserves each operation of the reference. -/
structure Hom (o : Ops α) (p : Ops β) where
  toFun : α → β
  literal : ∀ n, toFun (o.literal n) = p.literal n
  alu : ∀ op x y, toFun (o.alu op x y) = p.alu op (toFun x) (toFun y)
  aluWord : ∀ op x y, toFun (o.aluWord op x y) = p.aluWord op (toFun x) (toFun y)
  byte : ∀ x, toFun (o.byte x) = p.byte (toFun x)

section Hom
variable {o : Ops α} {p : Ops β} (h : Hom o p)

theorem map_word (a b c d : α) :
    h.toFun (word o a b c d) = word p (h.toFun a) (h.toFun b) (h.toFun c) (h.toFun d) := by
  simp only [word, h.alu, h.literal]

theorem map_loadWords {b : Nat → α} {b' : Nat → β} (hb : ∀ i, h.toFun (b i) = b' i)
    (base n : Nat) :
    (loadWords o b base n).map h.toFun = loadWords p b' base n := by
  apply Vector.ext
  intro i hi
  simp only [loadWords, Vector.getElem_map, Vector.getElem_ofFn, map_word h, hb]

theorem map_arrange (f : α → β) (inp : Vector α 4) (key : Vector α 8)
    (constant : Vector α 4) :
    (arrange inp key constant).map f = arrange (inp.map f) (key.map f) (constant.map f) := by
  simp only [arrange, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
    Vector.getElem_map]

def mapQuad (f : α → β) (q : Quad α) : Quad β :=
  (f q.1, f q.2.1, f q.2.2.1, f q.2.2.2)

theorem map_quarter (a b c d : α) :
    mapQuad h.toFun (quarter o a b c d) =
      quarter p (h.toFun a) (h.toFun b) (h.toFun c) (h.toFun d) := by
  simp only [mapQuad, quarter, h.alu, h.aluWord, h.literal]

theorem map_round (s : Vector α 16) :
    (round o s).map h.toFun = round p (s.map h.toFun) := by
  simp only [round, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
    Vector.getElem_map, ← map_quarter h, mapQuad]

theorem map_rounds (n : Nat) (s : Vector α 16) :
    (rounds o n s).map h.toFun = rounds p n (s.map h.toFun) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rounds, map_round h, ih]

theorem map_split (w : α) :
    (split o w).map h.toFun = split p (h.toFun w) := by
  simp only [split, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
    h.alu, h.byte, h.literal]

private theorem map_add (s t : Vector α 16) :
    (s.zipWith (o.alu .add) t).map h.toFun =
      (s.map h.toFun).zipWith (p.alu .add) (t.map h.toFun) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_zipWith, h.alu]

private theorem map_encode (s : Vector α 16) :
    (s.map (split o)).flatten.map h.toFun = ((s.map h.toFun).map (split p)).flatten := by
  rw [Vector.map_flatten]
  apply congrArg (fun blocks : Vector (Vector β 4) 16 => blocks.flatten)
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, map_split h]

/-- Interpreting the output of the reference is equivalent to interpreting
its operations and each value read from its input function. -/
theorem map_core {b : Nat → α} {b' : Nat → β} (hb : ∀ i, h.toFun (b i) = b' i)
    (inp key constant : Nat) :
    (core o b inp key constant).map h.toFun = core p b' inp key constant := by
  change Vector.map (n := 16 * 4) h.toFun _ = _
  simp only [core, map_encode h, map_add h, map_rounds h, map_arrange, map_loadWords h hb]

end Hom

open Salsa20Spec (Bytes)

/-- Interpret reference values as XLEN-wide words, using the same ALU as
TinyFive. A byte value is the zero extension of the low eight bits. -/
def concreteOps : Ops (BitVec 64) where
  literal := id
  alu := TinyFive.alu
  aluWord op a b := (TinyFive.alu op (a.setWidth 32) (b.setWidth 32)).signExtend 64
  byte a := (a.setWidth 8).setWidth 64

/-- The input function reads the given bytes from the region starting at `base`. -/
def ByteRegion {n : Nat} (b : Nat → BitVec 64) (base : Nat) (bytes : Bytes n) : Prop :=
  ∀ i (hi : i < n), b (base + i) = bytes[i].setWidth 64

theorem word_concrete_eq_loadLE64 (a b c d : BitVec 8) :
    word concreteOps (a.setWidth 64) (b.setWidth 64) (c.setWidth 64) (d.setWidth 64) =
      Salsa20LowWords.loadLE64 a b c d := by
  rfl

theorem loadWords_concrete_eq_loadWords64 {n : Nat} {b : Nat → BitVec 64} {base : Nat}
    {bytes : Bytes (n * 4)} (h : ByteRegion b base bytes) :
    loadWords concreteOps b base n = Salsa20WideIO.loadWords64 bytes := by
  apply Vector.ext
  intro i hi
  rw [loadWords, Vector.getElem_ofFn, Salsa20WideIO.getElem_loadWords64]
  have h0 := h (4 * i) (by omega)
  have h1 := h (4 * i + 1) (by omega)
  have h2 := h (4 * i + 2) (by omega)
  have h3 := h (4 * i + 3) (by omega)
  simp only [Nat.add_assoc, h0, h1, h2, h3, word_concrete_eq_loadLE64]

theorem quarter_concrete_eq_quarterRound64 (a b c d : BitVec 64) :
    quarter concreteOps a b c d = Salsa20LowWords.quarterRound64 a b c d := by
  rfl

theorem round_concrete_eq_loopRound (s : Salsa20Schedule.WideState) :
    round concreteOps s = Salsa20Schedule.loopRound s := by
  simp only [round, Salsa20Schedule.loopRound, quarter_concrete_eq_quarterRound64]

theorem rounds_concrete_eq_loopRounds (n : Nat) (s : Salsa20Schedule.WideState) :
    rounds concreteOps n s = Salsa20Schedule.loopRounds n s := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rounds, Salsa20Schedule.loopRounds, ih, round_concrete_eq_loopRound]

theorem split_concrete_eq_storeLE64 (w : BitVec 64) :
    (split concreteOps w).map (·.setWidth 8) = Salsa20WideIO.storeLE64 w := by
  have trunc (v : BitVec 64) : (concreteOps.byte v).setWidth 8 = v.setWidth 8 := by
    rw [concreteOps, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  have shift (v : BitVec 64) : concreteOps.alu .srl v (concreteOps.literal 8) = v >>> 8 := rfl
  apply Vector.ext
  intro i hi
  have hs : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl <;>
    simp only [split, Vector.getElem_map, Salsa20WideIO.storeLE64, Vector.getElem_ofFn, shift]
  · change (concreteOps.byte w).setWidth 8 = (w >>> 0).setWidth 8
    rw [trunc, BitVec.ushiftRight_zero]
  · change (concreteOps.byte (w >>> 8)).setWidth 8 = (w >>> 8).setWidth 8
    rw [trunc]
  · change (concreteOps.byte (w >>> 8 >>> 8)).setWidth 8 = (w >>> 16).setWidth 8
    rw [trunc, ← BitVec.shiftRight_add]
  · change (concreteOps.byte (w >>> 8 >>> 8 >>> 8)).setWidth 8 = (w >>> 24).setWidth 8
    rw [trunc, ← BitVec.shiftRight_add, ← BitVec.shiftRight_add]

private theorem encode_concrete_eq_encode64 (s : Salsa20Schedule.WideState) :
    ((s.map (split concreteOps)).flatten).map (·.setWidth 8) = Salsa20WideIO.encode64 s := by
  rw [Vector.map_flatten, Salsa20WideIO.encode64]
  apply congrArg (fun blocks : Vector (Bytes 4) 16 => blocks.flatten)
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, split_concrete_eq_storeLE64]

/-- Concrete evaluation of the reference, restricted to the stored bytes,
agrees with the wide-word model on any three matching input regions. -/
theorem core_concrete_eq_core64 (b : Nat → BitVec 64) (inp key constant : Nat)
    (inputBytes : Bytes 16) (keyBytes : Bytes 32) (constantBytes : Bytes 16)
    (hi : ByteRegion b inp inputBytes) (hk : ByteRegion b key keyBytes)
    (hc : ByteRegion b constant constantBytes) :
    (core concreteOps b inp key constant).map (·.setWidth 8) =
      Salsa20WideIO.core64 inputBytes keyBytes constantBytes := by
  have hs : arrange (loadWords concreteOps b inp 4) (loadWords concreteOps b key 8)
      (loadWords concreteOps b constant 4) =
      Salsa20WideIO.initialState64 inputBytes keyBytes constantBytes := by
    rw [loadWords_concrete_eq_loadWords64 (n := 4) hi,
      loadWords_concrete_eq_loadWords64 (n := 8) hk,
      loadWords_concrete_eq_loadWords64 (n := 4) hc]
    rfl
  have add : concreteOps.alu .add = ((· + ·) : BitVec 64 → BitVec 64 → BitVec 64) := rfl
  change Vector.map (n := 16 * 4) (BitVec.setWidth 8 : BitVec 64 → BitVec 8) _ = _
  simp only [core, Salsa20WideIO.core64, hs, rounds_concrete_eq_loopRounds, add,
    encode_concrete_eq_encode64]

end TweetNaCl.Salsa20Reference
