import TweetNaCl.ForHumans.Salsa20Spec

/-!
# The Salsa20 core over an abstract word algebra

`core` repeats the definitions of `TweetNaCl.Salsa20Spec` over operations `Ops`. With the
concrete operations it is `Salsa20Spec.core` (`core_concrete`). Run over wires, it gives the
normal form of each output byte. `core_rel` transfers any relation between two algebras that
the operations preserve, from the input bytes to the output bytes.
-/
namespace NaClSalsa20.Reference
open TweetNaCl

structure Ops (α β : Type) where
  add : α → α → α
  xor : α → α → α
  rotl : α → Nat → α
  /-- Four bytes, least significant first. -/
  pack : β → β → β → β → α
  /-- Byte `k` of a word. -/
  byte : α → Fin 4 → β

variable {α β : Type} (o : Ops α β)

def quarterRound (a b c d : α) : α × α × α × α :=
  let b' := o.xor b (o.rotl (o.add a d) 7)
  let c' := o.xor c (o.rotl (o.add b' a) 9)
  let d' := o.xor d (o.rotl (o.add c' b') 13)
  let a' := o.xor a (o.rotl (o.add d' c') 18)
  (a', b', c', d')

def columnRound (s : Vector α 16) : Vector α 16 :=
  let (y0,  y4,  y8,  y12) := quarterRound o s[0]  s[4]  s[8]  s[12]
  let (y5,  y9,  y13, y1)  := quarterRound o s[5]  s[9]  s[13] s[1]
  let (y10, y14, y2,  y6)  := quarterRound o s[10] s[14] s[2]  s[6]
  let (y15, y3,  y7,  y11) := quarterRound o s[15] s[3]  s[7]  s[11]
  #v[y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15]

def rowRound (s : Vector α 16) : Vector α 16 :=
  let (y0,  y1,  y2,  y3)  := quarterRound o s[0]  s[1]  s[2]  s[3]
  let (y5,  y6,  y7,  y4)  := quarterRound o s[5]  s[6]  s[7]  s[4]
  let (y10, y11, y8,  y9)  := quarterRound o s[10] s[11] s[8]  s[9]
  let (y15, y12, y13, y14) := quarterRound o s[15] s[12] s[13] s[14]
  #v[y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15]

def rounds : Nat → Vector α 16 → Vector α 16
  | 0, s => s
  | n + 1, s => rowRound o (columnRound o (rounds n s))

def decodeWords {n : Nat} (b : Vector β (n * 4)) : Vector α n :=
  Vector.ofFn fun i =>
    have hi := i.isLt
    o.pack (b[4 * i.val]'(by omega)) (b[4 * i.val + 1]'(by omega))
      (b[4 * i.val + 2]'(by omega)) (b[4 * i.val + 3]'(by omega))

def initialState (input : Vector β 16) (key : Vector β 32) (constant : Vector β 16) :
    Vector α 16 :=
  let n := decodeWords o (n := 4) input
  let k := decodeWords o (n := 8) key
  let c := decodeWords o (n := 4) constant
  #v[c[0], k[0], k[1], k[2],
     k[3], c[1], n[0], n[1],
     n[2], n[3], c[2], k[4],
     k[5], k[6], k[7], c[3]]

def encode (s : Vector α 16) : Vector β 64 :=
  (s.map fun w => #v[o.byte w 0, o.byte w 1, o.byte w 2, o.byte w 3]).flatten

def core (input : Vector β 16) (key : Vector β 32) (constant : Vector β 16) : Vector β 64 :=
  let s := initialState o input key constant
  encode o (s.zipWith o.add (rounds o 10 s))

/-- The operations of `Salsa20Spec`. -/
def concrete : Ops (BitVec 32) (BitVec 8) where
  add := (· + ·)
  xor := (· ^^^ ·)
  rotl := BitVec.rotateLeft
  pack b0 b1 b2 b3 := Salsa20Spec.loadLE #v[b0, b1, b2, b3]
  byte w k := w.extractLsb' (8 * k.val) 8

theorem rounds_concrete (n : Nat) (s : Salsa20Spec.State) :
    rounds concrete n s = Salsa20Spec.rounds n s := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rounds, Salsa20Spec.rounds, ih]; rfl

theorem core_concrete (input : Salsa20Spec.Bytes 16) (key : Salsa20Spec.Bytes 32)
    (constant : Salsa20Spec.Bytes 16) :
    core concrete input key constant = Salsa20Spec.core input key constant := by
  simp only [core, Salsa20Spec.core, Salsa20Spec.coreWords, Salsa20Spec.feedForward,
    Salsa20Spec.permute, rounds_concrete]
  rfl

/-- A relation between two algebras, preserved by their operations. -/
structure Rel (o : Ops α β) (p : Ops α' β') where
  word : α → α' → Prop
  byte : β → β' → Prop
  add : word a a' → word b b' → word (o.add a b) (p.add a' b')
  xor : word a a' → word b b' → word (o.xor a b) (p.xor a' b')
  rotl : word a a' → word (o.rotl a k) (p.rotl a' k)
  pack : byte b0 b0' → byte b1 b1' → byte b2 b2' → byte b3 b3' →
    word (o.pack b0 b1 b2 b3) (p.pack b0' b1' b2' b3')
  toByte : word a a' → byte (o.byte a k) (p.byte a' k)

section Rel
variable {α' β' : Type} {o : Ops α β} {p : Ops α' β'} (R : Rel o p)

def Pointwise {γ γ' : Type} (r : γ → γ' → Prop) {n : Nat} (v : Vector γ n) (v' : Vector γ' n) :
    Prop :=
  ∀ i (hi : i < n), r v[i] v'[i]

theorem quarterRound_rel {a b c d : α} {a' b' c' d' : α'} (ha : R.word a a') (hb : R.word b b')
    (hc : R.word c c') (hd : R.word d d') :
    R.word (quarterRound o a b c d).1 (quarterRound p a' b' c' d').1 ∧
    R.word (quarterRound o a b c d).2.1 (quarterRound p a' b' c' d').2.1 ∧
    R.word (quarterRound o a b c d).2.2.1 (quarterRound p a' b' c' d').2.2.1 ∧
    R.word (quarterRound o a b c d).2.2.2 (quarterRound p a' b' c' d').2.2.2 := by
  have hb' := R.xor hb (R.rotl (k := 7) (R.add ha hd))
  have hc' := R.xor hc (R.rotl (k := 9) (R.add hb' ha))
  have hd' := R.xor hd (R.rotl (k := 13) (R.add hc' hb'))
  have ha' := R.xor ha (R.rotl (k := 18) (R.add hd' hc'))
  exact ⟨ha', hb', hc', hd'⟩

private theorem vec16 {s : Vector α 16} {s' : Vector α' 16}
    (h : ∀ i : Fin 16, R.word s[i.val] s'[i.val]) : Pointwise R.word s s' :=
  fun i hi => h ⟨i, hi⟩

omit R in
private theorem pw16 {γ γ' : Type} {r : γ → γ' → Prop} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : γ} {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : γ'}
    (h0 : r a0 b0)
    (h1 : r a1 b1)
    (h2 : r a2 b2)
    (h3 : r a3 b3)
    (h4 : r a4 b4)
    (h5 : r a5 b5)
    (h6 : r a6 b6)
    (h7 : r a7 b7)
    (h8 : r a8 b8)
    (h9 : r a9 b9)
    (h10 : r a10 b10)
    (h11 : r a11 b11)
    (h12 : r a12 b12)
    (h13 : r a13 b13)
    (h14 : r a14 b14)
    (h15 : r a15 b15) :
    Pointwise r #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] #v[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  intro i hi
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7
  | 8, _ => exact h8
  | 9, _ => exact h9
  | 10, _ => exact h10
  | 11, _ => exact h11
  | 12, _ => exact h12
  | 13, _ => exact h13
  | 14, _ => exact h14
  | 15, _ => exact h15
  | _ + 16, h => exact absurd h (by omega)

theorem columnRound_rel {s : Vector α 16} {s' : Vector α' 16} (h : Pointwise R.word s s') :
    Pointwise R.word (columnRound o s) (columnRound p s') := by
  obtain ⟨a0, a4, a8, a12⟩ := quarterRound_rel R (h 0 (by omega)) (h 4 (by omega))
    (h 8 (by omega)) (h 12 (by omega))
  obtain ⟨a5, a9, a13, a1⟩ := quarterRound_rel R (h 5 (by omega)) (h 9 (by omega))
    (h 13 (by omega)) (h 1 (by omega))
  obtain ⟨a10, a14, a2, a6⟩ := quarterRound_rel R (h 10 (by omega)) (h 14 (by omega))
    (h 2 (by omega)) (h 6 (by omega))
  obtain ⟨a15, a3, a7, a11⟩ := quarterRound_rel R (h 15 (by omega)) (h 3 (by omega))
    (h 7 (by omega)) (h 11 (by omega))
  exact pw16 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15

theorem rowRound_rel {s : Vector α 16} {s' : Vector α' 16} (h : Pointwise R.word s s') :
    Pointwise R.word (rowRound o s) (rowRound p s') := by
  obtain ⟨a0, a1, a2, a3⟩ := quarterRound_rel R (h 0 (by omega)) (h 1 (by omega))
    (h 2 (by omega)) (h 3 (by omega))
  obtain ⟨a5, a6, a7, a4⟩ := quarterRound_rel R (h 5 (by omega)) (h 6 (by omega))
    (h 7 (by omega)) (h 4 (by omega))
  obtain ⟨a10, a11, a8, a9⟩ := quarterRound_rel R (h 10 (by omega)) (h 11 (by omega))
    (h 8 (by omega)) (h 9 (by omega))
  obtain ⟨a15, a12, a13, a14⟩ := quarterRound_rel R (h 15 (by omega)) (h 12 (by omega))
    (h 13 (by omega)) (h 14 (by omega))
  exact pw16 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15

theorem rounds_rel (n : Nat) {s : Vector α 16} {s' : Vector α' 16} (h : Pointwise R.word s s') :
    Pointwise R.word (rounds o n s) (rounds p n s') := by
  induction n with
  | zero => exact h
  | succ n ih => exact rowRound_rel R (columnRound_rel R ih)

theorem decodeWords_rel {n : Nat} {b : Vector β (n * 4)} {b' : Vector β' (n * 4)}
    (h : Pointwise R.byte b b') : Pointwise R.word (decodeWords o b) (decodeWords p b') := by
  intro i hi
  simp only [decodeWords, Vector.getElem_ofFn]
  exact R.pack (h _ (by omega)) (h _ (by omega)) (h _ (by omega)) (h _ (by omega))

theorem core_rel {input : Vector β 16} {key : Vector β 32} {constant : Vector β 16}
    {input' : Vector β' 16} {key' : Vector β' 32} {constant' : Vector β' 16}
    (hi : Pointwise R.byte input input') (hk : Pointwise R.byte key key')
    (hc : Pointwise R.byte constant constant') :
    Pointwise R.byte (core o input key constant) (core p input' key' constant') := by
  have n := decodeWords_rel R (n := 4) hi
  have k := decodeWords_rel R (n := 8) hk
  have c := decodeWords_rel R (n := 4) hc
  have hs : Pointwise R.word (initialState o input key constant)
      (initialState p input' key' constant') := by
    exact pw16 (c 0 (by omega)) (k 0 (by omega)) (k 1 (by omega)) (k 2 (by omega))
      (k 3 (by omega)) (c 1 (by omega)) (n 0 (by omega)) (n 1 (by omega))
      (n 2 (by omega)) (n 3 (by omega)) (c 2 (by omega)) (k 4 (by omega))
      (k 5 (by omega)) (k 6 (by omega)) (k 7 (by omega)) (c 3 (by omega))
  have hf : Pointwise R.word ((initialState o input key constant).zipWith o.add
      (rounds o 10 (initialState o input key constant)))
      ((initialState p input' key' constant').zipWith p.add
      (rounds p 10 (initialState p input' key' constant'))) := by
    intro i hi
    simp only [Vector.getElem_zipWith]
    exact R.add (hs i hi) (rounds_rel R 10 hs i hi)
  intro i hi
  have hi' : i < 16 * 4 := hi
  simp only [core, encode, Vector.getElem_flatten hi', Vector.getElem_map]
  have hw := hf (i / 4) (by omega)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h <;>
    simp only [h, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] <;>
    exact R.toByte hw

end Rel
end NaClSalsa20.Reference
