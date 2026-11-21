import Init.Data.Vector
import Init.Data.BitVec
import Init.Omega

/-!
# Salsa20/20 core

The core follows D. J. Bernstein, [*Salsa20 specification*](https://cr.yp.to/snuffle/spec.pdf),
§§2–9.
The state is a row-major 4×4 matrix of 32-bit words; all word additions
are modulo 2^32. This model does not refer to machine code or memory.
-/

namespace TweetNaCl.Salsa20Spec

abbrev Word := BitVec 32
abbrev State := Vector Word 16
abbrev Bytes (n : Nat) := Vector (BitVec 8) n

/-- Mix four words, returning the results in the same order as the inputs. -/
def quarterRound (a b c d : Word) : Word × Word × Word × Word :=
  let b' := b ^^^ (a + d).rotateLeft 7
  let c' := c ^^^ (b' + a).rotateLeft 9
  let d' := d ^^^ (c' + b').rotateLeft 13
  let a' := a ^^^ (d' + c').rotateLeft 18
  (a', b', c', d')

/-- Mix each column, starting at its diagonal entry and wrapping downwards. -/
def columnRound (s : State) : State :=
  let (y0,  y4,  y8,  y12) := quarterRound s[0]  s[4]  s[8]  s[12]
  let (y5,  y9,  y13, y1)  := quarterRound s[5]  s[9]  s[13] s[1]
  let (y10, y14, y2,  y6)  := quarterRound s[10] s[14] s[2]  s[6]
  let (y15, y3,  y7,  y11) := quarterRound s[15] s[3]  s[7]  s[11]
  #v[y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15]

/-- Mix each row, starting at its diagonal entry and wrapping rightwards. -/
def rowRound (s : State) : State :=
  let (y0,  y1,  y2,  y3)  := quarterRound s[0]  s[1]  s[2]  s[3]
  let (y5,  y6,  y7,  y4)  := quarterRound s[5]  s[6]  s[7]  s[4]
  let (y10, y11, y8,  y9)  := quarterRound s[10] s[11] s[8]  s[9]
  let (y15, y12, y13, y14) := quarterRound s[15] s[12] s[13] s[14]
  #v[y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15]

def doubleRound (s : State) : State :=
  rowRound (columnRound s)

/-- Apply `n` double rounds (rather than `n` individual rounds). -/
def rounds (n : Nat) (s : State) : State :=
  match n with
  | 0 => s
  | n + 1 => doubleRound (rounds n s)

/-- The twenty-round permutation before feed-forward. -/
def permute (s : State) : State :=
  rounds 10 s

def feedForward (initial mixed : State) : State :=
  initial.zipWith (· + ·) mixed

def coreWords (s : State) : State :=
  feedForward s (permute s)

/-- Interpret four bytes, least significant first, as one word. -/
def loadLE (b : Bytes 4) : Word :=
  b[3] ++ b[2] ++ b[1] ++ b[0]

/-- Split a word into bytes, least significant first. -/
def storeLE (w : Word) : Bytes 4 :=
  #v[w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- Decode consecutive groups of four bytes as little-endian words. -/
def decodeWords {n : Nat} (b : Bytes (n * 4)) : Vector Word n :=
  Vector.ofFn fun i =>
    have hi := i.isLt
    loadLE #v[b[4 * i.val]'(by omega), b[4 * i.val + 1]'(by omega),
      b[4 * i.val + 2]'(by omega), b[4 * i.val + 3]'(by omega)]

def decode (b : Bytes 64) : State :=
  decodeWords (n := 16) b

def encode (s : State) : Bytes 64 :=
  (s.map storeLE).flatten

/-- Salsa20 core on a single 64-byte block. -/
def coreBytes (b : Bytes 64) : Bytes 64 :=
  encode (coreWords (decode b))

/-- Place constant words on the diagonal, key words on either side of the
    four input words in the flattened state. -/
def initialState (input : Bytes 16) (key : Bytes 32) (constant : Bytes 16) : State :=
  let n := decodeWords (n := 4) input
  let k := decodeWords (n := 8) key
  let c := decodeWords (n := 4) constant
  #v[c[0], k[0], k[1], k[2],
     k[3], c[1], n[0], n[1],
     n[2], n[3], c[2], k[4],
     k[5], k[6], k[7], c[3]]

/-- The 64 output bytes of `crypto_core_salsa20`, with caller-supplied constants. -/
def core (input : Bytes 16) (key : Bytes 32) (constant : Bytes 16) : Bytes 64 :=
  encode (coreWords (initialState input key constant))

/-- The 32-byte-key expansion example in Bernstein's specification, §9. -/
theorem core_knownAnswer :
    core #v[101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]
      #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
         201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]
      #v[101, 120, 112, 97, 110, 100, 32, 51, 50, 45, 98, 121, 116, 101, 32, 107] =
      #v[69, 37, 68, 39, 41, 15, 107, 193, 255, 139, 122, 6, 170, 233, 217, 98,
         89, 144, 182, 106, 21, 51, 200, 65, 239, 49, 222, 34, 215, 114, 40, 126,
         104, 197, 7, 225, 197, 153, 31, 2, 102, 78, 76, 176, 84, 245, 246, 184,
         177, 160, 133, 130, 6, 72, 149, 119, 192, 195, 132, 236, 234, 103, 246, 74] := by
  decide +kernel

end TweetNaCl.Salsa20Spec
