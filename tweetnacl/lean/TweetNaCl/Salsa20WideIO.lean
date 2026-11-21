import TweetNaCl.Salsa20LowWords
import TweetNaCl.Salsa20Schedule

/-!
# Salsa20 byte I/O for the wide-word model

This connects the RV64-shaped loads, rounds, feed-forward, and byte stores
to the independent core specification. It does not model memory accesses,
instruction execution, or the routine's return value.
-/

namespace TweetNaCl.Salsa20WideIO
open Salsa20Spec (Bytes)
open Salsa20LowWords (low32 loadLE64 low32_loadLE64 storeByte64_eq_storeLE)
open Salsa20Schedule (WideState lowWords loopRounds lowWords_feedForward)

/-- Apply the four-byte load pattern at each aligned byte offset. -/
def loadWords64 {n : Nat} (b : Bytes (n * 4)) : Vector (BitVec 64) n :=
  Vector.ofFn fun i =>
    have hi := i.isLt
    loadLE64 (b[4 * i.val]'(by omega)) (b[4 * i.val + 1]'(by omega))
      (b[4 * i.val + 2]'(by omega)) (b[4 * i.val + 3]'(by omega))

theorem getElem_loadWords64 {n : Nat} (b : Bytes (n * 4)) (i : Nat) (hi : i < n) :
    (loadWords64 b)[i] =
      loadLE64 (b[4 * i]'(by omega)) (b[4 * i + 1]'(by omega))
        (b[4 * i + 2]'(by omega)) (b[4 * i + 3]'(by omega)) := by
  rw [loadWords64, Vector.getElem_ofFn]

theorem low32_loadWords64_at {n : Nat} (b : Bytes (n * 4)) (i : Nat) (hi : i < n) :
    low32 ((loadWords64 b)[i]) = (Salsa20Spec.decodeWords b)[i] := by
  simp only [getElem_loadWords64, Salsa20Spec.decodeWords, Vector.getElem_ofFn, low32_loadLE64]
  rfl

/-- The initial 16 wide words as laid out by the implementation's loads. -/
def initialState64 (input : Bytes 16) (key : Bytes 32) (constant : Bytes 16) : WideState :=
  let n := loadWords64 (n := 4) input
  let k := loadWords64 (n := 8) key
  let c := loadWords64 (n := 4) constant
  #v[c[0], k[0], k[1], k[2],
     k[3], c[1], n[0], n[1],
     n[2], n[3], c[2], k[4],
     k[5], k[6], k[7], c[3]]

theorem lowWords_initialState64 (input : Bytes 16) (key : Bytes 32) (constant : Bytes 16) :
    lowWords (initialState64 input key constant) = Salsa20Spec.initialState input key constant := by
  simp only [lowWords, initialState64, Salsa20Spec.initialState, Vector.map_mk,
    List.map_toArray, List.map_cons, List.map_nil, low32_loadWords64_at]

/-- The four bytes exposed by the logical right shifts and byte stores. -/
def storeLE64 (x : BitVec 64) : Bytes 4 :=
  Vector.ofFn fun i => (x >>> (8 * i.val)).setWidth 8

theorem storeLE64_eq_storeLE (x : BitVec 64) :
    storeLE64 x = Salsa20Spec.storeLE (low32 x) := by
  apply Vector.ext
  intro i hi
  rw [storeLE64, Vector.getElem_ofFn]
  exact storeByte64_eq_storeLE x ⟨i, hi⟩

/-- Write four bytes per wide word in state order. -/
def encode64 (s : WideState) : Bytes 64 :=
  (s.map storeLE64).flatten

theorem getElem_encode64 (s : WideState) (i : Nat) (hi : i < 64) :
    (encode64 s)[i] = (s[i / 4]'(by omega) >>> (8 * (i % 4))).setWidth 8 := by
  change (s.map storeLE64).flatten[i]'(show i < 16 * 4 from hi) = _
  simp only [Vector.getElem_flatten, Vector.getElem_map, storeLE64,
    Vector.getElem_ofFn]

theorem encode64_eq_encode (s : WideState) :
    encode64 s = Salsa20Spec.encode (lowWords s) := by
  unfold encode64 Salsa20Spec.encode
  apply congrArg (fun blocks : Vector (Bytes 4) 16 => blocks.flatten)
  apply Vector.ext
  intro i hi
  simp only [lowWords, Vector.getElem_map, storeLE64_eq_storeLE]

/-- The Salsa20 path through the implementation, as a pure function on bytes. -/
def core64 (input : Bytes 16) (key : Bytes 32) (constant : Bytes 16) : Bytes 64 :=
  let s := initialState64 input key constant
  encode64 ((loopRounds 20 s).zipWith (· + ·) s)

theorem core64_eq_core (input : Bytes 16) (key : Bytes 32) (constant : Bytes 16) :
    core64 input key constant = Salsa20Spec.core input key constant := by
  unfold core64 Salsa20Spec.core
  rw [encode64_eq_encode, lowWords_feedForward, lowWords_initialState64]

end TweetNaCl.Salsa20WideIO
