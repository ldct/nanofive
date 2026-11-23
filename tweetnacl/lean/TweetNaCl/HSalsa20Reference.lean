import TweetNaCl.Salsa20Reference
import TweetNaCl.ForHumans.HSalsa20Spec

/-!
# The HSalsa20 path of `core` as a word program

`hcore` extends `Salsa20Reference.core` to the `h = 1` branch of TweetNaCl's `core`: after the
rounds it still adds the initial state, then subtracts the constant and input words again,
each reloaded with the same four-byte pattern, and stores eight words. Over `concreteOps` the
added and subtracted words cancel exactly, so the bytes are `HSalsa20Spec.hsalsa20`
(`hcore_concrete_eq_hsalsa20`).
-/
namespace TweetNaCl.HSalsa20Reference
open TinyFive Salsa20Reference

variable {α β : Type}

/-- The eight words the `h = 1` branch stores, from the feed-forward `z` and the reloaded
constant `c` and input `n` words. -/
def outputs (o : Ops α) (z : Vector α 16) (n c : Vector α 4) : Vector α 8 :=
  let sub := o.alu .sub
  #v[sub z[0] c[0], sub z[5] c[1], sub z[10] c[2], sub z[15] c[3],
     sub z[6] n[0], sub z[7] n[1], sub z[8] n[2], sub z[9] n[3]]

def hcore (o : Ops α) (b : Nat → α) (inp key constant : Nat) : Vector α 32 :=
  let n := loadWords o b inp 4
  let c := loadWords o b constant 4
  let s := arrange n (loadWords o b key 8) c
  let z := (rounds o 20 s).zipWith (o.alu .add) s
  ((outputs o z n c).map (split o)).flatten

section Hom
variable {o : Ops α} {p : Ops β} (h : Hom o p)

private theorem map_add (s t : Vector α 16) :
    (s.zipWith (o.alu .add) t).map h.toFun =
      (s.map h.toFun).zipWith (p.alu .add) (t.map h.toFun) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_zipWith, h.alu]

private theorem map_outputs (z : Vector α 16) (n c : Vector α 4) :
    (outputs o z n c).map h.toFun = outputs p (z.map h.toFun) (n.map h.toFun) (c.map h.toFun) := by
  simp only [outputs, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
    Vector.getElem_map, h.alu]

private theorem map_encode (s : Vector α 8) :
    (s.map (split o)).flatten.map h.toFun = ((s.map h.toFun).map (split p)).flatten := by
  rw [Vector.map_flatten]
  apply congrArg (fun blocks : Vector (Vector β 4) 8 => blocks.flatten)
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, map_split h]

/-- Interpreting the output of `hcore` is interpreting its operations and inputs. -/
theorem map_hcore {b : Nat → α} {b' : Nat → β} (hb : ∀ i, h.toFun (b i) = b' i)
    (inp key constant : Nat) :
    (hcore o b inp key constant).map h.toFun = hcore p b' inp key constant := by
  change Vector.map (n := 8 * 4) h.toFun _ = _
  simp only [hcore, map_encode h, map_outputs h, map_add h, map_rounds h, map_arrange,
    map_loadWords h hb]

end Hom

open Salsa20Spec (Bytes)
open Salsa20LowWords (low32)
open Salsa20Schedule (lowWords loopRounds)

private theorem lowWord_rounds (s : Salsa20Schedule.WideState) (i : Nat) (hi : i < 16) :
    low32 (loopRounds 20 s)[i] = (Salsa20Spec.permute (lowWords s))[i] := by
  have h := congrArg (fun v : Salsa20Spec.State => v[i]) (Salsa20Schedule.lowWords_loopRounds s 10)
  simpa [lowWords, Salsa20Spec.permute] using h

/-- Concrete evaluation of `hcore`, restricted to the stored bytes, is HSalsa20 of any three
matching input regions. -/
theorem hcore_concrete_eq_hsalsa20 (b : Nat → BitVec 64) (inp key constant : Nat)
    (inputBytes : Bytes 16) (keyBytes : Bytes 32) (constantBytes : Bytes 16)
    (hi : ByteRegion b inp inputBytes) (hk : ByteRegion b key keyBytes)
    (hc : ByteRegion b constant constantBytes) :
    (hcore concreteOps b inp key constant).map (·.setWidth 8) =
      HSalsa20Spec.hsalsa20 inputBytes keyBytes constantBytes := by
  let s := Salsa20WideIO.initialState64 inputBytes keyBytes constantBytes
  have hn := loadWords_concrete_eq_loadWords64 (n := 4) hi
  have hkey := loadWords_concrete_eq_loadWords64 (n := 8) hk
  have hcon := loadWords_concrete_eq_loadWords64 (n := 4) hc
  have hs : arrange (loadWords concreteOps b inp 4) (loadWords concreteOps b key 8)
      (loadWords concreteOps b constant 4) = s := by
    rw [hn, hkey, hcon]
    rfl
  have hl : lowWords s = Salsa20Spec.initialState inputBytes keyBytes constantBytes :=
    Salsa20WideIO.lowWords_initialState64 inputBytes keyBytes constantBytes
  -- The reloaded words are the words of the initial state, so they cancel.
  have hout : outputs concreteOps ((rounds concreteOps 20 s).zipWith (concreteOps.alu .add) s)
      (loadWords concreteOps b inp 4) (loadWords concreteOps b constant 4) =
      #v[(loopRounds 20 s)[0], (loopRounds 20 s)[5], (loopRounds 20 s)[10],
         (loopRounds 20 s)[15], (loopRounds 20 s)[6], (loopRounds 20 s)[7],
         (loopRounds 20 s)[8], (loopRounds 20 s)[9]] := by
    have add : concreteOps.alu .add = ((· + ·) : BitVec 64 → BitVec 64 → BitVec 64) := rfl
    have sub : concreteOps.alu .sub = ((· - ·) : BitVec 64 → BitVec 64 → BitVec 64) := rfl
    rw [hn, hcon, rounds_concrete_eq_loopRounds]
    simp only [outputs, add, sub, Vector.getElem_zipWith, s, Salsa20WideIO.initialState64]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, BitVec.add_sub_cancel]
  have hstore (w : BitVec 64) :
      (split concreteOps w).map (·.setWidth 8) = Salsa20Spec.storeLE (low32 w) := by
    rw [split_concrete_eq_storeLE64, Salsa20WideIO.storeLE64_eq_storeLE]
  change Vector.map (n := 8 * 4) (BitVec.setWidth 8 : BitVec 64 → BitVec 8) _ = _
  simp only [hcore, hs, hout, HSalsa20Spec.hsalsa20, HSalsa20Spec.outputWords]
  rw [Vector.map_flatten, ← hl]
  apply congrArg (fun blocks : Vector (Bytes 4) 8 => blocks.flatten)
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, hstore]
  match i, hi with
  | 0, _ => simp [lowWord_rounds]
  | 1, _ => simp [lowWord_rounds]
  | 2, _ => simp [lowWord_rounds]
  | 3, _ => simp [lowWord_rounds]
  | 4, _ => simp [lowWord_rounds]
  | 5, _ => simp [lowWord_rounds]
  | 6, _ => simp [lowWord_rounds]
  | 7, _ => simp [lowWord_rounds]

end TweetNaCl.HSalsa20Reference
