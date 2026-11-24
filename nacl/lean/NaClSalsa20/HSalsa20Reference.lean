import NaClSalsa20.Reference
import TweetNaCl.ForHumans.HSalsa20Spec

/-!
# HSalsa20 over an abstract word algebra

`hcore` repeats `TweetNaCl.HSalsa20Spec.hsalsa20` over the operations of `Reference`: the
Salsa20 rounds without the feed-forward, then words 0, 5, 10, 15, 6, 7, 8 and 9. With the
concrete operations it is `hsalsa20` (`hcore_concrete`), and `hcore_rel` transfers a relation
between two algebras from the input bytes to the output bytes, as `core_rel` does.
-/
namespace NaClSalsa20.Reference
open TweetNaCl

variable {α β : Type} (o : Ops α β)

/-- The eight output words: the diagonal, then the words that held the input. -/
def outputWords (z : Vector α 16) : Vector α 8 :=
  #v[z[0], z[5], z[10], z[15], z[6], z[7], z[8], z[9]]

def encode8 (s : Vector α 8) : Vector β 32 :=
  (s.map fun w => #v[o.byte w 0, o.byte w 1, o.byte w 2, o.byte w 3]).flatten

def hcore (input : Vector β 16) (key : Vector β 32) (constant : Vector β 16) : Vector β 32 :=
  encode8 o (outputWords (rounds o 10 (initialState o input key constant)))

theorem hcore_concrete (input : Salsa20Spec.Bytes 16) (key : Salsa20Spec.Bytes 32)
    (constant : Salsa20Spec.Bytes 16) :
    hcore concrete input key constant = HSalsa20Spec.hsalsa20 input key constant := by
  simp only [hcore, encode8, outputWords, HSalsa20Spec.hsalsa20, HSalsa20Spec.outputWords,
    Salsa20Spec.permute, rounds_concrete]
  rfl

section Rel
variable {α' β' : Type} {o : Ops α β} {p : Ops α' β'} (R : Rel o p)

theorem outputWords_rel {z : Vector α 16} {z' : Vector α' 16} (h : Pointwise R.word z z') :
    Pointwise R.word (outputWords z) (outputWords z') := by
  intro i hi
  match i, hi with
  | 0, _ => exact h 0 (by omega)
  | 1, _ => exact h 5 (by omega)
  | 2, _ => exact h 10 (by omega)
  | 3, _ => exact h 15 (by omega)
  | 4, _ => exact h 6 (by omega)
  | 5, _ => exact h 7 (by omega)
  | 6, _ => exact h 8 (by omega)
  | 7, _ => exact h 9 (by omega)
  | _ + 8, h => exact absurd h (by omega)

theorem encode8_rel {s : Vector α 8} {s' : Vector α' 8} (h : Pointwise R.word s s') :
    Pointwise R.byte (encode8 o s) (encode8 p s') := by
  intro i hi
  have hi' : i < 8 * 4 := hi
  simp only [encode8, Vector.getElem_flatten hi', Vector.getElem_map]
  have hw := h (i / 4) (by omega)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h <;>
    simp only [h, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] <;>
    exact R.toByte hw

theorem hcore_rel {input : Vector β 16} {key : Vector β 32} {constant : Vector β 16}
    {input' : Vector β' 16} {key' : Vector β' 32} {constant' : Vector β' 16}
    (hi : Pointwise R.byte input input') (hk : Pointwise R.byte key key')
    (hc : Pointwise R.byte constant constant') :
    Pointwise R.byte (hcore o input key constant) (hcore p input' key' constant') := by
  have n := decodeWords_rel R (n := 4) hi
  have k := decodeWords_rel R (n := 8) hk
  have c := decodeWords_rel R (n := 4) hc
  have hs : Pointwise R.word (initialState o input key constant)
      (initialState p input' key' constant') := by
    intro i hi
    simp only [initialState]
    match i, hi with
    | 0, _ => exact c 0 (by omega)
    | 1, _ => exact k 0 (by omega)
    | 2, _ => exact k 1 (by omega)
    | 3, _ => exact k 2 (by omega)
    | 4, _ => exact k 3 (by omega)
    | 5, _ => exact c 1 (by omega)
    | 6, _ => exact n 0 (by omega)
    | 7, _ => exact n 1 (by omega)
    | 8, _ => exact n 2 (by omega)
    | 9, _ => exact n 3 (by omega)
    | 10, _ => exact c 2 (by omega)
    | 11, _ => exact k 4 (by omega)
    | 12, _ => exact k 5 (by omega)
    | 13, _ => exact k 6 (by omega)
    | 14, _ => exact k 7 (by omega)
    | 15, _ => exact c 3 (by omega)
    | _ + 16, h => exact absurd h (by omega)
  exact encode8_rel R (outputWords_rel R (rounds_rel R 10 hs))

end Rel
end NaClSalsa20.Reference
