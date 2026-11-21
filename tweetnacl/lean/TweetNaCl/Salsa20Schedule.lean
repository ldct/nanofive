import TweetNaCl.Salsa20LowWords
import TweetNaCl.ForHumans.Salsa20Spec

/-! The shared ELF loop gathers a diagonal-starting column and scatters the
result transposed: input indices `(5*j+4*m)%16`, output `4*j+(j+m)%4`.
Consequently each pair of iterations implements a Salsa20 double round.
This file proves the data-layout and low-word identities at the vector level. -/
namespace TweetNaCl.Salsa20Schedule
open Salsa20LowWords

abbrev WideState := Vector (BitVec 64) 16

def lowWords (s : WideState) : Salsa20Spec.State := s.map low32

def transpose (s : Salsa20Spec.State) : Salsa20Spec.State :=
  #v[s[0], s[4], s[8], s[12], s[1], s[5], s[9], s[13],
     s[2], s[6], s[10], s[14], s[3], s[7], s[11], s[15]]

/-- One iteration of the ELF's 20-iteration outer loop as a word function. -/
def loopRound (s : WideState) : WideState :=
  let q0 := quarterRound64 s[0] s[4] s[8] s[12]
  let q1 := quarterRound64 s[5] s[9] s[13] s[1]
  let q2 := quarterRound64 s[10] s[14] s[2] s[6]
  let q3 := quarterRound64 s[15] s[3] s[7] s[11]
  #v[q0.1, q0.2.1, q0.2.2.1, q0.2.2.2,
     q1.2.2.2, q1.1, q1.2.1, q1.2.2.1,
     q2.2.2.1, q2.2.2.2, q2.1, q2.2.1,
     q3.2.1, q3.2.2.1, q3.2.2.2, q3.1]

theorem row_as_transposed_column (s : Salsa20Spec.State) :
    transpose (Salsa20Spec.columnRound (transpose s)) = Salsa20Spec.rowRound s := by
  rfl

theorem lowWords_loopRound (s : WideState) :
    lowWords (loopRound s) = transpose (Salsa20Spec.columnRound (lowWords s)) := by
  let scatter (q0 q1 q2 q3 : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) :
      Salsa20Spec.State :=
    #v[q0.1, q0.2.1, q0.2.2.1, q0.2.2.2,
       q1.2.2.2, q1.1, q1.2.1, q1.2.2.1,
       q2.2.2.1, q2.2.2.2, q2.1, q2.2.1,
       q3.2.1, q3.2.2.1, q3.2.2.2, q3.1]
  let t := lowWords s
  simp only [lowWords, loopRound, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  change scatter (low32Quarter (quarterRound64 s[0] s[4] s[8] s[12]))
    (low32Quarter (quarterRound64 s[5] s[9] s[13] s[1]))
    (low32Quarter (quarterRound64 s[10] s[14] s[2] s[6]))
    (low32Quarter (quarterRound64 s[15] s[3] s[7] s[11])) =
    scatter (Salsa20Spec.quarterRound t[0] t[4] t[8] t[12])
      (Salsa20Spec.quarterRound t[5] t[9] t[13] t[1])
      (Salsa20Spec.quarterRound t[10] t[14] t[2] t[6])
      (Salsa20Spec.quarterRound t[15] t[3] t[7] t[11])
  simp only [quarterRound64_low32, t, lowWords, Vector.getElem_map]

def loopRounds (n : Nat) (s : WideState) : WideState :=
  match n with
  | 0 => s
  | n + 1 => loopRound (loopRounds n s)

theorem lowWords_loopRounds (s : WideState) (n : Nat) :
    lowWords (loopRounds (2 * n) s) = Salsa20Spec.rounds n (lowWords s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    simp only [loopRounds, lowWords_loopRound, ih, row_as_transposed_column,
      Salsa20Spec.rounds, Salsa20Spec.doubleRound]

/-- Feed-forward in the emitted code uses 64-bit adds; the output consumes
only their low words. -/
theorem lowWords_feedForward (s : WideState) :
    lowWords ((loopRounds 20 s).zipWith (· + ·) s) = Salsa20Spec.coreWords (lowWords s) := by
  have h := lowWords_loopRounds s 10
  change lowWords (loopRounds 20 s) = Salsa20Spec.permute (lowWords s) at h
  apply Vector.ext
  intro i hi
  have hi' := congrArg (fun v : Salsa20Spec.State => v[i]) h
  simp only [Salsa20Spec.coreWords, Salsa20Spec.feedForward, lowWords,
    Vector.getElem_map, Vector.getElem_zipWith, low32_add] at hi' ⊢
  rw [hi', BitVec.add_comm]

end TweetNaCl.Salsa20Schedule
