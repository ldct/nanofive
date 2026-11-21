import TinyFive.Pad
import ForHumans.Spec

/-!
# Moving a correctness proof to a larger memory

The proofs run each input `n` in a machine with just enough memory for `n`. `isCorrect_of_load`
and `programSize_load` move them to the one large machine that `IsCorrect` is about.
-/
namespace TinyFive.CountingPrimes

/-- Zero padding does not change the program size. -/
theorem programSize_load (words : List (BitVec 32)) (small large : Nat)
    (hw : 4 * words.length ≤ small) (hs : small ≤ large) :
    programSize (load 64 words large []) = programSize (load 64 words small []) := by
  rw [load_eq_pad words small large hw hs]
  simp [programSize, Machine.pad, Array.countP_append, Array.countP_replicate]

/-- A program proved correct with `memSize n` bytes of memory for each input is correct as one
machine with `large` bytes, provided `large` covers every `memSize n`. -/
theorem isCorrect_of_load (words : List (BitVec 32)) (memSize : Nat → Nat) (large : Nat)
    (hw : ∀ n < 10^11, 4 * words.length ≤ memSize n) (hl : ∀ n < 10^11, memSize n ≤ large)
    (h : ∃ fuel, ∀ n < 10^11,
      is_exited_with_output (run fuel ((load 64 words (memSize n) []).loadInput n))
        (toString (countPrimes n) ++ "\n")) :
    IsCorrect (load 64 words large []) := by
  obtain ⟨fuel, h⟩ := h
  refine ⟨fuel, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := h n hn
  have he : (load 64 words large []).loadInput n =
      ((load 64 words (memSize n) []).loadInput n).pad (large - memSize n) := by
    rw [load_eq_pad words (memSize n) large (hw n hn) (hl n hn)]
    rfl
  rw [he, run_pad _ _ _ (by rw [h1]; decide)]
  exact ⟨h1, h2⟩

end TinyFive.CountingPrimes
