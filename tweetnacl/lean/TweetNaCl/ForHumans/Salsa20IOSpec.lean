import TinyFive.Machine
import TweetNaCl.ForHumans.Salsa20Spec

/-!
# Salsa20 as a program

To check the definitions, read

`TinyFive.Machine`: the RISCV64 semantics, via `is_exited_with_output` and `run`.
`ForHumans/Salsa20Spec.lean`: the Salsa20/20 core function `core`.
-/
namespace TweetNaCl.Salsa20Spec
open TinyFive

/-- Bytes as characters, as the machine reads (`ecall` 12) and prints (`ecall` 11) them. -/
def toChars (b : List (BitVec 8)) : List Char := b.map fun x => Char.ofNat x.toNat

/-- Started with the 64 bytes of input, key and constant on standard input, the machine `m`
prints the 64 bytes of the Salsa20/20 core and exits with code zero, for every input. -/
def IsCorrect (m : Machine 64) : Prop :=
  ∃ fuel, ∀ (input : Bytes 16) (key : Bytes 32) (constant : Bytes 16),
    is_exited_with_output
      (run fuel { m with input := toChars (input.toList ++ key.toList ++ constant.toList) })
      (String.ofList (toChars (core input key constant).toList))

end TweetNaCl.Salsa20Spec
