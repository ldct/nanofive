import TinyFive.Machine
import TweetNaCl.ForHumans.HSalsa20Spec
import TweetNaCl.ForHumans.Salsa20IOSpec

/-!
# HSalsa20 as a program

To check the definitions, read

`TinyFive.Machine`: the RISCV64 semantics, via `is_exited_with_output` and `run`.
`ForHumans/HSalsa20Spec.lean`: the HSalsa20 function `hsalsa20`.
`ForHumans/Salsa20IOSpec.lean`: `toChars`, bytes as the machine reads and prints them.
-/
namespace TweetNaCl.HSalsa20Spec
open TinyFive Salsa20Spec

/-- Started with the 64 bytes of input, key and constant on standard input, the machine `m`
prints the 32 bytes of HSalsa20 and exits with code zero, for every input. -/
def IsCorrect (m : Machine 64) : Prop :=
  ∃ fuel, ∀ (input : Bytes 16) (key : Bytes 32) (constant : Bytes 16),
    is_exited_with_output
      (run fuel { m with input := toChars (input.toList ++ key.toList ++ constant.toList) })
      (String.ofList (toChars (hsalsa20 input key constant).toList))

end TweetNaCl.HSalsa20Spec
