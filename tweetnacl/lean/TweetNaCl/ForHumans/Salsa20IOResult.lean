import TweetNaCl.Salsa20IO

/-!
# Salsa20 as a program: correctness result

To check the result, read

* `ForHumans/Salsa20IOSpec.lean`: `IsCorrect`
* `ForHumans/Salsa20Spec.lean`: the Salsa20/20 core `core`
* (optional) `Salsa20IOProgram.lean`: the machine code `prog` and the machine `initial`
-/
namespace TweetNaCl.Salsa20Spec

example : IsCorrect Salsa20IOProgram.initial := Salsa20IO.isCorrect

end TweetNaCl.Salsa20Spec
