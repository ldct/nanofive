import TweetNaCl.HSalsa20IO

/-!
# HSalsa20 as a program: correctness result

To check the result, read

* `ForHumans/HSalsa20IOSpec.lean`: `IsCorrect`
* `ForHumans/HSalsa20Spec.lean`: HSalsa20, `hsalsa20`
* (optional) `HSalsa20IOProgram.lean`: the machine code `prog` and the machine `initial`
-/
namespace TweetNaCl.HSalsa20Spec

example : IsCorrect HSalsa20IOProgram.initial := HSalsa20IO.isCorrect

end TweetNaCl.HSalsa20Spec
