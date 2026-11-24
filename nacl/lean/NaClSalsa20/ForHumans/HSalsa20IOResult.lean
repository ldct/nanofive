import NaClSalsa20.HSalsa20IO

/-!
# NaCl's HSalsa20 as a program: correctness result

To check the result, read

* `TweetNaCl/ForHumans/HSalsa20IOSpec.lean`: `IsCorrect`, the definition also used for TweetNaCl
* `TweetNaCl/ForHumans/HSalsa20Spec.lean`: HSalsa20, `hsalsa20`
* (optional) `NaClSalsa20/HSalsa20Program.lean`: the machine code `prog` and the machine `initial`
-/
namespace TweetNaCl.HSalsa20Spec

example : IsCorrect NaClSalsa20.HSalsa20.initial := NaClSalsa20.HSalsa20.IO.isCorrect

end TweetNaCl.HSalsa20Spec
