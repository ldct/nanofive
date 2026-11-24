import LibsodiumSalsa20.HSalsa20IO

/-!
# libsodium's HSalsa20 as a program: correctness result

To check the result, read

* `TweetNaCl/ForHumans/HSalsa20IOSpec.lean`: `IsCorrect`, the definition also used for TweetNaCl
* `TweetNaCl/ForHumans/HSalsa20Spec.lean`: HSalsa20, `hsalsa20`
* (optional) `LibsodiumSalsa20/HSalsa20Program.lean`: the machine code `prog` and the machine `initial`
-/
namespace TweetNaCl.HSalsa20Spec

example : IsCorrect LibsodiumSalsa20.HSalsa20.initial := LibsodiumSalsa20.HSalsa20.IO.isCorrect

end TweetNaCl.HSalsa20Spec
