import LibsodiumSalsa20.IO

/-!
# libsodium's Salsa20 core as a program: correctness result

To check the result, read

* `TweetNaCl/ForHumans/Salsa20IOSpec.lean`: `IsCorrect`, the definition also used for TweetNaCl
* `TweetNaCl/ForHumans/Salsa20Spec.lean`: the Salsa20/20 core `core`
* (optional) `LibsodiumSalsa20/Program.lean`: the machine code `prog` and the machine `initial`
-/
namespace TweetNaCl.Salsa20Spec

example : IsCorrect LibsodiumSalsa20.initial := LibsodiumSalsa20.IO.isCorrect

end TweetNaCl.Salsa20Spec
