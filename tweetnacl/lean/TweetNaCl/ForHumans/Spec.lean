namespace TweetNaCl

/-- RV64 `a0` on return from a 32-byte comparison: 0 for equal, -1 otherwise. -/
def verify32Result (left right : Vector (BitVec 8) 32) : BitVec 64 :=
  if left = right then 0 else -1

end TweetNaCl
