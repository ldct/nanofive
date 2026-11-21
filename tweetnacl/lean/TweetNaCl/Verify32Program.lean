namespace TweetNaCl.Verify32Program

/-- Linked entry address of `crypto_verify_32_tweet` in `tweetnacl.elf`. -/
def entry : Nat := 0x1114

/-- Linked instruction words at `entry`, checked by `tweetnacl_test.py`. -/
def prog : List (BitVec 32) := [
  0x02050613, 0x00000713, 0x00054783, 0x0005c683, 0x00150513,
  0x00158593, 0x00d7c7b3, 0x00f76733, 0xfea614e3, 0xfff70513,
  0x00855513, 0x00157513, 0xfff50513, 0x00008067]

end TweetNaCl.Verify32Program
