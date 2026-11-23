import TweetNaCl.Salsa20Program

/-!
# The linked HSalsa20 wrapper

`crypto_core_hsalsa20_tweet` calls the helper `core` of `Salsa20Program` with `h = 1`.
-/
namespace TweetNaCl.HSalsa20Program

def entry : Nat := 0x1170

/-- Linked RV64IM machine code of
`int crypto_core_hsalsa20(u8 *out,const u8 *in,const u8 *k,const u8 *c)` in
`tweetnacl/vendor/tweetnacl.c` (linked as `crypto_core_hsalsa20_tweet`), which
calls `core(out,in,k,c,1)` and returns 0. -/
def wrapperWords : List (BitVec 32) := [
  0xff010113, 0x00100713, 0x00113423, 0xfffff097, 0xeb4080e7,
  0x00813083, 0x00000513, 0x01010113, 0x00008067]

end TweetNaCl.HSalsa20Program
