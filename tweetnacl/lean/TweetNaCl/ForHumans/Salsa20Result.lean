import TweetNaCl.Salsa20Correct

/-! The audited statement for the linked Salsa20/20 core. See `Salsa20Spec`
for the independent byte function and `Salsa20Program` for the linked words. -/
namespace TweetNaCl
open TinyFive Salsa20Correct
open Salsa20Replay.Wrapper

/-- The public RV64IM wrapper writes the specified block and returns, for
arbitrary input bytes at the stated ABI layout. The instruction and address
trace does not depend on those bytes. -/
theorem salsa20_correct {m : Machine 64}
    (h : Salsa20Replay.Related initial m) (hc : m.mem.size = capacity)
    (inputBytes : Salsa20Spec.Bytes 16) (keyBytes : Salsa20Spec.Bytes 32)
    (constantBytes : Salsa20Spec.Bytes 16)
    (hi : BytesAt m inp inputBytes) (hk : BytesAt m key keyBytes)
    (ht : BytesAt m constant constantBytes) :
    let r := TinyFive.run steps m
    BytesAt r out (Salsa20Spec.core inputBytes keyBytes constantBytes) ∧
    r.pc = returnPC ∧ r.status = .running ∧ r.x.get 10 = 0 ∧
    r.x.get 2 = BitVec.ofNat 64 capacity ∧ r.x.get 1 = returnPC ∧
    Salsa20Replay.Frame writable m r ∧ Salsa20Replay.Trace schedule m := by
  obtain ⟨trace, _, frame, hp, hr, h0, hsp, hra⟩ := verified h hc
  exact ⟨output_correct h hc inputBytes keyBytes constantBytes hi hk ht,
    hp, hr, h0, hsp, hra, frame, trace⟩

end TweetNaCl
