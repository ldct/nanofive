import TweetNaCl.Salsa20Correct

/-! The audited statement for the linked Salsa20/20 core. See `Salsa20Spec`
for the independent byte function and `Salsa20Program` for the linked words. -/
namespace TweetNaCl
open TinyFive Salsa20Correct
open Salsa20Replay.Wrapper

/-- The public RV64IM wrapper writes the specified block and returns, for
arbitrary input bytes at the stated ABI layout. The instruction and address
trace does not depend on those bytes.

Assumptions: memory is `capacity` bytes and holds the linked helper and wrapper
words; execution starts at the wrapper entry; `ra`, `sp`, and `a0`–`a3` hold the
return address, stack top, and the output, input, key, and constant addresses.
Nothing else about the registers or memory is assumed. -/
theorem salsa20_correct {m : Machine 64}
    (hc : m.mem.size = capacity)
    (hcore : WordsAt m Salsa20Program.coreEntry Salsa20Program.coreWords)
    (hwrap : WordsAt m Salsa20Program.entry Salsa20Program.wrapperWords)
    (hpc : m.pc = BitVec.ofNat 64 Salsa20Program.entry) (hrun : m.status = .running)
    (hra : m.x.get 1 = returnPC) (hsp : m.x.get 2 = BitVec.ofNat 64 capacity)
    (ha0 : m.x.get 10 = BitVec.ofNat 64 out) (ha1 : m.x.get 11 = BitVec.ofNat 64 inp)
    (ha2 : m.x.get 12 = BitVec.ofNat 64 key) (ha3 : m.x.get 13 = BitVec.ofNat 64 constant)
    (inputBytes : Salsa20Spec.Bytes 16) (keyBytes : Salsa20Spec.Bytes 32)
    (constantBytes : Salsa20Spec.Bytes 16)
    (hi : BytesAt m inp inputBytes) (hk : BytesAt m key keyBytes)
    (ht : BytesAt m constant constantBytes) :
    let r := TinyFive.run steps m
    BytesAt r out (Salsa20Spec.core inputBytes keyBytes constantBytes) ∧
    r.pc = returnPC ∧ r.status = .running ∧ r.x.get 10 = 0 ∧
    r.x.get 2 = BitVec.ofNat 64 capacity ∧ r.x.get 1 = returnPC ∧
    Salsa20Replay.Frame writable m r ∧ Salsa20Replay.Trace schedule m := by
  have h := initial_related hpc hrun hra hsp ha0 ha1 ha2 ha3 (image_agrees hcore hwrap)
  obtain ⟨trace, _, frame, hp, hr, h0, hsp', hra'⟩ := verified h hc
  exact ⟨output_correct h hc inputBytes keyBytes constantBytes hi hk ht,
    hp, hr, h0, hsp', hra', frame, trace⟩

end TweetNaCl
