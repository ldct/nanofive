import TweetNaCl.HSalsa20Correct

/-! The audited statement for the linked HSalsa20 core. See `HSalsa20Spec` for the
independent byte function, and `Salsa20Program` and `HSalsa20Program` for the linked words. -/
namespace TweetNaCl
open TinyFive HSalsa20Correct
open HSalsa20Replay (capacity out inp key constant returnPC steps writable schedule WordsAt)

/-- The public RV64IM wrapper `crypto_core_hsalsa20_tweet` writes HSalsa20 of the input,
key and constant and returns zero, for arbitrary input bytes at the stated ABI layout. The
instruction and address trace does not depend on those bytes.

Assumptions: memory is `capacity` bytes and holds the linked helper and wrapper words;
execution starts at the wrapper entry; `ra`, `sp`, and `a0`–`a3` hold the return address,
stack top, and the output, input, key, and constant addresses. Nothing else about the
registers or memory is assumed. -/
example {m : Machine 64}
    (hc : m.mem.size = capacity)
    (hcore : WordsAt m Salsa20Program.coreEntry Salsa20Program.coreWords)
    (hwrap : WordsAt m HSalsa20Program.entry HSalsa20Program.wrapperWords)
    (hpc : m.pc = BitVec.ofNat 64 HSalsa20Program.entry) (hrun : m.status = .running)
    (hra : m.x.get 1 = returnPC) (hsp : m.x.get 2 = BitVec.ofNat 64 capacity)
    (ha0 : m.x.get 10 = BitVec.ofNat 64 out) (ha1 : m.x.get 11 = BitVec.ofNat 64 inp)
    (ha2 : m.x.get 12 = BitVec.ofNat 64 key) (ha3 : m.x.get 13 = BitVec.ofNat 64 constant)
    (inputBytes : Salsa20Spec.Bytes 16) (keyBytes : Salsa20Spec.Bytes 32)
    (constantBytes : Salsa20Spec.Bytes 16)
    (hi : Salsa20Correct.BytesAt m inp inputBytes) (hk : Salsa20Correct.BytesAt m key keyBytes)
    (ht : Salsa20Correct.BytesAt m constant constantBytes) :
    let r := TinyFive.run steps m
    Salsa20Correct.BytesAt r out (HSalsa20Spec.hsalsa20 inputBytes keyBytes constantBytes) ∧
    r.pc = returnPC ∧ r.status = .running ∧ r.x.get 10 = 0 ∧
    r.x.get 2 = BitVec.ofNat 64 capacity ∧ r.x.get 1 = returnPC ∧
    Salsa20Replay.Frame writable m r ∧ Salsa20Replay.Trace schedule m :=
  hsalsa20_correct hc hcore hwrap hpc hrun hra hsp ha0 ha1 ha2 ha3 inputBytes keyBytes
    constantBytes hi hk ht

end TweetNaCl
