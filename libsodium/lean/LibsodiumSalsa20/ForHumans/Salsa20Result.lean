import LibsodiumSalsa20.Call

/-! The audited statement for libsodium's `crypto_core_salsa20` as a call. See
`TweetNaCl/ForHumans/Salsa20Spec.lean` for the independent Salsa20/20 core `core`, and
`LibsodiumSalsa20/Program.lean` for the linked words. -/
namespace LibsodiumSalsa20
open TinyFive Call

/-- For arbitrary input, key and constant bytes at the stated buffers, the linked
`crypto_core_salsa20` writes the Salsa20/20 core and returns zero. The instruction and
address trace does not depend on those bytes.

Assumptions: memory is `capacity` bytes and holds `coreWords` at `coreStart`; execution
starts at `coreEntry`; `ra`, `sp` and `a0`–`a3` hold the return address, the top of memory,
and the output, input, key and constant addresses. Nothing else about the registers or memory is assumed. -/
example {m : Machine 64}
    (hc : m.mem.size = capacity) (hcore : WordsAt m coreStart coreWords)
    (hpc : m.pc = BitVec.ofNat 64 coreEntry) (hrun : m.status = .running)
    (hra : m.x.get 1 = returnPC) (hsp : m.x.get 2 = BitVec.ofNat 64 capacity)
    (ha0 : m.x.get 10 = BitVec.ofNat 64 out) (ha1 : m.x.get 11 = BitVec.ofNat 64 inp)
    (ha2 : m.x.get 12 = BitVec.ofNat 64 key) (ha3 : m.x.get 13 = BitVec.ofNat 64 constant)
    (inputBytes : TweetNaCl.Salsa20Spec.Bytes 16) (keyBytes : TweetNaCl.Salsa20Spec.Bytes 32)
    (constantBytes : TweetNaCl.Salsa20Spec.Bytes 16)
    (hi : BytesAt m inp inputBytes) (hk : BytesAt m key keyBytes)
    (ht : BytesAt m constant constantBytes) :
    let r := run steps m
    BytesAt r out (TweetNaCl.Salsa20Spec.core inputBytes keyBytes constantBytes) ∧
    r.pc = returnPC ∧ r.status = .running ∧ r.x.get 10 = 0 ∧
    r.x.get 2 = BitVec.ofNat 64 capacity ∧ r.x.get 1 = returnPC ∧
    TweetNaCl.Salsa20Replay.Frame writable m r ∧ TweetNaCl.Salsa20Replay.Trace schedule m :=
  salsa20_correct hc hcore hpc hrun hra hsp ha0 ha1 ha2 ha3 inputBytes keyBytes constantBytes
    hi hk ht

end LibsodiumSalsa20
