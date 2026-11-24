import NettleSalsa20.Call

/-! The audited statement for Nettle's `_nettle_salsa20_core` as a call. See
`TweetNaCl/ForHumans/Salsa20Spec.lean` for the independent Salsa20/20 core: `coreBytes` maps a
64-byte state to its core, and `core` builds that state from input, key and constant. See
`NettleSalsa20/Program.lean` for the linked words. -/
namespace NettleSalsa20
open TinyFive Call

/-- For an arbitrary 64-byte state at `src`, the linked `_nettle_salsa20_core(dst, src, 20)`
writes the Salsa20/20 core of the state to `dst` and returns. The instruction and address trace
does not depend on the state.

Assumptions: memory is `capacity` bytes and holds `coreWords` at `coreEntry`; execution starts
there; `ra`, `sp` and `a0`–`a2` hold the return address, the top of memory, `dst` (`out`),
`src` and 20. Nothing else about the registers or memory is assumed. -/
example {m : Machine 64}
    (hc : m.mem.size = capacity) (hcore : WordsAt m coreEntry coreWords)
    (hpc : m.pc = BitVec.ofNat 64 coreEntry) (hrun : m.status = .running)
    (hra : m.x.get 1 = returnPC) (hsp : m.x.get 2 = BitVec.ofNat 64 capacity)
    (ha0 : m.x.get 10 = BitVec.ofNat 64 out) (ha1 : m.x.get 11 = BitVec.ofNat 64 src)
    (ha2 : m.x.get 12 = BitVec.ofNat 64 20)
    (state : TweetNaCl.Salsa20Spec.Bytes 64) (hs : BytesAt m src state) :
    let r := run steps m
    BytesAt r out (TweetNaCl.Salsa20Spec.coreBytes state) ∧
    r.pc = returnPC ∧ r.status = .running ∧
    r.x.get 2 = BitVec.ofNat 64 capacity ∧ r.x.get 1 = returnPC ∧
    TweetNaCl.Salsa20Replay.Frame writable m r ∧ TweetNaCl.Salsa20Replay.Trace schedule m :=
  salsa20_correct_bytes hc hcore hpc hrun hra hsp ha0 ha1 ha2 state hs

end NettleSalsa20
