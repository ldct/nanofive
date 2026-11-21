import TinyFive.Machine

/-!
# The lucy prime counter (audited)

`prog` is the RISC-V machine code of `counting_primes_lucy.py`: Lucy_Hedgehog's algorithm in
O(√N) memory, using `mul`, `divu`, `ld` and `sd`. `initial'` is the machine with `prog` loaded
at address 0 of zeroed memory, every register and `pc` zero, and no input.
`CountingPrimes.IsCorrect` puts `n` in `a0` before running it.

Code at address 0, then tables of 8-byte words from address 512, `isqrt n + 1` words for
input `n`. `isqrt (10^11) = 316227`, so the machine has the memory every input below `10^11`
needs.
-/
namespace TinyFive.CountingPrimesLucy

def prog : List (BitVec 32) := [
  0x00300393, 0x16756863, 0x01800b13, 0x00100293, 0x00000313, 0x00050f13,
  0x03635e33, 0x21c33023, 0xffff0e13, 0xffee7e13, 0x027e5e33, 0x21c33423,
  0x01030313, 0x00228293, 0x02555f33, 0xfc5f7ee3, 0xff830593, 0x00251613,
  0x20803683, 0x02800713, 0x00000f93, 0x10e5e063, 0x1f873f03, 0x0dff0663,
  0x20073e03, 0x41fe0e33, 0x41c686b3, 0x00375793, 0x02f78833, 0x00e708b3,
  0x00381a93, 0x02f584b3, 0x0155f663, 0x03055e33, 0x02ee04b3, 0x011a8433,
  0x0a84ec63, 0x21070913, 0x0285e263, 0x20043e03, 0x00093e83, 0x41fe0e33,
  0x41ce8eb3, 0x01d93023, 0x01090913, 0x01140433, 0xfe85f2e3, 0x00145e13,
  0x41c60e33, 0xff8e7993, 0x0289de33, 0x004e1e13, 0x200e3e03, 0x00093e83,
  0x41fe0e33, 0x41ce8eb3, 0x01d93023, 0x01090913, 0x01140433, 0x40e989b3,
  0xfc84fce3, 0x0355e863, 0x00058a13, 0x40ea0e33, 0x031e5e33, 0x004e1e13,
  0x200e3e03, 0x1f8a3e83, 0x41fe0e33, 0x41ce8eb3, 0x1fda3c23, 0xff0a0a13,
  0xfd5a7ee3, 0x001f8f93, 0x01070713, 0xf2e5f6e3, 0x0240006f, 0x1f873f03,
  0x01ff0a63, 0x20073e03, 0x41fe0e33, 0x41c686b3, 0x001f8f93, 0x01070713,
  0xfee5f2e3, 0x00268513, 0x00100893, 0x00000073, 0x00a00513, 0x00b00893,
  0x00000073, 0x00a00893, 0x00000073, 0x00155513, 0xfe1ff06f]

/-- The machine with `prog` loaded, before any input. -/
def initial' : Machine 64 := load 64 prog (512 + 8 * 316228) []

end TinyFive.CountingPrimesLucy
