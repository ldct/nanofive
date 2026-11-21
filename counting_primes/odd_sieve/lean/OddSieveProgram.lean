import TinyFive.Machine

/-!
# The odd sieve prime counter (audited)

`prog` is the RISC-V machine code of `counting_primes_odd_sieve.py`: an odds-only Sieve of
Eratosthenes. `initial'` is the machine with `prog` loaded at address 0 of zeroed memory, every
register and `pc` zero, and no input. `CountingPrimes.IsCorrect` puts `n` in `a0` before running
it.

Code at address 0, then one flag byte per odd number up to `n` from address 256, and 16 bytes
of padding for the word-summing count. The machine has the memory every input below `10^11`
needs.
-/
namespace TinyFive.CountingPrimesOddSieve

def prog : List (BitVec 32) := [
  0x00100f13, 0x00af32b3, 0x00a282b3, 0x0012d513, 0x10050613,
  0x10100e13, 0x10400e93, 0x00300f93, 0x02cef863, 0x000e4283,
  0x00029a63, 0x000e8313, 0x01e30023, 0x01f30333, 0xfec36ce3,
  0x001e0e13, 0x01fe8eb3, 0x002f8f93, 0x01fe8eb3, 0xfcceece3,
  0x10000593, 0x00000313, 0x1f058393, 0x00767463, 0x00060393,
  0x0005a283, 0x00530333, 0x0045a283, 0x00530333, 0x0085a283,
  0x00530333, 0x00c5a283, 0x00530333, 0x01058593, 0xfc75eee3,
  0x01035293, 0x00530333, 0x0ff37293, 0x40550533, 0x00835313,
  0x0ff37313, 0x40650533, 0xfac5e6e3, 0x00100893, 0x00000073,
  0x00a00513, 0x00b00893, 0x00000073, 0x00a00893, 0x00000073]

/-- The machine with `prog` loaded, before any input. -/
def initial' : Machine 64 := load 64 prog (256 + (10^11 + 1) / 2 + 16) []

end TinyFive.CountingPrimesOddSieve
