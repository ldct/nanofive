import TinyFive.Machine

/-!
# The sieve prime counter (audited)

`prog` is the RISC-V machine code of `counting_primes_sieve.py`: a byte-array Sieve of
Eratosthenes. `initial'` is the machine with `prog` loaded at address 0 of zeroed memory, every
register and `pc` zero, and no input. `CountingPrimes.IsCorrect` puts `n` in `a0` before running
it.

Code at address 0, then one flag byte at `128 + i` for each `i ≤ n`. The machine has the
memory every input below `10^11` needs.
-/
namespace TinyFive.CountingPrimesSieve

def prog : List (BitVec 32) := [
  0x00200293, 0x00000313, 0x00100f13, 0x08000f93, 0x02556a63,
  0x005f8e33, 0x000e4e83, 0x020e9063, 0x00130313, 0x005283b3,
  0x00756a63, 0x007f8e33, 0x01ee0023, 0x005383b3, 0xff1ff06f,
  0x00128293, 0xfd1ff06f, 0x00030513, 0x00100893, 0x00000073,
  0x00a00513, 0x00b00893, 0x00000073, 0x00a00893, 0x00000073]

/-- The machine with `prog` loaded, before any input. -/
def initial' : Machine 64 := load 64 prog (128 + 10^11) []

end TinyFive.CountingPrimesSieve
