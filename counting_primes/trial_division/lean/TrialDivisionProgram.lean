import TinyFive.Machine

/-!
# The trial division prime counter

The program `prog`, loaded into a RISCV64 machine, with registers
  - `a0` set to `n`
  - everything else (including `pc`) set to 0
and with `ECALL` defined by the RARS calling convention, when run, terminates with `π(n)` printed
on one line, for all `n < 10^11`.

`prog` is the machine code of `counting_primes_trial_division.py`. `initial'` is `prog` loaded
into 128 bytes of zeroed memory, before the input; `CountingPrimes.IsCorrect` puts `n` in `a0`.
The program needs no memory beyond its own 92 bytes.
-/
namespace TinyFive.CountingPrimesTrialDivision

def prog : List (BitVec 32) := [
  0x00200293, 0x00000313, 0x02556a63, 0x00200393, 0x02538063,
  0x00028e13, 0x007e6663, 0x407e0e33, 0xff9ff06f, 0x000e0863,
  0x00138393, 0xfe5ff06f, 0x00130313, 0x00128293, 0xfd1ff06f,
  0x00030513, 0x00100893, 0x00000073, 0x00a00513, 0x00b00893,
  0x00000073, 0x00a00893, 0x00000073]

/-- The machine with `prog` loaded, before any input. -/
def initial' : Machine 64 := load 64 prog (128) []

end TinyFive.CountingPrimesTrialDivision
