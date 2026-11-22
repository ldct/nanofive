import TinyFive.Machine
import TinyFive.Primes

/-!
# Counting primes functional correctness

To check the definitios, read

`TinyFive.Machine`: the RISCV64 semantics is defined via `is_exited_with_output` and `run`.
`TinyFive.Primes`: the prime-counting function is defined.
-/
namespace TinyFive

/-- Preload the input `n` in `a0`. -/
def Machine.loadInput (m : Machine 64) (n : Nat) : Machine 64 :=
  m.setReg 10 (BitVec.ofNat 64 n)

/-- Number of nonzero bytes in the machine's memory. -/
def programSize (m : Machine 64) : Nat := m.mem.countP (· ≠ 0)

namespace CountingPrimes

/--
The machine `m` correctly implements the prime-counting function for all inputs below `10^11`.
-/
def IsCorrect (m : Machine 64) : Prop :=
  ∃ fuel, ∀ n < 10^11,
    is_exited_with_output (run fuel (m.loadInput n)) (toString (countPrimes n) ++ "\n")

end CountingPrimes
end TinyFive
