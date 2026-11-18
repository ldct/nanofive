import OddWheelFlags
import OddWheelMarking

namespace TinyFive.CountingPrimesOddWheel
open OddWheelMath SieveMemory

/-- Register, memory, and flag invariant at a candidate-pair boundary. -/
structure OuterCore (n k : Nat) (x : Regs 64) (mem : Array (BitVec 8)) : Prop where
  positive : 1 ≤ k
  bound : x.get 5 = BitVec.ofNat 64 (E n)
  marker : x.get 7 = 16777217
  square64 : sqPlus k < 2^64
  square : x.get 12 = BitVec.ofNat 64 (sqPlus k)
  delta : x.get 14 = BitVec.ofNat 64 (8*k)
  stride : x.get 15 = BitVec.ofNat 64 (12*k-2)
  candidate : x.get 16 = BitVec.ofNat 64 (2*k)
  layout : Layout image 512 (memSize n) mem
  flags : WheelFlags mem (E n) (6*k+1)

/-- PC100 is entered either with a live square or on the unconditional first pair. -/
def OuterEntry (n k : Nat) (x : Regs 64) (mem : Array (BitVec 8)) : Prop :=
  OuterCore n k x mem ∧ (sqPlus k < E n ∨ k = 1)

/-- Interface of the separately verified machine execution of one candidate pair.
The output is at PC196, immediately before the outer-loop branch. -/
def OuterPairSpec (n : Nat) (out : String) : Prop :=
  ∀ k x mem, OuterEntry n k x mem →
    ∃ fuel x' mem', run fuel ⟨x, 100, mem, [], out, .running⟩ =
      ⟨x', 196, mem', [], out, .running⟩ ∧
      fuel ≤ 14 + 10*(E n+1) ∧ OuterCore n (k+1) x' mem'

end TinyFive.CountingPrimesOddWheel
