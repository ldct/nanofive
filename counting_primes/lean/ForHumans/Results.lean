import CountingPrimesTrialDivision
import CountingPrimesSieve
import CountingPrimesWheel
import CountingPrimesOddSieve
import CountingPrimesLucy
import GrumpyBinary.Correct
import ZjyBinary.Correct

/-!
# Counting primes: correctness results

To check the results, read

* `ForHumans/Spec.lean`: `IsCorrect` and `programSize`
* (optional) each `<variant>/lean/*Program.lean`: the machine code `prog` and the machine `initial'` to check the actual machine code
-/
namespace TinyFive.CountingPrimes

example : IsCorrect CountingPrimesTrialDivision.initial' := CountingPrimesTrialDivision.isCorrect
example : programSize CountingPrimesTrialDivision.initial' = 68 :=
  CountingPrimesTrialDivision.programSize_eq

example : IsCorrect CountingPrimesSieve.initial' := CountingPrimesSieve.isCorrect
example : programSize CountingPrimesSieve.initial' = 72 :=
  CountingPrimesSieve.programSize_eq

example : IsCorrect CountingPrimesWheel.initial' := CountingPrimesWheel.isCorrect
example : programSize CountingPrimesWheel.initial' = 106 :=
  CountingPrimesWheel.programSize_eq

example : IsCorrect CountingPrimesOddSieve.initial' :=
  CountingPrimesOddSieve.isCorrect
example : programSize CountingPrimesOddSieve.initial' = 161 :=
  CountingPrimesOddSieve.programSize_eq

example : IsCorrect CountingPrimesLucy.initial' := CountingPrimesLucy.isCorrect
example : programSize CountingPrimesLucy.initial' = 344 :=
  CountingPrimesLucy.programSize_eq

example : IsCorrect GrumpyBinary.initial' := GrumpyBinary.isCorrect
example : programSize GrumpyBinary.initial' = 1016 :=
  GrumpyBinary.programSize_eq

example : IsCorrect ZjyBinary.initial' := ZjyBinary.isCorrect
example : programSize ZjyBinary.initial' = 1239 :=
  ZjyBinary.programSize_eq

end TinyFive.CountingPrimes
