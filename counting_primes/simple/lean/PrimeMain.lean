import CountingPrimes

open TinyFive

private partial def runToEnd (m : Machine 32) : Machine 32 :=
  if m.status = .running then runToEnd (step m) else m

/-- Host-side input adapter, like `counting_primes_simple.py`. -/
def main : IO UInt32 := do
  let line ← (← IO.getStdin).getLine
  let some n := line.trimAscii.toString.toNat?
    | IO.eprintln "expected a natural number" *> pure 1
  if n > 2^31 - 2 then
    IO.eprintln "N exceeds 2147483646"
    return 1
  let m := runToEnd ((load 32 CountingPrimes.prog 128 []).setReg 10 (BitVec.ofNat 32 n))
  IO.print m.output
  match m.status with
  | .exited code => pure code.toNat.toUInt32
  | _ => IO.eprintln "fault" *> pure 1
