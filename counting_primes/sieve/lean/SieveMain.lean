import CountingPrimesSieve

open TinyFive

private partial def runToEnd (m : Machine 32) : Machine 32 :=
  if m.status = .running then runToEnd (step m) else m

/-- Host-side input adapter, like `counting_primes_sieve.py`. -/
def main : IO UInt32 := do
  let line ← (← IO.getStdin).getLine
  let some n := line.trimAscii.toString.toNat?
    | IO.eprintln "expected a natural number" *> pure 1
  if n > 2^30 - 1 then
    IO.eprintln "N exceeds 1073741823"
    return 1
  let m := runToEnd (CountingPrimesSieve.initial n)
  IO.print m.output
  match m.status with
  | .exited code => pure code.toNat.toUInt32
  | _ => IO.eprintln "fault" *> pure 1
