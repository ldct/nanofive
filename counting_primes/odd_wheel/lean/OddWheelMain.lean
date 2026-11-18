import CountingPrimesOddWheel

open TinyFive

private partial def runToEnd (m : Machine 64) : Machine 64 :=
  if m.status = .running then runToEnd (step m) else m

/-- The input adapter for the executable machine model. -/
def main : IO UInt32 := do
  let line ← (← IO.getStdin).getLine
  let some n := line.trimAscii.toString.toNat?
    | IO.eprintln "expected a natural number" *> pure 1
  if n ≥ 10^11 then
    IO.eprintln "N must be below 10^11"
    return 1
  let m := runToEnd (CountingPrimesOddWheel.initial n)
  IO.print m.output
  match m.status with
  | .exited code => pure code.toNat.toUInt32
  | _ => IO.eprintln "fault" *> pure 1
