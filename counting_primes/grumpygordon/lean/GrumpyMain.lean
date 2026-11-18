import GrumpyGordon

/-- One natural number per input line, one prime count per output line. -/
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let some n := line.trimAscii.toString.toNat? | IO.eprintln "expected a natural number"; return 1
    IO.println (TinyFive.GrumpyGordon.primePi n)
  return 0
