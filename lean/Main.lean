import TinyFive

open TinyFive

partial def runToEnd {w : Nat} (m : Machine w) : Machine w :=
  if m.status = .running then runToEnd (step m) else m

partial def readAll (h : IO.FS.Stream) (acc : String := "") : IO String := do
  let line ← h.getLine
  if line.isEmpty then pure acc else readAll h (acc ++ line)

/-- Run `abc101_a` on standard input, on the model of width 64 if the first argument is `64` and
of width 32 otherwise. -/
def main (args : List String) : IO UInt32 := do
  let input := (← readAll (← IO.getStdin)).toList
  let finish {w : Nat} (m : Machine w) : IO UInt32 := do
    IO.print m.output
    match m.status with
    | .exited code => pure code.toNat.toUInt32
    | _ => IO.eprintln "fault" *> pure 1
  if args.head? = some "64" then finish (runToEnd (load 64 Abc101a.prog 256 input))
  else finish (runToEnd (load 32 Abc101a.prog 256 input))
