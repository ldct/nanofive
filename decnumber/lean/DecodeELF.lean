import TinyFive.Machine

/-! Read words from the Python ELF runner and report only those that Lean cannot decode. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let some word := line.trimAscii.toString.toNat? | throw (IO.userError "expected an instruction word")
    if (TinyFive.decode 64 (BitVec.ofNat 32 word)).isNone then
      stdout.putStrLn (toString word)
