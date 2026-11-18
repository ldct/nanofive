import DecNumber.Image

/-! Read words from the Python ELF runner and report only those that Lean cannot decode. -/
private def decodeStdin : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let some word := line.trimAscii.toString.toNat? | throw (IO.userError "expected an instruction word")
    if (TinyFive.decode 64 (BitVec.ofNat 32 word)).isNone then
      stdout.putStrLn (toString word)

open DecNumber.Image in
private def dumpImage : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn s!"symbol decNumberFromString {parseEntry}"
  stdout.putStrLn s!"symbol decNumberCompare {compareEntry}"
  -- Export the very byte lookup used in the proof, not a duplicate encoding.
  for (start, len) in code.map (fun (start, words) => (start, words.size * 4)) ++
      [(table.1, table.2.size)] do
    let data ← (List.range len).mapM fun offset => do
      let some b := bytes (start + offset) | throw (IO.userError "hole in proof image")
      pure (toString b.toNat)
    stdout.putStrLn s!"bytes {start} {String.intercalate " " data}"

def main : List String → IO Unit
  | [] => decodeStdin
  | ["--image"] => dumpImage
  | _ => throw (IO.userError "usage: decnumber_decode [--image]")
