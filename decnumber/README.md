# jq's decNumber on NanoFive

Run from the repository root:

```sh
python3 decnumber/decnumber_test.py
lake build DecNumber
```

The test fetches jq `jq-1.8.2` at `34f7186b86743a083a589741b6cea95293524108`.
Use `--jq /path/to/jq` to build an existing checkout and `--elf /tmp/decnumber.elf`
to retain the binary. It compiles jq's unmodified `decNumber.c` and
`decContext.c` at `-O2 -march=rv64im -mabi=lp64` with
`riscv64-unknown-elf-gcc`, links them with the shared startup code and vendored
newlib subset, and runs the ELF in `machine64`. The harness supplies `strcpy`
and a fatal `raise` fallback; its contexts disable traps.

With GCC 13.2.0, all 222 cases passed against Python `Decimal`: 77 parse/format,
72 compare, and 73 add (17-digit precision, half-even). The oracle checks
formatted output, status flags, and representation fields including finite
coefficient units. Inputs include signed zero, malformed strings, special
values, large exponents, coefficients up to 160 digits, and rounding ties.
The harness uses jq's literal parse/compare context, **not** jq's JSON lexer,
number allocation, or decimal-to-binary conversion. The addition test is for
the library API; jq's ordinary arithmetic uses binary64.

## Proof feasibility

`lean/DecContextClear.lean` proves that the five instructions of
`decContextClearStatus` clear exactly the low-32-bit mask in the status word at
offset 20, return the context pointer to the caller, and write no other memory.
The theorem is for any register file and memory satisfying the instruction-fetch,
writable status-slot, and return-instruction nonaliasing assumptions. The runner
checks the linked ELF symbol against the proved instruction words. This is a
binary proof in Lean's machine model, not a proof of GCC or of Python's emulator.

The emulator executed 2,627,378 instructions. In the library routines it
visited 2,088 distinct instruction addresses, 315 of which use instructions
missing from the Lean model (including `addiw`, `mulw`, `divw`, `lwu` and
word shifts). That count is dynamic coverage, not an inventory of all
instructions needed for a proof. The runner reports the breakdown.

A useful next target is **exact parse and numerical comparison for a bounded
subset of finite JSON numbers**. Start with a spec for sign, base-1000
coefficient units and the decimal exponent, and make input length, exponent
range, output capacity and aliasing explicit. After extending the Lean decoder
and semantics, prove the fixed-buffer parse and compare paths separately,
including termination and memory bounds. Compare against exact mathematical
value, not the original spelling: formatting can normalize a literal.

Correct rounding across contexts, NaNs and infinities, status propagation,
and memory allocation make the general library a much larger project. A proof
of jq behavior would additionally need to cover its wrappers and binary64
conversion. The current tests and theorem do not establish those properties.
