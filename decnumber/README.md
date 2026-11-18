# jq's decNumber on NanoFive

Run from the repository root:

```sh
python3 decnumber/decnumber_test.py
lake build DecNumber TinyFive
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

## Binary proofs

`DecContextClear.clear_status` proves that the five instructions of
`decContextClearStatus` clear exactly the low-32-bit mask in the status word at
offset 20, return the context pointer to the caller, and write no other memory.
The theorem is for any register file and memory satisfying the instruction-fetch,
writable status-slot, and return-instruction nonaliasing assumptions. The runner
checks the linked ELF symbol against the proved instruction words.

`DecNumber.Bounded` covers two public entry points in the same linked ELF:

| Theorem | Covered inputs | Result and instruction bound |
|---|---|---|
| `parse_exact` | All 220 NUL-terminated spellings `-?[0-9](\.[0-9])?`, including `-0` and `-0.0` | Exact sign, significant digit count, coefficient in one base-1000 unit, and exponent (0 or -1); returns in at most 160 instructions |
| `compare_exact` | All 400 ordered pairs of finite exponent-zero single-digit representations, including both signs of zero | A decNumber representing -1, 0, or +1 according to exact rational order; returns in at most 153 instructions, including internal helper calls |

`exact_value` is a spec-only lemma identifying the parser's expected
representation with the rational value of the input spelling. The two binary
theorems additionally establish return to `ra` with `a0` pointing to the result,
preservation of `sp`, `gp`, `tp`, `ra`, and all `s` registers for the stated
initial register file, zero context status, and no changes to I/O or memory
capacity. Stores are confined to the 11 field bytes of the 12-byte output
object and the 144-byte (parse) or 168-byte (compare) stack frame. The output
padding, context, inputs, and code are unchanged.

**Call assumptions.** The model's 1 MiB memory uses fixed, aligned, disjoint
addresses: output `0x80000`, text/left operand `0x80020`, right operand
`0x80040`, context `0x80060`, entry `sp = 0x90000`, and return PC `0x100`.
`abi` fixes the argument registers and gives the other registers specific
initial values; arbitrary register values or relocatable addresses are not
proved. The context is jq's literal context (precision 147483648, exponent
limits ±999999999, round half up, zero traps/status/clamp). Memory need only
agree with the input, context fields, and sparse code/table image; the stack,
output and all unspecified memory may contain arbitrary bytes.

**Trust and reproducibility.** `Replay.untilReturn_sound` proves that successful
sparse replay corresponds to `TinyFive.run` on every agreeing memory. The replay
fails on unknown reads/fetches and checks each store's byte range. The finite
certificates use Lean's `native_decide`, so the bounded theorems trust Lean's
native evaluator in addition to its kernel and the machine model; there are no
`sorry`s. The runner compares the data exported from `DecNumber.Image` with the
linked ELF's entry symbols and exact code/table bytes. The image is specific to
this build (GCC 13.2.0 and the pinned source/flags/harness); a changed layout or
byte is rejected, not silently accepted. These are binary proofs in the Lean
model, not proofs of GCC, the Python emulator, or physical RISC-V hardware.

## Testing and next steps

The differential run executes 2,627,378 instructions and visits 2,088 distinct
library PCs. All those words now pass the actual Lean decoder (previously 315
were unsupported). `TinyFive.MachineRV64Tests` separately exercises word
truncation/sign extension, zero divisors and signed overflow, high
multiplication, load sign/zero extension, and reserved encodings. Neither test
establishes semantic coverage for all decNumber paths.

The next proof targets are to remove the fixed-register/address restrictions,
verify bounded comparisons across different exponents, and replace exhaustive
replay with symbolic loop/branch lemmas for longer inputs (or kernel-checked
replay certificates for finite domains). Neither binary theorem covers
rounding, status propagation on failures, allocation, NaNs or infinities. A
proof of jq behavior would additionally need its lexer, wrappers and binary64
conversion.
