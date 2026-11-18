# RV64I mod-6 wheel sieve

```sh
printf '100\n' | python3 counting_primes/odd_wheel/counting_primes_odd_wheel.py
# 25
python3 counting_primes/odd_wheel/counting_primes_odd_wheel_test.py
```

This program uses 82 base instructions (328 bytes). The
host supplies `N` in `a0` and allocates zeroed memory; the machine code
computes the count, prints it, and exits. The supported range is
`0 ≤ N < 10^11`; memory use is proportional to `N`, about 33 GB near the
upper limit.

Flag `i`, at address `512 + i`, represents `(3*i+1)|1`: only the residues
1 and 5 modulo 6 are stored. Startup computes the number of live flags
using shifts and adds in place of division. Marking visits two progressions
for each candidate, both starting at or above its square. The special
pass for 5 marks four flags with two word stores, before any other pass
can set the intervening bytes. The marking loops test after storing, so
the buffer includes slack for marks beyond the last live flag.

The count visits the live flags in reverse, 16 per round, and subtracts
their sum from the number of live flags plus one (exclude 1, include 2
and 3). The final round can read up to 15 zero bytes just below address
512. At most 31 rounds contribute to any one four-lane accumulator,
so no lane carries into the next.

At `N = 1,000`, the Python emulator measures 725 instructions, counting
each modeled `ecall` as one instruction.

## Lean proof

`TinyFive.CountingPrimesOddWheel.correct` proves that the unchanged
loaded machine code exits with status zero and prints exactly `π(N)`
and a newline, for every `N < 10^11`. The proof covers the shift-add
division, the capacity of the actual allocation (including unconditional
stores past the live flags), and the signed cursor and byte-lane arithmetic
of the count. `correct_uniform_fuel` provides a single fuel value for the
whole range. The instruction bound is intentionally loose; it is not a
performance estimate.

The theorem is about `TinyFive.Machine`, not a formal refinement of the
Python emulator or an implementation of RISC-V. The test checks that the
proof and Python load the same words, and compares both executable models
against an independent sieve.
