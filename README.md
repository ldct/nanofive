# nanofive

A RISC-V RV32IM / RV64IM emulator in Python (`machine.py`), programs that run
on it, and Lean proofs that some of those programs' machine code is correct.

## Layout

Shared, at the top level:

- `machine.py` — the emulator; `tests.py` and `tests64.py` test it;
  `factorial.py` is a minimal example
- `elf.py` — loads compiled RISC-V ELF files into the emulator
- `asm/` — startup code, system calls and linker script for compiled C programs
- `lean/TinyFive/` — the Lean model of the machine (`Machine.lean`) and lemmas
  used by more than one proof: the prime-counting specification (`Primes`),
  trial-division budgets (`TrialDivisionCost`), sieve facts (`SieveMath`) and
  memory lemmas (`SieveMemory`)
- `lakefile.toml` — one Lake package for all the Lean code

One folder per project, with its tests, and its proofs in
`<project>/lean/` (`counting_primes/<variant>/lean/` for the prime counters):

| Project | What it is |
|---|---|
| `abc101a/` | AtCoder ABC101 A in RV32I machine code (assembled in Python), proved correct |
| `counting_primes/` | six proved prime counters: `trial_division/`, `sieve/`, `wheel/` (mod 30), `odd_sieve/`, `lucy/` (O(√N) memory), and `odd_wheel/` (mod 6) |
| `prime_benchmark/` | instruction counts of `trial_division/`, `sieve/`, `wheel/` and six third-party prime programs |
| `newlib/` | C with newlib's printf and malloc, on RV32 and RV64 |
| `ratpoints/` | Michael Stoll's ratpoints, compiled C with GMP |
| `urlh/` | jwerle/url.h, compiled C, with a proof of its `decode_percent` |
| `decnumber/` | jq's decNumber on RV64IM, with differential tests and binary proofs of status clearing, bounded exact parsing and comparison |
| `tweetnacl/` | TweetNaCl on RV64IM, with Lean proofs of the linked Salsa20 and HSalsa20 cores and emulator tests |
| `nacl/` | NaCl 20110221's reference Salsa20 core on RV64IM, proved against the TweetNaCl Salsa20 specification |
| `libsodium/` | libsodium 1.0.22's `crypto_core_salsa20` on RV64IM, proved against the same specification |
| `nettle/` | Nettle 3.10.2's `_nettle_salsa20_core` on RV64IM, proved against the same specification |

## Running

Python scripts run from any directory, e.g. `python3 urlh/urlh_test.py`.
`lake build` at the root builds every proof and the executable Lean models the
tests compare against.
