# Common-input instruction comparison

Run every prime-counting program on **N = 1,000**, with **π(N) = 168**:

```sh
python prime_benchmark.py --n 1000 --repair-plummer --json prime_benchmark_results.json
python prime_benchmark_test.py
```

All numbers below are **measured emulator instructions**, not time estimates,
formulas, or upper bounds. The harness counts successful `machine.step()`
calls from PC 0 through exit; an instruction that faults is not counted as
successfully completed. Every successful run's printed count is independently
checked against an ordinary sieve.

| Program | Lean-proved original image? | Instructions |
|---|:---:|---:|
| `counting_primes_zjy2008.py` | no | 6,170 |
| `counting_primes_grumpygordon.py` | no | 6,270 |
| `byte_sieve.py` (input-adapted, one pass) | no | 8,493 |
| `rosetta_sieve.py` (input-adapted) | no | 11,567 |
| `counting_primes_wheel.py` | **yes** | 12,787 |
| `counting_primes_sieve.py` | **yes** | 16,301 |
| `plummer_sieve.py` (**bounds-repaired**, input-adapted) | no | 28,467 |
| `counting_primes_lpha.py` | no | 953,730 |
| `counting_primes_simple.py` | **yes** | 2,799,716 |
| `plummer_sieve.py` (input-adapted, **original logic**) | no | **fails** |

The original Plummer logic fails after **251,172 successful instructions**,
attempting an out-of-bounds load at PC 776. This is not a completed
prime-count execution and must not be ranked as one.

## Making fixed-size programs comparable

The original files are **not modified**. `prime_benchmark_fixed.py` reads their
literal machine images and applies auditable patches to an in-memory copy,
checking every old word before replacing it. Each patch and its reason is
recorded in the JSON results.

* **BYTE:** replace the fixed odd-number bounds, change ten passes to one,
  and initialize the RV32 count to one to include prime 2. There is no
  host-side correction of its calculated answer.
* **Rosetta:** change the sieve argument, initial count, and printed limit
  from 10,000 to 1,000. Its original prime-list output below 100 is retained.
* **Plummer:** set its exclusive limit to 1,001, making it count primes
  at most 1,000, and update the expected-count validation constant.
  That validation never supplies the algorithm's calculated count.

### Separate Plummer bounds repair

The small-input failure comes from unsigned underflow in the bulk-marking
bound `iStop - cumOffset`. For example, with prime 11, `iStop = 7` and
`cumOffset = 11`; the subtraction wraps instead of skipping the bulk loop.

The **separately labeled repaired run** changes one branch at PC 744:
`BLTU` to `BLT`. A negative difference then selects the existing bounded
tail loop. This is an explicit **algorithmic bounds bug fix**, not a
constant-only input adaptation. It remains unproved. The harness runs and
reports the original logic too; `--repair-plummer` does not hide its failure.

The adapter also rejects inputs for which the original Plummer integer
Newton loop oscillates; that second defect is not repaired here.

## Interpretation and limits

* All startup, program-specific input/output, validation, and exit
  instructions are included. The proved programs receive `N` in `a0`;
  the three Library Checker ports parse decimal input on the RV32 machine.
* Each `ecall` counts as one instruction; work inside the host system call
  does not. M-extension multiply/divide also count as one instruction,
  not one CPU cycle. The compiled unproved ports may use RV32M and run on
  the RV32 machine. The three proved programs use only base instructions and
  run on the RV64 machine they are proved for; the same instruction count
  would result on RV32.
* Host allocation, loading, input adaptation, and reference checking are
  excluded. Post-execution Python printing is excluded too.
* This is a whole-program comparison, not an equal-I/O kernel benchmark.
  The small common input keeps repeated-subtraction trial division practical;
  rankings can change for larger inputs. In particular, lpha's fixed-size
  scratch-array initialization is costly even at small N: profiling counted
  948,684 instructions in the loop clearing its 316,228-byte `smooth` array.
* Only the three unchanged proved images have the previously established
  Lean correctness guarantees. The new harness, fixed-input adapters, and
  optional bounds repair are tested, not formally proved.

`prime_benchmark_results.json` contains the measured counts, captured output,
proof-status labels, failure diagnostic, and exact adapter patch notes.
Unrelated programs such as factorial and ABC101 A are not prime counters
and therefore cannot perform this same workload.

## Comparison with the original Yosupo submissions

The three Library Checker ports identify their exact original submissions.
Looking them up on Yosupo gives the following reported judge summary times
(recorded with retrieval time and per-case times in
`yosupo_comparison_results.json`):

| Original submission | RV32 instructions at N=1,000 | Yosupo reported time |
|---|---:|---:|
| lpha #195894 | 953,730 | 13 ms |
| grumpygordon #50137 | 6,270 | 14 ms |
| zjy2008 #346093 | 6,170 | 15 ms |

For **these three pairs**, comparing instruction count with runtime:

* Spearman rank correlation: **−1** (the rankings are exactly reversed).
* Pearson correlation: approximately **−0.8660711**.

This is a descriptive calculation, **not an estimate of a general
instruction-count/runtime relationship**. There are only three pairs;
our counts are for small-input RV32 ports, whereas the displayed judge times
belong to the original native submissions over the judge's test suite.
The ports also changed arithmetic and target-specific optimizations.
The result shows that the current N=1,000 ranking does not predict the
reported Yosupo ranking; it does not show that more instructions generally
make code faster.

Reproduce the lookup and calculation using the same official API endpoint
as the submission pages:

```sh
python yosupo_comparison.py --json yosupo_comparison_results.json
```

The JSON records the exact official submission and API URLs, overview
metadata, and per-case timings. Timings may change if the judge rejudges
the submissions.
