"""Pair the three original Yosupo submissions with our measured RV32 counts.

python yosupo_comparison.py --json yosupo_comparison_results.json

The official API is the same public endpoint used by the submission pages.
This intentionally labels the comparison as mismatched-workload: N=1000
RV32 ports versus the original submissions' judge-reported summary times.
"""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
from statistics import StatisticsError, correlation
import urllib.request

HERE = Path(__file__).resolve().parent
SUBMISSIONS = (
    ("counting_primes_lpha.py", 195894),
    ("counting_primes_grumpygordon.py", 50137),
    ("counting_primes_zjy2008.py", 346093),
)


def ranks(values):
    """Average ranks, including possible ties in rounded judge times."""
    return [(1 + sum(x < value for x in values) +
             sum(x <= value for x in values)) / 2 for value in values]


def maybe_correlation(xs, ys):
    try:
        return correlation(xs, ys)
    except StatisticsError:
        return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, default=HERE / "yosupo_comparison_results.json")
    args = parser.parse_args()
    benchmark = json.loads((HERE / "prime_benchmark_results.json").read_text())
    measured = {row["program"]: row for row in benchmark["results"]
                if row["status"] == "ok" and row["variant"] == "original"}
    rows = []
    for program, sid in SUBMISSIONS:
        api = f"https://v3.api.judge.yosupo.jp/submissions/{sid}"
        with urllib.request.urlopen(api, timeout=30) as response:
            data = json.load(response)
        overview = data["overview"]
        assert overview["id"] == sid
        assert overview["problem_name"] == "counting_primes" and overview["status"] == "AC"
        row = {
            "program": program,
            "submission_id": sid,
            "submission_url": f"https://judge.yosupo.jp/submission/{sid}",
            "api_url": api,
            "rv32_instructions": measured[program]["instructions"],
            "overview": overview,
            "case_times_seconds": {case["case"]: case["time"]
                                   for case in data["case_results"]},
        }
        rows.append(row)
        print(f"{overview['user_name']:14} #{sid:<7} "
              f"{row['rv32_instructions']:>10,} RV32 instructions; "
              f"{1000 * overview['time']:g} ms judge time")
    xs = [row["rv32_instructions"] for row in rows]
    ys = [row["overview"]["time"] for row in rows]
    statistics = {
        "pairs": len(rows),
        "pearson_instructions_vs_runtime": maybe_correlation(xs, ys),
        "spearman_instructions_vs_runtime": maybe_correlation(ranks(xs), ranks(ys)),
    }
    result = {
        "retrieved_at_utc": datetime.now(timezone.utc).isoformat(),
        "rv32_input_n": benchmark["n"],
        "warning": "Only three pairs, different workloads and architectures/ports; "
                   "not a matched-input estimate of a general correlation.",
        "records": rows,
        "statistics": statistics,
    }
    args.json.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(statistics, indent=2))
    print(result["warning"])


if __name__ == "__main__":
    main()
