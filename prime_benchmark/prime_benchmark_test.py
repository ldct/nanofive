"""Reproduce the common-input measurements and the disclosed Plummer failure."""

import hashlib
import json

from prime_benchmark import HERE, PROGRAMS, path, reference_count, run_one


def main():
    fixture = json.loads((HERE / "prime_benchmark_results.json").read_text())
    assert fixture["n"] == 1000 and fixture["expected_count"] == 168
    assert reference_count(fixture["n"]) == fixture["expected_count"]
    before = {name: hashlib.sha256(path(name).read_bytes()).digest()
              for name in PROGRAMS}
    rows = fixture["results"]
    assert len(rows) == 10
    assert {row["program"] for row in rows} == set(PROGRAMS)
    assert sum(row["variant"] == "bounds-repaired" for row in rows) == 1
    failures = [row for row in rows if row["status"] != "ok"]
    assert len(failures) == 1
    assert failures[0]["program"] == "plummer_sieve.py"
    assert failures[0]["variant"] == "input-adapted"
    assert failures[0]["pc"] == 776
    unsupported = run_one("plummer_sieve.py", 1022, reference_count(1022), 100)
    assert unsupported["status"] == "not-run" and unsupported["instructions"] == 0
    assert "oscillates" in unsupported["error"]
    for expected in rows:
        actual = run_one(expected["program"], 1000, 168, 100_000_000,
                         expected["variant"] == "bounds-repaired")
        for key in ("status", "instructions", "count", "pc", "output", "proved"):
            assert actual.get(key) == expected.get(key), (expected["program"], key)
        print(f"{expected['program']} ({expected['variant']}): reproduced", flush=True)
    assert before == {name: hashlib.sha256(path(name).read_bytes()).digest()
                      for name in PROGRAMS}, "benchmark changed original program files"
    print("All nine programs and separate repair reproduced; original sources unchanged.")


if __name__ == "__main__":
    main()
