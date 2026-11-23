# runs two_sat on every case in tests/, checks the answer and times it
# usage: python run_tests.py [--quick] [--repeat N] [--layout]
# --layout also times formulas whose clauses only join nearby variables, before
# and after renaming the variables at random (layout.csv). Both have the same
# graph up to renaming, so this separates the algorithm from memory effects

import argparse
import csv
import gc
import glob
import os
import random
import sys
import time
from generate_tests import RATIO, SIZES, local_formula, renamed
from two_sat import refutation, two_sat

HERE = os.path.dirname(os.path.abspath(__file__))

def load_case(path):
    expected = n = m = None
    clauses = []
    with open(path) as f:
        for line in f:
            if line.startswith("c expected "):
                expected = {"SATISFIABLE": True, "UNSATISFIABLE": False}[line.split()[2]]
            elif line.startswith("p cnf "):
                n, m = map(int, line.split()[2:4])
            elif line[0] not in "c\n":
                a, b, zero = line.split()
                assert zero == "0", f"{path}: clause line {line!r}"
                clauses.append((int(a), int(b)))
    assert len(clauses) == m, f"{path}: expected {m} clauses, read {len(clauses)}"
    return n, clauses, expected

def best_time(fn, repeat, min_total=1.0):
    times = []
    result = None
    gc.collect()
    gc.disable()
    try:
        while len(times) < repeat or (sum(times) < min_total and len(times) < 1000):
            t0 = time.perf_counter()
            result = fn()
            times.append(time.perf_counter() - t0)
    finally:
        gc.enable()
    return min(times), len(times), result

def check(n, clauses, res, expected):
    # a satisfiable answer must make every clause true. An unsatisfiable one
    # must come with x => ... => not x => ... => x where each step u => v is
    # the clause (not u or v), which proves no assignment works
    if res.satisfiable != expected:
        return False
    if res.satisfiable:
        a = res.assignment
        return len(a) == n and all(
            a[abs(x) - 1] == (x > 0) or a[abs(y) - 1] == (y > 0) for x, y in clauses)
    k = res.conflict
    chain = refutation(n, clauses, k)
    if not chain or chain[0] != k or chain[-1] != k or -k not in chain:
        return False
    have = {frozenset(c) for c in clauses}
    return all(frozenset((-u, v)) in have for u, v in zip(chain, chain[1:]))

def layout_sweep(sizes, repeat):
    rows = []
    print("\nsame graphs, two memory layouts:")
    print(f"{'n':>9}{'n + m':>10}{'comps':>10}{'local (s)':>12}{'renamed (s)':>13}"
          f"{'us/(n+m)':>10}{'renamed':>9}")
    for i, n in enumerate(sizes, start=1):
        rng = random.Random(7000 + i)
        local = local_formula(n, RATIO * n, rng)
        shuffled = renamed(n, local, rng)
        t1, runs1, r1 = best_time(lambda: two_sat(n, local), repeat)
        t2, runs2, r2 = best_time(lambda: two_sat(n, shuffled), repeat)
        assert r1.satisfiable and r2.satisfiable and r1.components == r2.components
        assert check(n, local, r1, True) and check(n, shuffled, r2, True)
        size = n + len(local)
        print(f"{n:>9}{size:>10}{r1.components:>10}{t1:>12.4f}{t2:>13.4f}"
              f"{t1 / size * 1e6:>10.3f}{t2 / size * 1e6:>9.3f}")
        rows.append({"n": n, "m": len(local), "size": size, "components": r1.components,
                     "seconds_local": t1, "runs_local": runs1,
                     "seconds_renamed": t2, "runs_renamed": runs2})
    return rows

def write_csv(name, rows):
    with open(os.path.join(HERE, name), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader()
        w.writerows(rows)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repeat", type=int, default=3)
    ap.add_argument("--quick", action="store_true", help="skip cases 9 and 10")
    ap.add_argument("--layout", action="store_true")
    args = ap.parse_args()

    cases = sorted(glob.glob(os.path.join(HERE, "tests", "case*.cnf")))
    if not cases:
        sys.exit("no test cases found, run generate_tests.py first")
    if args.quick:
        cases = cases[:8]

    rows = []
    failed = 0
    print(f"{'case':<8}{'n':>9}{'m':>10}{'n + m':>10}{'comps':>10}{'time (s)':>11}"
          f"{'runs':>6}   result")
    for path in cases:
        name = os.path.basename(path)[:-4]
        n, clauses, expected = load_case(path)
        t, runs, res = best_time(lambda: two_sat(n, clauses), args.repeat)
        ok = check(n, clauses, res, expected)
        failed += not ok
        answer = "SAT" if res.satisfiable else "UNSAT"
        print(f"{name:<8}{n:>9}{len(clauses):>10}{n + len(clauses):>10}{res.components:>10}"
              f"{t:>11.4f}{runs:>6}   {'PASS' if ok else 'FAIL'} "
              f"({answer}, expected {'SAT' if expected else 'UNSAT'})")
        rows.append({"case": name, "n": n, "m": len(clauses), "size": n + len(clauses),
                     "satisfiable": res.satisfiable, "components": res.components,
                     "seconds": t, "runs": runs, "passed": ok})

    # separate pass, so these big allocations can't slow the timings above
    if args.layout:
        write_csv("layout.csv", layout_sweep(SIZES[:8] if args.quick else SIZES, args.repeat))

    write_csv("results.csv", rows)
    print(f"\n{len(rows) - failed}/{len(rows)} passed, timings in results.csv")
    sys.exit(1 if failed else 0)

if __name__ == "__main__":
    main()
