# makes tests/case01.cnf .. case10.cnf (DIMACS cnf)
# case k has n = 2^(k+10) variables and m = 2n random 2-literal clauses over
# distinct variables. odd cases have a planted solution: clauses are drawn at
# random and kept only if a hidden random assignment satisfies them, so the
# formula is satisfiable. even cases are uniform random, which at m = 2n is
# unsatisfiable (random 2-SAT turns unsatisfiable past m = n)
#
# the expected answer comes from oracle_satisfiable, unit propagation in the
# style of Even, Itai & Shamir (1976, the paper's [3]). It never builds strong
# components and shares no code with two_sat.py

import os
import random

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "tests")

SIZES = [2 ** k for k in range(11, 21)]
RATIO = 2  # clauses per variable

def random_clause(n, rng):
    i, j = rng.sample(range(1, n + 1), 2)
    return (i if rng.random() < 0.5 else -i, j if rng.random() < 0.5 else -j)

def planted_formula(n, m, rng):
    hidden = [None] + [rng.random() < 0.5 for _ in range(n)]
    clauses = []
    while len(clauses) < m:
        a, b = random_clause(n, rng)
        if hidden[abs(a)] == (a > 0) or hidden[abs(b)] == (b > 0):
            clauses.append((a, b))
    return clauses

def uniform_formula(n, m, rng):
    return [random_clause(n, rng) for _ in range(m)]

def local_formula(n, m, rng, window=8):
    # for run_tests.py --layout: a planted formula whose clauses only join
    # variables at most `window` apart, listed in order of their first variable
    hidden = [None] + [rng.random() < 0.5 for _ in range(n)]
    clauses = []
    while len(clauses) < m:
        i = rng.randint(1, n - window)
        j = i + rng.randint(1, window)
        a, b = (i if rng.random() < 0.5 else -i), (j if rng.random() < 0.5 else -j)
        if hidden[i] == (a > 0) or hidden[j] == (b > 0):
            clauses.append((a, b))
    clauses.sort(key=lambda c: abs(c[0]))
    return clauses

def renamed(n, clauses, rng):
    # the same formula with the variables renamed at random and the clauses
    # shuffled. The implication graph is isomorphic, so the algorithm does the
    # same work, but now it touches memory in random order
    name = list(range(1, n + 1))
    rng.shuffle(name)
    name.insert(0, 0)
    out = [(name[a] if a > 0 else -name[-a], name[b] if b > 0 else -name[-b])
           for a, b in clauses]
    rng.shuffle(out)
    return out

def oracle_satisfiable(n, clauses):
    # pick an unset variable x and try x = true and x = false at the same
    # time, one propagation step each in turn. Keep whichever finishes first
    # without a contradiction: every clause it touched is now true and the
    # rest are untouched, so the formula left is satisfiable iff the old one
    # was. If both sides hit a contradiction, nothing satisfies the formula.
    # Running the sides in turn keeps the total work linear
    need = {}  # literal t -> literals that must be true once t is true
    for clause in clauses:
        a, b = (clause[0], clause[0]) if len(clause) == 1 else clause
        need.setdefault(-a, []).append(b)
        need.setdefault(-b, []).append(a)
    value = [None] * (n + 1)

    def propagate(start):
        # generator: one yield per step, returns the new values or None
        new = {abs(start): start > 0}
        todo = [start]
        while todo:
            t = todo.pop()
            for o in need.get(t, ()):
                k = abs(o)
                have = value[k] if value[k] is not None else new.get(k)
                if have is None:
                    new[k] = o > 0
                    todo.append(o)
                elif have != (o > 0):
                    return None
            yield
        return new

    for k in range(1, n + 1):
        if value[k] is not None:
            continue
        sides = [propagate(k), propagate(-k)]
        won = None
        while sides and won is None:
            for side in list(sides):
                try:
                    next(side)
                except StopIteration as stop:
                    if stop.value is None:
                        sides.remove(side)
                    else:
                        won = stop.value
                        break
        if won is None:
            return False
        for var, val in won.items():
            value[var] = val
    return True

def write_cnf(path, n, clauses, comment):
    with open(path, "w") as f:
        for line in comment:
            f.write(f"c {line}\n")
        f.write(f"p cnf {n} {len(clauses)}\n")
        f.write("".join(f"{a} {b} 0\n" for a, b in clauses))

def main():
    os.makedirs(OUT, exist_ok=True)
    for i, n in enumerate(SIZES, start=1):
        seed = 6000 + i
        rng = random.Random(seed)
        m = RATIO * n
        planted = i % 2 == 1
        clauses = planted_formula(n, m, rng) if planted else uniform_formula(n, m, rng)
        expected = oracle_satisfiable(n, clauses)
        assert expected == planted, f"case {i}: expected {planted}, oracle says {expected}"
        kind = "planted solution" if planted else "uniform random"
        answer = "SATISFIABLE" if expected else "UNSATISFIABLE"
        path = os.path.join(OUT, f"case{i:02d}.cnf")
        write_cnf(path, n, clauses, [
            f"2-sat case {i}: {n} variables, {m} clauses, {kind}, seed {seed}",
            f"expected {answer}",
        ])
        print(f"wrote {os.path.relpath(path, HERE)}  ({n} variables, {m} clauses, {answer})")

if __name__ == "__main__":
    main()
