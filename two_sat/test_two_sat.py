# extra correctness tests, run with: python -m unittest -v test_two_sat

import itertools
import os
import random
import tempfile
import unittest
from collections import Counter
from generate_tests import oracle_satisfiable, planted_formula, uniform_formula
from two_sat import (FIGURE_1, evaluate_qbf, implication_graph, literal, read_dimacs,
                     refutation, strong_components, two_sat, vertex)

NAMES = {1: "a", 2: "b", 3: "c", 4: "d"}

def name(lit):
    return NAMES[abs(lit)] + ("" if lit > 0 else "'")

def true_under(assignment, clause):
    return any(assignment[abs(l) - 1] == (l > 0) for l in clause)

def brute_sat(n, clauses):
    return any(all(true_under(bits, c) for c in clauses)
               for bits in itertools.product((False, True), repeat=n))

def brute_qbf(quantifiers, clauses):
    def value(i, bits):
        if i == len(quantifiers):
            return all(true_under(bits, c) for c in clauses)
        branches = (value(i + 1, bits + [b]) for b in (False, True))
        return all(branches) if quantifiers[i] == "A" else any(branches)
    return value(0, [])

def random_formula(rng, n, m):
    # repeated variables, tautologies, duplicates and one-literal clauses too
    clauses = []
    for _ in range(m):
        a = rng.randint(1, n) * rng.choice((1, -1))
        if rng.random() < 0.1:
            clauses.append((a,))
        else:
            clauses.append((a, rng.randint(1, n) * rng.choice((1, -1))))
    return clauses

def reachable(adj, s):
    seen = {s}
    todo = [s]
    while todo:
        for w in adj[todo.pop()]:
            if w not in seen:
                seen.add(w)
                todo.append(w)
    return seen

def valid_refutation(clauses, k, chain):
    have = {frozenset(c) for c in clauses}
    return (chain[0] == k and chain[-1] == k and -k in chain
            and all(frozenset((-u, v)) in have for u, v in zip(chain, chain[1:])))

def published_qbf(quantifiers, clauses):
    # the paper's evaluation algorithm (p. 123, Steps 1-6) exactly as printed,
    # with "predecessor" meaning an edge into S, as defined on p. 122
    n = len(quantifiers)
    adj = implication_graph(n, clauses)
    comp, count = strong_components(adj)
    members = [[] for _ in range(count)]
    succ = [set() for _ in range(count)]
    pred = [set() for _ in range(count)]
    for v in range(2 * n):
        members[comp[v]].append(v)
        for w in adj[v]:
            if comp[v] != comp[w]:
                succ[comp[v]].add(comp[w])
                pred[comp[w]].add(comp[v])
    mark = [None] * count
    for s in range(count):
        if mark[s]:                                                     # Step 1
            continue
        univ = [v // 2 + 1 for v in members[s] if quantifiers[v // 2] == "A"]
        if any(mark[t] in ("false", "contingent") for t in succ[s]):
            if univ:                                                    # Step 2
                return False
            mark[s] = "false"
        elif len(univ) >= 2:                                            # Step 3
            return False
        elif univ:                                                      # Step 4
            if any(quantifiers[v // 2] == "E" and v // 2 + 1 < univ[0] for v in members[s]):
                return False
            mark[s] = "contingent"
        else:
            mark[s] = "true"
        s_bar = comp[members[s][0] ^ 1]
        if s_bar == s:                                                  # Step 5
            return False
        if mark[s] in ("contingent", "false") and s_bar in pred[s]:     # Step 6
            return False
        mark[s_bar] = {"true": "false", "contingent": "contingent", "false": "true"}[mark[s]]
    return True

class TwoSatTests(unittest.TestCase):

    def test_figure_1_graph(self):
        # the 10 edges drawn in the paper's Fig. 1
        adj = implication_graph(4, FIGURE_1)
        edges = Counter((name(literal(v)), name(literal(w))) for v in range(8) for w in adj[v])
        self.assertEqual(edges, Counter([
            ("a'", "b"), ("b'", "a"), ("b'", "c'"), ("c", "b"), ("b", "d'"),
            ("d", "b'"), ("b'", "d"), ("d'", "b"), ("d'", "a"), ("a'", "d")]))

    def test_figure_1_components(self):
        comp, count = strong_components(implication_graph(4, FIGURE_1))
        groups = {}
        for v in range(8):
            groups.setdefault(comp[v], set()).add(name(literal(v)))
        self.assertEqual(count, 6)
        self.assertEqual(sorted(map(sorted, groups.values())),
                         [["a"], ["a'"], ["b", "d'"], ["b'", "d"], ["c"], ["c'"]])
        res = two_sat(4, FIGURE_1)
        self.assertTrue(res.satisfiable)
        self.assertTrue(all(true_under(res.assignment, c) for c in FIGURE_1))

    def test_duality_property(self):
        # G(F) is isomorphic to G(F) with edges reversed and names complemented
        rng = random.Random(1)
        for _ in range(300):
            n = rng.randint(1, 10)
            adj = implication_graph(n, random_formula(rng, n, rng.randint(0, 25)))
            edges = Counter((v, w) for v in range(2 * n) for w in adj[v])
            self.assertEqual(edges, Counter((w ^ 1, v ^ 1) for v, w in edges.elements()))

    def test_components_against_reachability(self):
        # any directed graph, not just implication graphs: same component iff
        # mutually reachable, and generated in reverse topological order
        rng = random.Random(2)
        for _ in range(500):
            N = rng.randint(1, 14)
            adj = [[rng.randrange(N) for _ in range(rng.randint(0, 3))] for _ in range(N)]
            comp, count = strong_components(adj)
            reach = [reachable(adj, v) for v in range(N)]
            self.assertEqual(set(comp), set(range(count)))
            for v in range(N):
                for w in range(N):
                    self.assertEqual(comp[v] == comp[w], w in reach[v] and v in reach[w])
                for w in adj[v]:
                    self.assertGreaterEqual(comp[v], comp[w])

    def test_each_edge_read_once(self):
        # the O(n + m) bound needs the DFS to look at every edge exactly once.
        # Count the reads, since a re-scan would give right answers, just slowly
        reads = [0]

        class Counted(list):
            def __getitem__(self, i):
                reads[0] += 1
                return list.__getitem__(self, i)

        rng = random.Random(9)
        for n in (1, 10, 1000, 20000):
            adj = implication_graph(n, uniform_formula(n, 2 * n, rng) if n > 1 else [(1, -1)])
            reads[0] = 0
            strong_components([Counted(edges) for edges in adj])
            self.assertEqual(reads[0], sum(map(len, adj)))
        star = [Counted(range(1, 5001))] + [Counted() for _ in range(5000)]
        reads[0] = 0
        strong_components(star)
        self.assertEqual(reads[0], 5000)

    def test_against_brute_force(self):
        rng = random.Random(3)
        seen = Counter()
        for _ in range(4000):
            n = rng.randint(1, 8)
            clauses = random_formula(rng, n, rng.randint(0, 3 * n))
            res = two_sat(n, clauses)
            self.assertEqual(res.satisfiable, brute_sat(n, clauses), clauses)
            seen[res.satisfiable] += 1
            if res.satisfiable:
                self.assertEqual(len(res.assignment), n)
                self.assertTrue(all(true_under(res.assignment, c) for c in clauses))
            else:
                k = res.conflict
                self.assertEqual(res.comp[vertex(k)], res.comp[vertex(-k)])
                self.assertTrue(valid_refutation(clauses, k, refutation(n, clauses, k)))
        self.assertGreater(min(seen.values()), 1000)  # plenty of both answers

    def test_marking_matches_component_order(self):
        # S is marked before S-bar exactly when it is generated first, so x_k
        # is true iff its component number is smaller than not x_k's
        rng = random.Random(4)
        for _ in range(500):
            n = rng.randint(1, 30)
            clauses = random_formula(rng, n, rng.randint(0, 2 * n))
            res = two_sat(n, clauses)
            if res.satisfiable:
                self.assertEqual(res.assignment, [res.comp[2 * k] < res.comp[2 * k + 1]
                                                  for k in range(n)])

    def test_edge_cases(self):
        self.assertEqual(two_sat(0, []).assignment, [])
        self.assertTrue(two_sat(3, []).satisfiable)                 # no clauses
        self.assertEqual(two_sat(1, [(1, -1)]).satisfiable, True)  # tautology
        self.assertEqual(two_sat(2, [(2,)]).assignment[1], True)    # unit clause
        self.assertEqual(two_sat(2, [(-2, -2)]).assignment[1], False)
        res = two_sat(1, [(1, 1), (-1, -1)])
        self.assertEqual((res.satisfiable, res.conflict), (False, 1))
        self.assertTrue(two_sat(2, [(1, 2)] * 5).satisfiable)       # duplicates
        res = two_sat(4, FIGURE_1 + [(-2, 4), (2, -4)])  # b and b' merge
        self.assertFalse(res.satisfiable)
        for bad in [(), (1, 2, 3), (0, 1), (5, 1), (1, -5)]:
            with self.assertRaises(ValueError):
                two_sat(4, [bad])

    def test_long_chain(self):
        # x1 is forced true, x1 => x2 => ... => xn, and xn => not x1. The DFS
        # goes n deep, far past Python's recursion limit
        n = 200000
        clauses = [(1,)] + [(-i, i + 1) for i in range(1, n)] + [(-n, -1)]
        res = two_sat(n, clauses)
        self.assertFalse(res.satisfiable)
        chain = refutation(n, clauses, res.conflict)
        self.assertTrue(valid_refutation(clauses, res.conflict, chain))
        res = two_sat(n, clauses[1:])  # without the unit clause, x1 = false works
        self.assertTrue(res.satisfiable)
        self.assertTrue(all(true_under(res.assignment, c) for c in clauses[1:]))

    def test_oracle_against_brute_force(self):
        rng = random.Random(5)
        for _ in range(3000):
            n = rng.randint(1, 8)
            clauses = random_formula(rng, n, rng.randint(0, 3 * n))
            self.assertEqual(oracle_satisfiable(n, clauses), brute_sat(n, clauses), clauses)

    def test_matches_oracle_near_threshold(self):
        # at these sizes random 2-SAT is about as likely to be satisfiable as
        # not near m = 1.15n (the threshold is m = n only as n -> infinity)
        rng = random.Random(6)
        seen = Counter()
        for _ in range(60):
            n = rng.randint(200, 3000)
            clauses = uniform_formula(n, int(1.15 * n), rng)
            res = two_sat(n, clauses)
            self.assertEqual(res.satisfiable, oracle_satisfiable(n, clauses))
            seen[res.satisfiable] += 1
        self.assertGreater(min(seen.values()), 5)
        for _ in range(10):
            clauses = planted_formula(3000, 6000, rng)
            self.assertTrue(two_sat(3000, clauses).satisfiable)

    def test_read_dimacs(self):
        text = "c comment\np cnf 3 4\n1 -2 0\n2 3 0 -1\n-3 0\n% end marker\n"
        with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
            f.write(text)
        try:
            self.assertEqual(read_dimacs(f.name), (3, [(1, -2), (2, 3), (-1, -3)]))
        finally:
            os.remove(f.name)

    def test_qbf_against_brute_force(self):
        rng = random.Random(7)
        for _ in range(100000):
            n = rng.randint(1, 6)
            quantifiers = [rng.choice("AE") for _ in range(n)]
            clauses = random_formula(rng, n, rng.randint(0, 10))
            truth, _ = evaluate_qbf(quantifiers, clauses)
            self.assertEqual(truth, brute_qbf(quantifiers, clauses), (quantifiers, clauses))
            if "A" not in quantifiers:
                self.assertEqual(truth, two_sat(n, clauses).satisfiable)

    def test_qbf_conditions(self):
        self.assertEqual(evaluate_qbf("EA", [(1, 2), (-1, -2)]), (False, "3(ii)"))
        self.assertEqual(evaluate_qbf("AE", [(1, 2), (-1, -2)]), (True, None))
        self.assertEqual(evaluate_qbf("AA", [(1, 2)]), (False, "3(iii)"))
        self.assertEqual(evaluate_qbf("E", [(1,), (-1,)]), (False, "3(i)"))

    def test_published_procedure_counterexample(self):
        # for all x for all y (x or y) is false (take x = y = false), but the
        # procedure as printed says true: the DFS meets x first, so not y is
        # marked contingent as y's dual and never checked against its
        # contingent successor x. Theorem 2 itself gives the right answer
        quantifiers, clauses = "AA", [(1, 2)]
        self.assertFalse(brute_qbf(quantifiers, clauses))
        self.assertTrue(published_qbf(quantifiers, clauses))
        self.assertEqual(evaluate_qbf(quantifiers, clauses), (False, "3(iii)"))
        # it is not just one formula
        rng = random.Random(8)
        wrong = 0
        for _ in range(2000):
            n = rng.randint(1, 6)
            quantifiers = [rng.choice("AE") for _ in range(n)]
            clauses = random_formula(rng, n, rng.randint(0, 10))
            wrong += published_qbf(quantifiers, clauses) != brute_qbf(quantifiers, clauses)
        self.assertGreater(wrong, 0)

if __name__ == "__main__":
    unittest.main()
