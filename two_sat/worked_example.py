# prints the worked example in the write-up: the paper's Fig. 1 formula, its
# implication graph, Tarjan's DFS numbers, the components in the order they are
# generated, how each one is marked, and the final assignment. Then the same
# formula with two more clauses, which makes it unsatisfiable.
# usage: python worked_example.py [--qbf]
# --qbf also traces the paper's QBF procedure on "for all x for all y (x or y)"
#
# the DFS is a plain recursive Tarjan, written separately from two_sat.py, and
# the script checks it gets the same components and answer, and that a search
# over all 16 assignments agrees

import itertools
import sys
from two_sat import (FIGURE_1, evaluate_qbf, implication_graph, literal, refutation,
                     strong_components, two_sat)

NAMES = {1: "a", 2: "b", 3: "c", 4: "d"}

def name(lit):
    return NAMES[abs(lit)] + ("" if lit > 0 else "'")

def vname(v):
    return name(literal(v))

def clause_name(c):
    return " or ".join(name(l) for l in c)

def tarjan_trace(adj):
    # textbook recursive Tarjan that records each vertex's DFS number and low
    # link, and the components in the order they are generated
    index, low, on_stack, stack, comps = {}, {}, set(), [], []

    def visit(v):
        index[v] = low[v] = len(index) + 1
        stack.append(v)
        on_stack.add(v)
        for w in adj[v]:
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                comp.append(w)
                if w == v:
                    break
            comps.append(comp)

    for v in range(len(adj)):
        if v not in index:
            visit(v)
    return index, low, comps

def show(n, clauses, title):
    print(f"== {title}")
    print("clauses: " + ", ".join(f"({clause_name(c)})" for c in clauses))
    adj = implication_graph(n, clauses)
    print("edges (clause u or v gives u' -> v and v' -> u):")
    for c in clauses:
        a, b = c
        print(f"  ({clause_name(c)}):  {name(-a)} -> {name(b)},  {name(-b)} -> {name(a)}")

    index, low, comps = tarjan_trace(adj)
    comp_of = {v: i for i, comp in enumerate(comps) for v in comp}
    print("\nDFS from a, a', b, b', c, c', d, d' in turn:")
    print("  vertex  " + "  ".join(f"{vname(v):>3}" for v in range(2 * n)))
    print("  index   " + "  ".join(f"{index[v]:>3}" for v in range(2 * n)))
    print("  low     " + "  ".join(f"{low[v]:>3}" for v in range(2 * n)))
    print("  comp    " + "  ".join(f"{'S' + str(comp_of[v] + 1):>3}" for v in range(2 * n)))

    # same components and numbering as two_sat.py's iterative version
    comp, count = strong_components(adj)
    assert count == len(comps) and all(comp[v] == comp_of[v] for v in range(2 * n))

    print("\ncomponents in the order generated (reverse topological), and marking:")
    mark = [None] * len(comps)
    stopped = None
    for s, members in enumerate(comps):
        s_bar = comp_of[members[0] ^ 1]
        succ = sorted({comp_of[w] for v in members for w in adj[v]} - {s})
        label = "{" + ", ".join(vname(v) for v in sorted(members)) + "}"
        info = (f"  S{s + 1} = {label:<14} successors "
                f"{', '.join('S' + str(t + 1) for t in succ) or '-':<9} S-bar = S{s_bar + 1}")
        if mark[s] is not None:
            print(f"{info}   already marked {mark[s]}, skip")
            continue
        if s_bar == s:
            print(f"{info}   S = S-bar: stop, unsatisfiable")
            stopped = members
            break
        mark[s], mark[s_bar] = "true", "false"
        print(f"{info}   mark S{s + 1} true, S{s_bar + 1} false")

    res = two_sat(n, clauses)
    brute = any(all(any(bits[abs(l) - 1] == (l > 0) for l in c) for c in clauses)
                for bits in itertools.product((False, True), repeat=n))
    assert res.satisfiable == (stopped is None) == brute
    if stopped is None:
        values = [mark[comp_of[2 * k]] == "true" for k in range(n)]
        assert values == res.assignment
        print("\nassignment: " + ", ".join(f"{NAMES[k + 1]} = {'T' if x else 'F'}"
                                           for k, x in enumerate(values)))
        for c in clauses:
            assert any(values[abs(l) - 1] == (l > 0) for l in c)
        print("every clause is true; matches two_sat and a search over all "
              f"{2 ** n} assignments")
    else:
        chain = refutation(n, clauses, res.conflict)
        print(f"\n{name(res.conflict)} and {name(-res.conflict)} are in one component, so "
              f"{' => '.join(name(l) for l in chain)}")
        print("no assignment works; matches two_sat and a search over all "
              f"{2 ** n} assignments")
    print()

def qbf_trace():
    # the paper's Steps 1-6 on for all x1 for all x2 (x1 or x2), which is false
    print("== the paper's QBF procedure on: for all x for all y (x or y)")
    quantifiers, clauses = "AA", [(1, 2)]
    adj = implication_graph(2, clauses)
    comp, count = strong_components(adj)
    names = {0: "x", 1: "x'", 2: "y", 3: "y'"}
    members = [[v for v in range(4) if comp[v] == c] for c in range(count)]
    succ = [{comp[w] for v in members[c] for w in adj[v]} - {c} for c in range(count)]
    print("edges: x' -> y, y' -> x.  components in the order generated: "
          + ", ".join("{" + ", ".join(names[v] for v in m) + "}" for m in members))
    mark = [None] * count
    for c in range(count):
        label = "{" + ", ".join(names[v] for v in members[c]) + "}"
        if mark[c]:
            print(f"  {label}: already marked {mark[c]} (as a dual), Step 1 skips it")
            continue
        assert not succ[c]
        mark[c] = "contingent"  # Steps 3-4: one universal vertex, nothing after it
        dual = comp[members[c][0] ^ 1]
        mark[dual] = "contingent"
        print(f"  {label}: no successors, one universal vertex -> contingent (Steps 3-4); "
              f"Step 6 marks its dual {{{names[members[c][0] ^ 1]}}} contingent")
    print("  no step stops, so the procedure says true. But x = y = false makes it false,")
    print("  and y' -> x is a path between universal vertices, condition 3(iii) of Theorem 2.")
    print(f"  evaluate_qbf (checks Theorem 2 directly): {evaluate_qbf(quantifiers, clauses)}")

def main():
    show(4, FIGURE_1, "the paper's Fig. 1 (a, b, c, d = x1, x2, x3, x4)")
    show(4, FIGURE_1 + [(-2, 4), (2, -4)], "Fig. 1 plus (b' or d) and (b or d')")
    if "--qbf" in sys.argv:
        qbf_trace()

if __name__ == "__main__":
    main()
