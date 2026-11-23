# Linear-time 2-SAT
# Aspvall, Plass & Tarjan, "A linear-time algorithm for testing the truth of
# certain quantified boolean formulas", Information Processing Letters 8(3),
# 1979, pp. 121-123. Strong components come from Tarjan, "Depth-first search
# and linear graph algorithms", SIAM J. Comput. 1(2), 1972 (the paper's [7]).
#
# literals are DIMACS-style ints: k means x_k and -k means not x_k, 1 <= k <= n.
# vertex 2(k-1) is x_k and 2(k-1)+1 is not x_k, so v ^ 1 is the complement of v
#
# implication_graph = construction 1(i)-(ii), strong_components = Tarjan,
# two_sat = the paper's two-satisfiability algorithm, evaluate_qbf = Theorem 2

import sys
from collections import namedtuple

Result = namedtuple("Result", "satisfiable assignment conflict comp components")

def vertex(lit):
    return 2 * lit - 2 if lit > 0 else -2 * lit - 1

def literal(v):
    return -(v // 2 + 1) if v & 1 else v // 2 + 1

def implication_graph(n, clauses):
    # 1(i): 2n vertices. 1(ii): clause (u or v) gives edges not u -> v and
    # not v -> u. A one-literal clause u is treated as (u or u)
    adj = [[] for _ in range(2 * n)]
    for clause in clauses:
        if len(clause) == 2:
            a, b = clause
        elif len(clause) == 1:
            a = b = clause[0]
        else:
            raise ValueError(f"not a 2-CNF clause: {clause!r}")
        if not (0 < abs(a) <= n and 0 < abs(b) <= n):
            raise ValueError(f"literal out of range 1..{n} in clause {clause!r}")
        va = 2 * a - 2 if a > 0 else -2 * a - 1
        vb = 2 * b - 2 if b > 0 else -2 * b - 1
        adj[va ^ 1].append(vb)
        adj[vb ^ 1].append(va)
    return adj

def strong_components(adj):
    # Tarjan's algorithm with an explicit stack, since Python's recursion limit
    # is far below the path lengths in the big tests. comp[v] is the number of
    # v's component, numbered in the order the components are generated, which
    # is reverse topological order: an edge v -> w always has comp[v] >= comp[w]
    N = len(adj)
    index = [0] * N    # DFS number, 0 = not visited yet
    low = [0] * N      # smallest DFS number reachable through the subtree
    comp = [-1] * N    # -1 while v is still on Tarjan's stack
    stack = []
    count = 0
    counter = 0
    for root in range(N):
        if index[root]:
            continue
        counter += 1
        index[root] = low[root] = counter
        stack.append(root)
        path = [root]  # the DFS path, and how far through each vertex's edges
        pos = [0]
        while path:
            v = path[-1]
            edges = adj[v]
            i = pos[-1]
            k = len(edges)
            while i < k:
                w = edges[i]
                i += 1
                if not index[w]:
                    # tree edge, go down to w and come back to v's edge i later
                    pos[-1] = i
                    counter += 1
                    index[w] = low[w] = counter
                    stack.append(w)
                    path.append(w)
                    pos.append(0)
                    break
                if comp[w] < 0 and index[w] < low[v]:
                    low[v] = index[w]  # w is still on the stack
            else:
                # all of v's edges are done
                path.pop()
                pos.pop()
                if low[v] == index[v]:
                    # v is the root of a component, which is everything above
                    # it on the stack
                    while True:
                        w = stack.pop()
                        comp[w] = count
                        if w == v:
                            break
                    count += 1
                if path:
                    u = path[-1]
                    if low[v] < low[u]:
                        low[u] = low[v]
    return comp, count

def two_sat(n, clauses):
    # the paper's two-satisfiability algorithm. Process the strong components
    # in reverse topological order: skip S if it is already marked, stop if
    # S = S-bar (unsatisfiable), otherwise mark S true and S-bar false
    adj = implication_graph(n, clauses)
    comp, count = strong_components(adj)

    # one vertex of each component. S-bar holds the complements of S's
    # vertices, so it is the component of rep ^ 1 for any rep in S
    rep = [0] * count
    for v in range(2 * n):
        rep[comp[v]] = v

    mark = [None] * count
    for s in range(count):
        if mark[s] is not None:
            continue
        r = rep[s]
        s_bar = comp[r ^ 1]
        if s_bar == s:
            return Result(False, None, r // 2 + 1, comp, count)
        mark[s] = True
        mark[s_bar] = False

    # each vertex gets the value of its component. assignment[k - 1] is x_k
    assignment = [mark[comp[2 * k]] for k in range(n)]
    return Result(True, assignment, None, comp, count)

def satisfies(clauses, assignment):
    # True if the assignment makes every clause true
    for clause in clauses:
        if not any(assignment[abs(l) - 1] == (l > 0) for l in clause):
            return False
    return True

def refutation(n, clauses, k):
    # proof of unsatisfiability for a variable k whose x_k and not x_k share a
    # component: the implications x_k => ... => not x_k => ... => x_k, found by
    # breadth-first search. Each step u => v is backed by the clause (not u or v)
    adj = implication_graph(n, clauses)

    def path(src, dst):
        parent = {src: None}
        queue = [src]
        for v in queue:
            if v == dst:
                break
            for w in adj[v]:
                if w not in parent:
                    parent[w] = v
                    queue.append(w)
        if dst not in parent:
            return None
        out = [dst]
        while out[-1] != src:
            out.append(parent[out[-1]])
        return out[::-1]

    x, not_x = vertex(k), vertex(-k)
    there, back = path(x, not_x), path(not_x, x)
    if there is None or back is None:
        return None
    return [literal(v) for v in there + back[1:]]

def evaluate_qbf(quantifiers, clauses):
    # Theorem 2: F = Q1 x1 ... Qn xn C is true unless
    #   3(i)   an existential vertex is in the same component as its complement
    #   3(ii)  a universal u_i shares a component with an existential u_j, j < i
    #   3(iii) a path leads from a universal vertex to a different universal one
    # quantifiers[k - 1] is "A" (for all) or "E" (there exists) for x_k.
    # returns (truth value, the condition that holds or None)
    #
    # the paper proves Theorem 2 with a marking procedure (p. 123, Steps 1-6),
    # but as written that procedure answers true for "for all x for all y
    # (x or y)" when the DFS meets x before not y: not y is marked contingent as
    # the dual of y, so it is never processed and its contingent successor x is
    # never seen. The theorem itself is right (see the tests), so this checks
    # its three conditions directly, still in O(n + m)
    n = len(quantifiers)
    if any(q not in ("A", "E") for q in quantifiers):
        raise ValueError("quantifiers must be 'A' or 'E'")
    adj = implication_graph(n, clauses)
    comp, count = strong_components(adj)

    universal = [0] * count        # universal vertices in each component
    first_exist = [n + 1] * count  # smallest existential variable in each
    for v in range(2 * n):
        c = comp[v]
        k = v // 2 + 1
        if quantifiers[k - 1] == "A":
            universal[c] += 1
        else:
            if comp[v ^ 1] == c:
                return False, "3(i)"
            if k < first_exist[c]:
                first_exist[c] = k

    for v in range(0, 2 * n, 2):
        k = v // 2 + 1
        if quantifiers[k - 1] == "A" and (first_exist[comp[v]] < k or
                                         first_exist[comp[v + 1]] < k):
            return False, "3(ii)"

    # below[c] = some universal vertex can be reached from component c by a
    # path that leaves c. Successors have smaller numbers, so one pass in
    # component order sees each successor's final value first
    members = [[] for _ in range(count)]
    for v in range(2 * n):
        members[comp[v]].append(v)
    below = [False] * count
    for c in range(count):
        if universal[c] >= 2:
            return False, "3(iii)"
        for v in members[c]:
            for w in adj[v]:
                d = comp[w]
                if d != c and (universal[d] or below[d]):
                    below[c] = True
        if universal[c] and below[c]:
            return False, "3(iii)"
    return True, None

def read_dimacs(path):
    # reads a DIMACS cnf file, returns (n, clauses)
    n = None
    clauses = []
    pending = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line[0] in "c%":
                continue
            if line[0] == "p":
                _, fmt, nv, _ = line.split()
                if fmt != "cnf":
                    raise ValueError(f"{path}: not a cnf file")
                n = int(nv)
                continue
            for tok in line.split():
                lit = int(tok)
                if lit:
                    pending.append(lit)
                else:
                    clauses.append(tuple(pending))
                    pending = []
    if n is None:
        raise ValueError(f"{path}: no 'p cnf' line")
    if pending:
        clauses.append(tuple(pending))
    return n, clauses

# the paper's Fig. 1: C = {a or b, b or not c, not b or not d, b or d, d or a}
# with a, b, c, d = x1, x2, x3, x4
FIGURE_1 = [(1, 2), (2, -3), (-2, -4), (2, 4), (4, 1)]

def main():
    if len(sys.argv) > 1:
        n, clauses = read_dimacs(sys.argv[1])
    else:
        n, clauses = 4, FIGURE_1
        print("the paper's Fig. 1 (a, b, c, d = x1, x2, x3, x4)")
    res = two_sat(n, clauses)
    if res.satisfiable:
        print("s SATISFIABLE")
        print("v " + " ".join(str(k if val else -k)
                              for k, val in enumerate(res.assignment, 1)) + " 0")
    else:
        print("s UNSATISFIABLE")
        proof = refutation(n, clauses, res.conflict)
        print(f"c x{res.conflict} and its complement are in one component:")
        print("c " + " => ".join(str(l) for l in proof))

if __name__ == "__main__":
    main()
