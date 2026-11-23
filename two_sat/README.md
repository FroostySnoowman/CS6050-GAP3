# Linear-time 2-SAT

`two_sat.py` is a Python implementation of the algorithm in B. Aspvall,
M. F. Plass and R. E. Tarjan, "A linear-time algorithm for testing the truth
of certain quantified Boolean formulas", Information Processing Letters 8(3),
1979, pp. 121-123. The paper prints no code; this follows its description:

1. Build the implication graph G(F): a vertex for each literal x_k and not x_k,
   and for each clause (u or v) the edges not u -> v and not v -> u.
2. Find the strong components with Tarjan's algorithm (the paper's reference
   [7]), which generates them in reverse topological order.
3. Process the components in that order. Skip a component that is already
   marked. If a component S contains a literal and its complement (S = S-bar),
   stop: the formula is unsatisfiable. Otherwise mark S true and S-bar false.
4. Each variable gets the value of the component holding x_k.

Functions:

* `two_sat(n, clauses)` is the main algorithm. Clauses are pairs of DIMACS-style
  literals (`3` is x3, `-3` is not x3); a one-literal clause `(u,)` counts as
  `(u or u)`. It returns `satisfiable`, the `assignment` (`assignment[k - 1]` is
  x_k), and for an unsatisfiable formula a `conflict` variable whose x_k and
  not x_k share a component.
* `implication_graph(n, clauses)` and `strong_components(adj)` are steps 1 and 2.
  Tarjan's algorithm keeps its own stack, because Python's recursion limit is
  far below the path lengths in the big tests.
* `refutation(n, clauses, k)` turns a conflict into a proof that nothing
  satisfies the formula: implications x_k => ... => not x_k => ... => x_k, each
  backed by one clause. It is used by the tests and isn't timed.
* `evaluate_qbf(quantifiers, clauses)` is the paper's other result (Theorem 2),
  for formulas where some variables are "for all". See the note below.
* `read_dimacs(path)` reads a standard DIMACS `.cnf` file.

The paper gives the running time as O(n + m), where n is the number of
variables and m the number of clauses (the paper counts the graph's 2m edges).

To solve the paper's Fig. 1 example, or any DIMACS file:

```
python two_sat.py
python two_sat.py tests/case02.cnf
```

## Run the 10 test cases

```
python run_tests.py              # all 10, about 50 s
python run_tests.py --quick      # skip the 2 largest
python run_tests.py --layout     # also run the memory-layout experiment
                                 # (about 2 min in total)
```

A satisfiable answer passes if it matches the expected answer and the
assignment makes every clause true. An unsatisfiable answer passes if it
matches and `refutation` produces a chain x_k => ... => not x_k => ... => x_k in
which every step is a clause from the file, which proves no assignment works.
Reading the file isn't timed. Building the graph is, since it's part of the
algorithm. Timings go to `results.csv`.

`--layout` builds formulas whose clauses only join variables at most 8 apart,
then the same formulas with the variables renamed at random. The two graphs are
identical up to renaming, so the algorithm does exactly the same work on both,
and any difference in time comes from how memory is accessed. Results go to
`layout.csv`.

## Worked example

```
python worked_example.py          # add --qbf for the QBF note below
```

This prints the worked example in the write-up: the paper's Fig. 1 formula,
its 10 edges, the DFS numbers and low links, the components in the order they
are generated, how each one is marked, and the final assignment. Then it adds
two clauses that make the formula unsatisfiable. It checks the answers against
`two_sat` and a search over all 16 assignments.

## Test cases

`tests/caseNN.cnf` has n = 2^(NN+10) variables, so 2,048 for case 1 up to
1,048,576 for case 10, and m = 2n clauses. Each clause joins two different
variables, each with a random sign. The odd cases have a planted solution:
clauses are drawn at random and kept only if a hidden random assignment
satisfies them, so the formula is satisfiable. The even cases are uniform
random, and at m = 2n they are unsatisfiable (random 2-SAT turns unsatisfiable
past about m = n). The files are standard DIMACS, with the expected answer in a
comment:

```
c 2-sat case 1: 2048 variables, 4096 clauses, planted solution, seed 6001
c expected SATISFIABLE
p cnf 2048 4096
415 1331 0
...
```

The expected answer comes from `oracle_satisfiable` in `generate_tests.py`,
unit propagation in the style of Even, Itai and Shamir (1976, the paper's [3]).
It never builds strong components and shares no code with `two_sat.py`. To
regenerate the files (identical, since the seeds are fixed):

```
python generate_tests.py
```

## Unit tests

```
python -m unittest -v test_two_sat
```

These cover the paper's Fig. 1 (all 10 edges and its components), the duality
property, Tarjan's algorithm against brute-force reachability on random graphs,
4,000 random formulas against a search over every assignment (with one-literal
clauses, tautologies and duplicates), a check that the DFS reads every edge
exactly once, edge cases, a 200,000-step implication chain, the oracle against
brute force, the DIMACS reader, and the QBF evaluator against brute force on
100,000 random quantified formulas.

## A note on the paper's QBF procedure

Theorem 2 says a quantified 2-CNF formula is false exactly when one of three
graph conditions holds. The paper proves it with a marking procedure
(p. 123, Steps 1-6), but as printed that procedure gives the wrong answer for
some formulas. The smallest is "for all x for all y (x or y)", which is false
(take x = y = false). When the DFS reaches x before not y, the procedure marks
not y "contingent" as the dual of y, so Step 1 skips it later and never sees
its contingent successor x. It answers true. `python worked_example.py --qbf`
prints the trace, and `test_published_procedure_counterexample` runs the
procedure as printed. Theorem 2 itself agreed with brute force on every random
formula tried, so `evaluate_qbf` checks its three conditions directly, still in
O(n + m).
