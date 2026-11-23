# CS 6050 Graduate Algorithm Project 3

One graph algorithm, implemented in Python, tested on 10 inputs of increasing
size, and timed to check the runtime against the theoretical bound.

| folder | algorithm | source | expected runtime |
|---|---|---|---|
| [`two_sat/`](two_sat/) | Linear-time 2-SAT (implication graph + strong components) | Aspvall, Plass & Tarjan, Information Processing Letters 8(3), 1979 | O(n + m): n variables, m clauses |

The write-up is [`writeup/writeup.pdf`](writeup/writeup.pdf).

## Requirements

* Python 3.8 or newer. The algorithm, test cases and test runner use only the
  standard library.
* `numpy` and `matplotlib` are needed only to remake the plot (`make_plots.py`).

```
pip install -r requirements.txt
```

## Running the test cases

From the folder, run the 10 test cases:

```
cd two_sat && python run_tests.py && cd ..
```

The runner prints PASS/FAIL and the runtime for every case and saves the
timings to `results.csv` in that folder. Every case runs at least 3 times and
the fastest time is kept. On an M1 Max the slowest single run takes about
5.5 s, and a full run with repeats takes about 50 s. Pass `--quick` to skip the
two largest cases.

The extra edge-case tests are separate from the timed cases:

```
cd two_sat && python -m unittest -v test_two_sat
```

## Remaking the plot

After `python run_tests.py --layout` in `two_sat/` (the `--layout` pass is
needed for the bottom panel), run:

```
python make_plots.py
```

This writes the runtime figure `writeup/figures/two_sat.{svg,png}`, the
worked example's graph `figure1_graph.{svg,png}`, and the fitted numbers in
`fits.json`.

## Regenerating the test cases

The test files in `tests/` were made by `generate_tests.py` with fixed seeds,
so re-running it produces identical files. They are standard DIMACS `.cnf`
files, so other SAT solvers can read them too. The expected answers come from
unit propagation in the style of Even, Itai and Shamir (1976), which never
builds strong components and shares no code with the implementation being
tested.

## Layout

```
two_sat/
    two_sat.py           implementation
    generate_tests.py    makes tests/case01..case10.cnf
    run_tests.py         checks + times the 10 cases -> results.csv
    test_two_sat.py      unit tests (edge cases, randomized checks)
    worked_example.py    prints the worked example in the write-up
    tests/               the 10 test case files
    README.md
make_plots.py            figures for the write-up
writeup/                 writeup.pdf and the figures
```
