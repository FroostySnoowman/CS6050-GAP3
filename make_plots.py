# makes the runtime plot in writeup/figures from two_sat/results.csv and layout.csv
# usage: python make_plots.py

import csv
import json
import math
import os
import sys
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch
from matplotlib.ticker import FuncFormatter

HERE = os.path.dirname(os.path.abspath(__file__))
FIG_DIR = os.path.join(HERE, "writeup", "figures")
sys.path.insert(0, os.path.join(HERE, "two_sat"))
sys.dont_write_bytecode = True
from two_sat import FIGURE_1, implication_graph, literal, two_sat  # noqa: E402

MEASURED = "#2a78d6"
THEORY = "#eb6834"
OTHER = "#8a8984"
LOCAL = "#1f9e74"
INK = "#1f1f1e"
INK2 = "#52514e"
GRID = "#e4e3df"

N_FIT = 5  # fit c on the largest 5 cases

def read_csv(path):
    with open(path) as f:
        return list(csv.DictReader(f))

def style_axes(ax):
    ax.grid(True, which="major", color=GRID, linewidth=0.8)
    ax.grid(False, which="minor")
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color("#b9b8b2")
    ax.tick_params(colors=INK2, labelsize=7)
    ax.xaxis.label.set_color(INK)
    ax.yaxis.label.set_color(INK)

def seconds_fmt(v, _):
    if v >= 1:
        return f"{v:g} s"
    if v >= 1e-3:
        return f"{v * 1e3:g} ms"
    return f"{v * 1e6:g} µs"

def slope(x, t):
    return float(np.polyfit(np.log(x), np.log(t), 1)[0])

def graph_figure():
    # the paper's Fig. 1 drawn the same way: top row not a, d, not b, not c and
    # bottom row c, b, not d, a. Components with 2 vertices are outlined, true
    # literals are blue
    names = {1: "a", 2: "b", 3: "c", 4: "d"}

    def name(v):
        lit = literal(v)
        return ("" if lit > 0 else "¬") + names[abs(lit)]

    pos = {"¬a": (0, 1), "d": (1, 1), "¬b": (2, 1), "¬c": (3, 1),
           "c": (0, 0), "b": (1, 0), "¬d": (2, 0), "a": (3, 0)}
    adj = implication_graph(4, FIGURE_1)
    res = two_sat(4, FIGURE_1)
    fig, ax = plt.subplots(figsize=(2.05, 2.05 * 1.6 / 3.6))
    ax.set_xlim(-0.3, 3.3)
    ax.set_ylim(-0.3, 1.3)
    ax.set_aspect("equal")
    ax.axis("off")
    groups = {}
    for v in range(8):
        groups.setdefault(res.comp[v], []).append(name(v))
    for members in groups.values():
        if len(members) > 1:
            xs = [pos[m][0] for m in members]
            y = pos[members[0]][1]
            ax.add_patch(FancyBboxPatch((min(xs) - 0.25, y - 0.25), max(xs) - min(xs) + 0.5, 0.5,
                                        boxstyle="round,pad=0,rounding_size=0.22", fc="#fbe3d6",
                                        ec=THEORY, lw=0.8, zorder=0))
    edges = {(name(v), name(w)) for v in range(8) for w in adj[v]}
    for u, w in sorted(edges):
        rad = 0.4 if (w, u) in edges else 0.0
        ax.add_patch(FancyArrowPatch(pos[u], pos[w], arrowstyle="-|>", mutation_scale=6,
                                     connectionstyle=f"arc3,rad={rad}", shrinkA=6.5, shrinkB=6.5,
                                     color=INK2, lw=0.6, zorder=1))
    for v in range(8):
        x, y = pos[name(v)]
        true = res.assignment[v // 2] == (v % 2 == 0)
        ax.add_patch(plt.Circle((x, y), 0.19, fc=MEASURED if true else "#ecebe6", ec="white",
                                lw=0.8, zorder=2))
        ax.text(x, y, name(v), ha="center", va="center", fontsize=6.3, fontweight="bold",
                color="white" if true else INK, zorder=3)
    fig.subplots_adjust(0, 0, 1, 1)
    for ext in ("svg", "png"):
        fig.savefig(os.path.join(FIG_DIR, f"figure1_graph.{ext}"), dpi=300, facecolor="white")
    plt.close(fig)

def main():
    plt.rcParams.update({"font.family": "DejaVu Sans", "svg.fonttype": "path",
                         "mathtext.fontset": "dejavusans"})
    rows = read_csv(os.path.join(HERE, "two_sat", "results.csv"))
    x = np.array([float(r["size"]) for r in rows])
    t = np.array([float(r["seconds"]) for r in rows])
    sat = np.array([r["satisfiable"] == "True" for r in rows])

    c = math.exp(np.mean(np.log(t[-N_FIT:]) - np.log(x[-N_FIT:])))
    ratio = t / (c * x)
    slope_top = slope(x[-N_FIT:], t[-N_FIT:])
    slope_all = slope(x, t)
    slope_nlogn = slope(x[-N_FIT:], x[-N_FIT:] * np.log2(x[-N_FIT:]))

    lrows = read_csv(os.path.join(HERE, "two_sat", "layout.csv"))
    lx = np.array([float(r["size"]) for r in lrows])
    tl = np.array([float(r["seconds_local"]) for r in lrows])
    tr = np.array([float(r["seconds_renamed"]) for r in lrows])

    # one page limit, so the panels are stacked to sit in a column beside the text
    fig = plt.figure(figsize=(3.6, 3.8), layout="constrained")
    outer = fig.add_gridspec(2, 1, height_ratios=[2.95, 1.95])
    top = outer[0].subgridspec(2, 1, height_ratios=[2.15, 0.8], hspace=0.04)
    ax = fig.add_subplot(top[0])
    ax2 = fig.add_subplot(top[1])
    ax3 = fig.add_subplot(outer[1])

    xx = np.geomspace(x[0] / 1.3, x[-1] * 1.3, 200)
    ax.plot(xx, c * xx, color=THEORY, lw=2, zorder=2, label=r"theory, $c\cdot(n+m)$")
    k = t[-1] / (x[-1] * np.log2(x[-1]))  # through the largest point
    ax.plot(xx, k * xx * np.log2(xx), color=OTHER, lw=1.0, ls=(0, (4, 3)), zorder=1,
            label=r"$(n+m)\log(n+m)$")
    ax.plot(x[sat], t[sat], "o", ms=5.5, color=MEASURED, mec="white", mew=1, zorder=3,
            label="measured, satisfiable")
    ax.plot(x[~sat], t[~sat], "s", ms=5, color=MEASURED, mec="white", mew=1, zorder=3,
            label="measured, unsatisfiable")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_ylim(t.min() / 60, t.max() * 3)  # room for the note (upper left) and legend (lower right)
    ax.yaxis.set_major_formatter(FuncFormatter(seconds_fmt))
    ax.set_ylabel("runtime", fontsize=7.5)
    style_axes(ax)
    ax.tick_params(labelbottom=False)
    ax.legend(loc="lower right", fontsize=6.5, frameon=False, labelcolor=INK,
              handlelength=2.2, borderaxespad=0.2, labelspacing=0.3)
    ax.set_title("Runtime vs. input size", loc="left", fontsize=8.5, color=INK,
                 fontweight="bold")
    ax.text(0.02, 0.97, f"log-log slope, 5 largest: {slope_top:.3f}\n"
            f"log-log slope, all 10: {slope_all:.3f}", transform=ax.transAxes,
            ha="left", va="top", fontsize=6.8, color=INK2, linespacing=1.4)

    ax2.axhline(1.0, color=THEORY, lw=1.2, zorder=1)
    ax2.axhspan(0.9, 1.1, color=THEORY, alpha=0.08, lw=0, zorder=0)
    ax2.plot(x, ratio, "-", color=MEASURED, lw=1.5, zorder=2)
    ax2.plot(x[sat], ratio[sat], "o", color=MEASURED, ms=4.5, mec="white", mew=0.8, zorder=3)
    ax2.plot(x[~sat], ratio[~sat], "s", color=MEASURED, ms=4, mec="white", mew=0.8, zorder=3)
    ax2.set_xscale("log")
    ax2.set_xlim(ax.get_xlim())
    ax2.set_ylim(0, max(1.25, ratio.max() + 0.1))
    ax2.set_ylabel(r"T / c$\cdot$(n+m)", fontsize=7)
    ax2.set_xlabel("n + m, variables + clauses (the 10 test cases)", fontsize=7.5)
    style_axes(ax2)
    ax2.text(0.98, 0.08, "shaded band = ±10%", transform=ax2.transAxes,
             ha="right", va="bottom", fontsize=6.5, color=INK2)

    per = t / x * 1e6
    per_l = tl / lx * 1e6
    per_r = tr / lx * 1e6
    ax3.plot(lx, per_r, "-D", color=OTHER, lw=1.5, ms=4.2, mec="white", mew=0.8, zorder=2,
             label="local formulas, variables renamed")
    ax3.plot(x, per, "-o", color=MEASURED, lw=1.5, ms=5, mec="white", mew=1, zorder=3,
             label="the 10 test cases")
    ax3.plot(lx, per_l, "-^", color=LOCAL, lw=1.5, ms=5, mec="white", mew=0.8, zorder=2,
             label="local formulas (nearby variables)")
    ax3.set_xscale("log")
    ax3.set_xlim(ax.get_xlim())
    ax3.set_ylim(0, max(per.max(), per_r.max()) * 1.45)  # room for the legend
    ax3.set_ylabel("µs per (n + m)", fontsize=7.5)
    ax3.set_xlabel("n + m (m = 2n)", fontsize=7.5)
    style_axes(ax3)
    handles, labels = ax3.get_legend_handles_labels()
    order = [1, 0, 2]
    ax3.legend([handles[i] for i in order], [labels[i] for i in order], loc="upper left",
               fontsize=6.8, frameon=False, labelcolor=INK)
    ax3.set_title("Time per unit of input (flat = linear)", loc="left", fontsize=8.5,
                  color=INK, fontweight="bold")

    fig.get_layout_engine().set(h_pad=0.03, hspace=0.04)
    os.makedirs(FIG_DIR, exist_ok=True)
    for ext in ("svg", "png"):
        fig.savefig(os.path.join(FIG_DIR, f"two_sat.{ext}"), dpi=200, facecolor="white")
    plt.close(fig)
    graph_figure()

    out = {"c": c, "slope_top5": slope_top, "slope_all": slope_all,
           "slope_nlogn_top5": slope_nlogn, "ratio": ratio.tolist(), "x": x.tolist(),
           "t": t.tolist(), "us_per_element": per.tolist(),
           "doubling_ratio": (t[1:] / t[:-1]).tolist(),
           "layout": {"x": lx.tolist(), "us_local": per_l.tolist(),
                      "us_renamed": per_r.tolist(),
                      "slope_local_all": slope(lx, tl), "slope_renamed_all": slope(lx, tr),
                      "slope_local_top5": slope(lx[-N_FIT:], tl[-N_FIT:]),
                      "slope_renamed_top5": slope(lx[-N_FIT:], tr[-N_FIT:])}}
    with open(os.path.join(FIG_DIR, "fits.json"), "w") as fh:
        json.dump({"two_sat": out}, fh, indent=1)

    print(f"two_sat: c = {c:.3e}, slope (5 largest) = {slope_top:.3f}, slope (all) = "
          f"{slope_all:.3f}, T/(c f) = " + " ".join(f"{r:.2f}" for r in ratio))
    print("us per (n+m): " + " ".join(f"{p:.3f}" for p in per))
    print("local:        " + " ".join(f"{p:.3f}" for p in per_l))
    print("renamed:      " + " ".join(f"{p:.3f}" for p in per_r))
    print(f"layout slopes: local {out['layout']['slope_local_all']:.3f} (all) "
          f"{out['layout']['slope_local_top5']:.3f} (5 largest), renamed "
          f"{out['layout']['slope_renamed_all']:.3f} (all) "
          f"{out['layout']['slope_renamed_top5']:.3f} (5 largest)")

if __name__ == "__main__":
    main()
