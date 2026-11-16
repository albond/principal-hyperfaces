"""Figures for the paper on the certified principal hyperface method.

Run from the repository root:

    python3 paper/figures/make_figures.py

All numbers are computed exactly with the `principal_hyperfaces` package
(python/src), so the figures always agree with the text and the Lean proofs.
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch, Polygon, Wedge
from mpl_toolkits.mplot3d.art3d import Poly3DCollection

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "python" / "src"))
from principal_hyperfaces import LinearProgram, projection_order, solve  # noqa: E402

OUT = Path(__file__).resolve().parent

# Validated categorical palette (dataviz reference, light mode).
BLUE = "#2a78d6"    # principal hyperfaces
ORANGE = "#eb6834"  # objective vector
AQUA = "#1baf7a"    # second active normal / highlighted non-principal face
INK = "#222222"
MUTED = "#8a8a8a"
FILL = "#e9eef5"

plt.rcParams.update({
    "font.family": "serif",
    "mathtext.fontset": "cm",
    "font.size": 10,
    "axes.linewidth": 0.6,
    "savefig.bbox": "tight",
    "savefig.pad_inches": 0.03,
})


def arrow(ax, p, q, color, lw=1.6, ms=11, z=5):
    ax.add_patch(FancyArrowPatch(p, q, arrowstyle="-|>", mutation_scale=ms,
                                 color=color, lw=lw, zorder=z, shrinkA=0, shrinkB=0))


def save(fig, name):
    """PDF for the paper, PNG for the README; no timestamps, so rebuilds are byte-stable."""
    fig.savefig(OUT / f"{name}.pdf", metadata={"CreationDate": None})
    fig.savefig(OUT / f"{name}.png", dpi=200, facecolor="white", metadata={"Software": None})


def clean(ax):
    ax.set_aspect("equal")
    for s in ax.spines.values():
        s.set_visible(False)
    ax.set_xticks([])
    ax.set_yticks([])


# ---------------------------------------------------------------------------
# The 2-D example used in Figures 1 and 2:
#   maximize 3x + 2y  s.t.  L1: x+y<=4, L2: x+3y<=7, L3: 2x-y<=6, L4: -x<=0, L5: -y<=0
# ---------------------------------------------------------------------------
LP2 = LinearProgram.create(c=[3, 2], A=[[1, 1], [1, 3], [2, -1], [-1, 0], [0, -1]],
                           b=[4, 7, 6, 0, 0])
POLY2 = [(0, 0), (3, 0), (10 / 3, 2 / 3), (5 / 2, 3 / 2), (0, 7 / 3)]
# faces as (constraint index, endpoint a, endpoint b)
FACES2 = [(0, (5 / 2, 3 / 2), (10 / 3, 2 / 3)), (1, (0, 7 / 3), (5 / 2, 3 / 2)),
          (2, (3, 0), (10 / 3, 2 / 3)), (3, (0, 0), (0, 7 / 3)), (4, (0, 0), (3, 0))]


def proj(lp, k):
    a = lp.A[k]
    return float(sum(x * y for x, y in zip(lp.c, a))) / math.sqrt(float(sum(x * x for x in a)))


def figure_geometry():
    sol = solve(LP2)
    assert sol is not None and sol.certified
    xs = tuple(float(v) for v in sol.x)
    order = projection_order(LP2)
    principal = order[0]

    fig, ax = plt.subplots(figsize=(6.2, 4.3))
    ax.add_patch(Polygon(POLY2, closed=True, facecolor=FILL, edgecolor=MUTED, lw=0.8, zorder=1))
    names = ["$L_1$", "$L_2$", "$L_3$", "$L_4$", "$L_5$"]
    for k, a, b in FACES2:
        mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
        nx, ny = (float(v) for v in LP2.A[k])
        r = math.hypot(nx, ny)
        nx, ny = 0.62 * nx / r, 0.62 * ny / r
        color = BLUE if k == principal else MUTED
        if k == principal:
            ax.plot([a[0], b[0]], [a[1], b[1]], color=BLUE, lw=3.2, zorder=3,
                    solid_capstyle="round")
        arrow(ax, (mx, my), (mx + nx, my + ny), color, lw=1.4 if k == principal else 1.0)
        p = proj(LP2, k)
        off = {0: (0.05, 0.25), 1: (-0.15, 0.22), 2: (0.55, -0.05), 3: (-0.55, 0.05), 4: (0.05, -0.32)}[k]
        ax.text(mx + nx + off[0], my + ny + off[1],
                f"{names[k]}\n$\\mathrm{{pr}}={p:+.2f}$", ha="center", va="center",
                fontsize=8.5, color=INK, zorder=6)

    # objective vector and level line through the optimum
    cx, cy = 3 / math.hypot(3, 2), 2 / math.hypot(3, 2)
    arrow(ax, (1.0, 0.75), (1.0 + 1.1 * cx, 0.75 + 1.1 * cy), ORANGE, lw=2.0, ms=13)
    ax.text(1.0 + 1.1 * cx + 0.05, 0.75 + 1.1 * cy + 0.12, "$c$", color=INK, fontsize=12)
    t = [-1.1, 0.9]
    ax.plot([xs[0] - 2 * u for u in t], [xs[1] + 3 * u for u in t], ls="--", lw=0.9,
            color=ORANGE, zorder=2)
    ax.text(xs[0] + 2 * 0.36 + 0.1, xs[1] - 3 * 0.36, "level line $c\\cdot x = z^*$",
            fontsize=8.5, color=INK, ha="left")

    # optimum and the cone of active normals
    ax.add_patch(Wedge(xs, 0.55, math.degrees(math.atan2(-1, 2)), 45, color=BLUE,
                       alpha=0.13, zorder=2))
    ax.plot(*xs, "o", color=INK, ms=6, zorder=7)
    for (vx, vy), col in [((1, 1), BLUE), ((2, -1), AQUA)]:
        r = math.hypot(vx, vy)
        arrow(ax, xs, (xs[0] + 0.5 * vx / r, xs[1] + 0.5 * vy / r), col, lw=1.3, ms=9, z=6)
    arrow(ax, xs, (xs[0] + 0.5 * cx, xs[1] + 0.5 * cy), ORANGE, lw=1.6, ms=10, z=6)
    ax.text(xs[0] + 0.62, xs[1] + 0.05, "$c$ in the cone of\nactive normals", fontsize=8.5,
            color=INK, va="center")
    ax.text(xs[0] - 0.15, xs[1] - 0.3, "$x^*=(10/3,\\,2/3)$", fontsize=9, color=INK, ha="right")

    ax.set_xlim(-1.0, 5.6)
    ax.set_ylim(-0.75, 3.2)
    clean(ax)
    save(fig, "fig1_geometry")
    plt.close(fig)


def figure_reduction():
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.9),
                                   gridspec_kw={"width_ratios": [1.15, 1]})
    # (a) the chosen principal face becomes an equality
    ax1.add_patch(Polygon(POLY2, closed=True, facecolor=FILL, edgecolor=MUTED, lw=0.8))
    a, b = (5 / 2, 3 / 2), (10 / 3, 2 / 3)
    ax1.plot([a[0], b[0]], [a[1], b[1]], color=BLUE, lw=3.2, solid_capstyle="round")
    ax1.plot(*b, "o", color=INK, ms=5)
    ax1.text(2.55, 1.85, "$L_1:\\ x+y=4$", color=INK, fontsize=9)
    ax1.text(0.9, 0.8, "$P\\subset\\mathbb{R}^2$", color=INK, fontsize=10)
    ax1.set_title("(a) inequality $L_1$ replaced by equality", fontsize=9.5)
    ax1.set_xlim(-0.3, 4.2)
    ax1.set_ylim(-0.3, 2.7)
    clean(ax1)

    # (b) the reduced one-dimensional problem: y = 4 - x, maximize x + 8 on [5/2, 10/3]
    ax2.plot([2.2, 3.7], [0, 0], color=MUTED, lw=0.8)
    ax2.plot([2.5, 10 / 3], [0, 0], color=BLUE, lw=4, solid_capstyle="round")
    for v, lab in [(2.5, "$5/2$"), (10 / 3, "$10/3$")]:
        ax2.plot([v, v], [-0.04, 0.04], color=INK, lw=0.8)
        ax2.text(v, -0.16, lab, ha="center", fontsize=9, color=INK)
    ax2.plot(10 / 3, 0, "o", color=INK, ms=5, zorder=5)
    arrow(ax2, (2.75, 0.17), (3.15, 0.17), ORANGE, lw=1.8)
    ax2.text(2.95, 0.27, "$\\max\\ x+8$", ha="center", fontsize=9, color=INK)
    ax2.text(2.95, -0.42, "eliminate $y=4-x$;\nback substitution: $y^*=4-10/3=2/3$",
             ha="center", fontsize=8.5, color=INK)
    ax2.set_title("(b) reduced problem in $\\mathbb{R}^1$", fontsize=9.5)
    ax2.set_xlim(2.1, 3.8)
    ax2.set_ylim(-0.75, 0.55)
    ax2.axis("off")
    save(fig, "fig2_reduction")
    plt.close(fig)


def figure_selection_rule():
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 3.3))

    # (a) plane: directions on the unit circle, c pointing up
    ax1.add_patch(Circle((0, 0), 1, fill=False, color=MUTED, lw=0.7))
    def d(deg):
        return math.cos(math.radians(90 + deg)), math.sin(math.radians(90 + deg))
    a1, a2, ak = -58, 47, -22
    ax1.add_patch(Wedge((0, 0), 1, 90 + a1, 90 + a2, color=BLUE, alpha=0.13))
    arrow(ax1, (0, 0), d(0), ORANGE, lw=2.0, ms=13)
    arrow(ax1, (0, 0), d(a1), BLUE)
    arrow(ax1, (0, 0), d(a2), BLUE)
    arrow(ax1, (0, 0), d(ak), INK, lw=1.3)
    ax1.text(*(1.13 * v for v in d(0)), "$c$", ha="center", fontsize=11, color=INK)
    ax1.text(*(1.2 * v for v in d(a1)), "$a_1$", ha="center", fontsize=10, color=INK)
    ax1.text(*(1.2 * v for v in d(a2)), "$a_2$", ha="center", fontsize=10, color=INK)
    ax1.text(*(1.17 * v for v in d(ak)), "$a_k$", ha="center", fontsize=10, color=INK)
    ax1.text(0, -1.3, "smaller angle with $c$ than every active normal\n"
             "$\\Rightarrow a_k$ inside the cone $\\Rightarrow$ $k$ active",
             ha="center", fontsize=8.5, color=INK)
    ax1.set_title("(a) dimension 2: the rule is exact", fontsize=9.5)
    ax1.set_xlim(-1.45, 1.45)
    ax1.set_ylim(-1.75, 1.35)
    clean(ax1)

    # (b) dimension 3: cross-section of normal directions at height 1 (c = (0,0,1))
    tri = [(1, 0), (-1, 1), (-1, -1)]      # tips of the active normals L1, L2, L3
    ax2.add_patch(Polygon(tri, closed=True, facecolor=BLUE, alpha=0.13, edgecolor=BLUE, lw=1.0))
    ax2.add_patch(Circle((0, 0), 1, fill=False, color=MUTED, lw=0.9, ls="--"))
    ax2.plot(0, 0, "o", color=ORANGE, ms=7, zorder=5)
    ax2.text(0.07, -0.17, "$c$", fontsize=11, color=INK)
    for (x, y), lab, off in zip(tri, ["$a_1$", "$a_2$", "$a_3$"],
                                [(0.12, -0.05), (-0.05, 0.13), (-0.28, -0.05)]):
        ax2.plot(x, y, "o", color=BLUE, ms=5)
        ax2.text(x + off[0], y + off[1], lab, fontsize=10, color=INK)
    ax2.plot(0, 0.7, "o", color=AQUA, ms=7, zorder=5)
    ax2.text(0.1, 0.78, "$a_4$", fontsize=10, color=INK)
    ax2.text(0, -1.45, "inside the dashed disc: larger projection than $a_1$;\n"
             "$a_4$ is there but outside the cone, so $L_4$ is not principal",
             ha="center", fontsize=8.5, color=INK)
    ax2.set_title("(b) dimension 3: the counterexample", fontsize=9.5)
    ax2.set_xlim(-1.45, 1.45)
    ax2.set_ylim(-1.85, 1.35)
    clean(ax2)
    save(fig, "fig3_selection_rule")
    plt.close(fig)


# ---------------------------------------------------------------------------
# The 3-D counterexample
# ---------------------------------------------------------------------------
A3 = [(1, 0, 1), (-1, 1, 1), (-1, -1, 1), (0, 7, 10), (0, 0, -1)]
B3 = [0, 0, 0, 1, 10]


def _solve3(rows, rhs):
    M = [[F(v) for v in r] + [F(y)] for r, y in zip(rows, rhs)]
    for col in range(3):
        p = next((r for r in range(col, 3) if M[r][col] != 0), None)
        if p is None:
            return None
        M[col], M[p] = M[p], M[col]
        for r in range(3):
            if r != col and M[r][col] != 0:
                f = M[r][col] / M[col][col]
                M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    return tuple(M[i][3] / M[i][i] for i in range(3))


def polytope_faces():
    verts = set()
    for S in combinations(range(5), 3):
        x = _solve3([A3[i] for i in S], [B3[i] for i in S])
        if x is not None and all(sum(a * v for a, v in zip(A3[i], x)) <= B3[i] for i in range(5)):
            verts.add(x)
    faces = {}
    for k in range(5):
        on = [v for v in verts if sum(a * w for a, w in zip(A3[k], v)) == B3[k]]
        if len(on) < 3:
            continue
        cen = [sum(float(v[t]) for v in on) / len(on) for t in range(3)]
        n = [float(t) for t in A3[k]]
        # two in-plane axes
        e1 = [on[0][t] - F(cen[t]) for t in range(3)]
        e1 = [float(t) for t in e1]
        e2 = [n[1] * e1[2] - n[2] * e1[1], n[2] * e1[0] - n[0] * e1[2], n[0] * e1[1] - n[1] * e1[0]]
        def ang(v):
            w = [float(v[t]) - cen[t] for t in range(3)]
            return math.atan2(sum(a * b for a, b in zip(w, e2)), sum(a * b for a, b in zip(w, e1)))
        faces[k] = [tuple(float(t) for t in v) for v in sorted(on, key=ang)]
    return faces


def figure_counterexample():
    lp = LinearProgram.create(c=[0, 0, 1], A=A3, b=B3)
    sol = solve(lp)
    assert sol is not None and sol.certified and sol.x == (0, 0, 0)
    assert projection_order(lp)[0] == 3
    faces = polytope_faces()

    fig = plt.figure(figsize=(5.6, 4.6))
    ax = fig.add_subplot(projection="3d")
    for k, poly in faces.items():
        if k in (0, 1, 2):
            color, alpha = BLUE, 0.22
        elif k == 3:
            color, alpha = AQUA, 0.45
        else:
            color, alpha = MUTED, 0.10
        ax.add_collection3d(Poly3DCollection([poly], facecolor=color, alpha=alpha,
                                             edgecolor=INK, linewidths=0.5))
    ax.scatter([0], [0], [0], color=INK, s=22, depthshade=False)
    ax.quiver(0, 0, 0.3, 0, 0, 4.5, color=ORANGE, linewidth=2.0, arrow_length_ratio=0.18)
    ax.text(0.3, 0.3, 5.2, "$c$", fontsize=12, color=INK)
    p4 = [sum(v[t] for v in faces[3]) / len(faces[3]) for t in range(3)]
    n4 = (0, 0.7 * 3.5, 3.5)
    ax.quiver(*p4, *n4, color=AQUA, linewidth=1.8, arrow_length_ratio=0.18)
    ax.set_xlabel("$x$", labelpad=-12)
    ax.set_ylabel("$y$", labelpad=-12)
    ax.set_zlabel("$z$", labelpad=-12)
    ax.set_xticklabels([])
    ax.set_yticklabels([])
    ax.set_zticklabels([])
    for axis in (ax.xaxis, ax.yaxis, ax.zaxis):
        axis.pane.set_alpha(0.0)
        axis._axinfo["grid"]["color"] = (0.85, 0.85, 0.85, 1.0)
    ax.text(0.4, 0.4, -0.9, "$x^*$", fontsize=11, color=INK)
    ax.text(p4[0] + 0.4, p4[1] + 2.6, p4[2] + 3.6, "$a_4$", fontsize=11, color=INK)
    ax.view_init(elev=18, azim=-58)
    ax.set_box_aspect((1, 1, 0.75))
    save(fig, "fig4_counterexample")
    plt.close(fig)


if __name__ == "__main__":
    figure_geometry()
    figure_reduction()
    figure_selection_rule()
    figure_counterexample()
    print("figures written to", OUT)
