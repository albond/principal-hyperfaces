"""Animated GIF of the principal hyperface method, for the README.

Run from the repository root:

    python3 paper/figures/make_animation.py

The scene is the 2-D example of the paper (Figure 1). The solution and the certificate
are computed exactly by the `principal_hyperfaces` package.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, Polygon, Wedge
from PIL import Image

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "python" / "src"))
from principal_hyperfaces import LinearProgram, projection_order, solve  # noqa: E402

OUT = Path(__file__).resolve().parent / "method.gif"

BLUE, ORANGE, AQUA = "#2a78d6", "#eb6834", "#1baf7a"
INK, MUTED, FILL = "#222222", "#9a9a9a", "#e9eef5"

plt.rcParams.update({"font.family": "serif", "mathtext.fontset": "cm", "font.size": 11})

LP = LinearProgram.create(c=[3, 2], A=[[1, 1], [1, 3], [2, -1], [-1, 0], [0, -1]],
                          b=[4, 7, 6, 0, 0])
SOL = solve(LP)
assert SOL is not None and SOL.certified
XS = tuple(float(v) for v in SOL.x)
assert projection_order(LP)[0] == 0

POLY = [(0, 0), (3, 0), (10 / 3, 2 / 3), (5 / 2, 3 / 2), (0, 7 / 3)]
FACES = [(0, (5 / 2, 3 / 2), (10 / 3, 2 / 3)), (1, (0, 7 / 3), (5 / 2, 3 / 2)),
         (2, (3, 0), (10 / 3, 2 / 3)), (3, (0, 0), (0, 7 / 3)), (4, (0, 0), (3, 0))]
NAMES = ["$L_1$", "$L_2$", "$L_3$", "$L_4$", "$L_5$"]
LABEL_OFF = {0: (0.05, 0.28), 1: (-0.1, 0.25), 2: (0.45, -0.1), 3: (-0.5, 0.0), 4: (0.0, -0.32)}

FPS = 20
STAGES = [  # (seconds, caption)
    (1.6, "Maximise $c\\cdot x$ over the polygon"),
    (3.0, "How strongly does $c$ point at each face?  (projection)"),
    (1.8, "Largest projection: make $L_1$ an equality, $x+y=4$"),
    (2.0, "One variable left: slide along $L_1$ to the best end"),
    (3.4, "Optimum: $c$ lies between the active normals (the certificate)"),
]


def ease(t: float) -> float:
    t = min(max(t, 0.0), 1.0)
    return t * t * (3 - 2 * t)


def arrow(ax, p, q, color, lw=1.6, ms=12, alpha=1.0):
    ax.add_patch(FancyArrowPatch(p, q, arrowstyle="-|>", mutation_scale=ms, color=color,
                                 lw=lw, alpha=alpha, shrinkA=0, shrinkB=0, zorder=5))


def proj(k: int) -> float:
    a = LP.A[k]
    return float(sum(x * y for x, y in zip(LP.c, a))) / math.sqrt(float(sum(x * x for x in a)))


def draw(ax, stage: int, t: float) -> None:
    ax.clear()
    ax.set_xlim(-1.35, 5.2)
    ax.set_ylim(-1.2, 3.0)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.set_title(f"{stage + 1}.  {STAGES[stage][1]}", fontsize=12, color=INK, pad=6)

    fade = 1.0 if stage < 2 else (1.0 - 0.75 * ease(t) if stage == 2 else 0.25)
    poly_alpha = ease(t) if stage == 0 else 1.0
    ax.add_patch(Polygon(POLY, closed=True, facecolor=FILL, edgecolor=MUTED, lw=0.9,
                         alpha=max(poly_alpha, 0.05) * (0.6 + 0.4 * fade), zorder=1))

    # objective vector
    cx, cy = 3 / math.hypot(3, 2), 2 / math.hypot(3, 2)
    grow = ease(t) if stage == 0 else 1.0
    if grow > 0.02:
        arrow(ax, (1.0, 0.7), (1.0 + 1.15 * cx * grow, 0.7 + 1.15 * cy * grow), ORANGE,
              lw=2.4, ms=15, alpha=fade if stage >= 3 else 1.0)
        ax.text(1.0 + 1.15 * cx + 0.05, 0.7 + 1.15 * cy + 0.1, "$c$", fontsize=14, color=INK,
                alpha=grow * (fade if stage >= 3 else 1.0))

    # normals and projections
    if stage >= 1:
        for idx, (k, a, b) in enumerate(FACES):
            appear = ease(t * len(FACES) * 1.25 - idx) if stage == 1 else 1.0
            if appear <= 0:
                continue
            winner = k == 0 and (stage >= 2 or t > 0.85)
            alpha = 1.0 if winner else (fade if stage >= 2 else 1.0)
            mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
            nx, ny = (float(v) for v in LP.A[k])
            r = math.hypot(nx, ny)
            L = 0.6 * appear
            arrow(ax, (mx, my), (mx + L * nx / r, my + L * ny / r), BLUE if winner else MUTED,
                  lw=1.8 if winner else 1.1, alpha=alpha)
            ox, oy = LABEL_OFF[k]
            ax.text(mx + 0.6 * nx / r + ox, my + 0.6 * ny / r + oy,
                    f"{NAMES[k]}  {proj(k):+.2f}", ha="center", va="center", fontsize=10,
                    color=INK, alpha=alpha * appear,
                    fontweight="bold" if winner else "normal")
    if stage >= 2 or (stage == 1 and t > 0.85):
        (a, b) = FACES[0][1], FACES[0][2]
        ax.plot([a[0], b[0]], [a[1], b[1]], color=BLUE, lw=4.2, solid_capstyle="round", zorder=4)

    # slide along the face
    if stage >= 3:
        a, b = FACES[0][1], FACES[0][2]
        s = ease(t) if stage == 3 else 1.0
        px, py = a[0] + (b[0] - a[0]) * s, a[1] + (b[1] - a[1]) * s
        ax.plot(px, py, "o", color=INK, ms=8, zorder=7)
        if stage == 3:
            ax.text(px - 0.1, py + 0.25, f"value $= {3 * px + 2 * py:.2f}$", fontsize=10,
                    color=INK, ha="right")

    # certificate: c in the cone of the active normals
    if stage == 4:
        g = ease(t * 1.6)
        ax.add_patch(Wedge(XS, 0.75 * g, math.degrees(math.atan2(-1, 2)), 45, color=BLUE,
                           alpha=0.15, zorder=2))
        for (vx, vy), col in [((1, 1), BLUE), ((2, -1), AQUA)]:
            r = math.hypot(vx, vy)
            arrow(ax, XS, (XS[0] + 0.7 * g * vx / r, XS[1] + 0.7 * g * vy / r), col, lw=1.8)
        arrow(ax, XS, (XS[0] + 0.7 * g * cx, XS[1] + 0.7 * g * cy), ORANGE, lw=2.2)
        ax.text(XS[0] + 0.85, XS[1] + 0.55, "$a_1$", fontsize=12, color=INK, alpha=g)
        ax.text(XS[0] + 0.85, XS[1] - 0.45, "$a_3$", fontsize=12, color=INK, alpha=g)
        ax.text(XS[0] - 0.15, XS[1] - 0.42, "$x^*=(10/3,\\ 2/3)$", fontsize=11, color=INK,
                ha="right", alpha=g)
        ax.text(3.55, -0.95, "$c = \\frac{7}{3}\\,a_1 + \\frac{1}{3}\\,a_3$,  "
                "both $\\geq 0$  $\\Rightarrow$  optimal",
                fontsize=12, color=INK, ha="center", alpha=ease(t * 2 - 0.6))


def main() -> None:
    fig, ax = plt.subplots(figsize=(6.8, 4.6), dpi=90)
    fig.subplots_adjust(left=0.01, right=0.99, top=0.9, bottom=0.01)
    frames = []
    for stage, (secs, _) in enumerate(STAGES):
        n = int(secs * FPS)
        for i in range(n):
            draw(ax, stage, i / max(n - 1, 1))
            fig.canvas.draw()
            img = Image.frombuffer("RGBA", fig.canvas.get_width_height(),
                                   fig.canvas.buffer_rgba()).convert("RGB")
            frames.append(img.quantize(colors=64, method=Image.Quantize.MEDIANCUT))
    plt.close(fig)
    durations = [1000 // FPS] * len(frames)
    durations[-1] = 1800  # hold the last frame
    frames[0].save(OUT, save_all=True, append_images=frames[1:], duration=durations, loop=0,
                   optimize=True, disposal=2)
    print(f"{OUT} ({len(frames)} frames, {OUT.stat().st_size // 1024} KiB)")


if __name__ == "__main__":
    main()
