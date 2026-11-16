"""Certified principal hyperface method (Potapov–Grishin method, certified variant).

Example::

    from principal_hyperfaces import LinearProgram, solve

    lp = LinearProgram.create(c=[3, 2], A=[[1, 1], [1, 3], [-1, 0], [0, -1]], b=[4, 6, 0, 0])
    sol = solve(lp)
    sol.x, sol.value, sol.certified
"""

from .core import (
    LinearProgram,
    Solution,
    Stats,
    compose_dual,
    dot,
    greedy,
    is_certified,
    lift,
    pivot,
    projection_order,
    projection_score,
    reduce,
    solve,
)

__all__ = [
    "LinearProgram",
    "Solution",
    "Stats",
    "compose_dual",
    "dot",
    "greedy",
    "is_certified",
    "lift",
    "pivot",
    "projection_order",
    "projection_score",
    "reduce",
    "solve",
]

__version__ = "1.0.0"
