"""Certified principal hyperface method for linear programming.

The problem is

    maximize c . x   subject to   A[i] . x <= b[i]  for every row i,

solved in exact rational arithmetic (``fractions.Fraction``).

This module mirrors the algorithm ``PotapovSat.LP.Problem.solve`` that is formally
verified in Lean 4 (``lean/PotapovSat/LP/Solver.lean``). For every input, the two
implementations make the same choices in the same order and return the same answer.

The method of principal hyperfaces is due to G. G. Potapov and I. Yu. Grishin (2007).
The certified variant with backtracking is described in the accompanying paper.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Iterable, Sequence, Union

Number = Union[int, Fraction, str, float]
Vector = tuple[Fraction, ...]


def _q(value: Number) -> Fraction:
    """Convert a number to an exact rational. Floats are converted exactly."""
    return value if isinstance(value, Fraction) else Fraction(value)


def dot(u: Sequence[Fraction], v: Sequence[Fraction]) -> Fraction:
    """Dot product of two vectors of equal length."""
    return sum((a * b for a, b in zip(u, v, strict=True)), Fraction(0))


@dataclass(frozen=True)
class LinearProgram:
    """``maximize c . x`` subject to ``A[i] . x <= b[i]``, stored exactly.

    Build instances with :meth:`create`, which converts numbers to ``Fraction``.
    """

    c: Vector
    A: tuple[Vector, ...]
    b: Vector

    @classmethod
    def create(
        cls,
        c: Iterable[Number],
        A: Iterable[Iterable[Number]],
        b: Iterable[Number],
    ) -> "LinearProgram":
        c_q = tuple(_q(v) for v in c)
        A_q = tuple(tuple(_q(v) for v in row) for row in A)
        b_q = tuple(_q(v) for v in b)
        if len(A_q) != len(b_q):
            raise ValueError(f"A has {len(A_q)} rows but b has {len(b_q)} entries")
        for i, row in enumerate(A_q):
            if len(row) != len(c_q):
                raise ValueError(f"row {i} of A has {len(row)} entries, expected {len(c_q)}")
        return cls(c_q, A_q, b_q)

    @property
    def n(self) -> int:
        """Number of variables."""
        return len(self.c)

    @property
    def m(self) -> int:
        """Number of constraints."""
        return len(self.b)

    def objective(self, x: Sequence[Fraction]) -> Fraction:
        return dot(self.c, x)

    def is_feasible(self, x: Sequence[Fraction]) -> bool:
        return all(dot(row, x) <= bi for row, bi in zip(self.A, self.b))

    def is_active(self, i: int, x: Sequence[Fraction]) -> bool:
        return dot(self.A[i], x) == self.b[i]


def is_certified(lp: LinearProgram, x: Sequence[Fraction], y: Sequence[Fraction]) -> bool:
    """Check that ``y`` is a dual certificate proving ``x`` optimal.

    The conditions are: ``x`` feasible, ``y >= 0``, ``sum_i y[i] * A[i] = c`` and
    ``c . x = y . b``. By weak duality they imply optimality
    (Lean: ``Problem.isOptimal_of_certificate``).
    """
    if len(y) != lp.m or not lp.is_feasible(x) or any(v < 0 for v in y):
        return False
    for j in range(lp.n):
        if sum((y[i] * lp.A[i][j] for i in range(lp.m)), Fraction(0)) != lp.c[j]:
            return False
    return lp.objective(x) == dot(y, lp.b)


# --- the selection rule -------------------------------------------------------


def projection_score(lp: LinearProgram, k: int) -> Fraction:
    """Squared projection ``(c . A_k)^2 / |A_k|^2`` if positive, else ``-1``.

    Ranking constraints by this score is the same as ranking them by the projection
    ``(c . A_k) / |A_k|`` of the objective vector onto the constraint normal
    (the rule of Potapov and Grishin).
    """
    p = dot(lp.c, lp.A[k])
    if p > 0:
        return p * p / dot(lp.A[k], lp.A[k])
    return Fraction(-1)


def projection_order(lp: LinearProgram) -> list[int]:
    """Constraint indices by decreasing projection score; ties keep index order."""
    return sorted(range(lp.m), key=lambda k: projection_score(lp, k), reverse=True)


def pivot(lp: LinearProgram, k: int) -> int | None:
    """Variable with the largest ``|A[k][j]|`` (first one on ties), or ``None`` if row ``k`` is zero."""
    if lp.n == 0:
        return None
    j = max(range(lp.n), key=lambda t: abs(lp.A[k][t]))
    return j if lp.A[k][j] != 0 else None


# --- one step of the method -----------------------------------------------------


def reduce(lp: LinearProgram, k: int, j: int) -> LinearProgram:
    """Eliminate ``x_j`` with the equality ``A[k] . x = b[k]``; the dimension drops by one."""
    akj = lp.A[k][j]
    keep = [t for t in range(lp.n) if t != j]
    c = tuple(lp.c[t] - lp.c[j] * lp.A[k][t] / akj for t in keep)
    A = tuple(tuple(row[t] - row[j] * lp.A[k][t] / akj for t in keep) for row in lp.A)
    b = tuple(bi - row[j] * lp.b[k] / akj for row, bi in zip(lp.A, lp.b))
    return LinearProgram(c, A, b)


def lift(lp: LinearProgram, k: int, j: int, y: Sequence[Fraction]) -> Vector:
    """Back substitution: insert the value of ``x_j`` forced by ``A[k] . x = b[k]``."""
    keep = [t for t in range(lp.n) if t != j]
    rest = sum((lp.A[k][t] * yt for t, yt in zip(keep, y)), Fraction(0))
    xj = (lp.b[k] - rest) / lp.A[k][j]
    x = list(y)
    x.insert(j, xj)
    return tuple(x)


def compose_dual(lp: LinearProgram, k: int, j: int, z: Sequence[Fraction]) -> Vector:
    """Dual multipliers for ``lp`` assembled from those of ``reduce(lp, k, j)``."""
    rest = sum((z[i] * lp.A[i][j] for i in range(lp.m) if i != k), Fraction(0))
    zk = (lp.c[j] - rest) / lp.A[k][j]
    return tuple(zk if i == k else z[i] for i in range(lp.m))


# --- the certified method -------------------------------------------------------


@dataclass
class Stats:
    """Search statistics, for inspection."""

    calls: int = 0
    certified_exits: int = 0
    fallbacks: int = 0


@dataclass(frozen=True)
class Solution:
    """Result of :func:`solve`.

    ``certified`` is True when ``dual`` is a checked dual certificate, so ``x`` is
    provably optimal. Each step of the method is recorded in ``steps`` as
    ``(constraint, pivot_variable)``, outermost first.
    """

    x: Vector
    value: Fraction
    dual: Vector
    certified: bool
    steps: tuple[tuple[int, int], ...] = ()
    stats: Stats = field(default_factory=Stats, compare=False)


def _solve(lp: LinearProgram, stats: Stats) -> tuple[Vector, Vector, tuple] | None:
    stats.calls += 1
    zero_x = tuple(Fraction(0) for _ in range(lp.n))
    zero_y = tuple(Fraction(0) for _ in range(lp.m))
    if lp.n == 0:
        return ((), zero_y, ()) if lp.is_feasible(()) else None

    order = projection_order(lp)

    def step(k: int):
        j = pivot(lp, k)
        if j is None:
            return None
        sub = _solve(reduce(lp, k, j), stats)
        if sub is None:
            return None
        y, z, steps = sub
        return lift(lp, k, j, y), compose_dual(lp, k, j, z), ((k, j),) + steps

    # 1. first branch, in the order of the selection rule, whose certificate checks
    for k in order:
        r = step(k)
        if r is not None and is_certified(lp, r[0], r[1]):
            stats.certified_exits += 1
            return r

    # 2. repair failed everywhere: return the best feasible candidate
    stats.fallbacks += 1
    candidates = []
    if lp.is_feasible(zero_x):
        candidates.append((zero_x, zero_y, ()))
    for k in order:
        r = step(k)
        if r is not None:
            candidates.append(r)
    if not candidates:
        return None
    return max(candidates, key=lambda r: lp.objective(r[0]))


def solve(lp: LinearProgram) -> Solution | None:
    """Run the certified principal hyperface method.

    Guarantees, proved in Lean 4 for the identical algorithm:

    * every returned point is feasible (``Problem.solve_feasible``);
    * if the problem has an optimal point, the returned point is optimal
      (``Problem.solve_isOptimal``);
    * if ``certified`` is True, the returned ``dual`` proves optimality
      (``Problem.Certified.isOptimal``).

    Returns ``None`` when no feasible point is found. When the problem is unbounded,
    the result (if any) is a feasible point, but it is not certified.
    """
    stats = Stats()
    r = _solve(lp, stats)
    if r is None:
        return None
    x, y, steps = r
    return Solution(
        x=x,
        value=lp.objective(x),
        dual=y,
        certified=is_certified(lp, x, y),
        steps=steps,
        stats=stats,
    )


def greedy(lp: LinearProgram) -> Vector | None:
    """The original single-pass method: always follow the selection rule, never
    backtrack. Fast, but not always optimal (see the 3-D counterexample in the paper).
    """
    if lp.n == 0:
        return () if lp.is_feasible(()) else None
    for k in projection_order(lp):
        j = pivot(lp, k)
        if j is not None:
            y = greedy(reduce(lp, k, j))
            return None if y is None else lift(lp, k, j, y)
    return None
