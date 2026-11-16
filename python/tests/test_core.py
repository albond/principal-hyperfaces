"""Tests for the certified principal hyperface method.

The expected values for the two named examples are the ones checked in Lean
(`lean/PotapovSat/LP/Examples/SolverDemo.lean`).
"""

import random
from fractions import Fraction as F
from itertools import combinations

import pytest

from principal_hyperfaces import LinearProgram, greedy, is_certified, projection_order, solve

GRISHIN_2008 = LinearProgram.create(
    c=[3, 4, 8, 5, 12, 2],
    A=[
        [3, 2, -1, 6, 1, 1],
        [1, 6, 1, 0, 0, 2],
        [0, 0, 0, 1, 2, 0],
        [0, 0, 0, 3, 1, 0],
        [2, 1, 1, 0, 0, 0],
        [0, 0, 2, 0, 1, 3],
        [-1, 0, 0, 0, 0, 0],
        [0, -1, 0, 0, 0, 0],
        [0, 0, -1, 0, 0, 0],
        [0, 0, 0, -1, 0, 0],
        [0, 0, 0, 0, -1, 0],
        [0, 0, 0, 0, 0, -1],
    ],
    b=[24, 18, 12, 12, 24, 36, 0, 0, 0, 0, 0, 0],
)

COUNTEREXAMPLE_3D = LinearProgram.create(
    c=[0, 0, 1],
    A=[[1, 0, 1], [-1, 1, 1], [-1, -1, 1], [0, 7, 10], [0, 0, -1]],
    b=[0, 0, 0, 1, 10],
)


def test_grishin_2008_matches_lean():
    assert projection_order(GRISHIN_2008) == [2, 5, 3, 0, 4, 1, 6, 7, 8, 9, 10, 11]
    sol = solve(GRISHIN_2008)
    assert sol is not None
    assert sol.x == (F(12, 5), F(0), F(78, 5), F(12, 5), F(24, 5), F(0))
    assert sol.value == F(1008, 5)
    assert sol.certified
    assert sol.dual == tuple(F(v) for v in ["0", "3", "47/10", "1/10", "0", "5/2",
                                             "0", "14", "0", "0", "0", "23/2"])
    assert sol.steps[0][0] == 2  # first principal face is L3, as in the paper


def test_counterexample_greedy_fails_certified_repairs():
    assert projection_order(COUNTEREXAMPLE_3D) == [3, 0, 1, 2, 4]
    x_greedy = greedy(COUNTEREXAMPLE_3D)
    # the single-pass method misses the optimum: it ends at an infeasible face
    assert x_greedy is None or COUNTEREXAMPLE_3D.objective(x_greedy) < 0
    sol = solve(COUNTEREXAMPLE_3D)
    assert sol is not None
    assert sol.x == (0, 0, 0)
    assert sol.certified
    assert sol.dual == (F(1, 2), F(1, 4), F(1, 4), F(0), F(0))


def test_certificate_checker_rejects_wrong_dual():
    sol = solve(GRISHIN_2008)
    bad = list(sol.dual)
    bad[1] += 1
    assert not is_certified(GRISHIN_2008, sol.x, bad)


def test_infeasible_returns_none():
    lp = LinearProgram.create(c=[1, 1], A=[[1, 0], [-1, 0]], b=[-1, -1])
    assert solve(lp) is None


# --- comparison with exhaustive vertex enumeration ------------------------------


def _solve_square(M, v):
    n = len(M)
    M = [list(map(F, r)) + [F(y)] for r, y in zip(M, v)]
    for col in range(n):
        p = next((r for r in range(col, n) if M[r][col] != 0), None)
        if p is None:
            return None
        M[col], M[p] = M[p], M[col]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col] / M[col][col]
                M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    return [M[i][n] / M[i][i] for i in range(n)]


def _brute_force_optimum(lp):
    best = None
    for S in combinations(range(lp.m), lp.n):
        x = _solve_square([lp.A[i] for i in S], [lp.b[i] for i in S])
        if x is not None and lp.is_feasible(x):
            v = lp.objective(x)
            best = v if best is None or v > best else best
    return best


def _random_bounded_lp(rng, n, m):
    """Random constraints plus the box -10 <= x_j <= 10; the origin is feasible."""
    A, b = [], []
    for _ in range(m):
        A.append([rng.randint(-5, 5) for _ in range(n)])
        b.append(rng.randint(0, 10))
    for j in range(n):
        e = [0] * n
        e[j] = 1
        A.append(e)
        b.append(10)
        A.append([-v for v in e])
        b.append(10)
    c = [rng.randint(-5, 5) for _ in range(n)]
    return LinearProgram.create(c, A, b)


@pytest.mark.parametrize("seed", range(60))
def test_random_bounded_problems_match_vertex_enumeration(seed):
    rng = random.Random(seed)
    n = rng.choice([2, 3])
    lp = _random_bounded_lp(rng, n, rng.randint(2, 4))
    sol = solve(lp)
    assert sol is not None
    assert lp.is_feasible(sol.x)
    assert sol.value == _brute_force_optimum(lp)
