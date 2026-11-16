# principal-hyperfaces

The certified principal hyperface method for linear programming, in exact rational arithmetic.

The method of principal hyperfaces is due to G. G. Potapov and I. Yu. Grishin (2007). It picks the constraint whose normal points most nearly in the direction of the objective, turns it into an equality, eliminates one variable, and repeats. This package implements the *certified* variant described in the accompanying paper. It tries faces in the order of that rule, checks a dual certificate after every step, and backtracks when the check fails.

The same algorithm is formally verified in Lean 4 (`lean/PotapovSat/LP/Solver.lean`). The proven guarantees are:

- every returned point is feasible;
- if the problem has an optimal point, the returned point is optimal;
- when `certified` is `True`, `dual` is a certificate that proves optimality, and you can check it yourself with `is_certified`.

## Install

```bash
pip install ./python
```

## Use

The problem is `maximize c·x subject to A[i]·x <= b[i]`.

```python
from principal_hyperfaces import LinearProgram, solve, is_certified

lp = LinearProgram.create(
    c=[3, 2],
    A=[[1, 1], [1, 3], [2, -1], [-1, 0], [0, -1]],
    b=[4, 7, 6, 0, 0],
)
sol = solve(lp)
print(sol.x, sol.value)                    # (Fraction(10, 3), Fraction(2, 3)) 34/3
print(sol.certified, sol.dual)             # True (7/3, 0, 1/3, 0, 0)
assert is_certified(lp, sol.x, sol.dual)   # independent check
```

Numbers may be `int`, `str` such as `"3/2"`, `Fraction`, or `float`. Floats are converted exactly. `greedy(lp)` runs the original single-pass method, without backtracking, for comparison.

`solve` returns `None` when it finds no feasible point. For an unbounded problem, the result is a feasible point that is not certified.

## Complexity

In the worst case, backtracking explores exponentially many branches. The method guarantees correctness and a checkable proof for every certified answer, not speed.

## Tests

```bash
cd python && python3 -m pytest -q
```

The tests compare the results with the values checked in Lean and, on random problems, with exhaustive vertex enumeration.

## License

MIT
