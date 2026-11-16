# PotapovSat

Lean 4 formalisation of the certified principal hyperface method for linear programming.

| File | Content |
|-|-|
| `PotapovSat/LP/Basic.lean` | Linear programs over an ordered field, weak duality, certificates |
| `PotapovSat/LP/Elimination.lean` | One elimination step; a run is correct iff every chosen hyperface is principal |
| `PotapovSat/LP/Farkas.lean` | Farkas' lemma by Fourier–Motzkin elimination |
| `PotapovSat/LP/Optimality.lean` | Optimality conditions, strong duality at an optimum, existence of principal hyperfaces |
| `PotapovSat/LP/Redundancy.lean` | Cone obstruction for non-redundant constraints |
| `PotapovSat/LP/Plane.lean` | The projection rule is exact in dimension 2 |
| `PotapovSat/LP/Solver.lean` | The certified algorithm and its correctness and completeness |
| `PotapovSat/LP/Examples/` | Grishin's 2008 example, the 3-D counterexample, solver runs |

Build it with:

```bash
lake exe cache get
lake build
```
