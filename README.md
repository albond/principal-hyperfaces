# The Potapov–Grishin principal hyperface method, completed and machine-checked

This repository accompanies the paper *The Potapov–Grishin Principal Hyperface Method, Completed and Machine-Checked* (`paper/main.pdf`).

The principal hyperface method (G. G. Potapov and I. Yu. Grishin, 2007) solves a linear program geometrically. It selects the constraint whose normal points most nearly in the direction of the objective, turns that inequality into an equality, eliminates one variable, and repeats until the dimension reaches zero. The paper completes the method:

- **Correctness criterion.** A run of the method returns an optimum if and only if every selected hyperface is principal, that is, active at some optimum.
- **Existence.** If the objective is non-zero, a principal hyperface always exists. The proof uses Farkas' lemma, proved here over any ordered field by Fourier–Motzkin elimination.
- **Selection rule.** The projection rule is exact in the plane and can fail in three dimensions; there is an explicit counterexample.
- **Certified algorithm.** The rule orders the search, a dual certificate is checked after each step, and the search backtracks when the check fails. The algorithm always returns an optimum when one exists, and every certified answer carries a proof that can be checked independently.

Every result is formally verified in Lean 4.

## Contents

| Path | What it is |
|-|-|
| `lean/` | Lean 4 + Mathlib formalisation (`PotapovSat.LP`) |
| `python/` | `principal-hyperfaces`, a Python implementation of the certified algorithm in exact arithmetic |
| `paper/` | Paper source, PDF, figures and the script that draws them |

## Check the proofs

Install Lean with [elan](https://github.com/leanprover/elan), then run:

```bash
cd lean
lake exe cache get
lake build
```

The build has no `sorry`. For the main theorems, `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`. The solver's results on the worked examples are checked during the build.

## Use the Python package

```bash
pip install ./python
```

```python
from principal_hyperfaces import LinearProgram, solve

lp = LinearProgram.create(c=[3, 2], A=[[1, 1], [1, 3], [2, -1], [-1, 0], [0, -1]], b=[4, 7, 6, 0, 0])
sol = solve(lp)
print(sol.x, sol.value, sol.certified)   # (10/3, 2/3) 34/3 True
```

Run the tests with `cd python && python3 -m pytest -q`.

## Rebuild the paper

```bash
python3 paper/figures/make_figures.py
cd paper && pdflatex main.tex && pdflatex main.tex
```

## License

Code and Lean sources: MIT (see `LICENSE`). Paper: CC BY 4.0.
