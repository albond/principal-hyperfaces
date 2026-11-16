import PotapovSat.LP.Solver
import PotapovSat.LP.Examples.Grishin2008
import PotapovSat.LP.Examples.ProjectionCounterexample

/-!
# Running the certified principal-hyperface method

Each `#eval` prints the constraint order chosen by the selection rule, then the returned
point, its objective value, whether the dual certificate checks, and the certificate.

* Grishin (2008): the first branch (L3, as in the paper) leads to the reported optimum
  `(12/5, 0, 78/5, 12/5, 24/5, 0)` with value `1008/5`, certified.
* Projection counterexample: the selection rule puts L4 first. Its certificate fails, the
  method backtracks and returns the true optimum `(0, 0, 0)`, certified by
  `(1/2, 1/4, 1/4, 0, 0)`.

These evaluations illustrate the algorithm. The guarantees are the theorems
`Problem.solve_isOptimal` and `Problem.Certified.isOptimal`.
-/

open PotapovSat.LP

/-- info: [2, 5, 3, 0, 4, 1, 6, 7, 8, 9, 10, 11] -/
#guard_msgs in
#eval Grishin2008.P.order

/--
info: some ([12 / 5, 0, 78 / 5, 12 / 5, 24 / 5, 0],
  1008 / 5,
  true,
  [0, 3, 47 / 10, 1 / 10, 0, 5 / 2, 0, 14, 0, 0, 0, 23 / 2])
-/
#guard_msgs (whitespace := lax) in
#eval (Grishin2008.P.solve).map fun r =>
  (List.ofFn r.1, Grishin2008.P.obj r.1, decide (Grishin2008.P.Certified r.1 r.2),
    List.ofFn r.2)

/-- info: [3, 0, 1, 2, 4] -/
#guard_msgs in
#eval ProjectionCounterexample.P.order

/-- info: some ([0, 0, 0], 0, true, [1 / 2, 1 / 4, 1 / 4, 0, 0]) -/
#guard_msgs (whitespace := lax) in
#eval (ProjectionCounterexample.P.solve).map fun r =>
  (List.ofFn r.1, ProjectionCounterexample.P.obj r.1,
    decide (ProjectionCounterexample.P.Certified r.1 r.2), List.ofFn r.2)
