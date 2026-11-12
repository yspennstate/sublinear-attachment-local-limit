# The local limit of sublinear preferential attachment graphs with fixed out-degree

Yitzchak Shmalo, November 2026.

Every new vertex sends m >= 2 edges to the existing vertices. The endpoints are chosen one after another with
probability proportional to f(in-degree), and in-degrees are updated after every edge. The attachment function f is
bounded away from zero, has bounded increments and satisfies f(k)/k -> 0; no monotonicity or concavity is assumed.

The paper proves that

- the total weight of the first n vertices divided by n converges almost surely to the unique c_f with
  sum_{k>=1} prod_{j<k} m f(j)/(c_f + m f(j)) = m;
- the empirical in-degree distribution converges almost surely to the law of a pure birth process with rates
  m f(k)/c_f observed at an independent exponential time of mean one;
- the graph converges locally in probability to an infinite random tree, and the probability of every finite ball
  of the limit is an explicit integral over the ages of its vertices.

This answers, for this class of attachment functions, Open Problem 24 (Deijfen, van der Hofstad) of Aletti et al.,
"Open problems in stochastic reinforcement models" (MATRIX-MFO Tandem Workshop, 2023), which asks for local limits of
preferential attachment models with a fixed number of out-edges beyond the affine case. Attachment functions with
f(k)/k -> gamma > 0, unbounded increments or inf f = 0 are not covered.

## Files

- `sublinear_attachment.pdf`, `sublinear_attachment.tex`, `sec_*.tex`: the paper.
- `code/sim_check.py`: simulation of the process and comparison with the limits
  (`python sim_check.py 1000000 11 out.json`).
- `data/sim_1e6_s*.json`: outputs of four runs with n = 10^6 (seeds 11, 12, 21, 22), used in Table 1.
- `lean/P0089_Finite.lean`: a Lean 4 proof, with Mathlib, of the finite steps of the paper: the two sums in the
  a priori bound on the degrees, the normalisation inequality used for the forced process, and the closed-form
  mass and mean of the two-level example (`lake env lean P0089_Finite.lean` in a Mathlib project; checked with Lean 4.33.1).

The paper is part of the Math Brain project: https://github.com/yspennstate/math-brain-public
