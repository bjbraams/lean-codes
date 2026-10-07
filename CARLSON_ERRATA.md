# Errata for Carlson (1977)

B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.

This file lists printed statements found to be false, or to need a qualification, while
formalizing the book in this project. Each entry gives the counterexample, a correction, and
the Lean declarations that record it. All Lean results cited use only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## Summary

| Location | Kind | Lean |
| --- | --- | --- |
| Theorem 6.6-2 | False as printed (lower bound) | `carlsonRPolynomial_coincident_counterexample` |
| Exercise 6.9-17, last two formulas | False on half of the stated domain | `carlsonRC_cot_sq_csc_sq_complex`, `carlsonRC_coth_sq_csch_sq_complex` |
| Theorem 7.4-2 | Definition needs a qualification | `carlson_polynomial_two_saddle_ratio_counterexample` |
| Table 9.3-1, row `2b = (1, 3, 3)` | Wrong sign of `C` | `carlsonR_table_9_3_1_row4` |
| Exercise 9.7-2 | False as stated (missing branch condition) | `carlsonRF_add_carlsonRF_shift` |
| Exercise 9.8-6 | False as stated (missing sign condition) | `integral_quartic_eq_integral_cubic_of_nonneg` |

## Theorem 6.6-2 (growth of R-polynomials)

**As printed.** For `zᵢ ≠ 0` and `c = ∑ bᵢ` not a nonpositive integer,
`limsup ‖Rₙ(b, z)‖^{1/n} = max ‖zᵢ‖`.

**Counterexample.** `b = (1/2, -1/2, 1)`, `z = (2, 2, 1)`. All printed hypotheses hold, but the
generating function (6.6-1) is
`(1 - 2s)^{-1/2} (1 - 2s)^{1/2} (1 - s)^{-1} = (1 - s)^{-1}`, and since `(c)ₙ/n! = 1`,
`Rₙ(b, z) = 1` for every `n`. The limsup is `1`, not `2`.

**Cause.** The proof asserts that the singularity of each factor `(1 - t zᵢ)^{-bᵢ}` survives in
the product; parameters at a repeated node can cancel.

**Correction.** The upper bound `limsup ≤ max ‖zᵢ‖` holds as printed. For the lower bound,
either require pairwise distinct nodes with the parameter at a maximal node not a nonpositive
integer, or first aggregate equal nodes and require that the summed parameter at a maximal node
is not a nonpositive integer.

**Lean.** `Carlson.carlsonRPolynomial_coincident_counterexample`,
`Carlson.eventually_norm_carlsonRPolynomial_le`, `Carlson.frequently_le_norm_carlsonRPolynomial`
(`Carlson.RPolynomial.Growth`), `Carlson.frequently_le_norm_carlsonRPolynomial_aggregate`
(`Carlson.Aggregation`).

## Exercise 6.9-17 (last two formulas)

**As stated.** For complex `θ, φ ≠ 0` with `|Re θ| < π/2` and `|Im φ| < π/2`,
`θ = R_C(cot² θ, csc² θ)` and `φ = R_C(coth² φ, csch² φ)`.

**Counterexample.** The right sides are even functions of the angle, the left sides are odd. For
`θ = -π/4` the right side is `R_C(1, 2) = π/4` (the exercise itself states `4 R_C(1, 2) = π`),
not `-π/4`; similarly `φ = -1`.

**Correction.** The first formula holds for `0 < Re θ < π/2`, the second for `Re φ > 0` and
`|Im φ| < π/2`; for negative real parts the left sides must be replaced by `-θ` and `-φ`.

**Lean.** `Carlson.TwoVariable.carlsonRC_cot_sq_csc_sq_complex`,
`Carlson.TwoVariable.carlsonRC_coth_sq_csch_sq_complex` (`Carlson.TwoVariable.R.ElementaryValues`).

## Theorem 7.4-2 (two-saddle asymptotics of Jacobi polynomials), p. 198

**As printed.** A two-saddle approximation on `V = {(x, y) : xy ≠ 0, x² ≠ y²}`, with uniform
asymptotics defined by convergence of the quotient to one.

**Problem.** At `α = β = -1/2`, `(x, y) = (1, i)`, the polynomial vanishes in every odd degree
(its normalization is nonsingular in every degree). No quotient of it by any sequence can
converge to one along the odd degrees.

**Correction.** Read the quotient with removable extensions, or state the result as a
two-saddle expansion with an additive error controlled by the sum of the magnitudes of the two
saddle terms. Neither formulation is refuted by the example; neither is yet proved here at
general parameters.

**Lean.** `Carlson.TwoVariable.carlson_polynomial_two_saddle_ratio_counterexample`
(`Carlson.Jacobi.AsymptoticZeros`).

## Table 9.3-1, row `2b = (1, 3, 3)`

**As printed.** `C = (z - y) d/5`, with `d = (x - y)(y - z)(z - x)`.

**Correction.** `C = (y - z) d/5`; the coefficients `C_G = 2(3x - t)`, `C_F = 3yz - s`,
`C_A = x(t² - 2s - xt)` are correct. Confirmed formally and numerically.

**Lean.** `Carlson.carlsonR_table_9_3_1_row4` (`Carlson.Elliptic.ReductionTables`), stated with
`C = -(x - y)(x - z)(y - z)²/5`.

## Exercise 9.7-2

**As stated.** For `x, y, z, λ, μ, ν ≥ 0` with at most one of `x + ν, y + ν, z + ν` zero,
`λ > ν`, `μ > ν`, and `ν` given by Carlson's formula,
`R_F(x + λ, y + λ, z + λ) + R_F(x + μ, y + μ, z + μ) = R_F(x + ν, y + ν, z + ν)`.

**Counterexample.** `x = y = 1`, `z = 1/100`, with `λ, μ > 0` on the other branch of Euler's
relation (9.7-11). The formula gives `ν = 0` and all stated hypotheses hold, but numerically
the left side is `≈ 1.6794` while `R_F(x, y, z) ≈ 1.4780`.

**Correction.** Add the branch condition of Theorem 9.7-1, `(λ - ν)(μ - ν) > f(ν)`.

**Lean.** `Carlson.carlsonRF_add_carlsonRF_shift` (`Carlson.Elliptic.ChapterNineExercises`).

## Exercise 9.8-6

**As stated.** For `a > 0` and `Q(s) = as⁴ + bs³ + cs² + ds + e` positive on `(0, ∞)` (with
`e ≥ 0`), and `C(t) = t³ + ft² + gt + h` with `f = c + 6√(ae)`, `g = bd + 4c√(ae) + 8ae`,
`h = (b√e + d√a)²`, `∫₀^∞ Q(s)^{-1/2} ds = ∫₀^∞ C(t)^{-1/2} dt`.

**Counterexample.** `Q(s) = s⁴ - 1.9s³ + 2s² - 1.9s + 1` is positive on `(0, ∞)`, but the two
sides are `3.3721…` and `1.2574…`. Since `C` depends on `b, d` only through `bd` and
`(b√e + d√a)²`, it is unchanged when `b` and `d` change sign together, while the left side is
not.

**Correction.** Numerically the identity holds exactly when `b√e + d√a ≥ 0`, which is when the
substitution `t = 2as² + bs + 2√a √Q(s) - 2√(ae)` (for which `C(t) = t′(s)² Q(s)`) is
increasing. It is proved here for nonnegative coefficients; the sharp condition is not yet
proved.

**Lean.** `Carlson.integral_quartic_eq_integral_cubic_of_nonneg`
(`Carlson.Elliptic.QuarticIntegral`).
