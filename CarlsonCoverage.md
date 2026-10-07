# Carlson coverage

Status of the formalization against B. C. Carlson, *Special Functions of Applied Mathematics*
(Academic Press, 1977), Chapters 3 and 5–9, and against Carlson, *Dirichlet averages of
x^t log x*, SIAM J. Math. Anal. 18 (1987). The scans are in `Carlson/References/`. Section,
theorem and equation numbers refer to the book unless stated otherwise.

"Not located" means that no corresponding Lean statement exists in the project. Where a result
is proved under narrower hypotheses than in the book, the hypotheses are stated. No item is
represented by an admitted proof. Related documents:

* [CARLSON_ERRATA.md](CARLSON_ERRATA.md): printed statements found false or needing
  qualification, with counterexamples and the proved corrections.
* [SYNOPSIS_CARLSON.md](SYNOPSIS_CARLSON.md) and [SYNOPSIS_GAPS.md](SYNOPSIS_GAPS.md): the
  mathematical summary and the list of open items.
* [CarlsonChapter6Exercises.md](CarlsonChapter6Exercises.md),
  [CarlsonChapter7Exercises.md](CarlsonChapter7Exercises.md): exercise-by-exercise status for
  Chapters 6 and 7; the Chapter 8 and 9 exercises are tabulated below.
* [CARLSON_ARTICLES.md](CARLSON_ARTICLES.md): Carlson's articles in relation to the book.

## Conventions of the formalization

* `regCarlsonR t b z` (`Carlson.R.Explicit`) is the single definition of the regularized
  R-function `R_t(b; z)/Γ(∑ b)`: for every complex exponent and parameter vector and every node
  vector, by a finite recursion ending in Carlson's single Euler integral; it is jointly
  holomorphic in exponent, parameters and slit-plane nodes. `carlsonR` is `Γ(∑ b) regCarlsonR`.
  Agreement with the native integral `regCarlsonRIntegral` holds whenever the whole convex hull of
  the nodes lies in the slit plane; slit-plane membership of the individual nodes does not
  suffice. `regCarlsonL` (`Carlson.L.Continuation`) is the exponent derivative of `regCarlsonR`.
* Ordinary functions are Gamma multiples of regularized ones; Lean's totalized value at a Gamma
  pole is not a finite value of the ordinary function.
* Functions at boundary points of their domains (a vanishing variable) are represented by
  limits, not by values of the slit-domain function.
* Index types may be empty; statements that need nonempty index types say so.

## Chapter 3: Gamma function foundations

Mathlib supplies most of the chapter; local supplements are in `Pochhammer/` and `ToMathlib/`.

| Source | Available | Not located |
| --- | --- | --- |
| §3.2 integral, recurrence, Pochhammer ratios | Mathlib `Gamma.Basic`, `Gamma.Beta`; `Pochhammer.Gamma` | — |
| §3.3 holomorphy and poles | Mathlib differentiability and the limit at `0`; one-variable pole, residue and removability criteria in `Dirichlet.GammaPoles` | the packaged simple pole with residue `(-1)ⁿ/n!` at every nonpositive integer as a statement about `Γ` |
| §3.4 asymptotic ratio, Euler limit | Mathlib `GammaSeq_tendsto_Gamma` | the ratio asymptotic with fixed complex shifts; the infinite product as a reusable statement |
| §3.5 log-convexity, Bohr–Mollerup | Mathlib convexity and Bohr–Mollerup | strict log-convexity and its equality consequences |
| §3.6 reciprocal Gamma, digamma | Mathlib nonvanishing, entire `1/Γ`, digamma recurrence and values | Weierstrass's product; partial-fraction expansions of digamma |
| §3.7 duplication | Mathlib | — |
| §3.8 Stirling | Mathlib factorial Stirling | the logarithmic correction series, sectorial Stirling theorem and Gamma-ratio corollary |
| §3.9 reflection | Mathlib | — |
| §3.10 inequalities | Mathlib minimum in `(1, 2)`; `ToMathlib.Analysis.SpecialFunctions.GammaBounds`, `GammaRatio` | uniqueness of the minimum; the chapter's quantitative and complex bounds |
| §3.11 Euler measures, rotated rays | real Gamma laws and `Dirichlet.Gamma`; Euler measures and rotated rays for `₂F₀` in `Carlson.T.TwoF0`, `TwoF0Sector` | a general normalized complex Euler functional with moments and total variation |

Most Chapter 3 exercises are not formalized.

## Chapter 5: averages of an arbitrary function

| Section | Coverage | Not located or narrower |
| --- | --- | --- |
| 5.1–5.2 averaging | Affine simplex kernel, native integrals, parameter analyticity, permutation symmetry, equal-node aggregation (5.2-4, all complex parameters), diagonal values, affine substitution (`Dirichlet.Average.Basic`, `Associated.Analytic`, `Aggregation`) | — |
| 5.3 derivatives | Joint analyticity for holomorphic functions on convex open sets (5.3-3); differentiation under the integral, iterated; (5.3-4) for every power (`Dirichlet.Average.Intertwining`). Case (i), real nodes and `f ∈ Cⁿ` on an open interval: `Cⁿ` regularity, (5.3-2)–(5.3-4) (`Dirichlet.Average.RealNodes`) | — |
| 5.4 Euler–Poisson | 5.4-1 on the native convergence region for holomorphic `f`; case (i) for `f ∈ C²`; continued R and L satisfy their full systems on slit-plane nodes | the substitutions (5.4-3)–(5.4-21); the system for general continued averages at all parameters |
| 5.5 Newton–Taylor | Divided differences, recursion, symmetry, Newton–Taylor with average remainder, Taylor case, repeated integrals (`Dirichlet.Average.NewtonTaylor`); case (i) (`StdSimplexMeasure.Real.NewtonTaylor`); fractional integral (5.5-14), (5.5-15), continuation in the order and (5.5-16) for holomorphic `f` on convex sets (entire) and `f ∈ Cⁿ` (on `re ν > -n`) (`TwoVariable.FractionalIntegral`, `FractionalContinuation`) | (5.5-10)–(5.5-13) for merely continuous `f`, beyond (5.5-15) |
| 5.6 associated functions | Parameter shift, tangent/backward shift, three-node, multiplication by the argument, 5.6-4, all on the full parameter space (`Dirichlet.Average.ContinuedRelations`) | — |
| 5.7 power series | Termwise averaging; Taylor representation on a disk with entire-parameter continuation (`RPolynomial.PowerSeries`, `TaylorContinuation`) | conventional hypergeometric notation for general series |
| 5.8 exponential averages | S: native, entire series, joint entire dependence, derivatives (5.8-2), translation, symmetry, aggregation, zero-parameter deletion, ordinary normalization; (5.8-6) `S(a, b; x, 0) = ₁F₁` (`regCarlsonS_pair_zero_right`); (5.8-23) for `J_μ` | Whittaker and physical special functions |
| 5.9 power averages | R on the slit domain: joint holomorphy, associated relations, node derivatives, Euler transformation, two-variable interchange; homogeneity (5.9-3) under `arg μ + arg zᵢ ∈ (-π, π)` (`R.Homogeneity`); Exercises 5.9-6 to 5.9-10, 5.9-13; zero-parameter deletion | arbitrary-order continued node derivatives as a general R theorem |
| 5.10 confluence | (5.10-1) with complex exponent tending to infinity and the refinement (5.10-9) (`R.Confluence`); 5.10-2 on its native domain | confluence of the continued function at non-convergent parameters |
| 5.11 Cauchy averages | Resolvent analyticity (5.11-1); 5.11-2 on circles for every derivative order, continued to all parameters; on `C¹` cycles homologous to zero avoiding the node hull, with the index as weight (`Dirichlet.Average.CauchyCycle`) | rectifiable non-`C¹` Jordan curves |
| 5.12 reciprocal exponential | T: native, joint continuation on the zero-avoiding hull domain, principal slit-plane T-series (`Carlson.T`). `₂F₀`: Definition 5.12-3 (double and single Euler integrals), remainder representation (5.12-10), Theorems 5.12-2, 5.12-4, 5.12-5, error bounds (5.12-15), (5.12-16) and expansion (5.12-17), sectorial continuation (5.12-6) with bounds on closed subsectors, (5.12-7) for `|ph(-x)| < π`, Theorems 5.12-8 (5.12-18) and 5.12-9 (5.12-20), zero-node limit (5.12-2), (5.12-3) | the identifications (5.12-21)–(5.12-28) (Tricomi, Whittaker, parabolic cylinder, Macdonald, Hankel) |

## Chapter 6: averages of powers and continuation

Exercise status: [CarlsonChapter6Exercises.md](CarlsonChapter6Exercises.md).

| Section | Coverage | Not located or narrower |
| --- | --- | --- |
| 6.1–6.2 polynomials | Multi-index Pochhammer numerator, entire regularized polynomial, zero-parameter deletion, (6.2-7) estimate (`RPolynomial.Basic`, `.Coefficients`, `.SharpEstimates`, `Carlson.ZeroParameter`); Theorem 6.2-5 (`RPolynomial.Concentration`); Theorem 6.2-6 for any number of nodes (`Normalization.EqualParameter`) | symmetric-function specializations (6.2-11), (6.2-12) |
| 6.3 negative parameters | Taylor continuation 6.3-1, zero-parameter deletion (6.3-2), entire S, continued resolvents; 6.3-6 continuation for every derivative order on convex open domains, and its contour form on `C¹` cycles; Corollary 6.3-7 | rectifiable Jordan-curve form of 6.3-6 |
| 6.4 binomial theorem | `regCarlsonRPolynomial_add_const` for every parameter; Carlson's class `A_k` and (6.4-4) (`RPolynomial.Appell`); (6.4-6); the theory of Carlson (1970) (`ToMathlib.Analysis.AppellSequence`), Example 11 (`Jacobi.Appell`) | (2.14), (2.15) of Carlson (1970) in closed form |
| 6.5 linear transformation | Arbitrary-index numerator transformation; six `₂F₁` forms and their transformations (`TwoVariable.RPolynomial.Hypergeometric`) | the transformation group of order six as a group action |
| 6.6 generating functions | 6.6-1 with absolute convergence; Theorem 6.6-2 upper bound, and lower bound when the summed parameter at the maximal nodes is not a nonpositive integer (`RPolynomial.Growth`, `Carlson.Aggregation`); the printed statement is false (see the errata) | Stirling and Lucas identifications |
| 6.7 classical polynomials | (6.7-19), (6.7-21), `C_n^ν(1)` (`Jacobi.GegenbauerProduct`); Jacobi, Legendre, Chebyshev, Gegenbauer identifications through Chapter 7 | direct Carlson-function forms of the section's formulas |
| 6.8 R continuation | Single-integral representations; joint dependence on exponent, parameters and slit-plane nodes (6.8-2); Euler inversion (6.8-3); (6.8-7) on `C¹` cycles (`R.ContourRepresentation`); Theorem 6.8-4 (`equalR`); the two-variable `Γ(β + 1/2)` normalization (`TwoVariable.EqualParameterSlit`); the question on p. 156 for simply connected domains (`Dirichlet.Average.SimplyConnected`) | Legendre and Gegenbauer functions of complex degree |
| 6.9 first quadratic transformation | 6.9-1, 6.9-2 (regularized and ordinary), 6.9-3 (`regRSlit_firstQuadratic`), (6.9-8)–(6.9-11) division-free, 6.9-4 (`carlsonRC_of_lt`, `carlsonRC_of_gt`), Kummer's second formula, Bessel identifications (6.9-18)–(6.9-21), (6.9-25) and integer-order (6.9-22) | general-order (6.9-22) (needs a branch condition) |
| 6.10 second quadratic transformation | 6.10-1 (`regRSlit_secondQuadratic`) with its double series; 6.10-3 division-free (both transformed nodes squared; the unsquared variant is refuted by `secondQuadratic_unsquared_counterexample`); hybrid 6.10-4; `R_K` and Gauss's AGM formula (6.10-2); `R_C` and Borchardt's algorithm (6.10-5) with (6.10-27)–(6.10-30); (6.10-12), (6.10-18) last member and (6.10-19) | equality of the middle and last members of (6.10-18) for positive order |
| 6.11 product formulas | 6.11-1 and 6.11-2 for all complex parameters (`TwoVariable.BilateralContinuation`); 6.11-3 and 6.11-4 for complex angles (`Jacobi.GegenbauerProductComplex`); (6.11-6) (`Jacobi.GegenbauerAddition`) | — |

**Quadratic transformations.** With `A = ((x+y)/2)²`, `G = xy` and
`q(β) = 2^{1-2β}√π/Γ(β)`, for every complex `t, β` and `re x, re y > 0`:
`ℛ_{2t}(β, β; x, y) = q(β) ℛ_t(β + t, 1/2 - t; A, G)` and
`ℛ_t(β, β; x², y²) = q(β) ℛ_t(2β + t, 1/2 - β - t; A, G)`; `A`, `G`, `x²`, `y²` lie in the slit
plane. Since `q(β) = 0` at `β = 0, -1, …`, the values there are carried by the finer
normalization `regEqualR t β x y = 2^{2β-1}/√π · equalR t β (x, y)`, jointly holomorphic on
slit-plane nodes, for which both transformations hold on `re x, re y > 0` including those `β`;
likewise the L identities (6.4), (6.5), (6.8) of Carlson (1987) for `regEqualL`.

## Chapter 7: Jacobi polynomials and series

Notation: `pₙ = jacobiOn α β r s n` (monic, foci `r, s`), `qₙ = jacobiSecondKind α β r s n`,
`μ(x) = jacobiEllipseRadius r s x`; Carlson's condition `(1+α, 1+β) ∈ U₂` is
`IsGammaRegular (α + β + 2)`. Exercise status:
[CarlsonChapter7Exercises.md](CarlsonChapter7Exercises.md).

| Section | Coverage | Not located or narrower |
| --- | --- | --- |
| 7.1 Taylor and Jacobi series | `jacobiOn`, `jacobiSecondKind`; `eval_jacobiOn_eq_numerator`; joint analyticity of `qₙ` in all five variables; `x^{n+1} qₙ → 1`; coincident foci; both recurrences of Exercise 7.1-6, the second kind at every degree when `α + β + 1` is regular | the second-kind recurrence at small degrees for exceptional `α + β + 1` |
| 7.2 biorthogonality | Theorem 7.2-1 on circles and on `C¹` cycles with the index as factor; contour independence; Theorem 7.2-2 at arbitrary complex endpoints with duality | — |
| 7.3 addition theorems | Gegenbauer polynomials at every parameter and their derivatives; (7.3-7); Theorem 7.3-1 for complex arguments; its Jacobi form; (7.3-11) in both forms (`Jacobi.GegenbauerAddition`) | — |
| 7.4 asymptotics | Saddle-curve deformation of the Euler integral; Lemma 7.4-1 on `W`; `qₙ(z) ∼ C(4/Λ(z))ⁿ`, `C ≠ 0`, uniformly on compact sets off the segment, all complex parameters (`Jacobi.SaddleLaplace`, `SaddleUniform`), the second-kind part of Corollary 7.4-4; Theorem 7.4-3 uniformly on compact subsets of `W` (`SaddleJoint`); the exact Chebyshev formula (7.4-1) and its dominant-term limit (`PolynomialSaddle`); the obstruction to the printed ratio definition of 7.4-2 (`AsymptoticZeros`, see the errata) | Theorem 7.4-2 and the polynomial part of Corollary 7.4-4 at general parameters |
| 7.5 convergence | Ellipse geometry, elliptic disks and exteriors, confocal ellipses as `C¹` cycles of index one; Theorem 7.5-1 (pointwise), 7.5-2 (maxima on confocal ellipses), 7.5-3 | the compact-uniform root convergence asserted in 7.5-1; growth is stated by explicit bounds rather than `limsup` |
| 7.6 Jacobi series | Lemma 7.6-1 on `μ(x) < μ(y)`; Theorem 7.6-2 on open elliptic disks and general cycles, uniqueness, maximal ellipse of convergence, entire functions; (7.6-8) on circles and confocal ellipses | — |
| 7.7 applications | Examples 7.7-1 (plane wave with S-coefficients, spherical-Bessel form), 7.7-2 (Fourier cosine, (6)), 7.7-3 ((7)–(10), with `J_m` and `I_m`), 7.7-4 (Gegenbauer's addition theorem for Bessel functions, `Jacobi.BesselExercises`) | — |
| 7.8 Rodrigues and orthogonality | Rodrigues for real and complex parameters and at complex endpoints; orthogonality and norms for `α, β > -1` and `re α, re β > -1`; Representation 7.8-2 and Theorem 7.8-3 on complex segments; the jump (7.8-5) for all complex parameters (`Jacobi.SecondKindJump`); separate boundary values and principal values for `re α, re β > -1` (`Jacobi.SecondKindPlemelj`); orthogonality deduced from biorthogonality | separate boundary values outside `re α, re β > -1`; endpoint finite parts; branches along contours crossing the segment |
| 7.9 Laguerre | `monicLaguerre`; Theorems 7.9-1, 7.9-3, 7.9-4; Rodrigues (7.9-8); the second kind (7.9-4) for `re(1+β+n) > 0`; Theorem 7.9-5 and its converse | Theorem 7.9-3 assumes the growth bound also for `f⁽ⁿ⁾`; Examples 7.9-6, 7.9-7 |
| 7.10 Hermite | `monicHermite`; Theorems 7.10-1, 7.10-3, 7.10-4; Rodrigues (7.10-6); the second kind (7.10-3) | Theorem 7.10-3 assumes the growth bound also for `f⁽ⁿ⁾`; Example 7.10-5 |

## Chapter 8: averages of `x^t`

| Item | Status | Lean |
| --- | --- | --- |
| 8.1-1 (straight path) | All complex parameters, each affine factor in the slit plane | `integral_segment_eq_regCarlsonR` (`Carlson.R.IntegralEvaluation`) |
| 8.1-2, 8.1-3 (rays) | With the principal-phase condition explicit | `integral_Ioi_prod_cpow_eq_regCarlsonR`, `integral_Ioi_ray_eq_regCarlsonR`, `integral_Ioi_ray_neg_eq_regCarlsonR`, `carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR` |
| `R_F` (8.2-5), (8.2-6), symmetry, (8.2-13) | Proved | `carlsonRF`, `carlsonRF_eq_integral`, `carlsonRF_perm`, `carlsonRF_self_right` (`Carlson.Elliptic.RF`) |
| 8.2-1 to 8.2-3, phase of `w'` | Proved (8.2-2, 8.2-3 for `re a > 0`) | `hasDerivAt_carlsonR_sub`, `carlsonR_sub_eq_integral`, `prod_ofReal_sub_cpow` |
| Closed half-plane, vertices, `w(∞) = 0`, closure of the polygon | Proved | `continuousOn_scMap`, `tendsto_carlsonR_sub_nhdsWithin`, `tendsto_scMap_cobounded`, `integral_scIntegrand_eq_zero` (`Carlson.Elliptic.VertexLimits`) |
| Angles; convexity | Proved, convexity for `a ≤ 1` | `scAngle_sub_scAngle`, `im_mul_scMap_sub_nonneg_and` (`Carlson.Elliptic.Polygon`) |
| Theorem 8.2-1 and the holomorphic inverse | Proved for distinct real `xᵢ`, `0 < bᵢ < 1`, `0 < a ≤ 1` | `bijOn_scMap`, `hasDerivAt_scMap`, `differentiableOn_scMapInv` (`Carlson.Elliptic.Mapping`) |
| 8.2-8 to 8.2-10, Example 8.2-2, (8.2-11), (8.2-12) | Proved | `half_integral_Ioi_rsqrt_cubic`, `bijOn_carlsonRF_sub`, `sq_deriv_weierstrassInv`, `carlsonRK_lemniscatic` (`Carlson.Elliptic.Inversion`) |
| 8.2-14, 8.2-16, 8.2-18, 8.2-20, 8.2-21, Example 8.2-3 | Proved; (8.2-18) for `k² y² < 1` | `carlsonRF_sub_one_self_self`, `integral_Ioo_rsqrt_sn_incomplete_of_mul_lt`, `integral_Ioo_rsqrt_sn_complete`, `snK'_eq`, `bijOn_snV`, `sq_deriv_jacobiSn` |
| Doubly periodic continuation of the inverses | Not located | — |
| Theorems 8.3-1, 8.3-2 | 8.3-2 for all complex `a, b` with `re(a' - bₖ) > 0`, approach through the right half-plane, also jointly in the nodes | `Carlson.R.SmallVariable`, `tendsto_regCarlsonR_update_zero`, `tendsto_regCarlsonR_nhdsWithin_zero` |
| (8.3-7), Corollary 8.3-3, Theorem 8.3-4 | Proved; 8.3-3 approaching `1` inside the unit disk; 8.3-4 for `re(γ - α - β) > 0` | `regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun`, `tendsto_regularizedGaussHGFun_one`, `hasSum_gaussCoeff`, `ordinaryHypergeometric_one` |
| (8.3-10); (8.3-13)–(8.3-15) | Not located | — |
| (8.3-16) | Leading equivalent for fixed positive `x`, `y → 0+` | `isEquivalent_carlsonRK_zero` (`Carlson.Elliptic.Asymptotic`) |
| (8.3-17) | As a limit, jointly in the variables, also for `x, y` in the slit plane | `tendsto_carlsonRF_zero`, `tendsto_carlsonRF_nhdsWithin_zero`, `tendsto_carlsonRF_zero_of_tendsto_slit` |
| Relation 8.4-1, Lemma 8.4-2, Theorem 8.4-3 | Proved on slit-plane nodes; 8.4-3 for fixed exponent and parameters | `sum_carlsonAssociatedRecurrencePolynomial_mul_regCarlsonR`, `exists_polynomial_carlsonAssociated_exponent_reduction`, `exists_polynomial_relation_associatedCarlsonR` |
| Theorem 8.5-1, 8.5 (1), (2) | Log-rational form for all integral `t`, `b` on the slit domain | `isLogRationalOn_regCarlsonR`, `regCarlsonR_tangent_sub`, `regCarlsonR_single_add_single_log` |
| Theorems 8.5-3, 8.5-4; (8.5-5) | Not stated (they need formal function classes, the branch-point split (8.5-5), and independence of `R_C` and `x^{-1/2}`) | — |
| Table 8.5-1, Example 8.5-5 | All seven rows, `re x, re y > 0` | `carlsonR_table_row_one` … `_row_seven`, `integral_sqrt_div_sqrt_affine` (`Carlson.TwoVariable.Reduction`) |

| Exercise | Status | Lean / remark |
| --- | --- | --- |
| 8.1-1 | `0 < x < y`, `re α, re β > 0` | `integral_sq_sub_cpow_mul_cpow` (`Carlson.R.IntegralExercises`) |
| 8.1-2 | `0 < φ < π/2`, `1 - k² s` in the slit plane on `[0, sin² φ]` | `integral_one_sub_sq_sin_cpow` |
| 8.1-3 | `0 < φ < π/2`, `re a > 0`, both factors in the slit plane | `integral_sin_cos_cpow` |
| 8.1-4 | Not located | `∫ \|t - p\|⁻¹\|t - q\|⁻¹ dt = 2π R_K(…)` |
| 8.1-5 | `x > 0`, `re α > 0`, factors in the slit plane | `integral_cpow_mul_affine_sq_cpow` |
| 8.1-6 | All complex `a` | `complexDirichletIntegral_cpow_mul_cpow_of_sum`, `prod_cpow_mul_carlsonR_div_comm` (`Carlson.R.AverageExercise`) |
| 8.2-1 – 8.2-3 | Not located | images of particular Schwarz–Christoffel maps; 8.2-3 needs the periodic continuation |
| 8.3-1 – 8.3-4 | All complex parameters (regularized; `2c` regular in 8.3-4) | `regCarlsonR_two_mul_pair_half_one`, `regCarlsonR_pair_one_two`, `regCarlsonR_kummer`, `ordinaryHypergeometric_kummer_half` (`Carlson.TwoVariable.GaussExercises`) |
| 8.3-5 | `x` regular, `re y > 0` | `hasSum_beta_series` |
| 8.3-6 | Not located | needs 8.2-3 |
| 8.3-7 | Partial: arc length and perimeter; not the double periodicity of the lemniscatic sine | `integral_lemniscate_eq_carlsonRF`, `four_mul_integral_lemniscate` |
| 8.3-8 | Proved | `integral_rpow_sub_abs_rpow`, `hasDerivAt_integral_rpow_sub_abs_rpow`, `integral_rpow_sub_rpow_quarter_period` |
| 8.3-9 | All complex `t`, non-real `x`; regularized for all `β`, ordinary for `β` not a nonpositive integer | `regCarlsonR_pair_neg`, `carlsonR_pair_neg` (`Carlson.TwoVariable.QuadraticOpposite`), via the first quadratic transformation for nodes in opposite half-planes (`regR_firstQuadratic_of_im`) and Theorem 8.3-2 |
| 8.3-10 – 8.3-12 | Proved | `summable_threeFTwo`, `continuousOn_threeFTwo`, `betaIntegral_mul_threeFTwo`, `betaIntegral_mul_threeFTwo_one`, `Gamma_div_mul_threeFTwo_one` |
| 8.4-1 | Proved | `carlsonAssociatedRecurrenceCoeff_const` |
| 8.4-2 | Not located | — |
| 8.5-1 | Positive real `x, y, z`, `z ≠ x, y` | `carlsonR_neg_one_half_half_one` |
| 8.5-2 | Real `0 < w < x, y, z` | `carlsonR_quartic_eq_carlsonRF_sub` |

## Chapter 9: elliptic integrals

| Item | Status | Lean |
| --- | --- | --- |
| 9.2-1, 9.2-2: `R_G`, `R_H`, `R_K`, `R_E`, `R_L` | Defined; symmetric | `carlsonRG`, `carlsonRH`, `carlsonRE`, `carlsonRL`, `TwoVariable.carlsonRK` (`Carlson.Elliptic.Standard`) |
| 9.2-3, 9.2-4 | As limits through the right half-plane | `tendsto_carlsonRG_zero`, `tendsto_carlsonRH_zero`, `tendsto_carlsonRE_zero`, `tendsto_carlsonRL_zero` |
| Theorem 9.2-1 | The `R_H` part (independence over coefficients polynomial in `ρ`) | `coeff_carlsonRH_eq_zero` (`Carlson.Elliptic.Independence`) |
| 9.2-5 to 9.2-9 | Not located | — |
| 9.2-10 | Leading equivalent for fixed positive `x, y`, `z → ∞` | `isEquivalent_carlsonRF_atTop` |
| 9.2-11, 9.3-2: `F`, `E` | `0 < φ < π/2`, `k² sin² φ < 1` | `legendreF_eq_of_mul_lt`, `legendreE_eq_of_mul_lt` |
| 9.2-11, 9.2-14: `Π`, `Π₁` | R representations and reductions to `R_F, R_H` and `R_K, R_L`, for `k² < 1`, `n sin² φ < 1` (resp. `n < 1`) | `legendrePi_eq_standard`, `legendrePi_complete_eq_standard` (`Carlson.Elliptic.LegendreThird`) |
| 9.2-12 – 9.2-15 | Real `0 < x < y < z` (9.2-12, 9.2-13), `k² < 1` (9.2-14), `0 < x ≤ y` (9.2-15) | `legendreF_arccos_eq`, `carlsonRG_eq_legendre`, `legendreK_eq`, `legendreEc_eq`, `carlsonRK_eq_legendreK`, `carlsonRE_eq_legendreEc` |
| Tables 9.3-1 – 9.3-4 | All rows, on slit-plane nodes; the printed row `2b = (1, 3, 3)` of 9.3-1 has a sign error (see the errata) | `carlsonR_table_9_3_1_row1` … (`Carlson.Elliptic.ReductionTables`, `LegendreThird`) |
| Example 9.3-1 | `0 < φ < π/2`, `k² < 1` | `sin_mul_legendreE_eq` |
| 9.4 applications | Pendulum (9.4-21), (9.4-25), (9.4-26) ((9.4-22) is (8.2-20)); oscillator (9.4-17), (9.4-18); ellipse perimeter (9.4-5); ellipsoid potential (9.4-9), (9.4-10) ((9.4-12) is (8.2-13), (9.4-13) is (9.2-2)) | `Carlson.Elliptic.Applications` |
| 9.4 not located | ellipse arc (9.4-3), (9.4-4); ellipsoid surface area (9.4-6), (9.4-7); (9.4-14); (9.4-23), (9.4-24) beyond Exercise 9.2-1 | — |
| Theorem 9.5-1 | All complex `t`, regularized, all positive `x, y, z` (positive `v, w`, or conjugate `v², w²` when `z` lies between `x` and `y`) | `regCarlsonR_landen`, `regCarlsonR_landen_conj` (`Carlson.Elliptic.Landen`) |
| 9.5-4 | Also with Carlson's explicit `v, w`, real or conjugate | `carlsonRF_landen`, `carlsonRF_landen_explicit`, `carlsonRF_landen_conj` |
| (9.5-1) beyond Theorem 9.5-1; (9.5-18); complex `x, y, z` (remark p. 276) | Not located | — |
| Algorithm 9.5-2 | `s₀ ≥ 0`, `a₀ > c₀ > 0` | `tendsto_ascLanden`, `tendsto_ascLanden_zero` |
| Algorithm 9.5-3 | `t₀ ≥ a₀ > c₀ > 0` | `tendsto_descGauss`, `tendsto_descGauss_self` |
| Theorem 9.6-1 | Whole slit domain; with one variable `0` | `carlsonRF_duplication`, `carlsonRK_duplication` |
| Algorithm 9.6-2 | Strictly positive real initial values | `tendsto_dupSeq` |
| Algorithm 9.6-2 for complex initial values; (9.6-9)–(9.6-12) | Not located (a private squared-spread contraction `triSpread_dupStep` is used in the real proof) | — |
| Theorem 9.7-1 | Positive `x, y, z, λ, μ`; with `z = 0` as (9.7-17) | `carlsonRF_add_carlsonRF`, `carlsonRF_add_carlsonRF_zero` |
| 9.7-11, 9.7-12 | On the branch `λμ > f` | `eulerMu`, `eulerMu_spec`, `eq_eulerMu` |
| Theorem 9.8-1 | `A, …, D, X, Y, Z` with positive real parts; `D = 0`; `X = 0` (then `π R_K(Y², Z²)`) | `carlsonR_quartic_eq_carlsonRF`, `integral_quartic_eq_integral_cubic`, `carlsonR_triple_eq_carlsonRF`, `carlsonR_quartic_eq_carlsonRK` |
| 9.8-10 – 9.8-13 | Real `y < x`, four linear factors positive on `[y, x]` | `integral_quartic_eq_carlsonR`, `integral_quartic_eq_carlsonRF`, `quartic_sq_sub_sq` (`Carlson.Elliptic.QuarticIntegral`) |

| Exercise | Status | Lean / remark |
| --- | --- | --- |
| 9.2-1 | `y > 0` | `isEquivalent_carlsonRK_sq_zero` (`Carlson.Elliptic.ChapterNineExercises`) |
| 9.2-2 | `k > 0`, `0 < φ, φ₁ < π/2`, `sin φ₁ = k sin φ` | `legendreF_inv`, `legendreE_inv` |
| 9.2-3 | Slit-plane nodes, `λ ≥ 0` | `carlsonRF_add_eq_integral_of_slit`, `carlsonRH_add_eq_integral` |
| 9.3-1 | Real `0 < x < y < z`, `ρ > 0`, `ρ ≠ z` | `carlsonRH_eq_legendrePi` |
| 9.3-2 | The identity; the asymptotic `M ~ (4πa/c²)[log(8a/r₋) - 2]` is not located (it needs the `o(1)` remainder of `R_K`) | `integral_mutual_inductance` |
| 9.3-3 | Slit-plane nodes | `carlsonRH_self_right_eq` |
| 9.3-4 | Real `x, y, ρ > 0` | `carlsonRL_add_carlsonRL_div` |
| 9.4-1 | Proved | `hyperbola_arc_length`, `hasDerivAt_hyperbola` |
| 9.4-2, 9.4-3 | Not located | integrals over the sphere and over `ℝ⁶` |
| 9.5-1 | Its results are proved directly in Chapter 6 | `regRSlit_secondQuadratic`, `carlsonRK_sq_eq`, `carlsonRC_sq_eq` |
| 9.5-2 | `re x, re y > 0` | `carlsonRE_sq_eq` |
| 9.5-3, 9.5-4 | Real `x, y > 0` | `hasSum_agmA_zero`, `carlsonRE_eq_agm_div` (`Carlson.Elliptic.AGMSecondKind`) |
| 9.5-5 | Positive data | `carlsonRG_landen` |
| 9.5-6 | Numerical, not targeted | — |
| 9.6-1 | Not located | — |
| 9.6-2 | Positive `x, y, z` | `dupStep_inverse` |
| 9.7-1, 9.7-3, 9.7-4 | On the branch (9.7-12) | `sqrt_eulerP_sub_sq`, `eulerMu_eq_sq`, `eulerMu_mul_sqrt_sub` |
| 9.7-2, 9.7-5 | With the branch condition of Theorem 9.7-1; false without it (see the errata) | `carlsonRF_add_carlsonRF_shift`, `det_shiftCubic_eq_zero` |
| 9.8-1 | Both statements proved by other routes; the derivations asked for are not reproduced | `carlsonR_quartic_eq_carlsonRF`, `carlsonRF_add_carlsonRF` |
| 9.8-2 | Not located | — |
| 9.8-3 | `0 ≤ y < x < ∞`; `x = ∞` not located | `integral_quadratic_mul_quadratic`, `integral_rsqrt_quadratic_mul_quadratic` |
| 9.8-4 | Not located | — |
| 9.8-5 | Carlson's domain | `carlsonR_neg_one_half_half_one_sq` |
| 9.8-6 | For nonnegative coefficients; false as printed (see the errata); the sharp condition `b√e + d√a ≥ 0` is not proved | `integral_quartic_eq_integral_cubic_of_nonneg` |

## The R-function across Chapters 5, 6 and 8

| Content | Modules and scope |
| --- | --- |
| Native integral, parameter continuation, exponent analyticity | `R.Basic`, `R.Integral`, `R.Continuation`, `R.Exponent`, `R.JointParameter` |
| Single-integral representations, joint holomorphy, main definition | `R.SingleIntegral.*`, `R.Explicit`, `R.RayKernel`: full slit domain, entire in exponent and parameters |
| Euler inversion (6.8-3) | `R.EulerTransform`: all parameters, slit-plane nodes |
| Node derivatives, differential identities (5.9-2), relations 5.9-6, parameter raising and lowering, tangential relations, Euler–Poisson system | `R.SlitDeriv`, `R.SlitRelations`, `R.EulerPoisson`: full domain, repeated indices and coincident nodes included |
| Homogeneity recurrence 8.4-1 and its universal polynomial coefficients | `R.AssociatedRecurrence`, `R.SlitRecurrence`, `R.Recurrence.JointCoefficients`, `R.JointRecurrence` |
| Theorem 8.4-3 | `R.Associated.ExponentReduction`, `R.AssociatedDependence`: fixed exponent and parameters, slit domain |
| Two-node recurrences, inversion, parameter interchange, quadratic transformations | `TwoVariable.R.Associated`, `R.Inversion`, `ParameterSymmetry`, `QuadraticContinuation`, `QuadraticSlit` |
| Native agreement, circle and cycle representations | `R.SlitIntegral`, `R.ContourRepresentation` |
| Small-variable limits, integral parameters, zero parameters | `R.SmallVariable*`, `R.IntegerParameters`, `R.IntegerReduction`, `R.ZeroParameter`, `TwoVariable.Reduction` |
| Exterior-path kernels | `R.ContourKernel`: joint continuation for admissible paths and branches; the straight path recovers `regCarlsonR` |
| Confluence, Laplace representation, integral evaluations | `R.Confluence`, `R.Laplace`, `R.IntegralEvaluation` |

Not located: polynomial or analytic dependence on `(t, b)` of the relations of Theorem 8.4-3
(proved for the homogeneity recurrence only); small-variable limits through slit sectors; general
arbitrary-order node derivative formulas; the classification of integral and half-integral
configurations by elementary functions; further branch components of the quadratic identities.

## The L-function (Carlson 1987)

`regCarlsonLIntegral`, `carlsonLIntegral` are the native integrals; `regCarlsonL` is jointly
holomorphic in all complex `t, b` and slit-plane nodes and agrees with the native integral
whenever the node hull lies in the slit plane; `carlsonL` is the ordinary function. The
two-variable equal-parameter normalizations are `TwoVariable.regEqualL`, `equalLSlit`.

| Paper result | Module and scope |
| --- | --- |
| (1.2), (1.3), (2.1) | `L.Basic`, `L.Continuation`: unique entire regularized continuation, joint holomorphy |
| (2.2)–(2.5) | `L.Properties`: permutation, zero-parameter deletion, aggregation, coincident-node and singleton values, positive scaling with its logarithmic correction |
| (2.6) | `L.SlitRelations`: Euler inversion |
| (2.7) | `L.EulerPoisson` |
| (2.8)–(2.10) | `L.SlitDeriv` ((2.10) where the translated nodes lie in the slit plane) |
| (2.11) | `TwoVariable.L.Inversion`, with `log x + log y` on the slit domain; the `log(xy)` form on right-half-plane nodes |
| (2.12) | `TwoVariable.ParameterSymmetry`, `TwoVariable.LQuadratic`: right-half-plane input nodes |
| (3.1)–(3.8) | `L.SlitRelations`, `L.SlitDeriv` |
| (3.9), (3.10) | `TwoVariable.L`, `TwoVariable.L.Associated`: division-free, including `t = 0, -1` and coincident nodes |
| Theorem 3.1, homogeneity case | `L.JointRecurrence` |
| Section 5 Taylor representation, (5.8) | `L.Series`: absolutely convergent on the unit polydisk about `𝟙` |
| (6.4), (6.5), first forms of (6.6), (6.7), (6.8) | `TwoVariable.LQuadratic`, `TwoVariable.EqualParameterSlit` (on `re x, re y > 0`) |
| (8.8) and a reduction related to (8.5) | `TwoVariable.L` |

Not located: Theorem 3.1 for arbitrary associated shifts; Section 4 (zero-node boundary theory)
and (2.13)–(2.15); the coefficients (5.3)–(5.7), (5.9)–(5.17); the alternative forms of (6.6),
(6.7) and the half-integral and Legendre cases of Section 6; Section 7 (real bounds and
monotonicity of `L` and `L/R`); Section 8's integral reductions, three-node exceptional formulas,
dilogarithm limit and special hypergeometric values.

## Carlson (1969): continuation beyond convex domains

* Theorem 6.3-6 (continuation assertion) on convex open domains, for every derivative order:
  `Dirichlet.Average.JointContinuation`. Native-node-domain continuation on any open domain:
  `Dirichlet.Average.IntegralDomain`; domain-aware uniqueness and gluing:
  `Dirichlet.Average.HolomorphicDomain`.
* §5, Lemma 1 (convex-hull complement) and the circle form of Theorem 3 for all parameters:
  `Dirichlet.Average.ResolventContinuation`, `CauchyContinuation`.
* Theorem 8, simply connected case, any number of nodes, coincident nodes included:
  `Dirichlet.Average.SimplyConnected` (convex chart, two-node pull-back, merging identity (4.21),
  removal of Gamma poles); a second proof and the extension to vector nodes on domains with simply
  connected complex-line sections: `Dirichlet.Average.SeveralVariables`.
* Not located: the contour-adapted branches of Theorems 4–5, the multiply connected and
  Riemann-surface cases of Theorem 8, and path independence of the exterior-path kernels.
