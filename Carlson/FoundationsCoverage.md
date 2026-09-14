# Carlson 1977, Chapter 3: foundations coverage

Reviewed against `References/Carlson1977Ch3.pdf` (printed pages 31–58), including
the exercises, and the project's pinned Mathlib checkout. “Not found” below
means that no corresponding theorem was located in that checkout or this
project; it is not a claim about every external Lean library.

This supplements [R coverage](R/Coverage.md) and [L coverage](L/Coverage.md).
Gamma theory independent of simplex integration belongs in Mathlib's Gamma
development (temporarily `Pochhammer/` here), not in a Carlson-specific module.

## Main text

| Source | Available foundation | Remaining content |
| --- | --- | --- |
| §3.2: Gamma integral, recurrence, Pochhammer ratios | Mathlib `Gamma.Basic`, `Gamma.Beta`, and local `Pochhammer/Gamma.lean` | No substantial new definition is needed; use existing results with their pole hypotheses. |
| §3.3: holomorphy and poles | `Complex.differentiableAt_Gamma`, `tendsto_self_mul_Gamma_nhds_zero`, and non-differentiability at nonpositive integers | Package the simple-pole statement and residue `(-1)^n / n!` at every nonpositive integer, with the corresponding simple zeros of reciprocal Gamma. |
| §3.4: asymptotic ratio, Euler limit and product | `Complex.GammaSeq_tendsto_Gamma`; Gamma at one half is already available | The ratio asymptotic for real arguments tending to infinity with arbitrary fixed complex shifts; the displayed infinite product as a reusable statement. The Euler limit alone does not supply the ratio theorem. |
| §3.5: log-convexity and Bohr–Mollerup | `Real.convexOn_log_Gamma`, `Real.convexOn_Gamma`, `Real.eq_Gamma_of_log_convex` | Carlson's strict log-convexity and its equality consequences are stronger than the located non-strict convexity statements. |
| §3.6: reciprocal Gamma, digamma and products | `Complex.Gamma_ne_zero`, `Complex.differentiable_one_div_Gamma`; `Gamma.Digamma` defines digamma, proves a recurrence and special values | Weierstrass's infinite product and the general digamma partial-fraction expansions; the simple-zero API noted above. |
| §3.7: duplication | `Complex.Gamma_mul_Gamma_add_half` and its real counterpart | No duplicate proof needed. The general multiplication formula belongs to the exercise inventory. |
| §3.8: logarithmic correction and Stirling | Mathlib `Analysis/SpecialFunctions/Stirling.lean` treats factorial asymptotics | The logarithmic correction series, complex sectorial Stirling theorem, and the sectorial Gamma-ratio corollary. The existing factorial theorem and local reciprocal-Gamma bounds are not substitutes. This is a substantial analytic development. |
| §3.9: reflection and sine product | `Complex.Gamma_mul_Gamma_one_sub`; `Complex.tendsto_euler_sin_prod` is already used in Mathlib's reflection proof | No duplicate reflection/product development needed. The discussion of differential transcendence and Barnes's extension cites background results, rather than proving them as part of the chapter. |
| §3.10: inequalities and minimum | `Real.exists_isMinOn_Gamma_Ioi` locates a minimum in `(1,2)`; basic convexity and monotonicity support exists | Uniqueness/strictness and the chapter's quantitative bounds, particularly the complex absolute-value bounds and the explicit positive lower bound. |
| §3.11: Euler measures and rotated rays | Mathlib's real Gamma distribution; local `Dirichlet/Gamma.lean` relates independent real Gamma variables to Dirichlet variables | A normalized complex Euler integration functional, its moments and exact total variation; rotated-ray normalization, ray independence, and holomorphic parameter dependence under the stated growth conditions. Real Gamma probability alone does not supply these results. |

At Gamma poles, Mathlib's totalized value is not the value of a meromorphic
function at a finite regular point. Pole limits, quotients, and logarithmic
derivatives must retain their exclusions or use reciprocal-Gamma regularization.

## Exercises and scope

The exercises also request Laplace transforms of hypergeometric series,
incomplete-Gamma representations, Gauss's general multiplication formula,
further special values and inequalities, vertical-line asymptotics, Hankel's
reciprocal-Gamma contour integral, and an Euler-average representation of
Bessel polynomials. These are **not all implemented**. Some elementary
convexity and special-value exercises can already be discharged by Mathlib.
The whole exercise list should not be inferred to be covered by coverage of
the numbered main-text theorems.

## Effect on implementation priorities

Keep the previously recommended order:

1. Finish the averaged Cauchy machinery, then general joint continuation and
   the finer equal-parameter continuation interfaces.
2. Complete the small-variable theorem and logarithmic integrals.
3. Lift arbitrary associated-function dependence to joint polynomial
   coefficients in the exponent, Dirichlet parameters, and nodes.
4. Complete explicit L coefficients, hypergeometric identifications, special
   cases, and product formulas.
5. Complete probability inequalities and integer/half-integer classifications.
6. Develop §5.12 asymptotic theory as a separate cluster.

Chapter 3 identifies prerequisites for these stages rather than a reason to
restart from the beginning of the book. In particular, the complex Euler
functional and rotated-ray theory should precede the §5.12 asymptotic cluster;
sectorial Gamma asymptotics should be introduced when their full strength is
needed. Strict convexity and the quantitative Gamma inequalities naturally
join the inequalities stage. Reuse the existing Mathlib Gamma theory throughout.

## Cauchy representation: current status

`hasDerivAt_regCarlsonResolvent` identifies the derivative of every integer
resolvent, and `analyticOnNhd_regCarlsonResolvent` proves analyticity on the
entire complement of the node convex hull, on the native Dirichlet convergence
domain (the corresponding part of Theorem 5.11-1). This is analyticity of the
integral, not merely of the pointwise kernel. It uses the reusable weighted
compact-domain differentiation theorem in
`SeveralComplexVariables/ParametricIntegral.lean`.

`Dirichlet/Average/Cauchy.lean` proves the circle/simplex interchange
`circleIntegral_regDirichletIntegral` and, for every `n : ℕ`,
`regCarlsonDirichletAverage_iteratedDeriv_eq_circleIntegral`:
the average of `f`'s `n`th derivative equals `n! / (2πi)` times the circle
integral of `f` against the order-`n` regularized resolvent. The previous
zeroth-derivative representation is now a corollary. The assumptions are
positive real parts of the Dirichlet parameters, nodes inside a common open
disk, and an integrand holomorphic in that disk and continuous on its closure.
There is no assumption about derivatives on the boundary, nor a nonempty-index
assumption. The arbitrary-interior-point scalar Cauchy theorem is in
`SeveralComplexVariables/CauchyDerivatives.lean`.

This does **not** assert Carlson's general rectifiable Jordan-curve formula
or the contour formula (6.8-7).

## Theorem 6.3-6: joint continuation on a convex domain

The **continuation assertion** of Theorem 6.3-6 (printed p. 138) is now proved in
`Dirichlet/Average/JointContinuation.lean`, for every derivative order:

- `exists_joint_isRegCarlsonContinuation` supplies a joint continuation for a
  general holomorphic function on any convex open `Ω`.
- `exists_joint_isRegCarlsonContinuation_iteratedDeriv` supplies it for the
  averages of every derivative of that function.
- `analyticOnNhd_joint_of_isRegCarlsonContinuation` shows that any existing
  family with the pointwise continuation characterization inherits joint
  holomorphy, without changing its definition.

The domain is all complex Dirichlet parameters and all node vectors in `Ω^ι`.
There is no common-disk hypothesis, no Gamma-pole exclusion for the regularized
function, and no nonempty-index assumption. Native integral agreement retains
positive real parts of the Dirichlet parameters.

The proof preserves holomorphic auxiliary parameters through tangential
integration by parts, using `Dirichlet/Complex/Parametric.lean` and
`Dirichlet/Transform/Parametric.lean`. The finite-shift expressions agree on
overlaps by uniqueness and glue to a jointly holomorphic continuation.

For comparison, the earlier interfaces remain available:

- `exists_isRegCarlsonContinuation` supplies an entire continuation in `b`
  for each fixed node vector in a convex open holomorphy domain.
- `analyticOnNhd_regCarlsonTaylorSeries_joint` supplies joint continuation
  in parameters and nodes within a common Taylor disk.

**Still outstanding:** Carlson's general rectifiable Jordan-curve formula
(6.3-4) within Theorem 6.3-6. The integration-by-parts proof establishes the
continuation assertion, not the contour representation. The circle formula is
now extended to every complex Dirichlet parameter in
`Dirichlet/Average/CauchyContinuation.lean`, using the continued regularized
resolvent rather than the native integral outside its convergence region.

## Carlson 1969: continuation beyond convex domains

The remark at the bottom of Carlson 1977, p. 156, refers to Theorem 8,
pp. 145–146, of Carlson's *A Connection Between Elementary Functions and Higher
Transcendental Functions*, SIAM J. Appl. Math. 17 (1969), 116–148. Its local
contour construction is developed in §5, particularly Theorems 4–5.

The first implementation stage is complete:

- `Dirichlet/Average/ResolventContinuation.lean` constructs the integer
  regularized resolvent jointly holomorphic in all complex Dirichlet parameters,
  nodes, and an evaluation point outside their convex hull. Native agreement and
  uniqueness are proved. This supplies the convex-hull-complement kernel needed
  in §5, but not the contour-adapted branch of Theorem 4.
- `SeveralComplexVariables/ContourIntegral.lean` proves holomorphy of compact
  weighted integrals of jointly holomorphic kernels and its circle specialization.
  The fixed boundary function need only be continuous.
- `Dirichlet/Average/CauchyContinuation.lean` proves the circle version of
  Theorem 3 for every derivative order and all complex Dirichlet parameters,
  with joint node dependence and independence of the admissible enclosing circle.
  Only interior holomorphy and continuity on the closed disk are required of `f`.
- `Dirichlet/Average/HolomorphicDomain.lean` introduces
  `IsJointRegCarlsonContinuationOn`, proves locality in the scalar function,
  uniqueness on connected open scalar domains, and gluing along increasing
  connected open domains. Agreement with the native integral is required only
  when the entire node convex hull lies in the scalar domain. All these results
  allow empty and singleton index types.
- `Dirichlet/Average/IntegralDomain.lean` constructs joint entire-parameter
  continuation on the open set of node tuples whose convex hull stays in an
  arbitrary open scalar domain. This node set is star-convex when the scalar
  domain is. A recognition theorem extends native agreement from a convex
  seed to this whole node set, assuming a jointly holomorphic candidate on
  the full node product. `Carlson/R/SlitIntegral.lean` and
  `Carlson/L/SlitIntegral.lean` apply it to the already constructed slit
  functions. This does not construct a candidate for a general nonconvex domain.

**The simply connected theorem is not yet complete.** Still needed are:

1. Contour-adapted resolvent branches and the generalized Cauchy construction
   on nonconvex Jordan domains (Theorems 4–5). The present slit branch is not
   automatically the branch required by an arbitrary contour.
2. A suitable increasing Jordan-domain exhaustion of a simply connected planar
   domain. The gluing theorem accepts such a family but does not construct it.
   Polygonal contours are the proposed first implementation, with their
   sufficiency still to be proved.
3. Combining those two results with the proved gluing theorem to obtain the
   unconditional simply connected planar case of Theorem 8.

**Left open:** the multiply connected and Riemann-surface versions of Theorem 8.
These involve genuine branch phenomena; in the multiply connected case Carlson
generally excludes coincident-node diagonals when asserting continuation along
arbitrary paths. The single-valued simply connected case includes those diagonals.
