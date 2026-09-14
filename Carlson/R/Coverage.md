# Carlson's R-function: coverage and remaining work

This is a status map of the current modules, not an exhaustive assertion that
Carlson's Chapters 5, 6, and 8 have been formalized. The source chapters are in
`Carlson/References/`. The [module guide](../../STRUCTURE.md) describes the
separation of coefficient algebra, analytic construction, and functional identities.
The [Chapter 3 foundations review](../FoundationsCoverage.md) separately tracks
Gamma theory already available in Mathlib and the additional foundations still needed.

## Main interfaces

- `regCarlsonRIntegral` is the Gamma-regularized native simplex integral.
- `regCarlsonRContinued` is its entire parameter continuation on right-half-plane nodes.
- `regCarlsonRSlit` is jointly holomorphic in all complex exponents and Dirichlet
  parameters and all nodes in the product slit plane. Native-integral agreement
  is proved in `SlitIntegral` whenever the whole node convex hull stays in the
  slit plane. Nodewise slit-plane membership alone does not ensure this condition.
- Ordinary normalization multiplies by `Gamma (∑ i, b i)`; totalization at a
  Gamma pole must not be interpreted as a finite ordinary-function value.
- `TwoVariable.regEqualRContinued` uses the finer equal-parameter normalization
  by `Gamma (β + 1/2)`, retaining removable nonpositive integral values of `β`.
  Its node interface is still the right half-plane.

## Implemented core and its domains

| Content | Modules and scope |
| --- | --- |
| Integral definition, parameter continuation, exponent analyticity | `Basic`, `Integral`, `Continuation`, `Exponent`, `JointParameter` |
| Section 6.8 continuation assertion and beta-weighted single integral | `SingleIntegral.Series`, `SingleIntegral.UnitInterval`, `SingleIntegral.Continuation`, `SingleIntegralAnalytic`, `SlitContinuation`, `SlitJointAnalytic`: full slit-node domain and entire regularized parameter dependence |
| Euler inversion, Theorem 6.8-3 | `EulerTransform`: all complex parameters and slit-plane nodes |
| Node derivative, both differential identities of Theorem 5.9-2, relations 5.9-6(9)–(10), parameter raising, scalar-translation derivative | `SlitDeriv`, `SlitRelations`: all complex parameters and slit-plane nodes; no L-function dependency |
| Second node derivatives, parameter lowering and tangential relations, Euler–Poisson system | `SlitDeriv`, `SlitRelations`, `EulerPoisson`: full parameter and slit-node domains, including repeated indices and coincident nodes; regularized and ordinary Euler–Poisson identities |
| Homogeneity recurrence 8.4-1 | `AssociatedRecurrence`, `ContinuedRecurrence`, `SlitRecurrence`: polynomial-coefficient identity, now on the full slit domain |
| Universal homogeneity coefficients | `Recurrence.JointCoefficients`, `JointRecurrence`: a single polynomial family in the exponent parameter, Dirichlet parameters, and nodes; specialization and polynomial nontriviality are proved, and formal exponent differentiation is available |
| Two-node contiguous and three-term recurrences, factored R-correction and mixed derivative | `TwoVariable.R.Associated`: explicit division-free identities, on the full slit domain |
| Polynomial dependence of associated functions, Theorem 8.4-3 | `Associated.ExponentReduction`, `AssociatedDependence`, `SlitAssociated`: nonzero polynomial coefficients for each fixed exponent and parameter vector; full slit-node domain, including the empty index type |
| Both quadratic transformations | `TwoVariable.QuadraticContinuation`, `TwoVariable.QuadraticSlit`: all complex parameters in regularized form; the slit identities allow all square-root variables with positive real parts, without right-half-plane conditions on the squared or mean-square nodes. `TwoVariable.EqualParameter` retains its original node domains |
| Native-integral comparison and circle representation | `SlitIntegral`: native agreement whenever the node convex hull stays in the slit plane; circle Cauchy representation for all complex parameters when the enclosing closed disk stays in the slit plane |
| Two-variable exponent–parameter interchange | `TwoVariable.ParameterSymmetry`: Gauss numerator symmetry on the slit plane; arbitrary right-half-plane input nodes with slit-plane transformed ratios |
| Two-variable inversion | `TwoVariable.R.Inversion`: reflected exponent and exchanged parameters, with separate principal powers on the full slit-node domain |
| Small-variable limit, Section 8.3 | `SmallVariable`: arbitrary individual Dirichlet parameters, right-half-plane approach, positive real parts of both endpoint exponents |
| Integral-parameter reductions, Section 8.5 | `IntegerParameters`: finite reduction for a nonpositive integral parameter and complementary terminating expressions; not a complete elementary-function classification |
| Further representations and limits | `Confluence`, `Laplace`, `IntegralEvaluation`: see individual statements for convergence assumptions |

## Known remaining work

1. **Parameter-dependent polynomial relations.** The witnesses in
   `exists_polynomial_relation_associatedRSlit` are polynomials in the nodes
   chosen for fixed `t,b`. Their polynomial or analytic dependence on `t,b`
   has not been established. `JointRecurrence` now constructs this stronger
   coefficient representation for the homogeneity recurrence, including its
   formal coefficient derivatives; the corresponding L-recurrence is proved.
   The remaining step is lifting arbitrary exponent/parameter shift reduction
   and finite-dimensional dependence to this joint polynomial ring. Extending
   the node domain alone does not fix this separate issue.
2. **Further quadratic interfaces.** `QuadraticSlit` now extends both
   regularized R-transformations to all square-root variables with positive
   real parts, proving that their squared and transformed nodes stay in the
   slit plane. Extend the natural equal-parameter and differentiated L
   interfaces accordingly. Other branch components and ratio identities
   still require explicit branch tracking.
3. **Small-variable boundary theory.** Remove the current extra endpoint
   positivity restrictions by the available double-shift recurrence, and prove
   the wider slit-sector limit. Locally uniform control in the exponent is
   additionally needed before differentiating this limit for L.
4. **Contour representation.** `Contour.lean` is still a declaration-free
   placeholder for formula (6.8-7). Joint analytic continuation is proved by
   another construction; that does not prove the contour formula itself.
   Separately, `Dirichlet/Average/Cauchy.lean` now proves native-domain
   resolvent analyticity (5.11-1) and the circle version of the averaged Cauchy
   formula (5.11-2) for every derivative order, including Fubini interchange.
   `Dirichlet/Average/CauchyContinuation.lean` extends the circle formula to
   all complex Dirichlet parameters, with joint node dependence, using the
   continued regularized resolvent. `SlitIntegral` specializes this representation
   to the slit R-function. None of these results is formula (6.8-7), nor the
   general Jordan-curve version of (5.11-2). The progress toward the general
   simply connected average in Carlson 1969 is recorded in
   `Carlson/FoundationsCoverage.md`; multiply connected and Riemann-surface
   extensions remain open.
5. **Further slit-domain interfaces.** First and second node derivatives and
   the full Euler–Poisson system are now available in `SlitDeriv` and `EulerPoisson`. Arbitrary-order
   derivative formulas remain to be added. General integral identities and reductions elsewhere in the project
   should also be checked individually before using them outside their stated
   right-half-plane domains.
6. **Elementary-function classification and special cases.** The existing
   integral-parameter reductions do not classify all integral and half-integral
   configurations or supply all the book's special-function identifications.

No unfinished proof is represented by a Lean `sorry`; these are unimplemented
statements or extensions of domains, not admitted proofs.
