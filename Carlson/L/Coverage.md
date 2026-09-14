# Carlson's L-function: coverage and next steps

Source: B. C. Carlson, *Dirichlet averages of x^t log x*, SIAM Journal on
Mathematical Analysis 18 (1987), 550–565. The local PDF is
`Carlson/References/Carlson1987DirichletAveragesPowerLog-SIAMJMathAnal18.pdf`.

This is an initial development toward Sections 2–8, not a claim that those
sections are completely formalized. The kernel is `w ^ t * Complex.log w`.
See the [module guide](../../STRUCTURE.md) for the R/L dependency structure.

## Interfaces and domains

`Carlson.L` imports the multivariate theory. `Carlson.TwoVariable.L` supplies
the two-variable specializations and elementary values; both are exported by
`Carlson`.

- `regCarlsonLIntegral` and `carlsonLIntegral` are native Bochner integrals.
- `regCarlsonLContinued` is the exponent derivative of `regCarlsonRContinued`.
  It is jointly entire in the exponent and all Dirichlet parameters, and its
  agreement with the native integral and uniqueness are proved.
- `carlsonLContinued` multiplies by `Gamma (∑ i, b i)`. At Gamma poles this is
  only Lean's totalized expression, not a finite value of the ordinary function.
- `regCarlsonLSlit` is the exponent derivative of `regCarlsonRSlit`, jointly
  holomorphic in all complex `t,b` and all nodes off the nonpositive real axis.
  Its agreement with the original continuation and native integral, and its
  uniqueness on the slit domain, are proved. The native-integral agreement is
  proved in `SlitIntegral` whenever the entire node convex hull stays in the
  slit plane, not merely when the individual nodes do. On this wider native
  domain the exponent derivative of the R-integral is also the L-integral.
- `carlsonLSlit` is the ordinary Gamma-multiplied function, jointly holomorphic
  away from total-parameter Gamma poles. The original `Continued` interfaces
  remain available without changed statements.
- Empty-index integrals vanish. The regularized singleton value is
  `z ^ t * log z / Gamma b`. Deleting a zero parameter requires a nonempty
  remaining index type, as in the corresponding R-theorem.
- `TwoVariable.regEqualLContinued` uses the natural equal-parameter
  normalization by `Gamma (β + 1/2)`, retaining removable nonpositive integral
  values of `β`. `equalLContinued` is the ordinary function, jointly analytic
  in the exponent and equal parameter away from genuine poles of that Gamma
  factor. Both agree with their native integrals on convergent parameters.

## Implemented paper content

| Paper result | Module and scope |
| --- | --- |
| (1.2), (1.3) | `Basic`, `Continuation`: native integral, exponent derivative, unique entire regularized continuation |
| (2.1) | `SlitContinuation`: full joint holomorphy on the product slit plane, entire in `t,b`, using the SCV coordinate-derivative theorem |
| (2.7) | `EulerPoisson`: Euler–Poisson on the full slit-node domain, for all complex parameters; includes equal indices and coincident nodes |
| (2.2)–(2.4) | `SlitProperties`: permutation, zero-parameter deletion, arbitrary surjective aggregation, coincident-node and singleton values, on the full slit domain |
| (2.5) | `SlitProperties`: positive-real scaling, including the logarithmic correction, on the full slit domain and for all parameters |
| (2.6) | `SlitRelations`: Euler inversion on the full slit domain and for all parameters |
| (2.8), (2.9) | `SlitDeriv`: Euler and translation differential identities, for all parameters and slit-plane nodes |
| (2.10) | `SlitDeriv`: scalar-translation derivative wherever the translated nodes lie in the slit plane |
| (2.11) | `TwoVariable.L.Inversion`: all complex parameters and slit-plane nodes, with branch-correct `log x + log y`; the paper's `log (x * y)` version is proved on right-half-plane nodes |
| (2.12) | `TwoVariable.ParameterSymmetry`, `TwoVariable.LQuadratic`: both parameter-transfer formulas, for all complex parameters and right-half-plane input nodes; transformed ratios use slit continuation |
| (3.1), (3.2), (3.4) | `SlitRelations`: full-domain regularized associated identities; both parameter-raised and parameter-lowered forms of (3.4) |
| (3.3), (3.7) | `SlitRelations`: full-domain regularized three-node and backward-shift identities |
| (3.5) | `SlitDeriv`: first node derivative for all parameters and slit-plane nodes, with the inhomogeneous R-term |
| (3.6), (3.8) | `SlitDeriv`, `SlitRelations`: differential and weighted backward-shift identities on the full slit domain, including coincident nodes and equal indices |
| (3.9) | `TwoVariable.L`: division-free two-node contiguous relation on the full slit domain |
| (3.10) | `TwoVariable.L.Associated`: three-term L-recurrence with its R-correction, factored shifted-R form, and mixed-node-derivative form; division-free identities include `t = 0, -1` and coincident nodes, while the quotient form excludes those two exponents |
| Homogeneity instance of Theorem 3.1 | `JointRecurrence`: universal parameter/node polynomial coefficients and their formal derivatives give a nontrivial polynomial family for the consecutive-exponent L-recurrence; includes the empty index type |
| Section 5 Taylor representation | `Series`: R-polynomial expansion, absolutely convergent on the full unit polydisk for every `b`; coefficients use iterated scalar derivatives |
| (5.8) | `Series`: explicit logarithmic coefficients, using `z - 1` rather than `1 - z` |
| (6.4), (6.5) | `TwoVariable.LQuadratic`: both general L-only quadratic transformations, in natural regularized and ordinary normalizations, on the existing R-quadratic node domains; no Dirichlet parameter exclusions in the regularized identities |
| First forms of (6.6), (6.7) | `TwoVariable.LQuadratic`: the two terms in the second quadratic formula, including the correction at slit-plane nodes `(A/G, 1)` |
| (6.8) | `TwoVariable.LQuadratic`: both exponent-zero quadratic L-identities, for all complex Dirichlet parameters on the existing quadratic node domains |
| (8.8) | `TwoVariable.L`: elementary squared-logarithm divided difference, an undivided identity valid on the diagonal, and the diagonal value |
| Uniform two-node reduction related to (8.5) | `TwoVariable.L`: a division-free identity expressing `(t+1)L_t + R_t` through endpoint power-logarithms |

## Remaining work

1. Complete Theorem 3.1 for arbitrary associated shifts. The listed Section 2–3
   algebraic and differential identities, including (2.11) and all regularized
   forms of (3.10), are now proved on their documented domains.
   `R.JointRecurrence` supplies genuine
   parameter/node polynomials for the homogeneity recurrence, and
   `polynomial_R_relation_implies_L_relation` rigorously differentiates such a
   family. What remains is lifting the arbitrary-shift reduction and linear
   dependence argument to the joint polynomial ring. The fixed-parameter
   existential coefficient witnesses still cannot simply be differentiated.
2. Develop the alternative forms of (6.6)–(6.7) and the remaining half-integral
   and Legendre special cases of Section 6. The general L-only quadratic
   formulas (6.4)–(6.5) and both exponent-zero identities in (6.8) are proved.
   `TwoVariable.QuadraticSlit` now extends the raw regularized R identities
   to all square-root variables with positive real parts, allowing squared
   and mean-square nodes throughout the slit plane. Extending the natural
   equal-parameter normalization and the L-only formulas to this wider node
   domain remains separate work.
3. Evaluate the general Taylor coefficients by derivatives of Pochhammer
   polynomials, before translating to digamma notation. This avoids artificial
   exclusions at integral exponents. Then establish (5.3)–(5.7), (5.9)–(5.17),
   terminating parameter cases, and the hypergeometric interpretations.
4. Develop the zero-node boundary theory of Section 4 and logarithmic integral
   representations (2.13)–(2.15). Differentiating an existing pointwise limit is
   not justified by itself: establish locally uniform convergence in the
   exponent, or direct log-weighted domination. Express Gamma derivatives with
   Mathlib's logarithmic derivative machinery and track its poles explicitly.
5. Develop the real-probability layer for Section 7: logarithmic bounds,
   monotonicity of L and L/R, endpoint limits, and concentration limits in the
   total parameter. Strict inequalities need nonconstant nodes and a proof of
   the required support/nondegeneracy of the real Dirichlet distribution.
6. Complete Section 8's positive-integral parameter reductions, three-node
   exceptional formulas, dilogarithm limit, and special hypergeometric values.

No unfinished proof is represented by a Lean `sorry`; unimplemented statements
are tracked here instead.
