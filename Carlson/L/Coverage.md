# Carlson's L-function: coverage and next steps

Source: B. C. Carlson, *Dirichlet averages of x^t log x*, SIAM Journal on
Mathematical Analysis 18 (1987), 550–565. The local PDF is
`Carlson/References/Carlson1987DirichletAveragesPowerLog-SIAMJMathAnal18.pdf`.

This is an initial development toward Sections 2–8, not a claim that those
sections are completely formalized. The kernel is `w ^ t * Complex.log w`.

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
- The L-interface's continued node domain is still the right-half-plane product.
  R now has the jointly holomorphic `regCarlsonRSlit` on the full product slit plane
  (`Carlson.R.SlitJointAnalytic`). Extending L using its exponent derivative is the
  next domain improvement. Native node derivatives below require positive real parts of `b`.
- Empty-index integrals vanish. The regularized singleton value is
  `z ^ t * log z / Gamma b`. Deleting a zero parameter requires a nonempty
  remaining index type, as in the corresponding R-theorem.

## Implemented paper content

| Paper result | Module and scope |
| --- | --- |
| (1.2), (1.3) | `Basic`, `Continuation`: native integral, exponent derivative, unique entire regularized continuation |
| Parameter part of (2.1) | `Continuation`: joint entireness in `t` and `b`, using the SCV coordinate-derivative theorem |
| Native node part of (2.1), (2.7) | `Deriv`: node analyticity and Euler–Poisson, on the right-half-plane node domain |
| (2.2)–(2.4) | `Properties`: permutation, zero-parameter deletion, arbitrary surjective aggregation, coincident-node values |
| (2.5) | `Properties`: positive-real scaling, including the logarithmic correction, for all continued parameters |
| (2.6) | `Relations`: Euler inversion, for all continued parameters |
| (2.8), (2.9) | `Associated`: native Euler and translation differential identities |
| (3.1), (3.2), (3.4) | `Relations`: entire regularized associated identities; (3.4) is written with parameters raised |
| (3.3), (3.7) | `Associated`: entire regularized three-node and backward-shift identities |
| (3.5) | `Deriv`: native first node derivative, with the inhomogeneous R-term |
| Section 5 Taylor representation | `Series`: R-polynomial expansion, absolutely convergent on the full unit polydisk for every `b`; coefficients use iterated scalar derivatives |
| (5.8) | `Series`: explicit logarithmic coefficients, using `z - 1` rather than `1 - z` |
| (8.8) | `TwoVariable.L`: elementary squared-logarithm divided difference, an undivided identity valid on the diagonal, and the diagonal value |
| Uniform two-node reduction related to (8.5) | `TwoVariable.L`: a division-free identity expressing `(t+1)L_t + R_t` through endpoint power-logarithms |

## Remaining work

1. Complete the Section 2–3 identities: scalar translation (2.10), the
   two-variable inversion and parameter-transfer formulas (2.11)–(2.12),
   (3.6), (3.8)–(3.10), and Theorem 3.1. For Theorem 3.1, do not differentiate
   the arbitrary coefficient witnesses of the existing fixed-exponent
   R-dependence theorem: first obtain coefficient families with the required
   polynomial/analytic dependence on the exponent.
2. Use (2.12) and the existing joint R-analyticity to differentiate both
   quadratic transformations. The transformed Dirichlet parameters depend on
   the exponent, so differentiating only the degree is insufficient. Include
   the equal-parameter normalization used by `TwoVariable.EqualParameter` to
   retain removable values. This is the main prerequisite for Section 6's
   half-integral and Legendre special cases.
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
