# Mathematical synopsis

This document and its companions describe the mathematical content of the project for
mathematicians. Lean-specific matters (module layout, namespaces, tactics) are kept in the
background; the emphasis is on definitions, theorems and hypotheses as a mathematician would
state them. The module-level guide is [STRUCTURE.md](STRUCTURE.md).

The project is a formalization in Lean 4, against a pinned Mathlib and the pinned TauCeti
library, of B. C. Carlson's theory of special functions as Dirichlet averages (*Special
Functions of Applied Mathematics*, Academic Press, 1977, Chapters 5–9, and related articles),
together with the theory of the regularized Dirichlet (simplex Mellin) transform and the
supporting real, complex and several-variable analysis. All results are fully proved: the
libraries contain no unproved statements and no additional axioms. It is written with the
intent of contributing to Mathlib; where a result extends a Mathlib theorem (typically to
Banach-valued functions, general domains or fewer hypotheses) the specialized synopses say so.

## The libraries

| Library | Synopsis | Depends on |
| --- | --- | --- |
| `ToMathlib.Algebra` | [general algebra](SYNOPSIS_ALGEBRA.md) | Mathlib |
| `ToMathlib.Topology` | [general topology](SYNOPSIS_TOPOLOGY.md) | Mathlib, TauCeti |
| `ToMathlib.Analysis` | [general analysis](SYNOPSIS_ANALYSIS.md) | Mathlib, TauCeti |
| `ComplexAnalysis` | [one complex variable](SYNOPSIS_CA.md) | `ToMathlib` |
| `SeveralComplexVariables` | [several complex variables](SYNOPSIS_SCV.md) | `ToMathlib`, `ComplexAnalysis` |
| `Pochhammer` | [Pochhammer, Gamma, beta, Mellin](SYNOPSIS_POCHHAMMER.md) | Mathlib, TauCeti |
| `StdSimplexMeasure` | [the standard simplex](SYNOPSIS_STDSIMPLEX.md) | `Pochhammer` |
| `Dirichlet` | [Dirichlet measures, transforms, averages](SYNOPSIS_DIRICHLET.md) | all of the above |
| `SimplexMellin` | [the simplex Mellin transform](SYNOPSIS_SIMPLEXMELLIN.md) | `Dirichlet` |
| `Carlson` | [Carlson's special functions](SYNOPSIS_CARLSON.md) | `Dirichlet` |

`SimplexMellin` and `Carlson` are independent of each other. `ComplexAnalysis` and
`SeveralComplexVariables` are the parts of the separate libraries `lean-CA` and `lean-SCV`
used here. Open problems and unformalized material of the three target libraries are collected
in [SYNOPSIS_GAPS.md](SYNOPSIS_GAPS.md), and printed errors found in Carlson's book in
[CARLSON_ERRATA.md](CARLSON_ERRATA.md).

## Conventions

Finite coordinate spaces $\mathbb C^{I}$ carry the supremum norm, so balls are polydiscs; the
index set $I$ may be empty, and degenerate cases are handled. *Holomorphic* means complex
Fréchet-differentiable on an open set and *analytic* means locally given by a convergent power
series; in finite dimension they coincide. Target spaces are complex Banach spaces unless stated
otherwise. Powers and logarithms are principal, and the *slit plane* is
$\mathbb C \setminus (-\infty, 0]$. The *standard simplex* is
$E_I = \{u \in \mathbb R^{I} : u_i \ge 0, \sum_iu_i = 1\}$ with the hyperplane measure $\sigma$ of
mass $1/(|I| - 1)!$.

Functions with Gamma normalizations are usually stated in *regularized* form, divided by the
Gamma factor, so that they are entire in their parameters and identities hold at the Gamma
poles as well; the ordinary normalization is obtained by multiplying back.

## Overview

**Support libraries.** [General algebra](SYNOPSIS_ALGEBRA.md) supplies saturation of submodules
and polynomial-coefficient linear dependence. [General topology](SYNOPSIS_TOPOLOGY.md) supplies
gluing of functions with locally constant differences on simply connected spaces, injectivity of
proper local homeomorphisms onto simply connected spaces, and Baire-category bounds.
[General analysis](SYNOPSIS_ANALYSIS.md) covers parametric and curve integrals, Plemelj boundary
values, quantitative Laplace asymptotics, spaces of holomorphic maps (Montel, Vitali), the
multivariable Mellin transform, the Paley–Wiener theorem on $\mathbb R^n$, Carlson's theorem on
functions of exponential type, Mellin–Barnes integrals and Ramanujan's master theorem, Bessel and
Gamma estimates, and Carlson's theory of sequences satisfying a binomial theorem.

**Complex analysis.** [One variable](SYNOPSIS_CA.md): Banach-valued primitives and Cauchy's
theorem on simply connected domains, logarithms and roots, the curve index, the homology form of
Cauchy's theorem for cycles, Cauchy's derivative formula at any interior point, and holomorphic
inverses. [Several variables](SYNOPSIS_SCV.md): polydisc Cauchy theory, holomorphy equals
analyticity in finite dimension, Osgood's and Hartogs' theorems, Weierstrass convergence and
holomorphic dependence of integrals.

**Pochhammer symbols and the simplex.** [Pochhammer](SYNOPSIS_POCHHAMMER.md): division-free
identities, Chu–Vandermonde for rising factorials, the Pochhammer polynomial transform,
reciprocal-Gamma estimates and regularized incomplete Mellin transforms.
[StdSimplexMeasure](SYNOPSIS_STDSIMPLEX.md): coordinates and the hyperplane measure on the
simplex, slicing, monomial and radial integration, aggregation, smooth functions near the
simplex, moment determination and the solution of the moment problem on the simplex, and
Hermite–Genocchi divided differences.

**Dirichlet theory.** [Dirichlet](SYNOPSIS_DIRICHLET.md): multivariate beta functions; the
Dirichlet distribution with its moments, aggregation, Gamma construction, merging and Jensen
theory; regularized complex Dirichlet integrals and the entire regularized Dirichlet transform of
smooth kernels with its structural laws and merging identity; and Carlson's Dirichlet averages
with derivatives, Euler–Poisson equations, divided differences, Cauchy representations and
analytic continuation, including Carlson's (1969) Theorem 8 on simply connected domains and its
extension to functions of several variables.

**The simplex Mellin transform.** [SimplexMellin](SYNOPSIS_SIMPLEXMELLIN.md): face formulas,
uniqueness and estimates; the Mellin bridge identifying the regularized Dirichlet transform as
the angular part of the multivariable Mellin transform; inversion and Plancherel; Paley–Wiener
theory with a description of the image; lattice values via Carlson's theorem; and a master
theorem with simplex structure.

**Carlson's special functions.** [Carlson](SYNOPSIS_CARLSON.md): R-polynomials; the $R$-function
for all complex exponents, parameters and slit-plane nodes with its relations, recurrences,
integral representations and limits; the $L$-function of Carlson (1987); the $S$- and
$T$-functions and ${}_2F_0$; hypergeometric means and their inequalities; two-variable theory
(quadratic transformations, AGM and Borchardt algorithms, hypergeometric and Bessel
identifications); Jacobi polynomials and series (Chapter 7); and elliptic integrals and
conformal maps (Chapters 8 and 9: the Schwarz–Christoffel map, symmetric standard functions and
Legendre's integrals, reduction tables, Landen, duplication, addition and quartic reduction
theorems, and applications).
