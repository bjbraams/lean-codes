/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Analysis.Integral.CurveIntegral
public import Analysis.Integral.CurveIntegral.Improper
public import ComplexAnalysis.HasPrimitives
public import ComplexAnalysis.HasPrimitives.Pullback
public import ComplexAnalysis.BranchLog
public import ComplexAnalysis.BranchLog.Analytic
public import ComplexAnalysis.BranchLog.Homotopy
public import ComplexAnalysis.ExteriorPath
public import ComplexAnalysis.ExteriorPath.Integral
public import ComplexAnalysis.CauchyDerivatives
public import ComplexAnalysis.CauchyEstimates
public import ComplexAnalysis.CauchyFormula
public import ComplexAnalysis.CauchyIntegral
public import ComplexAnalysis.CauchyPompeiu
public import ComplexAnalysis.CauchySeries
public import ComplexAnalysis.CauchyTransform
public import ComplexAnalysis.CurveIndex
public import ComplexAnalysis.CurveIndex.Continuity
public import ComplexAnalysis.CurveIndex.Homotopy
public import ComplexAnalysis.HalfPlane
public import ComplexAnalysis.Injective
public import ComplexAnalysis.Integral.Circle
public import ComplexAnalysis.Integral.CirclePath
public import ComplexAnalysis.Integral.Map
public import ComplexAnalysis.Integral.Homotopy
public import ComplexAnalysis.Integral.ContinuousHomotopy
public import ComplexAnalysis.LaurentSeries
public import ComplexAnalysis.LaurentSeries.Annulus
public import ComplexAnalysis.LaurentSeries.Basic
public import ComplexAnalysis.LaurentSeries.Geometry
public import ComplexAnalysis.LocallyUniform
public import ComplexAnalysis.LogDerivIntegral
public import ComplexAnalysis.ParametricIntegral
public import ComplexAnalysis.PolygonIntegral
public import ComplexAnalysis.Pow
public import ComplexAnalysis.RealUniqueness
public import ComplexAnalysis.RemovableSingularity
public import ComplexAnalysis.Residue
public import ComplexAnalysis.Residue.LogDeriv
public import ComplexAnalysis.Residue.PrincipalPart
public import ComplexAnalysis.ArgumentPrinciple
public import ComplexAnalysis.Rouche
public import ComplexAnalysis.Hurwitz
public import ComplexAnalysis.FunctionSpace
public import ComplexAnalysis.Montel
public import ComplexAnalysis.Vitali
public import ComplexAnalysis.EssentialSingularity
public import ComplexAnalysis.RemovableLine
public import ComplexAnalysis.Reflection
public import ComplexAnalysis.Subharmonic
public import ComplexAnalysis.Subharmonic.Basic
public import ComplexAnalysis.Subharmonic.Convex
public import ComplexAnalysis.Subharmonic.Majorant
public import ComplexAnalysis.Subharmonic.SmoothCriterion
public import ComplexAnalysis.Subharmonic.Submean
public import ComplexAnalysis.UnivalentDisk
public import ComplexAnalysis.ZeroPersistence

/-!
# Single-variable complex analysis

General complex analysis supporting contour representations and analytic continuation.
The development extends Mathlib's complex-analysis infrastructure, with Banach-valued targets
where appropriate. Complex-specific declarations use `Complex`; extensions of existing APIs
retain their usual namespaces. There is no dependency on application or SCV function theory.
General support is imported from the independent `Analysis` and `Topology` libraries.
Divided differences and repeated integrals also use the general `StdSimplexMeasure` foundations.

* `HalfPlane`, `Pow`: right-half-plane geometry, sector roots, finite-family containing disks,
  and multiplication and holomorphy of principal powers.
* `BranchLog`: holomorphic logarithms and roots on simply connected open sets, with
  normalization and uniqueness of logarithm branches.
* `BranchLog.Homotopy`: continuous logarithm lifts of path homotopies in the punctured plane
  and invariance of the terminal branch value under continuous deformation.
* `ExteriorPath`, `ExteriorPath.Integral`: compactified paths escaping to infinity,
  their Jacobians, and Banach-valued endpoint formulas for exact exterior integrals.
* `Analysis.Integral.CurveIntegral`: the general endpoint formulas for exact one-forms,
  imported by the complex curve-integral theory.
* `HasPrimitives`: Banach-valued primitives on simply connected open domains, local-to-global
  exactness, normalization, uniqueness, and the global primitive consequence of Morera's theorem.
* `HasPrimitives.Pullback`: continuous potentials after pullback along maps from simply
  connected spaces, with local primitive increments computing image-path integrals.
* `CauchyIntegral`: path independence, Cauchy's theorem on simply connected open sets, and
  integration of logarithmic derivatives.
* `CauchyFormula`: Banach-valued Cauchy formulas on simply connected open sets, with an explicit
  scalar kernel integral.
* `LogDerivIntegral`, `CurveIndex`: the exponential endpoint identity, integer-valued index
  for closed C¹ curves avoiding the pole, index laws, and the index-weighted Cauchy formula.
* `CurveIndex.Continuity`: continuity and local constancy away from the curve, constancy on
  connected components, and vanishing on unbounded components of the complement.
* `Integral.Homotopy`, `CurveIndex.Homotopy`: Cauchy's theorem under `C²` path homotopies
  on arbitrary open domains; the curve index also respects continuous based homotopies of `C¹`
  loops.
* `Integral.ContinuousHomotopy`: Cauchy's theorem under continuous homotopies, including moving
  endpoints, and passage to limits of finite contours when endpoint-track integrals vanish.
* `Integral.CirclePath`: smooth circles as paths and agreement of curve and circle integrals;
  `CurveIndex` evaluates the index inside and outside a circle.
* `Integral.Map`, `UnivalentDisk`: holomorphic changes of variables, embedded image-circle
  boundaries, two-component separation, index normalization, Banach-valued Cauchy formulas,
  and relatively compact exhaustions for domains parametrized by injective holomorphic disk maps.
* `PolygonIntegral`: integration over oriented polygon edges and polygonal Cauchy's theorem.
* `CauchyDerivatives`, `CauchyEstimates`, `CauchySeries`: circle derivative formulas, compact
  derivative bounds, geometric Taylor-coefficient majorants, and Cauchy-series estimates.
* `LaurentSeries`: Banach-valued coefficients and expansions, annular formulas, and geometry.
* `Residue`, `Residue.LogDeriv`: residues at isolated singularities, pole computations,
  and logarithmic-derivative residues equal to meromorphic orders.
* `ArgumentPrinciple`, `Rouche`, `Hurwitz`: disk zero counting with multiplicities,
  stability under perturbation, and zero-free or injective limits of holomorphic functions.
* `FunctionSpace`, `Montel`, `Vitali`: compact-open holomorphic spaces, compactness and
  convergent subsequences under compact-local bounds, and Vitali convergence from an
  interior accumulation point, using shared `Analysis` foundations without SCV imports.
* `EssentialSingularity`: analytic extension of bounded punctured germs, the isolated
  singularity alternatives, and Casorati–Weierstrass density near essential singularities.
* `Subharmonic`: planar submean and maximum principles, majorants, convex examples, and the
  Laplacian criterion.
* `CauchyPompeiu`, `CauchyTransform`: planar integral identities and transforms with parameters.
* `RemovableSingularity`, `Injective`, `ZeroPersistence`: planar removal, injectivity, and zeros.
* `ParametricIntegral`, `RealUniqueness`, `LocallyUniform`, `Integral.Circle`: one-variable
  integration, uniqueness, convergence, and circle helpers.

General Jordan separation and normalization beyond these analytic disk contours remain open.
Exhaustion of arbitrary simply connected planar domains still requires a construction of
suitable contours or an injective holomorphic disk parametrization.
-/
