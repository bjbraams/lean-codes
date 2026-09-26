/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Basic
public import Carlson.R.Integral
public import Carlson.R.Continuation
public import Carlson.R.Deriv
public import Carlson.R.Exponent
public import Carlson.R.Relations
public import Carlson.R.JointParameter
public import Carlson.R.Confluence
public import Carlson.R.Laplace
public import Carlson.R.SlitPlane
public import Carlson.R.SingleIntegral
public import Carlson.R.SingleIntegralAnalytic
public import Carlson.R.Explicit
public import Carlson.R.SlitIntegral
public import Carlson.R.RayKernel
public import Carlson.R.ContourKernel
public import Carlson.R.EulerTransform
public import Carlson.R.IntegralEvaluation
public import Carlson.R.SmallVariable
public import Carlson.R.AssociatedRecurrence
public import Carlson.R.ZeroParameter
public import Carlson.R.IntegerParameters
public import Carlson.R.AssociatedDependence
public import Carlson.R.SlitDeriv
public import Carlson.R.SlitRelations
public import Carlson.R.EulerPoisson
public import Carlson.R.JointRecurrence

/-!
# Carlson's multivariate R-function

Umbrella import for the native integral, continuation interface, differentiation kernel,
associated-function theory, confluence, and Laplace representation of Carlson's `R_t`.
The regularized slit-plane function is jointly entire in the exponent and Dirichlet
parameters and holomorphic in all nodes off the nonpositive real axis.
Node differentiation, the homogeneity recurrence, and polynomial dependence of
associated functions are available on this full slit domain. See `CarlsonRCoverage.md`
for implemented results and known remaining work.

## Main results

This module re-exports the following developments:

* `Carlson.R.Basic`: Carlson's R-function: basic definitions.
* `Carlson.R.Integral`: Carlson's R-function: native integral representation.
* `Carlson.R.Continuation`: Carlson's R-function: continuation in the Dirichlet parameters.
* `Carlson.R.Deriv`: Carlson's R-function: analyticity and differentiation.
* `Carlson.R.Exponent`: Analytic dependence on the exponent of Carlson's R-integral.
* `Carlson.R.Relations`: Carlson's R-function: homogeneity and associated-function relations.
* `Carlson.R.JointParameter`: Joint dependence on the exponent and Dirichlet parameters.
* `Carlson.R.Confluence`: Confluence of Carlson's R-function to the S-function.
* `Carlson.R.Laplace`: The Laplace representation of Carlson's R-function.
* `Carlson.R.SlitPlane`: Slit-plane domains for Carlson's R-function.
* `Carlson.R.SingleIntegral`: Single-integral representations of R.
* `Carlson.R.SingleIntegralAnalytic`: Joint analyticity of Carlson's single integral.
* `Carlson.R.Explicit`: Explicit definition of the regularized Carlson R-function.
* `Carlson.R.SlitIntegral`: Native-integral agreement on the slit plane.
* `Carlson.R.RayKernel`: Convergence of Carlson ray kernels.
* `Carlson.R.ContourKernel`: Compactified exterior-path kernels for Carlson continuation.
* `Carlson.R.EulerTransform`: Euler transformations of Carlson's R-function.
* `Carlson.R.IntegralEvaluation`: Evaluation of Euler-type integrals by Carlson R-functions.
* `Carlson.R.SmallVariable`: Dependence of Carlson's R-function on a small variable.
* `Carlson.R.AssociatedRecurrence`: Fixed-parameter recurrence for associated Carlson
  R-functions.
* `Carlson.R.ZeroParameter`: Zero-parameter deletion for the continued R-function.
* `Carlson.R.IntegerParameters`: Reduction of integral Dirichlet parameters.
* `Carlson.R.AssociatedDependence`: Polynomial dependence of associated Carlson R-functions.
* `Carlson.R.SlitDeriv`: Differentiation of R on the full slit domain.
* `Carlson.R.SlitRelations`: Associated R-relations on the full slit domain.
* `Carlson.R.EulerPoisson`: The R Euler–Poisson system on the full slit domain.
* `Carlson.R.JointRecurrence`: Polynomial coefficients in parameters and nodes.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/
