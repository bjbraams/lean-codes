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
public import Carlson.R.SlitContinuation
public import Carlson.R.SlitJointAnalytic
public import Carlson.R.SlitIntegral
public import Carlson.R.RayKernel
public import Carlson.R.Contour
public import Carlson.R.EulerTransform
public import Carlson.R.IntegralEvaluation
public import Carlson.R.SmallVariable
public import Carlson.R.AssociatedRecurrence
public import Carlson.R.ContinuedRecurrence
public import Carlson.R.ZeroParameter
public import Carlson.R.IntegerParameters
public import Carlson.R.AssociatedDependence
public import Carlson.R.SlitAssociated
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
associated functions are available on this full slit domain. See `Carlson/R/Coverage.md`
for implemented results and known remaining work.
-/
