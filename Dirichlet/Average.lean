/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Basic
public import Dirichlet.Average.Deriv
public import Dirichlet.Average.Associated
public import Dirichlet.Average.PowerSeries
public import Dirichlet.Average.Cauchy
public import Dirichlet.Average.ResolventContinuation
public import Dirichlet.Average.ResolventDeriv
public import Dirichlet.Average.ResolventInfinity
public import Dirichlet.Average.CauchyContinuation
public import Dirichlet.Average.NewtonTaylor
public import Dirichlet.Average.Continuation
public import Dirichlet.Average.JointContinuation
public import Dirichlet.Average.HolomorphicDomain
public import Dirichlet.Average.IntegralDomain
public import Dirichlet.Average.Aggregation
public import Dirichlet.Average.ContinuedRelations

/-!
# Carlson's Dirichlet averages

This umbrella module collects the basic integral theory, differentiation theory,
Newton--Taylor theory, and analytic continuation theory for Carlson's Dirichlet averages.

## Main results

This module re-exports the following developments:

* `Dirichlet.Average.Basic`: Carlson's Dirichlet averages: basic definitions.
* `Dirichlet.Average.Deriv`: Euler--Poisson equations for Carlson's Dirichlet averages.
* `Dirichlet.Average.Associated`: Associated Dirichlet averages.
* `Dirichlet.Average.PowerSeries`: Averages of uniformly summable series.
* `Dirichlet.Average.Cauchy`: Averages of Cauchy's integral formula.
* `Dirichlet.Average.ResolventContinuation`: Entire-parameter continuation of the Cauchy
  resolvent.
* `Dirichlet.Average.ResolventDeriv`: First and second exterior derivatives of the
  continued resolvent, at arbitrary complex parameters.
* `Dirichlet.Average.ResolventInfinity`: Affine covariance and normalization at
  infinity, with an analytic reciprocal chart and arbitrary complex parameters.
* `Dirichlet.Average.CauchyContinuation`: Continued Cauchy representations of Dirichlet
  averages.
* `Dirichlet.Average.NewtonTaylor`: Dirichlet-average identities for divided differences and
  repeated integrals.
* `Dirichlet.Average.Continuation`: Analytic continuation of Carlson's Dirichlet averages.
* `Dirichlet.Average.JointContinuation`: Joint continuation of general Carlson averages.
* `Dirichlet.Average.HolomorphicDomain`: Dirichlet continuation on holomorphy domains.
* `Dirichlet.Average.IntegralDomain`: The native node domain of a holomorphic Dirichlet average.
* `Dirichlet.Average.Aggregation`: Aggregation of continued Dirichlet averages.
* `Dirichlet.Average.ContinuedRelations`: Associated relations on the full parameter space.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/
