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
public import Dirichlet.Average.CauchyCycle
public import Dirichlet.Average.Intertwining
public import Dirichlet.Average.NewtonTaylor
public import Dirichlet.Average.RealNodes
public import Dirichlet.Average.Continuation
public import Dirichlet.Average.JointContinuation
public import Dirichlet.Average.HolomorphicDomain
public import Dirichlet.Average.IntegralDomain
public import Dirichlet.Average.Aggregation
public import Dirichlet.Average.ContinuedRelations
public import Dirichlet.Average.Merge
public import Dirichlet.Average.Chart
public import Dirichlet.Average.TwoNode
public import Dirichlet.Average.SimplyConnected
public import Dirichlet.Average.FibreContinuation
public import Dirichlet.Average.SeveralVariables

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
* `Dirichlet.Average.CauchyCycle`: Cauchy representations on `C¹` cycles homologous to zero,
  and Cauchy's formula for derivatives on cycles.
* `Dirichlet.Average.Intertwining`: averaging intertwines Carlson's operators `δ` and `Δ`
  (formula (5.3-4)).
* `Dirichlet.Average.NewtonTaylor`: Dirichlet-average identities for divided differences and
  repeated integrals.
* `Dirichlet.Average.RealNodes`: averages with real nodes of finitely differentiable functions:
  Theorem 5.3-2, (5.3-3), (5.3-4) and the Euler–Poisson system 5.4-1 in case (i).
* `Dirichlet.Average.Continuation`: Analytic continuation of Carlson's Dirichlet averages.
* `Dirichlet.Average.JointContinuation`: Joint continuation of general Carlson averages.
* `Dirichlet.Average.HolomorphicDomain`: Dirichlet continuation on holomorphy domains.
* `Dirichlet.Average.IntegralDomain`: The native node domain of a holomorphic Dirichlet average.
* `Dirichlet.Average.Aggregation`: Aggregation of continued Dirichlet averages.
* `Dirichlet.Average.ContinuedRelations`: Associated relations on the full parameter space.
* `Dirichlet.Average.Merge`: Merging two nodes of a Dirichlet average (Carlson 1969, (4.21)).
* `Dirichlet.Average.Chart`: Convex charts of simply connected domains and the logarithm of
  their difference quotient.
* `Dirichlet.Average.TwoNode`: Two-node Dirichlet averages on simply connected domains, with
  holomorphic parameters.
* `Dirichlet.Average.SimplyConnected`: Carlson (1969), Theorem 8, simply connected case.
* `Dirichlet.Average.FibreContinuation`: two-node averages and Euler integrals of kernels whose
  domain of holomorphy has simply connected fibres varying with a parameter.
* `Dirichlet.Average.SeveralVariables`: averages of functions of several variables with vector
  nodes, continued to all nodes in a domain with simply connected complex-line sections.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/
