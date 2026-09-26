/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Pochhammer.BinomialSeries
public import Pochhammer.Estimates
public import Pochhammer.Gamma
public import Pochhammer.Identities
public import Pochhammer.PochhammerTransform
public import Pochhammer.Vandermonde
public import Pochhammer.BetaIntegral
public import Pochhammer.ComplexPowMeasurable
public import Pochhammer.IncompleteMellin
public import Pochhammer.PositiveCpow

/-!
# Pochhammer infrastructure

This umbrella module imports the project-local results about Pochhammer symbols, their
Gamma-function identities, estimates, binomial series, Vandermonde identities, and transforms.
It also collects simplex-independent scalar beta integrals, complex powers, and Mellin support.

## Main results

This module re-exports the following developments:

* `Pochhammer.BinomialSeries`: Binomial series for the ascending Pochhammer symbol.
* `Pochhammer.Estimates`: Elementary bounds for ascending Pochhammer symbols.
* `Pochhammer.Gamma`: Pochhammer identities for the Gamma function.
* `Pochhammer.Identities`: Algebraic identities for ascending Pochhammer symbols.
* `Pochhammer.PochhammerTransform`: The ascending Pochhammer polynomial transform.
* `Pochhammer.Vandermonde`: Chu–Vandermonde identities for the ascending Pochhammer polynomial.
* `Pochhammer.BetaIntegral`: Further results about the Euler Beta integral.
* `Pochhammer.ComplexPowMeasurable`: Measurability of complex powers with a real base.
* `Pochhammer.IncompleteMellin`: Regularized incomplete Mellin transforms.
* `Pochhammer.PositiveCpow`: Complex powers on the positive half-line.

## References

* `Pochhammer.BinomialSeries`: formal background used by this module.
* `Pochhammer.Estimates`: formal background used by this module.
* `Pochhammer.Gamma`: formal background used by this module.
-/
