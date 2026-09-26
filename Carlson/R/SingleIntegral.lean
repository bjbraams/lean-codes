/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SingleIntegral.Series
public import Carlson.R.SingleIntegral.UnitInterval
public import Carlson.R.SingleIntegral.PositiveRay

/-!
# Single-integral representations of R

Unit-interval series, analyticity, and positive-ray substitution have separate modules.

## Main results

This module re-exports the following developments:

* `Carlson.R.SingleIntegral.Series`: Unit-interval kernel and near-one series representation.
* `Carlson.R.SingleIntegral.UnitInterval`: The unit-interval representation and node
  analyticity.
* `Carlson.R.SingleIntegral.PositiveRay`: Positive-ray representation and its change of
  variables.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/
