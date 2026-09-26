/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.Quadratic.Geometry
public import Carlson.TwoVariable.Quadratic.Polynomial
public import Carlson.TwoVariable.Quadratic.Integral

/-!
# Quadratic transformations

Separate imports provide branch geometry, polynomial identities, and native
integral transformations. Parameter continuation is in `QuadraticContinuation`.

## Main results

This module re-exports the following developments:

* `Carlson.TwoVariable.Quadratic.Geometry`: Means and branch-safe quadratic domains.
* `Carlson.TwoVariable.Quadratic.Polynomial`: Polynomial quadratic transformations.
* `Carlson.TwoVariable.Quadratic.Integral`: Native integral quadratic transformations.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/
