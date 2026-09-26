/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.S.Basic
public import Carlson.S.Series
public import Carlson.S.Analytic
public import Carlson.S.Continuation
public import Carlson.S.Deriv
public import Carlson.S.Properties

/-!
# Carlson's S-function

Native integrals, the entire series continuation, joint analyticity,
differentiation, and properties have separate modules.

## Main results

This module re-exports the following developments:

* `Carlson.S.Basic`: Native Carlson S-integrals.
* `Carlson.S.Continuation`: named ordinary and regularized continuations.
* `Carlson.S.Series`: The exponential series and entire parameter continuation of S.
* `Carlson.S.Analytic`: Joint holomorphy and locally uniform S-series convergence.
* `Carlson.S.Deriv`: Differentiation of the entire Carlson S-function.
* `Carlson.S.Properties`: Permutation, translation, and special values of S.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/
