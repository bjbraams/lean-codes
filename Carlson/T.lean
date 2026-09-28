/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.T.Basic
public import Carlson.T.Slit
public import Carlson.T.TwoF0
public import Carlson.T.TwoF0Sector
public import Carlson.T.TwoF0Connection
public import Carlson.T.ZeroNode

/-!
# Carlson's reciprocal-exponential average

The native-domain regularized function `regCarlsonT` is jointly holomorphic in all
Dirichlet parameters and nodes whose convex hull avoids zero. The principal branch
`regCarlsonTSlit` extends to all tuples of slit-plane nodes. The two agree when the
whole node convex hull lies in the slit plane; that restriction records the branch choice.

## Main results

* `Carlson.analyticOnNhd_regCarlsonT_joint`: joint native-domain continuation.
* `Carlson.analyticOnNhd_regCarlsonTSlit_joint`: joint principal-branch continuation.
* `Carlson.regCarlsonTSlit_eq_integral`: agreement with the defining Dirichlet integral.
* `Carlson.regCarlsonTSlit_eq_regCarlsonT`: compatibility of the two continuations.
* `Carlson.carlson2F0`: Carlson's `₂F₀` function, with its remainder representation, symmetry,
  error bounds and asymptotic expansion (`Carlson.T.TwoF0`).
* `Carlson.carlson2F0Sector`: the continuation of `₂F₀` to the sector `|ph(-x)| < 3π/2`
  (Theorem 5.12-6), with the error bound and asymptotic expansion there (`Carlson.T.TwoF0Sector`).
* `Carlson.regCarlsonS_pair_eq_twoF0`, `Carlson.carlson2F0Sector_eq_carlsonS`: the connection
  formulas (5.12-18) and (5.12-20) (`Carlson.T.TwoF0Connection`).
* `Carlson.tendsto_regCarlsonT_pair_zero`, `Carlson.regCarlsonTIntegral_pair_zero_eq`: the
  zero-node limit (5.12-2) and formula (5.12-3) (`Carlson.T.ZeroNode`).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.12.
-/
