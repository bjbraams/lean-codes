/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.T.Basic
public import Carlson.T.Slit

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

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.12.
-/
