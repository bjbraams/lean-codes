/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Real.Moments
public import Dirichlet.Real.Aggregation
public import Dirichlet.Real.Marginals

/-!
# Real Dirichlet probability content

Moments, aggregation, and beta marginals are available as separate imports.

## Main results

This module re-exports the following developments:

* `Dirichlet.Real.Moments`: Moments, means, variances, and covariances of the real Dirichlet
  distribution.
* `Dirichlet.Real.Aggregation`: Aggregation of the real Dirichlet distribution.
* `Dirichlet.Real.Marginals`: Beta marginals of the real Dirichlet distribution.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/
