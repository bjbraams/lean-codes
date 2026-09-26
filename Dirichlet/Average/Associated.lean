/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Associated.Relations
public import Dirichlet.Average.Associated.Deriv
public import Dirichlet.Average.Associated.Analytic

/-!
# Associated Dirichlet averages

Umbrella for shift identities, differentiation, and joint analyticity.
Basic parameter shifts and density identities live in `Dirichlet.ParameterShift`.

## Main results

This module re-exports the following developments:

* `Dirichlet.Average.Associated.Relations`: Associated Dirichlet-average identities.
* `Dirichlet.Average.Associated.Deriv`: Differentiation of associated Dirichlet averages.
* `Dirichlet.Average.Associated.Analytic`: Node and joint analyticity of native Dirichlet
  averages.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/
