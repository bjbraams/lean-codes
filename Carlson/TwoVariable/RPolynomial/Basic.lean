/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.Basic
public import Carlson.RPolynomial.Basic

/-!
# Two-variable RPolynomial definitions

The two-node specialization of the regularized Carlson R-polynomial.

## Main statements

* `Carlson.TwoVariable.regRPolynomial`: `regCarlsonRPolynomial n ![b₀, b₁] ![z₀, z₁]`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The canonical two-variable specialization of the regularized Carlson polynomial. -/
abbrev regRPolynomial (n : ℕ) (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  regCarlsonRPolynomial n (pair b₀ b₁) (pair z₀ z₁)

end Carlson.TwoVariable
