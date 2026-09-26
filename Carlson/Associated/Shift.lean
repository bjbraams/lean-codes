/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic

/-!
# Associated shifts and rational coefficient data

Bookkeeping structures for Carlson's associated R-functions (Chapter 8): an associated shift
records integral shifts of the exponent and of the Dirichlet parameters, and a rational
coefficient is a quotient of two multivariate polynomials in the nodes with nonzero denominator.

## Main statements

* `Carlson.CarlsonRAssociatedShift`: an integral exponent shift together with integral parameter
  shifts, with `exponentValue` and `parameterValue` applying them.
* `Carlson.CarlsonRRationalCoefficient`: numerator and denominator polynomials, evaluated by
  `eval` on a node vector.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- Integral shifts specifying a Carlson R-function associated to a fixed exponent and
Dirichlet parameter vector. -/
structure CarlsonRAssociatedShift (ι : Type*) where
  /-- Integral shift of the homogeneity parameter. -/
  exponent : ℤ
  /-- Integral shifts of the Dirichlet parameters. -/
  parameter : ι → ℤ

/-- Apply an associated shift to an R-function's exponent. -/
def CarlsonRAssociatedShift.exponentValue
    (s : CarlsonRAssociatedShift ι) (t : ℂ) : ℂ :=
  t + s.exponent

/-- Apply an associated shift to an R-function's Dirichlet parameters. -/
def CarlsonRAssociatedShift.parameterValue
    (s : CarlsonRAssociatedShift ι) (b : ι → ℂ) : ι → ℂ :=
  fun i => b i + s.parameter i

/-- A numerator and a nonzero denominator polynomial representing a rational coefficient
in the Carlson variables. This structure records a representation, rather than an equivalence
class of representations. -/
structure CarlsonRRationalCoefficient (ι : Type*) where
  /-- Numerator polynomial. -/
  numerator : MvPolynomial ι ℂ
  /-- Denominator polynomial. -/
  denominator : MvPolynomial ι ℂ
  /-- The denominator is not the zero polynomial. -/
  denominator_ne_zero : denominator ≠ 0

/-- Evaluate a rational Carlson coefficient using totalized division. This agrees with rational
function evaluation away from the denominator’s zero set and is zero on that zero set. -/
def CarlsonRRationalCoefficient.eval
    (q : CarlsonRRationalCoefficient ι) (z : ι → ℂ) : ℂ :=
  q.numerator.eval z / q.denominator.eval z

end Carlson
