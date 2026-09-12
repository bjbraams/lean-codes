/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import StdSimplexMeasure.CarlsonTwoVariable.RPolynomial
public import StdSimplexMeasure.CarlsonTwoVariable.R
public import StdSimplexMeasure.CarlsonTwoVariable.S

/-!
# Quadratic transformations of two-variable Carlson functions

This is the home for Carlson's Sections 6.9 and 6.10.  Their polynomial forms will be proved
before the branch-sensitive complex-power forms.  In particular, the hypotheses `x,y ∈ C₀`
in Carlson's statements must be translated into an explicit square-root branch domain rather
than suppressed by notation.
-/

open Complex
open scoped Classical
@[expose] public noncomputable section CarlsonTwoVariable
namespace DirichletTransform.TwoVariable

/-- The squared arithmetic mean occurring in Carlson's first quadratic transformation. -/
def arithmeticMeanSq (x y : ℂ) : ℂ := ((x + y) / 2) ^ 2

/-- The squared geometric mean occurring in Carlson's first quadratic transformation. -/
def geometricMeanSq (x y : ℂ) : ℂ := x * y

/-- The arithmetic mean is symmetric in its arguments. -/
theorem arithmeticMeanSq_comm (x y : ℂ) : arithmeticMeanSq x y = arithmeticMeanSq y x := by
  simp [arithmeticMeanSq, add_comm]

/-- The squared geometric mean is symmetric in its arguments. -/
theorem geometricMeanSq_comm (x y : ℂ) : geometricMeanSq x y = geometricMeanSq y x := by
  simp [geometricMeanSq, mul_comm]

/-- Branch-safe domain for Carlson's first quadratic transformation 6.9-3. -/
def FirstQuadraticDomain (x y : ℂ) : Prop :=
  pair x y ∈ carlsonRVariableDomain ∧
    pair (arithmeticMeanSq x y) (geometricMeanSq x y) ∈ carlsonRVariableDomain

/-- Branch-safe domain for Carlson's second quadratic transformation 6.10-1. -/
def SecondQuadraticDomain (x y : ℂ) : Prop :=
  pair (x ^ 2) (y ^ 2) ∈ carlsonRVariableDomain ∧
    pair (arithmeticMeanSq x y) (geometricMeanSq x y) ∈ carlsonRVariableDomain

/-- Carlson's first quadratic transformation 6.9-3 on a common native integral domain.

The extra convergence hypotheses make both sides genuine Dirichlet integrals.  The book's
larger parameter domain is obtained afterward from continuation in the Dirichlet parameters. -/
theorem rIntegral_firstQuadratic (t β x y : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (β + t) (1 / 2 - t) ∈ mvBetaConvergent)
    (hz : FirstQuadraticDomain x y) :
    rIntegral (2 * t) β β x y =
      rIntegral t (β + t) (1 / 2 - t)
        (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  sorry

/-- Carlson's second quadratic transformation 6.10-1 on a common native integral domain. -/
theorem rIntegral_secondQuadratic (t β x y : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (2 * β + t) (1 / 2 - β - t) ∈ mvBetaConvergent)
    (hz : SecondQuadraticDomain x y) :
    rIntegral t β β (x ^ 2) (y ^ 2) =
      rIntegral t (2 * β + t) (1 / 2 - β - t)
        (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  sorry

/-- Division-free polynomial form of the even-degree first quadratic transformation 6.9-8.
It is valid at exceptional parameters because no Pochhammer symbol is divided out. -/
theorem carlsonRPolynomialNumerator₂_firstQuadratic_even
    (n : ℕ) (β x y : ℂ) :
    (ascPochhammer ℂ n).eval (β + 1 / 2) *
        carlsonRPolynomialNumerator₂ (2 * n) β β x y =
      (ascPochhammer ℂ (2 * n)).eval (2 * β) *
        carlsonRPolynomialNumerator₂ n (β + n) (1 / 2 - n)
          (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  sorry

/-- Division-free polynomial form of the odd-degree first quadratic transformation 6.9-9. -/
theorem carlsonRPolynomialNumerator₂_firstQuadratic_odd
    (n : ℕ) (β x y : ℂ) :
    (ascPochhammer ℂ n).eval (β + 1 / 2) *
        carlsonRPolynomialNumerator₂ (2 * n + 1) β β x y =
      ((x + y) / 2) * (ascPochhammer ℂ (2 * n + 1)).eval (2 * β) *
        carlsonRPolynomialNumerator₂ n (1 + β + n) (-1 / 2 - n)
          (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  sorry

/-- Division-free polynomial form of Carlson's involutive transformation 6.10-3. -/
theorem carlsonRPolynomialNumerator₂_secondQuadratic
    (n : ℕ) (β x y : ℂ) :
    (ascPochhammer ℂ n).eval (1 - 2 * β - 2 * n) *
        carlsonRPolynomialNumerator₂ n β β (x ^ 2) (y ^ 2) =
      (ascPochhammer ℂ n).eval β *
        carlsonRPolynomialNumerator₂ n (1 / 2 - β - n) (1 / 2 - β - n)
          (x + y) (x - y) := by
  sorry

/- The corresponding identities for a future concrete globally continued R-function should
be derived from `rIntegral_firstQuadratic` and `rIntegral_secondQuadratic` by uniqueness of
continuation.  No Legendre, Chebyshev, Gegenbauer, or elliptic-integral specialization belongs
in this file. -/

end DirichletTransform.TwoVariable
end CarlsonTwoVariable
