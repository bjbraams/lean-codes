/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonR.AssociatedRecurrence

/-!
# Polynomial dependence of associated Carlson R-functions

This file formalizes the interface of [Carl77, Lemma 8.4-2 and Theorem 8.4-3].
-/

open Complex ProbabilityTheory
open scoped Classical
public noncomputable section CarlsonR
namespace DirichletTransform
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

/-- A rational function in the Carlson variables, represented by a numerator and a nonzero
denominator polynomial. -/
structure CarlsonRRationalCoefficient (ι : Type*) where
  /-- Numerator polynomial. -/
  numerator : MvPolynomial ι ℂ
  /-- Denominator polynomial. -/
  denominator : MvPolynomial ι ℂ
  /-- The denominator is not the zero polynomial. -/
  denominator_ne_zero : denominator ≠ 0

/-- Evaluate a rational Carlson coefficient away from the zero set of its denominator. -/
def CarlsonRRationalCoefficient.eval
    (q : CarlsonRRationalCoefficient ι) (z : ι → ℂ) : ℂ :=
  q.numerator.eval z / q.denominator.eval z

/-- Carlson's set `U`: complex numbers that are not nonpositive integers, equivalently the
finite points at which the Gamma function has no pole. -/
def IsCarlsonGammaRegular (w : ℂ) : Prop :=
  ∀ n : ℕ, w ≠ -(n : ℂ)

/-- Carlson's reduction lemma 8.4-2: all integral exponent shifts with fixed parameters lie
in the rational-function span of `card ι` consecutive R-functions. -/
theorem exists_rational_carlsonAssociated_exponent_reduction
    (t : ℂ) (b : ι → ℂ) (n : ℤ)
    (hb : b ∈ mvBetaConvergent)
    (ht : IsCarlsonGammaRegular (1 - t))
    (hct : IsCarlsonGammaRegular ((∑ i, b i) + t - Fintype.card ι + 2)) :
    ∃ q : Fin (Fintype.card ι) → CarlsonRRationalCoefficient ι,
      ∀ z ∈ carlsonRVariableDomain,
        (∀ j, (q j).denominator.eval z ≠ 0) →
        carlsonRIntegral (t + n) b z =
          ∑ j, (q j).eval z *
            carlsonRIntegral (t - (j : ℕ)) b z := by
  sorry

/-- Carlson's existence theorem 8.4-3: any `card ι + 1` associated R-functions satisfy a
nontrivial homogeneous relation with polynomial coefficients. -/
theorem exists_polynomial_relation_associatedR
    (t : ℂ) (b : ι → ℂ)
    (s : Fin (Fintype.card ι + 1) → CarlsonRAssociatedShift ι)
    (hconv : ∀ j, (s j).parameterValue b ∈ mvBetaConvergent) :
    ∃ A : Fin (Fintype.card ι + 1) → MvPolynomial ι ℂ,
      (∃ j, A j ≠ 0) ∧
      ∀ z ∈ carlsonRVariableDomain,
        ∑ j, (A j).eval z *
          carlsonRIntegral ((s j).exponentValue t) ((s j).parameterValue b) z = 0 := by
  sorry

end DirichletTransform
end CarlsonR
