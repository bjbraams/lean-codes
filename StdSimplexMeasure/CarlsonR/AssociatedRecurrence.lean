/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import StdSimplexMeasure.CarlsonR.Relations
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Fixed-parameter recurrence for associated Carlson R-functions

This file contains the coefficient polynomials and recurrence of [Carl77, Relation 8.4-1].
-/

open Complex ProbabilityTheory
open scoped Classical
@[expose] public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The `n`th elementary symmetric polynomial evaluated at the Carlson variables. -/
def carlsonElementarySymmetric (n : ℕ) (z : ι → ℂ) : ℂ :=
  (MvPolynomial.esymm ι ℂ n).eval z

/-- Carlson's coefficient `Aₙ` from Relation 8.4-1, kept initially in its displayed quotient
form.  A later algebraic lemma should identify its removable-singularity polynomial form. -/
def carlsonAssociatedRecurrenceCoeff
    (n : ℕ) (a a' : ℂ) (b z : ι → ℂ) : ℂ :=
  (ascPochhammer ℂ n).eval a *
    (ascPochhammer ℂ (Fintype.card ι - n)).eval (a' - Fintype.card ι) /
      (a * (a' - Fintype.card ι)) *
    ((a + n) * carlsonElementarySymmetric n z -
      ∑ i, b i * z i * (MvPolynomial.pderiv i
        (MvPolynomial.esymm ι ℂ n)).eval z)

/-- Carlson's fixed-parameter recurrence, Relation 8.4-1, on the native domain. -/
theorem sum_carlsonAssociatedRecurrenceCoeff_mul_rIntegral
    {a a' : ℂ} {b z : ι → ℂ}
    (hsum : a + a' = ∑ i, b i)
    (ha : a ≠ 0) (ha' : a' ≠ Fintype.card ι)
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    ∑ n ∈ Finset.range (Fintype.card ι + 1),
      carlsonAssociatedRecurrenceCoeff n a a' b z *
        carlsonRIntegral (-a - n) b z = 0 := by
  sorry

end DirichletTransform
end CarlsonR
