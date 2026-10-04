/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.MeasureTheory.Integral.Pi

/-!
# Nonnegative integration on finite product spaces

Finite-product versions of Tonelli's theorem for products of almost-everywhere measurable coordinate
functions. The coordinate spaces may differ and the index type may be empty. The theorem
adapts the imported proof of the Tau Ceti contributors in `TauCeti.MeasureTheory.Integral.Pi`.

## Main results

* `MeasureTheory.lintegral_fintype_prod_eq_prod`: A nonnegative product of coordinate functions
  integrates as the product of its integrals on an arbitrary finite dependent product of
  sigma-finite measure spaces.

## References

* `TauCeti.MeasureTheory.Integral.Pi`: the finite-product lower-integral formula.
-/

public noncomputable section
open scoped ENNReal
namespace MeasureTheory

/-- Tonelli's formula for a finite dependent product of almost-everywhere measurable factors.
The index type may be empty. Uses `TauCeti.lintegral_fintype_prod_eq_prod₀`. -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i :=
  TauCeti.lintegral_fintype_prod_eq_prod₀ μ hf

end MeasureTheory
end
