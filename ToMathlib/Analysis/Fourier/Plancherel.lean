/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Classical Fourier integrals and the `L²` Fourier transform

Mathlib defines the Fourier transform on `L²` by extending the Schwartz isometry.
On `L¹ ∩ L²` this extension agrees almost everywhere with the Fourier integral.
The identification uses Tau Ceti's uniqueness theorem for locally integrable
representatives of tempered distributions; the multiplication formula itself is
Mathlib's Fourier Fubini theorem. In particular, classical Plancherel needs no
smoothness or integrability of the Fourier transform.
-/

@[expose] public noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform RealInnerProductSpace ComplexInnerProductSpace

namespace Real

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On `L¹ ∩ L²`, the abstract `L²` Fourier transform has the classical Fourier integral
as an almost everywhere representative. Tau Ceti supplies uniqueness of representatives
from their Schwartz pairings. -/
theorem fourier_toLp_ae_eq {f : V → H} (hf : Integrable f) (h₂ : MemLp f 2) :
    (𝓕 (h₂.toLp f) : Lp H 2) =ᵐ[volume] 𝓕 f := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  refine Lp.ae_eq_of_toTemperedDistribution_apply_eq (𝓕 (h₂.toLp f))
    hcont.locallyIntegrable fun φ => ?_
  rw [← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
    Lp.toTemperedDistribution_apply, SchwartzMap.fourier_coe]
  have hflip : (innerₗ V).flip = innerₗ V :=
    LinearMap.ext₂ fun x y => by simp
  have hL : Continuous fun p : V × V => innerₗ V p.1 p.2 := by
    simp only [innerₗ_apply_apply]
    fun_prop
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip continuous_fourierChar
    hL (φ.integrable (μ := volume)) hf
  rw [hflip] at h
  simp only [VectorFourier.fourierIntegral, innerₗ_apply_apply, ← Real.fourier_eq] at h
  refine (integral_congr_ae ?_).trans h
  filter_upwards [h₂.coeFn_toLp] with x hx
  rw [hx]

/-- The classical Fourier integral of an `L¹ ∩ L²` function is square integrable. -/
theorem memLp_fourier_of_integrable_memLp {f : V → H} (hf : Integrable f)
    (h₂ : MemLp f 2) : MemLp (𝓕 f) 2 :=
  (Lp.memLp (𝓕 (h₂.toLp f))).ae_eq (fourier_toLp_ae_eq hf h₂)

/-- Classical Plancherel on `L¹ ∩ L²`, without smoothness or an `L¹` assumption on
the Fourier transform. -/
theorem integral_norm_sq_fourier_of_integrable_memLp {f : V → H} (hf : Integrable f)
    (h₂ : MemLp f 2) : ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := Lp.inner_fourier_eq (h₂.toLp f) (h₂.toLp f)
  rw [L2.inner_def, L2.inner_def] at h
  have hleft : (∫ ξ, inner ℂ (𝓕 (h₂.toLp f) ξ) (𝓕 (h₂.toLp f) ξ)) =
      ∫ ξ, inner ℂ (𝓕 f ξ) (𝓕 f ξ) := by
    apply integral_congr_ae
    filter_upwards [fourier_toLp_ae_eq hf h₂] with ξ hξ
    rw [hξ]
  have hright : (∫ x, inner ℂ (h₂.toLp f x) (h₂.toLp f x)) =
      ∫ x, inner ℂ (f x) (f x) := by
    apply integral_congr_ae
    filter_upwards [h₂.coeFn_toLp] with x hx
    rw [hx]
  rw [hleft, hright] at h
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using h

end Real
