/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellContinuation
public import ToMathlib.Analysis.SpecialFunctions.AppellParameter
public import Dirichlet.GammaPoles

/-!
# Removable Gamma cancellation in the F₃ matrix representation

The regularized bare matrix vanishes at each exceptional common total parameter.
Multiplication by Gamma has a removable singularity there, with value equal to
the regularized F₃ series. The value can also be recovered as the Gamma residue
times the derivative of the continued matrix family. These statements concern
the matrix representation of regularized F₃, not removal of poles of ordinary F₃.
-/

open Complex Dirichlet Set Filter
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The bare regularized matrix family for `F₃`, varying its common total and exponent. -/
def appellF3RegularizedMatrix (a a' b b' x y c : ℂ) : ℂ :=
  continuedRegMatrixDirichletAverage (appellF3Matrix x y) (fun z => z ^ (-c))
    (appellF3Parameters a a' c, appellF3Parameters b b' c)

/-- The bare matrix family is entire in its common total parameter, including Gamma poles. -/
theorem analyticOnNhd_appellF3RegularizedMatrix (a a' b b' : ℂ)
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    AnalyticOnNhd ℂ (appellF3RegularizedMatrix a a' b b' x y) univ := by
  have he : appellF3RegularizedMatrix a a' b b' x y =
      fun c => (Gamma c)⁻¹ * regularizedAppellF3 a a' b b' c x y := by
    funext c
    exact continuedRegMatrixDirichletAverage_eq_inv_Gamma_mul_regularizedAppellF3
      a a' b b' c hx hy
  rw [he]
  intro c _
  apply AnalyticAt.mul
  · exact differentiable_one_div_Gamma.analyticAt c
  · exact analyticOnNhd_regularizedAppellF3_denominator a a' b b' hx hy c (mem_univ _)

/-- At every Gamma pole the normalized matrix expression has the regularized `F₃` series
as its finite limit. The value is obtained by a limit, not by evaluating totalized Gamma. -/
theorem tendsto_Gamma_mul_appellF3RegularizedMatrix (a a' b b' : ℂ) (m : ℕ)
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Tendsto (fun c => Gamma c * appellF3RegularizedMatrix a a' b b' x y c)
      (𝓝[≠] (-(m : ℂ))) (𝓝 (regularizedAppellF3 a a' b b' (-(m : ℂ)) x y)) := by
  have he : (fun c => Gamma c * appellF3RegularizedMatrix a a' b b' x y c) =ᶠ[𝓝[≠] (-(m : ℂ))]
      (fun c => regularizedAppellF3 a a' b b' c x y) := by
    filter_upwards [eventually_Gamma_ne_zero_nhdsNE (-(m : ℂ))] with c hc
    exact Gamma_mul_continuedRegMatrixDirichletAverage_eq_regularizedAppellF3
      a a' b b' c (fun k hk => hc ((Gamma_eq_zero_iff _).mpr ⟨k, hk⟩)) hx hy
  have hcont := (analyticOnNhd_regularizedAppellF3_denominator a a' b b' hx hy
    (-(m : ℂ)) (mem_univ _)).continuousAt
  exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm

/-- The removable value is the Gamma residue times the derivative of the entire bare matrix. -/
theorem regularizedAppellF3_neg_nat_eq_residue_mul_deriv_matrix
    (a a' b b' : ℂ) (m : ℕ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    regularizedAppellF3 a a' b b' (-(m : ℂ)) x y =
      ((-1 : ℂ) ^ m / m.factorial) *
        deriv (appellF3RegularizedMatrix a a' b b' x y) (-(m : ℂ)) := by
  have hF := (analyticOnNhd_appellF3RegularizedMatrix a a' b b' hx hy
    (-(m : ℂ)) (mem_univ _)).differentiableAt
  have hz : appellF3RegularizedMatrix a a' b b' x y (-(m : ℂ)) = 0 := by
    simpa only [appellF3RegularizedMatrix, neg_neg] using
      continuedRegMatrixDirichletAverage_appellF3_neg_nat a a' b b' m hx hy
  exact tendsto_nhds_unique (tendsto_Gamma_mul_appellF3RegularizedMatrix a a' b b' m hx hy)
    (tendsto_Gamma_mul_of_eq_zero m hF hz)

/-- Ordinary Gamma normalization of the continued `F₂` matrix identity.
The usual Pochhammer-denominator series requires both denominators to avoid poles. -/
theorem Gamma_mul_Gamma_mul_continuedRegMatrixDirichletAverage_eq_appellF2
    (a b b' c c' : ℂ) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    (Gamma c * Gamma c') * continuedRegMatrixDirichletAverage (appellF2Matrix x y)
      (fun z => z ^ (-a)) (appellF2Parameters b c, appellF2Parameters b' c') =
        appellF2 a b b' c c' x y := by
  rw [continuedRegMatrixDirichletAverage_eq_regularizedAppellF2 a b b' c c' hxy, appellF2]

/-- Ordinary `F₃` is its Gamma-normalized continued matrix at all nonpole common totals. -/
theorem Gamma_mul_Gamma_mul_continuedRegMatrixDirichletAverage_eq_appellF3
    (a a' b b' c : ℂ) (hc : ∀ m : ℕ, c ≠ -(m : ℂ))
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    (Gamma c * Gamma c) * continuedRegMatrixDirichletAverage (appellF3Matrix x y)
      (fun z => z ^ (-c)) (appellF3Parameters a a' c, appellF3Parameters b b' c) =
        appellF3 a a' b b' c x y := by
  rw [mul_assoc, Gamma_mul_continuedRegMatrixDirichletAverage_eq_regularizedAppellF3
    a a' b b' c hc hx hy, appellF3]

end Carlson.TwoVariable
