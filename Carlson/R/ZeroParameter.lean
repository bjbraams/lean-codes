/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Pow
public import Carlson.ZeroParameter
public import Carlson.R.Explicit

/-!
# Zero-parameter deletion for the continued R-function

Every finite set of right-half-plane nodes fits in a disk of holomorphy of
the principal power. Carlson's continued Taylor formula therefore deletes a
zero parameter for every complex exponent and every remaining parameter vector.

## Main results

* `Carlson.regCarlsonR_option_zero`: Carlson's zero-parameter deletion for the general continued
  R-function. The exponent and remaining Dirichlet parameters are arbitrary complex numbers.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- Carlson's zero-parameter deletion on right-half-plane nodes. -/
private theorem regCarlsonR_option_zero_of_mem_variableDomain [Nonempty ι] (t : ℂ)
    {b : Option ι → ℂ} (hb : b none = 0)
    {z : Option ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonR t b z =
      regCarlsonR t (b ∘ some) (z ∘ some) := by
  obtain ⟨A, hA, hzA⟩ := exists_pos_real_center_norm_sub_lt hz
  exact IsRegCarlsonContinuation.option_zero (analyticOnNhd_cpow_ball_ofReal t A) hzA
    (isRegCarlsonRContinuation_regCarlsonR t hz)
    (isRegCarlsonRContinuation_regCarlsonR t (fun i => hz (some i))) hb

/-- Carlson's zero-parameter deletion for the general continued R-function.
The exponent and remaining Dirichlet parameters are arbitrary complex numbers, and the nodes are
arbitrary slit-plane nodes. -/
theorem regCarlsonR_option_zero [Nonempty ι] (t : ℂ)
    {b : Option ι → ℂ} (hb : b none = 0)
    {z : Option ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR t b z =
      regCarlsonR t (b ∘ some) (z ∘ some) := by
  have hcomp : AnalyticOnNhd ℂ (fun w : Option ι → ℂ => regCarlsonR t (b ∘ some) (w ∘ some))
      carlsonRSlitDomain :=
    fun w hw => analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pi_iff.mpr fun i => (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Option ι => ℂ) (some i)).analyticAt w) (fun i => hw (some i))
  exact eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane (analyticOnNhd_regCarlsonR t b) hcomp
    (fun w hw => regCarlsonR_option_zero_of_mem_variableDomain t hb hw) hz

end Carlson
end
