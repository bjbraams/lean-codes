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

/-- Carlson's zero-parameter deletion for the general continued R-function.
The exponent and remaining Dirichlet parameters are arbitrary complex numbers. -/
theorem regCarlsonR_option_zero [Nonempty ι] (t : ℂ)
    {b : Option ι → ℂ} (hb : b none = 0)
    {z : Option ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonR t b z =
      regCarlsonR t (b ∘ some) (z ∘ some) := by
  obtain ⟨A, hA, hzA⟩ := exists_pos_real_center_norm_sub_lt hz
  exact IsRegCarlsonContinuation.option_zero (analyticOnNhd_cpow_ball_ofReal t A) hzA
    (isRegCarlsonRContinuation_regCarlsonR t hz)
    (isRegCarlsonRContinuation_regCarlsonR t (fun i => hz (some i))) hb

end Carlson
end
