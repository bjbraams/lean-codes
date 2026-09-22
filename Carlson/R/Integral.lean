/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Basic
public import Carlson.RPolynomial.Basic
public import Dirichlet.Average.Continuation

/-!
# Carlson's R-function: native integral representation

For a natural-number exponent the native R-integral is the Carlson R-polynomial of that degree.

## Main results

* `Carlson.regCarlsonRIntegral_natCast`: `regCarlsonRIntegral n b z = regCarlsonRPolynomial n b z`
  on the native convergence region.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex ProbabilityTheory
@[expose] public noncomputable section CarlsonR
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- For a natural exponent, the general-power integral is the polynomial Carlson average. -/
theorem regCarlsonRIntegral_natCast (n : ℕ) (z : ι → ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonRIntegral (n : ℂ) b z = regCarlsonRPolynomial n b z := by
  rw [regCarlsonRIntegral, ← regCarlsonDirichletAverage_pow n z hb]
  congr 2
  funext w
  exact cpow_natCast w n

end Carlson
end CarlsonR
