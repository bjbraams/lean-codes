/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.R.Basic
public import Carlson.TwoVariable.RPolynomial.Basic
public import Carlson.R.Explicit

/-!
# The two-variable Carlson R-function

Elementary properties of the two-node R-integral: agreement with the R-polynomial at natural
exponents, symmetry, and positive homogeneity.

## Main results

* `Carlson.TwoVariable.regRIntegral_natCast`, `Carlson.TwoVariable.regRIntegral_swap`,
  `Carlson.TwoVariable.regRIntegral_smul_of_pos`: basic identities.

The logarithmic elementary function `R₋₁(1, 1; x, y)` and its diagonal value are in
`Carlson.TwoVariable.R.Elementary`, on the whole slit plane.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex Filter
open scoped Topology
@[expose] public noncomputable section CarlsonTwoVariable
namespace Carlson.TwoVariable

/-- The two-variable integral at a natural exponent agrees with the Carlson polynomial. -/
theorem regRIntegral_natCast (n : ℕ) (b₀ b₁ z₀ z₁ : ℂ)
    (hb : pair b₀ b₁ ∈ mvBetaConvergent) :
    regRIntegral n b₀ b₁ z₀ z₁ = regRPolynomial n b₀ b₁ z₀ z₁ := by
  exact regCarlsonRIntegral_natCast n (pair z₀ z₁) hb

/-- Simultaneously exchanging the two parameters and variables leaves the native
regularized two-variable R-integral unchanged. -/
theorem regRIntegral_swap (t b₀ b₁ z₀ z₁ : ℂ) :
    regRIntegral t b₁ b₀ z₁ z₀ = regRIntegral t b₀ b₁ z₀ z₁ := by
  have h := regCarlsonDirichletAverage_perm (pair b₀ b₁) (pair z₀ z₁)
    (fun w => w ^ t) (Equiv.swap 0 1)
  rw [show pair b₀ b₁ ∘ Equiv.swap 0 1 = pair b₁ b₀ by
      funext i; fin_cases i <;> rfl,
    show pair z₀ z₁ ∘ Equiv.swap 0 1 = pair z₁ z₀ by
      funext i; fin_cases i <;> rfl] at h
  exact h

/-- Positive-real homogeneity of the native regularized two-variable R-integral. -/
theorem regRIntegral_smul_of_pos (t b₀ b₁ x y : ℂ) {a : ℝ} (ha : 0 < a)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    regRIntegral t b₀ b₁ ((a : ℂ) * x) ((a : ℂ) * y) =
      (a : ℂ) ^ t * regRIntegral t b₀ b₁ x y := by
  change regCarlsonRIntegral t (pair b₀ b₁)
      (pair ((a : ℂ) * x) ((a : ℂ) * y)) = _
  rw [show pair ((a : ℂ) * x) ((a : ℂ) * y) =
      fun i => (a : ℂ) * pair x y i by funext i; fin_cases i <;> rfl]
  exact Carlson.regCarlsonRIntegral_smul_of_pos t hz ha

end Carlson.TwoVariable
end CarlsonTwoVariable
