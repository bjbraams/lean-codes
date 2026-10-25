/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF4Reassembly

/-!
# Gauss slices of the F₂ and F₄ series

Absolute convergence justifies summation first in the second index. These
identities retain the Gamma regularization at every denominator parameter.
-/

open Complex Polynomial Finset Set
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- Summing the second index of F₂ gives a series of shifted Gauss functions. -/
theorem hasSum_regularizedAppellF2_gauss (a b B c d : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1) :
    HasSum (fun m => (ascPochhammer ℂ m).eval a * (ascPochhammer ℂ m).eval b /
        ((m.factorial : ℂ) * Gamma (c + m)) * x ^ m *
      regularizedGaussHGFun (a + m) B d y) (regularizedAppellF2 a b B c d x y) := by
  have hy : ‖y‖ < 1 := by linarith [norm_nonneg x]
  apply (hasSum_regularizedAppellF2 a b B c d hxy).prod_fiberwise
  intro m
  convert (hasSum_gaussCoeff_mul_pow (a + m) B d hy).mul_left
    ((ascPochhammer ℂ m).eval a * (ascPochhammer ℂ m).eval b /
      ((m.factorial : ℂ) * Gamma (c + m)) * x ^ m) using 1
  funext n
  rw [regularizedAppellF2Coeff_eq, ascPochhammer_add_eval]
  dsimp only [gaussCoeff]
  ring

/-- Summing the second index of F₄ gives a series of two-parameter shifted Gauss functions. -/
theorem hasSum_regularizedAppellF4_gauss (a b c d : ℂ) {x y : ℂ}
    (hxy : Real.sqrt ‖x‖ + Real.sqrt ‖y‖ < 1) :
    HasSum (fun m => (ascPochhammer ℂ m).eval a * (ascPochhammer ℂ m).eval b /
        ((m.factorial : ℂ) * Gamma (c + m)) * x ^ m *
      regularizedGaussHGFun (a + m) (b + m) d y) (regularizedAppellF4 a b c d x y) := by
  have hy : ‖y‖ < 1 := by
    have hs : Real.sqrt ‖y‖ < 1 := by linarith [Real.sqrt_nonneg ‖x‖]
    nlinarith [Real.sq_sqrt (norm_nonneg y), Real.sqrt_nonneg ‖y‖]
  apply (hasSum_regularizedAppellF4 a b c d hxy).prod_fiberwise
  intro m
  convert (hasSum_gaussCoeff_mul_pow (a + m) (b + m) d hy).mul_left
    ((ascPochhammer ℂ m).eval a * (ascPochhammer ℂ m).eval b /
      ((m.factorial : ℂ) * Gamma (c + m)) * x ^ m) using 1
  funext n
  rw [regularizedAppellF4Coeff_eq, ascPochhammer_add_eval, ascPochhammer_add_eval]
  dsimp only [gaussCoeff]
  ring

end Carlson.TwoVariable
