/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The multivariate complex Beta function

## Main definitions and results

* `Complex.mvGamma`: the product of the Gamma functions of a finite parameter family.
* `Complex.mvBeta`: the multivariate complex Beta function.
* `Complex.mvBetaConvergent`: the domain on which the usual simplex integral converges.
* `Complex.mvBeta_perm`: invariance under permutation of the parameters.
* `Complex.mvBeta_addNat`: the translation identity for nonnegative integer shifts.
-/

open Fintype

public noncomputable section MvBeta

namespace Complex

variable {ι : Type*} [Fintype ι]

/-- The product of Gamma functions. -/
def mvGamma (b : ι → ℂ) : ℂ :=
    ∏ i, Gamma (b i)

/-- The multivariate Beta function. -/
def mvBeta (b : ι → ℂ) : ℂ :=
    mvGamma b / Gamma (∑ i, b i)

/-- The domain on which the usual simplex integral representation of `mvBeta` converges
absolutely. -/
def mvBetaConvergent : Set (ι → ℂ) :=
  {b | ∀ i, 0 < (b i).re}

/-- `mvBeta` is symmetric in its arguments. -/
theorem mvBeta_perm (b : ι → ℂ) (σ : Equiv.Perm ι) :
    mvBeta (b ∘ σ) = mvBeta b := by
  change (∏ i, Gamma (b (σ i))) / Gamma (∑ i, b (σ i)) =
    (∏ i, Gamma (b i)) / Gamma (∑ i, b i)
  have hp : (∏ i, Gamma (b (σ i))) = ∏ i, Gamma (b i) :=
    Equiv.prod_comp σ (fun i => Gamma (b i))
  have hs : (∑ i, b (σ i)) = ∑ i, b i :=
    Equiv.sum_comp σ b
  rw [hp, hs]

/-- Positive integer translates of `mvBeta` on its absolutely convergent domain. The domain
hypothesis is necessary because the identity can fail at poles of the Gamma factors. -/
theorem mvBeta_addNat {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (m : ι → ℕ) :
    mvBeta (fun i : ι => b i + (m i : ℂ)) * (ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) =
    mvBeta b * ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
  sorry

end Complex

end MvBeta
