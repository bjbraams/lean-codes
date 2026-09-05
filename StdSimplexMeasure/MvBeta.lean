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
private def mvGamma (b : ι → ℂ) : ℂ :=
    ∏ i, Gamma (b i)

/-- The multivariate Beta function. -/
def mvBeta (b : ι → ℂ) : ℂ :=
    mvGamma b / Gamma (∑ i, b i)

/-- The multivariate Beta function written explicitly as a quotient of Gamma products. -/
theorem mvBeta_eq_prod_Gamma_div (b : ι → ℂ) :
    mvBeta b = (∏ i, Gamma (b i)) / Gamma (∑ i, b i) := rfl

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
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [mvBeta, mvGamma]
  | inr hι =>
      let _ := hι
      have hbpos (i : ι) : 0 < (b i).re := by
        simpa [mvBetaConvergent] using hb i
      have hb_ne_neg_nat (i : ι) (k : ℕ) : b i ≠ -(k : ℂ) := by
        intro hik
        have hi := hbpos i
        rw [hik] at hi
        simp only [neg_re] at hi
        exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg k))) hi
      have hsum_re : 0 < (∑ i, b i).re := by
        simpa using Finset.sum_pos (fun i _ ↦ hbpos i) Finset.univ_nonempty
      have hsum_ne_neg_nat (k : ℕ) : (∑ i, b i) ≠ -(k : ℂ) := by
        intro hk
        have : (∑ i, b i).re = -(k : ℝ) := by
          rw [hk]
          simp
        rw [this] at hsum_re
        exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg k))) hsum_re
      have hcoord (i : ι) :
          Gamma (b i + (m i : ℂ)) =
            (ascPochhammer ℂ (m i)).eval (b i) * Gamma (b i) := by
        apply (div_eq_iff (Gamma_ne_zero (fun k ↦ hb_ne_neg_nat i k))).mp
        exact Gamma_add_nat_div_Gamma_eq (b i) (hb_ne_neg_nat i)
      have hsum :
          ∑ i, (b i + (m i : ℂ)) = (∑ i, b i) + (∑ i, m i : ℕ) := by
        simp [Finset.sum_add_distrib]
      have hden :
          Gamma ((∑ i, b i) + (∑ i, m i : ℕ)) =
            (ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) * Gamma (∑ i, b i) := by
        apply (div_eq_iff (Gamma_ne_zero hsum_ne_neg_nat)).mp
        exact Gamma_add_nat_div_Gamma_eq (∑ i, b i) hsum_ne_neg_nat
      have hprod :
          ∏ i, Gamma (b i + (m i : ℂ)) =
            (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * ∏ i, Gamma (b i) := by
        simp_rw [hcoord, Finset.prod_mul_distrib]
      have hpoch_ne :
          (ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) ≠ 0 := by
        rw [← Gamma_add_nat_div_Gamma_eq (∑ i, b i) hsum_ne_neg_nat]
        exact div_ne_zero
          (Gamma_ne_zero_of_re_pos (by
            simp only [add_re]
            exact add_pos_of_pos_of_nonneg hsum_re (Nat.cast_nonneg _)))
          (Gamma_ne_zero_of_re_pos hsum_re)
      simp only [mvBeta, mvGamma, hsum, hprod, hden]
      field_simp

end Complex

end MvBeta
