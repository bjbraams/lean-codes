/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Beta.Real
public import ToMathlib.Analysis.SpecialFunctions.GammaStrictConvex
public import Mathlib.Analysis.Convex.Jensen

/-!
# Strict beta inequalities at fixed total parameter

Strict log-convexity of Gamma gives Carlson (1977), Exercises 4.2-3 and 4.3-2:
among positive parameter vectors with a fixed sum, the multivariate beta function
has its unique minimum at the constant vector.
-/

open Set

public noncomputable section

namespace Real

/-- Strict midpoint log-convexity of Gamma in product form. -/
theorem Gamma_midpoint_sq_lt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    Gamma ((x + y) / 2) ^ 2 < Gamma x * Gamma y := by
  have hm : 0 < (x + y) / 2 := by positivity
  have h := strictConvexOn_log_Gamma.2 hx hy hne
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [Function.comp_apply, smul_eq_mul] at h
  apply (log_lt_log_iff (sq_pos_of_pos (Gamma_pos_of_pos hm))
    (mul_pos (Gamma_pos_of_pos hx) (Gamma_pos_of_pos hy))).mp
  rw [log_pow, log_mul (Gamma_pos_of_pos hx).ne' (Gamma_pos_of_pos hy).ne']
  have he : (1 / 2 : ℝ) * x + (1 / 2) * y = (x + y) / 2 := by ring
  rw [he] at h
  norm_num only [Nat.cast_ofNat]
  linarith

end Real

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Carlson Exercise 4.3-2.** A nonconstant positive parameter vector has larger
multivariate beta value than the constant vector with the same total. -/
theorem mvRealBeta_const_lt {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (hne : ∃ i j, b i ≠ b j) :
    mvRealBeta (fun _ : ι => (∑ i, b i) / Fintype.card ι) < mvRealBeta b := by
  classical
  let k : ℝ := Fintype.card ι
  have hk : 0 < k := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hm : 0 < (∑ i, b i) / k := div_pos hsum hk
  have hj := Real.strictConvexOn_log_Gamma.map_sum_lt
    (t := Finset.univ) (w := fun _ : ι => k⁻¹) (p := b)
    (fun _ _ => inv_pos.mpr hk) (by simp [k, ne_of_gt hk]) (fun i _ => hb i)
    (by obtain ⟨i, j, h⟩ := hne; exact ⟨i, Finset.mem_univ _, j, Finset.mem_univ _, h⟩)
  simp only [smul_eq_mul, Function.comp_apply, ← Finset.mul_sum] at hj
  have hprod : Real.Gamma ((∑ i, b i) / k) ^ Fintype.card ι < ∏ i, Real.Gamma (b i) := by
    apply (Real.log_lt_log_iff (pow_pos (Real.Gamma_pos_of_pos hm) _)
      (Finset.prod_pos fun i _ => Real.Gamma_pos_of_pos (hb i))).mp
    rw [Real.log_pow, Real.log_prod (fun i _ => (Real.Gamma_pos_of_pos (hb i)).ne')]
    change k * Real.log (Real.Gamma ((∑ i, b i) / k)) < ∑ i, Real.log (Real.Gamma (b i))
    have hj' := (mul_lt_mul_of_pos_left hj hk)
    simpa only [div_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul] using hj'
  have he : (∑ _ : ι, (∑ i, b i) / k) = ∑ i, b i := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change k * ((∑ i, b i) / k) = ∑ i, b i
    field_simp
  unfold mvRealBeta
  rw [he]
  simp only [Finset.prod_const, Finset.card_univ]
  exact div_lt_div_of_pos_right hprod (Real.Gamma_pos_of_pos hsum)

/-- **Carlson Exercise 4.2-3.** The two-variable beta function is strictly larger
away from equal positive parameters when their sum is fixed. -/
theorem beta_midpoint_lt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    beta ((x + y) / 2) ((x + y) / 2) < beta x y := by
  unfold beta
  rw [show (x + y) / 2 + (x + y) / 2 = x + y by ring, ← sq]
  exact div_lt_div_of_pos_right (Real.Gamma_midpoint_sq_lt hx hy hne)
    (Real.Gamma_pos_of_pos (add_pos hx hy))

end ProbabilityTheory
