/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Standard
public import Carlson.Elliptic.SchwarzChristoffel

/-!
# Transformations of the complete elliptic integral `K` (Exercise 6.10-5)

With `K(k) = (π/2) R_K(k'², 1)` (`legendreK_eq`), the imaginary-modulus transformation follows
from the homogeneity of `R_K` and Landen's transformation from Gauss's invariance
`R_K(x², y²) = R_K(((x+y)/2)², xy)` (`TwoVariable.carlsonRK_sq_eq`).

## Main results

* `Carlson.legendreK_imaginary_modulus`: `K(k) = (1/k') K(ik/k')`, where `K` at the imaginary
  modulus `ik/k'` is `(π/2) R_K(1 + (k/k')², 1)`.
* `Carlson.legendreK_landen`: Landen's transformation `K(k) = 2/(1 + k') K((1 - k')/(1 + k'))`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Exercise 6.10-5.
-/

open Complex
open scoped Real
@[expose] public noncomputable section
namespace Carlson

open TwoVariable (carlsonRK carlsonRK_comm carlsonRK_sq_eq)

/-- `(l : ℂ)^(-1/2) = 1/√l` for real `l > 0`. -/
theorem ofReal_cpow_neg_half {l : ℝ} (hl : 0 < l) :
    (l : ℂ) ^ (-1 / 2 : ℂ) = ((Real.sqrt l)⁻¹ : ℝ) := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hl.le,
    Real.sqrt_eq_rpow, ← Real.rpow_neg hl.le]
  norm_num

/-- **Exercise 6.10-5, first relation**: for `k² < 1` and `k' = √(1 - k²)`,
`K(k) = (1/k') K(ik/k')`, where
`K(ik/k') = (π/2) R_K(1 - (ik/k')², 1) = (π/2) R_K(1 + (k/k')², 1)`. -/
theorem legendreK_imaginary_modulus {k : ℝ} (hk : k ^ 2 < 1) :
    (legendreK k : ℂ) = (1 / Real.sqrt (1 - k ^ 2) : ℝ) *
      (π / 2 * carlsonRK (1 + (k / Real.sqrt (1 - k ^ 2)) ^ 2 : ℝ) 1) := by
  set k' := Real.sqrt (1 - k ^ 2)
  have hk' : 0 < k' := Real.sqrt_pos.mpr (by linarith)
  have hk'2 : k' ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hne : 1 - k ^ 2 ≠ 0 := by linarith
  have hval : 1 + (k / k') ^ 2 = 1 / k' ^ 2 := by
    rw [div_pow, hk'2]; field_simp; ring
  rw [hval, legendreK_eq hk]
  have hl : 0 < 1 / k' ^ 2 := by positivity
  have h := carlsonRK_mul_of_pos hl (x := 1) (y := ((k' ^ 2 : ℝ) : ℂ)) one_mem_slitPlane
    (by rw [mem_slitPlane_iff]; left; simp only [ofReal_re]; exact pow_pos hk' 2)
  rw [mul_one, ← ofReal_mul, show 1 / k' ^ 2 * k' ^ 2 = 1 by field_simp, ofReal_one,
    ofReal_cpow_neg_half hl, Real.sqrt_div' _ (by positivity), Real.sqrt_one,
    Real.sqrt_sq hk'.le] at h
  rw [show ((1 / k' ^ 2 : ℝ) : ℂ) = ((1 / k' ^ 2 : ℝ) : ℂ) from rfl, h,
    carlsonRK_comm one_mem_slitPlane (by
      rw [mem_slitPlane_iff]; left; simp only [ofReal_re]; exact pow_pos hk' 2), hk'2]
  have hk'c : (k' : ℂ) ≠ 0 := by exact_mod_cast hk'.ne'
  push_cast
  field_simp

/-- **Exercise 6.10-5, Landen's transformation**: for `0 ≤ k < 1` and `k' = √(1 - k²)`,
`K(k) = 2/(1 + k') K((1 - k')/(1 + k'))`. -/
theorem legendreK_landen {k : ℝ} (hk : k ^ 2 < 1) :
    legendreK k = 2 / (1 + Real.sqrt (1 - k ^ 2)) *
      legendreK ((1 - Real.sqrt (1 - k ^ 2)) / (1 + Real.sqrt (1 - k ^ 2))) := by
  set k' := Real.sqrt (1 - k ^ 2)
  have hk' : 0 < k' := Real.sqrt_pos.mpr (by linarith)
  have hk'2 : k' ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hk'1 : k' ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith [sq_nonneg k]
  set k₁ := (1 - k') / (1 + k')
  have hk₁ : k₁ ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]; nlinarith
  have h1k₁ : 1 - k₁ ^ 2 = 4 * k' / (1 + k') ^ 2 := by
    simp only [k₁]; field_simp; ring
  apply Complex.ofReal_injective
  push_cast
  rw [legendreK_eq hk, legendreK_eq hk₁, h1k₁, ← hk'2]
  -- Gauss: `R_K(k'², 1²) = R_K(m², k')` with `m = (1 + k')/2`
  have hg := carlsonRK_sq_eq (k' : ℂ) 1 (by simpa using hk') (by simp)
  rw [one_pow, mul_one] at hg
  -- homogeneity: `R_K(4k'/(1+k')², 1) = ((1 + k')/2) R_K(k', m²)`
  set l : ℝ := 4 / (1 + k') ^ 2
  have hl : 0 < l := by positivity
  have hm : (((1 + k') / 2) ^ 2 : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left
    rw [show (((1 + k') / 2) ^ 2 : ℂ) = (((1 + k') / 2) ^ 2 : ℝ) by push_cast; ring, ofReal_re]
    positivity
  have hkk : (k' : ℂ) ∈ slitPlane := by rw [mem_slitPlane_iff]; left; simpa using hk'
  have hh := carlsonRK_mul_of_pos hl hkk hm
  have e1 : (l : ℂ) * k' = ((4 * k' / (1 + k') ^ 2 : ℝ) : ℂ) := by simp only [l]; push_cast; ring
  have h1kc : (1 + (k' : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < 1 + k').ne'
  have e2 : (l : ℂ) * ((1 + k') / 2) ^ 2 = 1 := by
    simp only [l]; push_cast; field_simp; ring
  have e3 : Real.sqrt l = 2 / (1 + k') := by
    simp only [l]
    rw [show (4 : ℝ) / (1 + k') ^ 2 = (2 / (1 + k')) ^ 2 by rw [div_pow]; norm_num,
      Real.sqrt_sq (by positivity)]
  rw [e1, e2, ofReal_cpow_neg_half hl, e3, carlsonRK_comm hkk hm] at hh
  rw [show ((k' ^ 2 : ℝ) : ℂ) = (k' : ℂ) ^ 2 by push_cast; ring, hg]
  push_cast at hh ⊢
  rw [hh]
  have : (1 + (k' : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < 1 + k').ne'
  field_simp
  ring_nf
