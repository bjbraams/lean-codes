/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.LegendreStandard
public import Carlson.Elliptic.Landen
public import Carlson.TwoVariable.QuadraticSlit
public import Carlson.R.EulerTransform

/-!
# Exercises on `R_E`, `R_G`, `R_L` (Carlson's Exercises 9.3-4, 9.5-2, 9.5-5)

## Main results

* `Carlson.carlsonRE_sq_eq`: Exercise 9.5-2, the Landen transformation of `R_E`, from the
  second quadratic transformation (6.10-1) and Table 9.3-2.
* `Carlson.carlsonRL_add_carlsonRL_div`: Exercise 9.3-4, from the Euler transformation,
  homogeneity and Table 9.3-4.
* `Carlson.carlsonRG_landen`: Exercise 9.5-5, the Landen transformation of `R_G`, from
  Theorem 9.5-1 at `t = 1/2` and the reduction to `R_G`, `R_F`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§9.3, 9.5.
-/

open Complex
open scoped Real

@[expose] public noncomputable section

namespace Carlson

open TwoVariable (pair carlsonRK carlsonRK_sq_eq)

/-- **Exercise 9.5-2**, the Landen transformation of `R_E`: for `re x, re y > 0`,
`R_E(x², y²) = 2 R_E(((x + y)/2)², xy) - xy R_K(x², y²)`. -/
theorem carlsonRE_sq_eq {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    carlsonRE (x ^ 2) (y ^ 2) =
      2 * carlsonRE (((x + y) / 2) ^ 2) (x * y) - x * y * carlsonRK (x ^ 2) (y ^ 2) := by
  have hq := TwoVariable.regRSlit_secondQuadratic (1 / 2) (1 / 2) x y hx hy
  rw [TwoVariable.quadraticGammaRatio_one_half, one_mul] at hq
  have hxy : 0 < ((x + y) / 2).re := by simp; linarith
  have ha := sq_mem_slitPlane_of_re_pos hxy
  have hg := mul_mem_slitPlane_of_re_pos hx hy
  have hh := carlsonR_half_three_halves_neg_half ha hg
  rw [carlsonRK_sq_eq x y hx hy]
  unfold carlsonRE carlsonR at *
  rw [hq]
  simp only [TwoVariable.arithmeticMeanSq, TwoVariable.geometricMeanSq, TwoVariable.pair] at *
  norm_num [Fin.sum_univ_two] at hh ⊢
  linear_combination hh

/-- **Exercise 9.3-4**: for real `x, y, ρ > 0`,
`R_L(x, y, ρ) + R_L(x, y, xy/ρ) = 2 R_K(x, y)`. -/
theorem carlsonRL_add_carlsonRL_div {x y ρ : ℝ} (hx : 0 < x) (hy : 0 < y) (hρ : 0 < ρ) :
    carlsonRL x y ρ + carlsonRL x y ((x * y / ρ : ℝ) : ℂ) = 2 * carlsonRK x y := by
  have hs : (![(x : ℂ), y, ρ] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr hx
    · exact ofReal_mem_slitPlane.mpr hy
    · exact ofReal_mem_slitPlane.mpr hρ
  have hρ' : 0 < x * y / ρ := by positivity
  have hw : (![(y : ℂ), x, ((x * y / ρ : ℝ) : ℂ)] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr hy
    · exact ofReal_mem_slitPlane.mpr hx
    · exact ofReal_mem_slitPlane.mpr hρ'
  -- the Euler transformation
  have he := regCarlsonR_euler (-1 / 2) ![1 / 2, 1 / 2, 1] hs
  -- homogeneity with the factor `1/(xy)`
  have hl : 0 < (x * y)⁻¹ := by positivity
  have hh := regCarlsonR_smul_of_pos (-3 / 2) ![1 / 2, 1 / 2, 1] hl hw
  have hinv : (fun i => ((![(x : ℂ), y, ρ] : Fin 3 → ℂ) i)⁻¹) =
      fun i => (((x * y)⁻¹ : ℝ) : ℂ) * (![(y : ℂ), x, ((x * y / ρ : ℝ) : ℂ)] i) := by
    have : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    have : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    have : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.ne'
    funext i; fin_cases i <;> simp <;> field_simp
  rw [show -(∑ i, (![1 / 2, 1 / 2, 1] : Fin 3 → ℂ) i) - (-1 / 2) = -3 / 2 by
    simp [Fin.sum_univ_three]; norm_num, hinv, hh] at he
  -- the fourth row of Table 9.3-4 at `(y, x, xy/ρ)`
  have h4 := carlsonR_complete_third_three_halves (ofReal_mem_slitPlane.mpr hy)
    (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hρ')
  rw [TwoVariable.carlsonRK_comm (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hx),
    carlsonRL_comm (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
      (ofReal_mem_slitPlane.mpr hρ')] at h4
  -- the power factor is `xy/ρ`
  have hpow : (∏ i, (![(x : ℂ), y, ρ] : Fin 3 → ℂ) i ^ (-(![(1 / 2 : ℂ), 1 / 2, 1] i))) *
      (((x * y)⁻¹ : ℝ) : ℂ) ^ (-3 / 2 : ℂ) = ((x * y / ρ : ℝ) : ℂ) := by
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [show -(1 : ℂ) = ((-1 : ℝ) : ℂ) by push_cast; ring,
      show -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
      show (-3 / 2 : ℂ) = ((-(3 / 2) : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow hx.le, ← ofReal_cpow hy.le, ← ofReal_cpow hρ.le, ← ofReal_cpow hl.le,
      ← ofReal_mul, ← ofReal_mul, ← ofReal_mul]
    congr 1
    rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_neg,
      Real.mul_rpow hx.le hy.le, Real.rpow_neg_one]
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_add hy,
      Real.rpow_one, Real.rpow_one, Real.rpow_neg hx.le, Real.rpow_neg hy.le]
    have h1 : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
    have h2 : 0 < y ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hy _
    field_simp
  have hsum : (∑ i, (![1 / 2, 1 / 2, 1] : Fin 3 → ℂ) i) = 2 := by
    simp [Fin.sum_univ_three]; norm_num
  have hL : ∀ a b c : ℂ,
      carlsonRL a b c = regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1] ![a, b, c] := fun a b c => by
    unfold carlsonRL carlsonR; rw [hsum, Gamma_two', one_mul]
  have hR : carlsonR (-3 / 2) ![1 / 2, 1 / 2, 1] ![(y : ℂ), x, ((x * y / ρ : ℝ) : ℂ)] =
      regCarlsonR (-3 / 2) ![1 / 2, 1 / 2, 1] ![(y : ℂ), x, ((x * y / ρ : ℝ) : ℂ)] := by
    unfold carlsonR; rw [hsum, Gamma_two', one_mul]
  have he' : regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1] ![(x : ℂ), y, ρ] =
      ((x * y / ρ : ℝ) : ℂ) *
        regCarlsonR (-3 / 2) ![1 / 2, 1 / 2, 1] ![(y : ℂ), x, ((x * y / ρ : ℝ) : ℂ)] := by
    rw [he, ← mul_assoc, hpow]
  rw [hR, hL] at h4
  rw [hL, hL]
  linear_combination he' + h4

/-- **Exercise 9.5-5**, the Landen transformation of `R_G`: with the notation and assumptions of
Theorem 9.5-1 (`x, y, z, v, w > 0`, `u = (x + y)/2`, `v² + w² = z² + xy`, `vw = zu`),
`2 R_G(x², y², z²) = 4 R_G(u², v², w²) - xy R_F(x², y², z²) - z`. -/
theorem carlsonRG_landen {x y z v w : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hv : 0 < v)
    (hw : 0 < w) (hv2 : v ^ 2 + w ^ 2 = z ^ 2 + x * y) (hvw : v * w = z * ((x + y) / 2)) :
    2 * carlsonRG ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ) =
      4 * carlsonRG ((((x + y) / 2) ^ 2 : ℝ) : ℂ) ((v ^ 2 : ℝ) : ℂ) ((w ^ 2 : ℝ) : ℂ) -
        x * y * carlsonRF ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ) - z := by
  have hu : 0 < (x + y) / 2 := by positivity
  have sl : ∀ {r : ℝ}, 0 < r → ((r ^ 2 : ℝ) : ℂ) ∈ slitPlane := fun hr =>
    ofReal_mem_slitPlane.mpr (by positivity)
  have hL := regCarlsonR_landen hx hy hz hv hw hv2 hvw (1 / 2)
  have h1 := carlsonR_half_half_half_neg_half (sl hx) (sl hy) (sl hz)
  have h2 := carlsonR_half_three_halves_neg_half_neg_half (sl hu) (sl hv) (sl hw)
  have hF := carlsonRF_landen hx hy hz hv hw hv2 hvw
  have hT : carlsonR (1 / 2) ![1 / 2, 1 / 2, -1 / 2]
        ![((x ^ 2 : ℝ) : ℂ), ((y ^ 2 : ℝ) : ℂ), ((z ^ 2 : ℝ) : ℂ)] =
      carlsonR (1 / 2) ![3 / 2, -1 / 2, -1 / 2]
        ![((((x + y) / 2) ^ 2 : ℝ) : ℂ), ((v ^ 2 : ℝ) : ℂ), ((w ^ 2 : ℝ) : ℂ)] := by
    unfold carlsonR
    norm_num [Fin.sum_univ_three] at hL ⊢
    exact Or.inl hL
  -- the algebraic term: `v² w² (u v w)^{-1} = vw/u = z`
  have hQ : ((v ^ 2 : ℝ) : ℂ) * ((w ^ 2 : ℝ) : ℂ) *
      (((((x + y) / 2) ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) * ((v ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
        ((w ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ)) = z := by
    rw [ofReal_cpow_neg_half (by positivity), ofReal_cpow_neg_half (by positivity),
      ofReal_cpow_neg_half (by positivity), Real.sqrt_sq hu.le, Real.sqrt_sq hv.le,
      Real.sqrt_sq hw.le]
    have : (z : ℝ) = v * w / ((x + y) / 2) := by field_simp; linarith
    rw [this]
    push_cast
    field_simp
  rw [hT, h2] at h1
  rw [← hF] at h1
  have hv2C : ((v ^ 2 : ℝ) : ℂ) + ((w ^ 2 : ℝ) : ℂ) = ((z ^ 2 : ℝ) : ℂ) + x * y := by
    push_cast; exact_mod_cast hv2
  linear_combination -h1 - hQ - carlsonRF ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ) *
    hv2C

end Carlson
