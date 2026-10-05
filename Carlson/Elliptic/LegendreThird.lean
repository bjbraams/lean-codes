/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Standard
public import Carlson.R.SlitRelations

/-!
# Legendre's third-kind integral

The incomplete integral `Π(φ, k, n)` is represented by Carlson's continued `R`
function as in (9.2-11), for real arguments with `0 < φ < π/2`, `k² < 1`, and
`n sin² φ < 1`. The complete case (9.2-14) is proved separately for `k² < 1`,
`n < 1`. These conditions keep the pole outside the integration interval.

The associated-function identities give two rows each of Tables 9.3-3 and 9.3-4
on the full complex slit domain, without assuming distinct nodes. These reduce
incomplete `Π` to `R_F` and `R_H`, and complete `Π` to `R_K` and `R_L`.

## Main results

* `legendrePi_eq`, `legendrePi_complete_eq`: the `R` representations.
* `legendrePi_eq_standard`, `legendrePi_complete_eq_standard`: reductions to
  symmetric standard functions, with polynomial coefficients.
* `carlsonR_third_neg_half`, `carlsonR_third_three_halves`: Table 9.3-3, rows 2 and 4.
* `carlsonR_complete_third_neg_half`, `carlsonR_complete_third_three_halves`:
  Table 9.3-4, rows 1 and 4.

The Legendre identities here concern real integrals without a pole. Complex
amplitudes and principal-value integrals are not treated.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, 1977, §§9.2–9.3.
-/

open Complex Set MeasureTheory
open scoped Real
@[expose] public noncomputable section

namespace Carlson

/-- The incomplete third-kind integral after the substitution `t = sin θ`,
expressed as an `R` function. The characteristic may be negative. -/
theorem integral_Ioo_sn_third {k y n : ℝ} (hk : k ^ 2 < 1) (hy0 : 0 < y) (hy1 : y < 1)
    (hn : n * y ^ 2 < 1) :
    ((∫ t in Ioo (0 : ℝ) y, (1 - t ^ 2) ^ (-1 / 2 : ℝ) *
        (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ) * (1 - n * t ^ 2)⁻¹ : ℝ) :
        ℂ) =
      y * carlsonR (-1 / 2) ![1 / 2, 1 / 2, -1 / 2, 1]
        ![((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ), ((1 - y ^ 2 : ℝ) : ℂ), 1,
          ((1 - n * y ^ 2 : ℝ) : ℂ)] := by
  set g : ℝ → ℝ := fun t => (1 - t ^ 2) ^ (-1 / 2 : ℝ) *
    (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ) * (1 - n * t ^ 2)⁻¹
  set φ : ℝ → ℝ := fun s => y * Real.sqrt s
  set N : Fin 4 → ℂ := ![((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ), ((1 - y ^ 2 : ℝ) : ℂ), 1,
          ((1 - n * y ^ 2 : ℝ) : ℂ)]
  set B : Fin 4 → ℂ := ![1 / 2, 1 / 2, -1 / 2, 1]
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt φ (y * (1 / (2 * Real.sqrt s)))
      (Ioo 0 1) s := fun s hs =>
    ((Real.hasDerivAt_sqrt hs.1.ne').const_mul y).hasDerivWithinAt
  have hinj : InjOn φ (Ioo 0 1) := by
    intro a ha b hb hab
    have := mul_left_cancel₀ hy0.ne' hab
    rwa [Real.sqrt_inj ha.1.le hb.1.le] at this
  have himg : φ '' Ioo 0 1 = Ioo 0 y := by
    ext t; constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨mul_pos hy0 (Real.sqrt_pos.mpr hs.1), ?_⟩
      have : Real.sqrt s < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using hs.2
      show y * Real.sqrt s < y
      nlinarith
    · rintro ⟨ht0, hty⟩
      refine ⟨(t / y) ^ 2, ⟨by positivity, ?_⟩, ?_⟩
      · rw [sq_lt_one_iff_abs_lt_one, abs_of_pos (by positivity), div_lt_one hy0]; exact hty
      · show y * Real.sqrt ((t / y) ^ 2) = t
        rw [Real.sqrt_sq (by positivity)]; field_simp
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  rw [himg] at hsub
  rw [hsub]
  have hz : N ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · show ((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ) ∈ slitPlane
      have hky := mul_nonneg (sq_nonneg k) (sq_nonneg y)
      have hy2 : y ^ 2 < 1 := by nlinarith
      exact ofReal_mem_slitPlane.mpr (by nlinarith)
    · show ((1 - y ^ 2 : ℝ) : ℂ) ∈ slitPlane
      exact ofReal_mem_slitPlane.mpr (by nlinarith)
    · simp [N]
    · exact ofReal_mem_slitPlane.mpr (by simpa [N] using sub_pos.mpr hn)
  have h := carlsonRUnitIntervalIntegral_eq_Gamma_mul_regCarlsonR (a := 1 / 2) (a' := 1)
    (b := B) (by norm_num) (by norm_num) (by simp [B, Fin.sum_univ_four]; norm_num) hz
  unfold carlsonRUnitIntervalIntegral at h
  rw [← integral_complex_ofReal]
  have hpt : ∀ s ∈ Ioo (0 : ℝ) 1, ((|y * (1 / (2 * Real.sqrt s))| • g (φ s) : ℝ) : ℂ) =
      (y / 2 : ℂ) * ((s : ℂ) ^ ((1 / 2 : ℂ) - 1) * (1 - s : ℂ) ^ ((1 : ℂ) - 1) *
        ∏ i, ((1 - s : ℂ) + (s : ℂ) * N i) ^ (-B i)) := by
    intro s hs
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.1.le
    have h1 : 0 < 1 - y ^ 2 * s := by nlinarith [hs.1, hs.2]
    have h2 : 0 < 1 - k ^ 2 * y ^ 2 * s := by
      nlinarith [hs.1, hs.2, sq_nonneg k, sq_nonneg y, mul_nonneg (sq_nonneg k) (sq_nonneg y)]
    have hg : g (φ s) =
        (1 - y ^ 2 * s) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * y ^ 2 * s) ^ (-1 / 2 : ℝ) *
          (1 - n * y ^ 2 * s)⁻¹ := by
      simp only [g, φ]
      rw [show (1 - (y * Real.sqrt s) ^ 2) = 1 - y ^ 2 * s by rw [mul_pow, hsq],
        show (1 - k ^ 2 * (y * Real.sqrt s) ^ 2) = 1 - k ^ 2 * y ^ 2 * s by rw [mul_pow, hsq]; ring,
        show (1 - n * (y * Real.sqrt s) ^ 2) = 1 - n * y ^ 2 * s by rw [mul_pow, hsq]; ring]
    have habs : |y * (1 / (2 * Real.sqrt s))| = y / 2 * s ^ (-1 / 2 : ℝ) := by
      rw [abs_of_pos (by have := Real.sqrt_pos.mpr hs.1; positivity),
        show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow]
      ring
    rw [hg, habs, smul_eq_mul]
    push_cast
    rw [ofReal_cpow hs.1.le, ofReal_cpow h1.le, ofReal_cpow h2.le]
    simp only [N, B, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    push_cast
    rw [show (1 : ℂ) - s + s * 1 = 1 by ring, one_cpow, mul_one, sub_self, cpow_zero, mul_one,
      show (1 : ℂ) - s + s * (1 - y ^ 2) = 1 - y ^ 2 * s by ring,
      show (1 : ℂ) - s + s * (1 - k ^ 2 * y ^ 2) = 1 - k ^ 2 * y ^ 2 * s by ring,
      show (1 : ℂ) - s + s * (1 - n * y ^ 2) = 1 - n * y ^ 2 * s by ring]
    rw [cpow_neg_one]
    norm_num
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul, h, carlsonR,
    Gamma_one, show (∑ i, B i) = 1 / 2 + 1 by simp [B, Fin.sum_univ_four]; norm_num,
    Gamma_add_one _ (by norm_num)]
  simp only [N, B]
  ring_nf


/-- The sine substitution in Legendre's third-kind integral, including the complete endpoint. -/
private theorem legendrePi_sin {φ k n : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) :
    legendrePi φ k n = ∫ t in Ioo (0 : ℝ) (Real.sin φ),
    (1 - t ^ 2) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ) *
      (1 - n * t ^ 2)⁻¹ := by
  rw [integral_Ioo_comp_sin h0 h1, legendrePi,
    intervalIntegral.integral_of_le h0.le, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hcancel : Real.cos θ * (1 - Real.sin θ ^ 2) ^ (-1 / 2 : ℝ) = 1 := by
    rw [← Real.cos_sq', show (-1 / 2 : ℝ) = -(1 / 2) by ring,
      Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq hc.le,
      mul_inv_cancel₀ hc.ne']
  symm
  calc
    _ = (Real.cos θ * (1 - Real.sin θ ^ 2) ^ (-1 / 2 : ℝ)) *
        (1 - Real.sin θ ^ 2 * k ^ 2) ^ (-1 / 2 : ℝ) *
          (1 - n * Real.sin θ ^ 2)⁻¹ := by rw [mul_comm (Real.sin θ ^ 2)]; ring
    _ = _ := by rw [hcancel, mul_comm (Real.sin θ ^ 2) (k ^ 2)]; ring

/-- **Carlson's (9.2-11), third kind**: Legendre's incomplete `Π` as an `R` function.
The characteristic `n` satisfies `n sin² φ < 1`, so the integral has no pole. -/
theorem legendrePi_eq {φ k n : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) (hk : k ^ 2 < 1)
    (hn : n * Real.sin φ ^ 2 < 1) :
    (legendrePi φ k n : ℂ) = Real.sin φ *
      carlsonR (-1 / 2) ![1 / 2, 1 / 2, -1 / 2, 1]
        ![((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ), ((Real.cos φ ^ 2 : ℝ) : ℂ), 1,
          ((1 - n * Real.sin φ ^ 2 : ℝ) : ℂ)] := by
  have hs0 : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hs1 : Real.sin φ < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl h1
  rw [legendrePi_sin h0 h1.le, integral_Ioo_sn_third hk hs0 hs1 hn, Real.cos_sq']

/-- A zero fourth parameter can be deleted from the first-kind integral, including slit-plane
nodes whose real parts are not positive. -/
private theorem regCarlsonR_half_four_zero {x y z ρ : ℂ}
    (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hρ : ρ ∈ slitPlane) :
    regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2, 0] ![x, y, z, ρ] =
      regCarlsonR (-1 / 2) (fun _ : Fin 3 => 1 / 2) ![x, y, z] := by
  have h4 := carlsonRUnitIntervalIntegral_eq_Gamma_mul_regCarlsonR
    (a := 1 / 2) (a' := 1) (b := ![1 / 2, 1 / 2, 1 / 2, 0])
    (z := ![x, y, z, ρ]) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_four]; norm_num) (by intro i; fin_cases i <;> assumption)
  have h3 := carlsonRUnitIntervalIntegral_eq_Gamma_mul_regCarlsonR
    (a := 1 / 2) (a' := 1) (b := fun _ : Fin 3 => 1 / 2)
    (z := ![x, y, z]) (by norm_num) (by norm_num)
    (by simp; norm_num) (by intro i; fin_cases i <;> assumption)
  have hi : carlsonRUnitIntervalIntegral (1 / 2) 1 ![1 / 2, 1 / 2, 1 / 2, 0] ![x, y, z, ρ] =
      carlsonRUnitIntervalIntegral (1 / 2) 1 (fun _ : Fin 3 => 1 / 2) ![x, y, z] := by
    simp [carlsonRUnitIntervalIntegral, Fin.prod_univ_four, Fin.prod_univ_three]
  rw [hi, h3] at h4
  have hG : Gamma (1 / 2 : ℂ) * Gamma 1 ≠ 0 := by
    rw [Gamma_one, mul_one]
    exact Gamma_ne_zero_of_re_pos (by norm_num)
  simpa only [neg_div] using mul_left_cancel₀ hG h4.symm

/-- The `(-1/2, 1/2, 1/2)` row of Carlson's Table 9.3-3, with the lowered parameter
in the third position. All four nodes may lie anywhere in the slit plane. -/
theorem carlsonR_third_neg_half {x y z ρ : ℂ}
    (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hρ : ρ ∈ slitPlane) :
    3 * ρ * carlsonR (-1 / 2) ![1 / 2, 1 / 2, -1 / 2, 1] ![x, y, z, ρ] =
      2 * (ρ - z) * carlsonRH x y z ρ + 3 * z * carlsonRF x y z := by
  classical
  have hs : (![x, y, z, ρ] : Fin 4 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  have h2 := regCarlsonR_eq_addDirichletUnit (-1 / 2) ![1 / 2, 1 / 2, -1 / 2, 1] hs 2
  have h3 := regCarlsonR_eq_addDirichletUnit (-1 / 2) ![1 / 2, 1 / 2, 1 / 2, 0] hs 3
  have hb2 : Dirichlet.addDirichletUnit (![1 / 2, 1 / 2, -1 / 2, 1] : Fin 4 → ℂ) 2 =
      ![1 / 2, 1 / 2, 1 / 2, 1] := by
    ext i; fin_cases i <;> simp [Dirichlet.addDirichletUnit]; norm_num
  have hb3 : Dirichlet.addDirichletUnit (![1 / 2, 1 / 2, 1 / 2, 0] : Fin 4 → ℂ) 3 =
      ![1 / 2, 1 / 2, 1 / 2, 1] := by
    ext i; fin_cases i <;> simp [Dirichlet.addDirichletUnit]
  rw [hb2] at h2
  rw [hb3, regCarlsonR_half_four_zero hx hy hz hρ] at h3
  norm_num [Fin.sum_univ_four] at h2 h3
  unfold carlsonRH carlsonRF carlsonR
  have hg : Gamma (5 / 2 : ℂ) = 3 / 2 * Gamma (3 / 2) := by
    rw [show (5 / 2 : ℂ) = 3 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
  norm_num [Fin.sum_univ_four, Fin.sum_univ_three] at ⊢
  rw [hg]
  linear_combination (3 * ρ * Gamma (3 / 2)) * h2 - (3 * z * Gamma (3 / 2)) * h3

/-- Legendre's incomplete third-kind integral reduced to the symmetric standard functions
`R_F` and `R_H`. This form avoids division by the characteristic. -/
theorem legendrePi_eq_standard {φ k n : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2)
    (hk : k ^ 2 < 1) (hn : n * Real.sin φ ^ 2 < 1) :
    3 * ((1 - n * Real.sin φ ^ 2 : ℝ) : ℂ) * (legendrePi φ k n : ℂ) =
      (Real.sin φ : ℂ) *
        (2 * (((1 - n * Real.sin φ ^ 2 : ℝ) : ℂ) - 1) *
            carlsonRH ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ)
              ((Real.cos φ ^ 2 : ℝ) : ℂ) 1 ((1 - n * Real.sin φ ^ 2 : ℝ) : ℂ) +
          3 * carlsonRF ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ)
            ((Real.cos φ ^ 2 : ℝ) : ℂ) 1) := by
  have hs : Real.sin φ ^ 2 ≤ 1 := Real.sin_sq_le_one φ
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], h1⟩
  have hx : ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) ∈ slitPlane :=
    ofReal_mem_slitPlane.mpr (by nlinarith [sq_nonneg k, sq_nonneg (Real.sin φ)])
  have hy : ((Real.cos φ ^ 2 : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr (sq_pos_of_pos hc)
  have hp : ((1 - n * Real.sin φ ^ 2 : ℝ) : ℂ) ∈ slitPlane :=
    ofReal_mem_slitPlane.mpr (by linarith)
  have H := carlsonR_third_neg_half hx hy (z := 1) (by simp) hp
  rw [legendrePi_eq h0 h1 hk hn]
  linear_combination (Real.sin φ : ℂ) * H

/-- The complete third-kind integral in the sine variable as a three-variable `R` function. -/
theorem integral_Ioo_sn_third_complete {k n : ℝ} (hk : k ^ 2 < 1) (hn : n < 1) :
    ((∫ t in Ioo (0 : ℝ) 1, (1 - t ^ 2) ^ (-1 / 2 : ℝ) *
        (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ) * (1 - n * t ^ 2)⁻¹ : ℝ) : ℂ) =
      (π / 2 : ℂ) * carlsonR (-1 / 2) ![1 / 2, -1 / 2, 1]
        ![((1 - k ^ 2 : ℝ) : ℂ), 1, ((1 - n : ℝ) : ℂ)] := by
  set g : ℝ → ℝ := fun t => (1 - t ^ 2) ^ (-1 / 2 : ℝ) *
    (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ) * (1 - n * t ^ 2)⁻¹
  set N : Fin 3 → ℂ := ![((1 - k ^ 2 : ℝ) : ℂ), 1, ((1 - n : ℝ) : ℂ)]
  set B : Fin 3 → ℂ := ![1 / 2, -1 / 2, 1]
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt Real.sqrt (1 / (2 * Real.sqrt s)) (Ioo 0 1) s :=
    fun s hs => (Real.hasDerivAt_sqrt hs.1.ne').hasDerivWithinAt
  have hinj : InjOn Real.sqrt (Ioo (0 : ℝ) 1) :=
    fun a ha b hb hab => (Real.sqrt_inj ha.1.le hb.1.le).mp hab
  have himg : Real.sqrt '' Ioo (0 : ℝ) 1 = Ioo 0 1 := by
    ext t; constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Real.sqrt_pos.mpr hs.1, (Real.sqrt_lt' one_pos).mpr (by simpa using hs.2)⟩
    · intro ht
      exact ⟨t ^ 2, ⟨sq_pos_of_pos ht.1, by nlinarith [ht.1, ht.2]⟩, Real.sqrt_sq ht.1.le⟩
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  rw [himg] at hsub
  rw [hsub, ← integral_complex_ofReal]
  have hz : N ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr (sub_pos.mpr hk)
    · simp [N]
    · exact ofReal_mem_slitPlane.mpr (sub_pos.mpr hn)
  have h := carlsonRUnitIntervalIntegral_eq_Gamma_mul_regCarlsonR (a := 1 / 2) (a' := 1 / 2)
    (b := B) (by norm_num) (by norm_num) (by simp [B, Fin.sum_univ_three]; norm_num) hz
  unfold carlsonRUnitIntervalIntegral at h
  have hpt : ∀ s ∈ Ioo (0 : ℝ) 1, ((|1 / (2 * Real.sqrt s)| • g (Real.sqrt s) : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ((s : ℂ) ^ ((1 / 2 : ℂ) - 1) * (1 - s : ℂ) ^ ((1 / 2 : ℂ) - 1) *
        ∏ i, ((1 - s : ℂ) + (s : ℂ) * N i) ^ (-B i)) := by
    intro s hs
    have h1 : 0 < 1 - s := sub_pos.mpr hs.2
    have h2 : 0 < 1 - k ^ 2 * s := by nlinarith [hs.1, hs.2, sq_nonneg k]
    have habs : |1 / (2 * Real.sqrt s)| = 1 / 2 * s ^ (-1 / 2 : ℝ) := by
      rw [abs_of_pos (by have := Real.sqrt_pos.mpr hs.1; positivity),
        show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow]
      ring
    simp only [g, Real.sq_sqrt hs.1.le, habs, smul_eq_mul]
    push_cast
    rw [ofReal_cpow hs.1.le, ofReal_cpow h1.le, ofReal_cpow h2.le]
    simp only [N, B, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast
    rw [show (1 : ℂ) - s + s * 1 = 1 by ring, one_cpow, mul_one,
      show (1 : ℂ) - s + s * (1 - k ^ 2) = 1 - k ^ 2 * s by ring,
      show (1 : ℂ) - s + s * (1 - n) = 1 - n * s by ring, cpow_neg_one]
    norm_num
    ring
  have hG : Gamma (1 / 2 : ℂ) * Gamma (1 / 2) = π := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Gamma_ofReal,
      Real.Gamma_one_half_eq, ← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul, h, hG, carlsonR,
    show (∑ i, B i) = 1 by simp [B, Fin.sum_univ_three]; norm_num, Gamma_one, one_mul]
  simp only [N, B, neg_div]
  ring

/-- **Carlson's (9.2-14), third kind**: the complete Legendre integral as an `R` function,
for `k² < 1` and characteristic `n < 1`. -/
theorem legendrePi_complete_eq {k n : ℝ} (hk : k ^ 2 < 1) (hn : n < 1) :
    (legendrePi (π / 2) k n : ℂ) = (π / 2 : ℂ) *
      carlsonR (-1 / 2) ![1 / 2, -1 / 2, 1] ![((1 - k ^ 2 : ℝ) : ℂ), 1, ((1 - n : ℝ) : ℂ)] := by
  rw [legendrePi_sin (by positivity) le_rfl, Real.sin_pi_div_two,
    integral_Ioo_sn_third_complete hk hn]

/-- The last row of Carlson's Table 9.3-3, equivalently (9.3-4), on slit-plane nodes. -/
theorem carlsonR_third_three_halves {x y z ρ : ℂ}
    (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hρ : ρ ∈ slitPlane) :
    ρ * carlsonR (-3 / 2) ![1 / 2, 1 / 2, 1 / 2, 1] ![x, y, z, ρ] =
      3 * carlsonRF x y z - 2 * carlsonRH x y z ρ := by
  have hs : (![x, y, z, ρ] : Fin 4 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  have h := regCarlsonR_eq_addDirichletUnit (-1 / 2) ![1 / 2, 1 / 2, 1 / 2, 0] hs 3
  have hb : Dirichlet.addDirichletUnit (![1 / 2, 1 / 2, 1 / 2, 0] : Fin 4 → ℂ) 3 =
      ![1 / 2, 1 / 2, 1 / 2, 1] := by
    ext i; fin_cases i <;> simp [Dirichlet.addDirichletUnit]
  rw [hb, regCarlsonR_half_four_zero hx hy hz hρ] at h
  norm_num [Fin.sum_univ_four] at h
  unfold carlsonRH carlsonRF carlsonR
  norm_num [Fin.sum_univ_four, Fin.sum_univ_three]
  rw [show (5 / 2 : ℂ) = 3 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
  linear_combination (-3 * Gamma (3 / 2)) * h

/-- Deleting a zero third parameter in the complete first-kind integral on slit-plane nodes. -/
private theorem regCarlsonR_half_three_zero {x y ρ : ℂ}
    (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ : ρ ∈ slitPlane) :
    regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 0] ![x, y, ρ] =
      regCarlsonR (-1 / 2) (TwoVariable.pair (1 / 2) (1 / 2)) (TwoVariable.pair x y) := by
  have h3 := carlsonRUnitIntervalIntegral_eq_Gamma_mul_regCarlsonR
    (a := 1 / 2) (a' := 1 / 2) (b := ![1 / 2, 1 / 2, 0])
    (z := ![x, y, ρ]) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_three]) (by intro i; fin_cases i <;> assumption)
  have h2 := carlsonRUnitIntervalIntegral_eq_Gamma_mul_regCarlsonR
    (a := 1 / 2) (a' := 1 / 2) (b := TwoVariable.pair (1 / 2) (1 / 2))
    (z := TwoVariable.pair x y) (by norm_num) (by norm_num)
    (by simp) (by intro i; fin_cases i <;> assumption)
  have hi : carlsonRUnitIntervalIntegral (1 / 2) (1 / 2) ![1 / 2, 1 / 2, 0] ![x, y, ρ] =
      carlsonRUnitIntervalIntegral (1 / 2) (1 / 2) (TwoVariable.pair (1 / 2) (1 / 2))
        (TwoVariable.pair x y) := by
    simp [carlsonRUnitIntervalIntegral, Fin.prod_univ_three, Fin.prod_univ_two, TwoVariable.pair]
  rw [hi, h2] at h3
  have hG : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  simpa only [neg_div] using mul_left_cancel₀ (mul_ne_zero hG hG) h3.symm

/-- The first row of Carlson's Table 9.3-4, with the lowered parameter in the second position.
No distinctness of the slit-plane nodes is required. -/
theorem carlsonR_complete_third_neg_half {x y ρ : ℂ}
    (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ : ρ ∈ slitPlane) :
    2 * ρ * carlsonR (-1 / 2) ![1 / 2, -1 / 2, 1] ![x, y, ρ] =
      (ρ - y) * carlsonRL x y ρ + 2 * y * TwoVariable.carlsonRK x y := by
  have hs : (![x, y, ρ] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  have h1 := regCarlsonR_eq_addDirichletUnit (-1 / 2) ![1 / 2, -1 / 2, 1] hs 1
  have h2 := regCarlsonR_eq_addDirichletUnit (-1 / 2) ![1 / 2, 1 / 2, 0] hs 2
  have hb1 : Dirichlet.addDirichletUnit (![1 / 2, -1 / 2, 1] : Fin 3 → ℂ) 1 =
      ![1 / 2, 1 / 2, 1] := by
    ext i; fin_cases i <;> simp [Dirichlet.addDirichletUnit]; norm_num
  have hb2 : Dirichlet.addDirichletUnit (![1 / 2, 1 / 2, 0] : Fin 3 → ℂ) 2 =
      ![1 / 2, 1 / 2, 1] := by
    ext i; fin_cases i <;> simp [Dirichlet.addDirichletUnit]
  rw [hb1] at h1
  rw [hb2, regCarlsonR_half_three_zero hx hy hρ] at h2
  norm_num [Fin.sum_univ_three] at h1 h2
  unfold carlsonRL TwoVariable.carlsonRK carlsonR
  norm_num [Fin.sum_univ_three, TwoVariable.sum_pair]
  linear_combination (2 * ρ) * h1 - (2 * y) * h2

/-- The fourth row of Carlson's Table 9.3-4, on slit-plane nodes. -/
theorem carlsonR_complete_third_three_halves {x y ρ : ℂ}
    (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ : ρ ∈ slitPlane) :
    ρ * carlsonR (-3 / 2) ![1 / 2, 1 / 2, 1] ![x, y, ρ] =
      2 * TwoVariable.carlsonRK x y - carlsonRL x y ρ := by
  have hs : (![x, y, ρ] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  have h := regCarlsonR_eq_addDirichletUnit (-1 / 2) ![1 / 2, 1 / 2, 0] hs 2
  have hb : Dirichlet.addDirichletUnit (![1 / 2, 1 / 2, 0] : Fin 3 → ℂ) 2 =
      ![1 / 2, 1 / 2, 1] := by
    ext i; fin_cases i <;> simp [Dirichlet.addDirichletUnit]
  rw [hb, regCarlsonR_half_three_zero hx hy hρ] at h
  norm_num [Fin.sum_univ_three] at h
  unfold carlsonRL TwoVariable.carlsonRK carlsonR
  norm_num [Fin.sum_univ_three, TwoVariable.sum_pair]
  linear_combination -2 * h

/-- The complete Legendre third-kind integral reduced to `R_K` and `R_L`, for `k² < 1`
and `n < 1`, including zero and negative characteristics. -/
theorem legendrePi_complete_eq_standard {k n : ℝ} (hk : k ^ 2 < 1) (hn : n < 1) :
    2 * ((1 - n : ℝ) : ℂ) * (legendrePi (π / 2) k n : ℂ) =
      (π / 2 : ℂ) *
        (-(n : ℂ) * carlsonRL ((1 - k ^ 2 : ℝ) : ℂ) 1 ((1 - n : ℝ) : ℂ) +
          2 * TwoVariable.carlsonRK ((1 - k ^ 2 : ℝ) : ℂ) 1) := by
  have hx : ((1 - k ^ 2 : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr (sub_pos.mpr hk)
  have hp : ((1 - n : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr (sub_pos.mpr hn)
  have H := carlsonR_complete_third_neg_half hx (y := 1) (by simp) hp
  rw [legendrePi_complete_eq hk hn]
  push_cast at H ⊢
  linear_combination (π / 2 : ℂ) * H

end Carlson
