/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.ReductionTables
public import Carlson.Elliptic.SchwarzChristoffel
public import Carlson.Elliptic.CompleteK
public import Carlson.Elliptic.Addition

/-!
# Legendre's integrals and the symmetric standard functions

Legendre's integrals `F`, `E`, `Π` and the symmetric standard functions `R_F`, `R_G`, `R_H`,
`R_K`, `R_E` of §9.2 are related by the reduction tables of §9.3 and homogeneity. This file
proves the relations of §9.2 and Example 9.3-1 for real arguments.

## Main results

* `Carlson.legendreEc_eq`: (9.2-14), `E(k) = (π/2) R_E(1 - k², 1)`.
* `Carlson.sin_mul_legendreE_eq`: Example 9.3-1, equation (3), `E(φ, k)` in the symmetric
  standard functions.
* `Carlson.legendreF_arccos_eq`, `Carlson.carlsonRG_eq_legendre`: (9.2-12) and (9.2-13).
* `Carlson.carlsonRK_eq_legendreK`, `Carlson.carlsonRE_eq_legendreEc`: (9.2-15).
* `Carlson.carlsonRH_eq_legendrePi`: Exercise 9.3-1.
* `Carlson.carlsonR_smul_of_pos`, `Carlson.carlsonRG_mul_of_pos`: homogeneity.
* `Carlson.legendreF_inv`, `Carlson.legendreE_inv`: Exercise 9.2-2, the reciprocal-modulus
  transformation, using `Carlson.legendreF_eq_of_mul_lt` and `Carlson.legendreE_eq_of_mul_lt`
  (Legendre's integrals as `R` functions whenever `k² sin² φ < 1`).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§9.2–9.3.
-/

open Complex MeasureTheory Set
open scoped Real

@[expose] public noncomputable section

namespace Carlson

open TwoVariable (pair carlsonRK)

/-- `∫₀¹ (1 - t²)^{-1/2} (1 - k² t²)^{1/2} dt = (π/2) R_{-1/2}(-1/2, 3/2; 1 - k², 1)`. -/
private theorem integral_Ioo_sn_second_complete {k : ℝ} (hk : k ^ 2 < 1) :
    ((∫ t in Ioo (0 : ℝ) 1, (1 - t ^ 2) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ) : ℝ) :
        ℂ) =
      π / 2 * regCarlsonR (-1 / 2) ![-1 / 2, 3 / 2] ![((1 - k ^ 2 : ℝ) : ℂ), 1] := by
  set g : ℝ → ℝ := fun t => (1 - t ^ 2) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ)
  set φ : ℝ → ℝ := fun s => Real.sqrt s
  set N : Fin 2 → ℂ := ![((1 - k ^ 2 : ℝ) : ℂ), 1]
  set B : Fin 2 → ℂ := ![-1 / 2, 3 / 2]
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt φ (1 / (2 * Real.sqrt s))
      (Ioo 0 1) s := fun s hs => (Real.hasDerivAt_sqrt hs.1.ne').hasDerivWithinAt
  have hinj : InjOn φ (Ioo 0 1) := fun a ha b hb hab => (Real.sqrt_inj ha.1.le hb.1.le).mp hab
  have himg : φ '' Ioo 0 1 = Ioo 0 1 := by
    ext t; constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Real.sqrt_pos.mpr hs.1, by rw [Real.sqrt_lt' one_pos]; simpa using hs.2⟩
    · rintro ⟨ht0, ht1⟩
      exact ⟨t ^ 2, ⟨by positivity, by nlinarith⟩, Real.sqrt_sq ht0.le⟩
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  rw [himg] at hsub
  rw [hsub]
  have hz : N ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr (by linarith)
    · simp [N]
  have h := carlsonRUnitIntervalIntegral_eq_Gamma_mul_regCarlsonR (a := 1 / 2) (a' := 1 / 2)
    (b := B) (by norm_num) (by norm_num) (by simp [B]; norm_num) hz
  unfold carlsonRUnitIntervalIntegral at h
  rw [← integral_complex_ofReal]
  have hpt : ∀ s ∈ Ioo (0 : ℝ) 1, ((|1 / (2 * Real.sqrt s)| • g (φ s) : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ((s : ℂ) ^ ((1 / 2 : ℂ) - 1) * (1 - s : ℂ) ^ ((1 / 2 : ℂ) - 1) *
        ∏ i, ((1 - s : ℂ) + (s : ℂ) * N i) ^ (-B i)) := by
    intro s hs
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.1.le
    have h1 : 0 < 1 - s := by linarith [hs.2]
    have h2 : 0 < 1 - k ^ 2 * s := by nlinarith [hs.1, hs.2, sq_nonneg k]
    have hg : g (φ s) = (1 - s) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * s) ^ (1 / 2 : ℝ) := by
      simp only [g, φ, hsq]
    have habs : |1 / (2 * Real.sqrt s)| = 1 / 2 * s ^ (-1 / 2 : ℝ) := by
      rw [abs_of_pos (by have := Real.sqrt_pos.mpr hs.1; positivity),
        show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow]
      ring
    rw [hg, habs, smul_eq_mul, ofReal_mul, ofReal_mul, ofReal_mul, ofReal_cpow hs.1.le,
      ofReal_cpow h1.le, ofReal_cpow h2.le]
    simp only [N, B, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    push_cast
    rw [show (1 : ℂ) - s + s * 1 = 1 by ring, one_cpow, mul_one,
      show (1 : ℂ) - s + s * (1 - k ^ 2) = 1 - k ^ 2 * s by ring]
    norm_num
    ring_nf
  have hG : Gamma (1 / 2 : ℂ) * Gamma (1 / 2) = π := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal,
      Real.Gamma_one_half_eq, ← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul, h, hG]
  simp only [N, B]
  ring_nf

/-- **Carlson's (9.2-14), second kind**: for `k² < 1`, the complete integral
`E(k) = (π/2) R_E(1 - k², 1)`. -/
theorem legendreEc_eq {k : ℝ} (hk : k ^ 2 < 1) :
    (legendreEc k : ℂ) = π / 2 * carlsonRE ((1 - k ^ 2 : ℝ) : ℂ) 1 := by
  have h := integral_legendre_eq (by positivity : (0 : ℝ) < π / 2) le_rfl
    (fun t => (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ))
  rw [Real.sin_pi_div_two] at h
  have hrow := carlsonR_table_9_3_2_row1 (x := ((1 - k ^ 2 : ℝ) : ℂ)) (y := 1)
    (ofReal_mem_slitPlane.mpr (by linarith)) one_mem_slitPlane
  unfold carlsonR at hrow
  rw [show (∑ i, (![-1 / 2, 3 / 2] : Fin 2 → ℂ) i) = 1 by simp; norm_num, Gamma_one] at hrow
  unfold legendreEc legendreE
  rw [h, integral_Ioo_sn_second_complete hk]
  linear_combination (π / 2 : ℂ) * hrow

/-- Homogeneity of the unregularized `R`-function under a positive real factor. -/
theorem carlsonR_smul_of_pos {ι : Type*} [Fintype ι] (t : ℂ) (b : ι → ℂ) {l : ℝ} (hl : 0 < l)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    carlsonR t b (fun i => (l : ℂ) * z i) = (l : ℂ) ^ t * carlsonR t b z := by
  unfold carlsonR
  rw [regCarlsonR_smul_of_pos t b hl hz]
  ring

/-- `R_G(l x, l y, l z) = l^{1/2} R_G(x, y, z)` for `l > 0`. -/
theorem carlsonRG_mul_of_pos {l : ℝ} (hl : 0 < l) {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    carlsonRG (l * x) (l * y) (l * z) = (l : ℂ) ^ (1 / 2 : ℂ) * carlsonRG x y z := by
  have hs : (![x, y, z] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  unfold carlsonRG
  rw [← carlsonR_smul_of_pos _ _ hl hs]
  congr 1
  funext i; fin_cases i <;> rfl

/-- `(r : ℂ) * r^{-1/2} = √r` for real `r > 0`. -/
private theorem ofReal_mul_cpow_neg_half {r : ℝ} (hr : 0 < r) :
    (r : ℂ) * (r : ℂ) ^ (-1 / 2 : ℂ) = (Real.sqrt r : ℂ) := by
  rw [ofReal_cpow_neg_half hr, ← ofReal_mul]
  congr 1
  rw [← Real.sqrt_sq hr.le, Real.sqrt_sq hr.le]
  field_simp
  rw [Real.sq_sqrt hr.le]

/-- **Carlson's Example 9.3-1**, equation (3): for `0 < φ < π/2` and `k² < 1`,
`sin φ E(φ, k) = 2 R_G(1 - k² sin² φ, cos² φ, 1) - cos² φ R_F(1 - k² sin² φ, cos² φ, 1)
- cos φ (1 - k² sin² φ)^{1/2}`. -/
theorem sin_mul_legendreE_eq {φ k : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) (hk : k ^ 2 < 1) :
    (Real.sin φ : ℂ) * legendreE φ k =
      2 * carlsonRG ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) ((Real.cos φ ^ 2 : ℝ) : ℂ) 1 -
        ((Real.cos φ ^ 2 : ℝ) : ℂ) *
          carlsonRF ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) ((Real.cos φ ^ 2 : ℝ) : ℂ) 1 -
        (Real.cos φ : ℂ) * (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) : ℂ) := by
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have hsc := Real.sin_sq_add_cos_sq φ
  have hX : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := by
    have := Real.sin_sq_le_one φ
    nlinarith [sq_nonneg k, sq_nonneg (Real.sin φ)]
  have hY : 0 < Real.cos φ ^ 2 := by positivity
  have hrow := carlsonR_table_9_3_1_row1 (ofReal_mem_slitPlane.mpr hX)
    (ofReal_mem_slitPlane.mpr hY) one_mem_slitPlane
  rw [legendreE_eq h0 h1 hk]
  have hQX := ofReal_mul_cpow_neg_half hX
  have hQY := ofReal_mul_cpow_neg_half hY
  rw [Real.sqrt_sq hc.le] at hQY
  rw [one_cpow, mul_one] at hrow
  have hs2 : (Real.sin φ : ℂ) ^ 2 = 1 - ((Real.cos φ ^ 2 : ℝ) : ℂ) := by
    have : Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 := by linarith
    exact_mod_cast this
  set RT := carlsonR (-1 / 2) ![-1 / 2, 1 / 2, 3 / 2]
    ![((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ), ((Real.cos φ ^ 2 : ℝ) : ℂ), 1]
  linear_combination hrow + RT * hs2 -
    (((Real.cos φ ^ 2 : ℝ) : ℂ) * ((Real.cos φ ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ)) * hQX -
    (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) : ℂ) * hQY

/-- The amplitude and modulus attached to real nodes `0 < x < y < z`:
`φ = arccos √(x/z)`, `k = √((z - y)/(z - x))`, with `cos² φ = x/z`, `sin φ = √((z - x)/z)` and
`1 - k² sin² φ = y/z`. -/
private theorem arccos_facts {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    let φ := Real.arccos (Real.sqrt (x / z))
    let k := Real.sqrt ((z - y) / (z - x))
    0 < φ ∧ φ < π / 2 ∧ k ^ 2 < 1 ∧ Real.cos φ ^ 2 = x / z ∧ Real.cos φ = Real.sqrt (x / z) ∧
      Real.sin φ = Real.sqrt (z - x) / Real.sqrt z ∧ 1 - k ^ 2 * Real.sin φ ^ 2 = y / z := by
  intro φ k
  have hz : 0 < z := by linarith
  have hxz : x / z < 1 := (div_lt_one hz).mpr (by linarith)
  have hc0 : 0 < Real.sqrt (x / z) := Real.sqrt_pos.mpr (by positivity)
  have hc1 : Real.sqrt (x / z) < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using hxz
  have hcos : Real.cos φ = Real.sqrt (x / z) := Real.cos_arccos (by linarith) hc1.le
  have hcos2 : Real.cos φ ^ 2 = x / z := by rw [hcos, Real.sq_sqrt (by positivity)]
  have hsin : Real.sin φ = Real.sqrt (z - x) / Real.sqrt z := by
    simp only [φ]
    rw [Real.sin_arccos, Real.sq_sqrt (by positivity), ← Real.sqrt_div' _ hz.le]
    congr 1; field_simp
  have hk2 : k ^ 2 = (z - y) / (z - x) := Real.sq_sqrt (div_nonneg (by linarith) (by linarith))
  refine ⟨Real.arccos_pos.mpr hc1, Real.arccos_lt_pi_div_two.mpr hc0, ?_, hcos2, hcos, hsin, ?_⟩
  · rw [hk2, div_lt_one (by linarith)]; linarith
  · have hzx : z - x ≠ 0 := by linarith
    rw [hk2, hsin, div_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hz.le]
    field_simp
    ring

/-- `R_F(x/z, y/z, 1) = √z R_F(x, y, z)` and the like: homogeneity with `l = 1/z`. -/
private theorem carlsonRF_div {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    carlsonRF ((x / z : ℝ) : ℂ) ((y / z : ℝ) : ℂ) 1 = Real.sqrt z * carlsonRF x y z := by
  have h := carlsonRF_mul_of_pos (inv_pos.mpr hz) (ofReal_mem_slitPlane.mpr hx)
    (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz)
  rw [ofReal_cpow_neg_half (inv_pos.mpr hz), Real.sqrt_inv, inv_inv] at h
  have hz0 : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
  rw [← h]
  push_cast
  congr 1 <;> field_simp

/-- `R_G(y/z, x/z, 1) = R_G(x, y, z)/√z`. -/
private theorem carlsonRG_div {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    carlsonRG ((y / z : ℝ) : ℂ) ((x / z : ℝ) : ℂ) 1 = (Real.sqrt z : ℂ)⁻¹ * carlsonRG x y z := by
  have h := carlsonRG_mul_of_pos (inv_pos.mpr hz) (ofReal_mem_slitPlane.mpr hy)
    (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hz)
  have hp : ((z⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt z : ℂ)⁻¹ := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_inv, ofReal_inv]
  rw [hp, carlsonRG_comm_left (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
    (ofReal_mem_slitPlane.mpr hz)] at h
  have hz0 : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
  rw [← h]
  push_cast
  congr 1 <;> field_simp

/-- **Carlson's (9.2-12)**: for real `0 < x < y < z`,
`F(arccos √(x/z), √((z - y)/(z - x))) = (z - x)^{1/2} R_F(x, y, z)`. -/
theorem legendreF_arccos_eq {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    (legendreF (Real.arccos (Real.sqrt (x / z))) (Real.sqrt ((z - y) / (z - x))) : ℂ) =
      Real.sqrt (z - x) * carlsonRF x y z := by
  obtain ⟨h0, h1, hk, hc2, -, hs, hX⟩ := arccos_facts hx hxy hyz
  have hz : 0 < z := by linarith
  rw [legendreF_eq h0 h1 hk, hc2, hX, carlsonRF_div hx (by linarith) hz, hs]
  have : (Real.sqrt z : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hz).ne'
  push_cast
  field_simp

/-- **Carlson's (9.2-13)**: for real `0 < x < y < z`, with `φ = arccos √(x/z)` and
`k = √((z - y)/(z - x))`,
`R_G(x, y, z) = (1/2)(z - x)^{1/2} E(φ, k) + (1/2) x (z - x)^{-1/2} F(φ, k) + (1/2)(xy/z)^{1/2}`. -/
theorem carlsonRG_eq_legendre {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    carlsonRG x y z =
      1 / 2 * Real.sqrt (z - x) *
          legendreE (Real.arccos (Real.sqrt (x / z))) (Real.sqrt ((z - y) / (z - x))) +
        1 / 2 * x / Real.sqrt (z - x) *
          legendreF (Real.arccos (Real.sqrt (x / z))) (Real.sqrt ((z - y) / (z - x))) +
        1 / 2 * Real.sqrt (x * y / z) := by
  obtain ⟨h0, h1, hk, hc2, hc, hs, hX⟩ := arccos_facts hx hxy hyz
  have hz : 0 < z := by linarith
  have hy : 0 < y := by linarith
  have hE := sin_mul_legendreE_eq h0 h1 hk
  rw [hX, hc2, hc, carlsonRG_div hx hy hz, carlsonRF_comm_left
    (ofReal_mem_slitPlane.mpr (div_pos hx hz))
    (ofReal_mem_slitPlane.mpr (div_pos hy hz)) one_mem_slitPlane,
    carlsonRF_div hx hy hz, hs] at hE
  rw [legendreF_arccos_eq hx hxy hyz]
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
  have hszx : 0 < Real.sqrt (z - x) := Real.sqrt_pos.mpr (by linarith)
  have e1 : Real.sqrt (x / z) * Real.sqrt (y / z) = Real.sqrt (x * y / z) / Real.sqrt z := by
    rw [← Real.sqrt_mul (by positivity), show x / z * (y / z) = x * y / z / z by ring,
      Real.sqrt_div' _ hz.le]
  have e2 : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz.le
  have hszC : (Real.sqrt z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsz.ne'
  have hszxC : (Real.sqrt (z - x) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hszx.ne'
  have hz0 : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
  have e1C : (Real.sqrt (x / z) : ℂ) * (Real.sqrt (y / z) : ℂ) =
      (Real.sqrt (x * y / z) : ℂ) / Real.sqrt z := by exact_mod_cast e1
  have e2C : (Real.sqrt z : ℂ) ^ 2 = z := by exact_mod_cast e2
  rw [e1C] at hE
  push_cast at hE ⊢
  linear_combination (norm := skip) (-(Real.sqrt z : ℂ) / 2) * hE +
    ((x : ℂ) * carlsonRF x y z / (2 * z)) * e2C
  field_simp
  ring

/-- **Carlson's (9.2-15)**, first kind: for real `0 < x ≤ y`,
`R_K(x, y) = (2/π) y^{-1/2} K((1 - x/y)^{1/2})`. -/
theorem carlsonRK_eq_legendreK {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    carlsonRK x y = 2 / π * (Real.sqrt y : ℂ)⁻¹ * legendreK (Real.sqrt (1 - x / y)) := by
  have hy : 0 < y := hx.trans_le hxy
  have h1 : 0 ≤ 1 - x / y := by rw [sub_nonneg, div_le_one hy]; exact hxy
  have hk : Real.sqrt (1 - x / y) ^ 2 < 1 := by
    rw [Real.sq_sqrt h1]; have := div_pos hx hy; linarith
  rw [legendreK_eq hk, Real.sq_sqrt h1, show 1 - (1 - x / y) = x / y by ring]
  have h := carlsonRK_mul_of_pos (inv_pos.mpr hy) (ofReal_mem_slitPlane.mpr hx)
    (ofReal_mem_slitPlane.mpr hy)
  rw [ofReal_cpow_neg_half (inv_pos.mpr hy), Real.sqrt_inv, inv_inv] at h
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hsy : (Real.sqrt y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have e : carlsonRK ((x / y : ℝ) : ℂ) 1 = Real.sqrt y * carlsonRK x y := by
    rw [← h]; push_cast; congr 1 <;> field_simp
  rw [e]
  field_simp

/-- **Carlson's (9.2-15)**, second kind: for real `0 < x ≤ y`,
`R_E(x, y) = (2/π) y^{1/2} E((1 - x/y)^{1/2})`. -/
theorem carlsonRE_eq_legendreEc {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    carlsonRE x y = 2 / π * (Real.sqrt y : ℂ) * legendreEc (Real.sqrt (1 - x / y)) := by
  have hy : 0 < y := hx.trans_le hxy
  have h1 : 0 ≤ 1 - x / y := by rw [sub_nonneg, div_le_one hy]; exact hxy
  have hk : Real.sqrt (1 - x / y) ^ 2 < 1 := by
    rw [Real.sq_sqrt h1]; have := div_pos hx hy; linarith
  rw [legendreEc_eq hk, Real.sq_sqrt h1, show 1 - (1 - x / y) = x / y by ring]
  have hs : pair (x : ℂ) y ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr hx
    · exact ofReal_mem_slitPlane.mpr hy
  have h := carlsonR_smul_of_pos (1 / 2) (pair (1 / 2) (1 / 2)) (inv_pos.mpr hy) hs
  have hp : ((y⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt y : ℂ)⁻¹ := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_inv, ofReal_inv]
  rw [hp] at h
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hsy : (Real.sqrt y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have e : carlsonRE ((x / y : ℝ) : ℂ) 1 = (Real.sqrt y : ℂ)⁻¹ * carlsonRE x y := by
    unfold carlsonRE
    rw [← h]
    congr 1
    funext i; fin_cases i <;> simp [pair] <;> field_simp
  rw [e]
  field_simp

/-- **Exercise 9.3-1**: for real `0 < x < y < z` and `ρ > 0` with `ρ ≠ z`, with
`φ = arccos √(x/z)`, `k = √((z - y)/(z - x))` and `α² = (z - ρ)/(z - x)`,
`R_H(x, y, z, ρ) = (3/2) (z - x)^{-1/2} (ρ - z)⁻¹ [ρ Π(φ, k, α²) - z F(φ, k)]`. -/
theorem carlsonRH_eq_legendrePi {x y z ρ : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hρ : 0 < ρ) (hρz : ρ ≠ z) :
    carlsonRH x y z ρ =
      3 / 2 * (Real.sqrt (z - x) : ℂ)⁻¹ * ((ρ : ℂ) - z)⁻¹ *
        (ρ * legendrePi (Real.arccos (Real.sqrt (x / z))) (Real.sqrt ((z - y) / (z - x)))
            ((z - ρ) / (z - x)) -
          z * legendreF (Real.arccos (Real.sqrt (x / z))) (Real.sqrt ((z - y) / (z - x)))) := by
  obtain ⟨h0, h1, hk, hc2, -, hs, hX⟩ := arccos_facts hx hxy hyz
  have hz : 0 < z := by linarith
  have hy : 0 < y := by linarith
  have hsin2 : Real.sin (Real.arccos (Real.sqrt (x / z))) ^ 2 = (z - x) / z := by
    rw [hs, div_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hz.le]
  have hn : (z - ρ) / (z - x) * Real.sin (Real.arccos (Real.sqrt (x / z))) ^ 2 < 1 := by
    rw [hsin2, show (z - ρ) / (z - x) * ((z - x) / z) = (z - ρ) / z by
      field_simp [show z - x ≠ 0 by linarith]]
    rw [div_lt_one hz]; linarith
  have hP := legendrePi_eq h0 h1 hk hn
  have hR : 1 - (z - ρ) / (z - x) * Real.sin (Real.arccos (Real.sqrt (x / z))) ^ 2 = ρ / z := by
    rw [hsin2]; field_simp [show z - x ≠ 0 by linarith]; ring
  rw [hX, hc2, hR, hs] at hP
  -- homogeneity of the four-variable function
  have hs4 : (![(y : ℂ), x, z, ρ] : Fin 4 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr hy
    · exact ofReal_mem_slitPlane.mpr hx
    · exact ofReal_mem_slitPlane.mpr hz
    · exact ofReal_mem_slitPlane.mpr hρ
  have hh := carlsonR_smul_of_pos (-1 / 2) ![1 / 2, 1 / 2, -1 / 2, 1] (inv_pos.mpr hz) hs4
  rw [ofReal_cpow_neg_half (inv_pos.mpr hz), Real.sqrt_inv, inv_inv] at hh
  have hz0 : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
  have e : carlsonR (-1 / 2) ![1 / 2, 1 / 2, -1 / 2, 1]
      ![((y / z : ℝ) : ℂ), ((x / z : ℝ) : ℂ), 1, ((ρ / z : ℝ) : ℂ)] =
      Real.sqrt z * carlsonR (-1 / 2) ![1 / 2, 1 / 2, -1 / 2, 1] ![(y : ℂ), x, z, ρ] := by
    rw [← hh]; congr 1; funext i; fin_cases i <;> simp <;> field_simp
  rw [e] at hP
  have h3 := carlsonR_third_neg_half (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hx)
    (ofReal_mem_slitPlane.mpr hz) (ofReal_mem_slitPlane.mpr hρ)
  rw [carlsonRH_comm_left (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
      (ofReal_mem_slitPlane.mpr hz) (ofReal_mem_slitPlane.mpr hρ),
    carlsonRF_comm_left (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
      (ofReal_mem_slitPlane.mpr hz)] at h3
  rw [legendreF_arccos_eq hx hxy hyz, hP]
  have hszx : (Real.sqrt (z - x) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by linarith)).ne'
  have hsz : (Real.sqrt z : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hz).ne'
  have hρz' : (ρ : ℂ) - z ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hρz)
  push_cast
  field_simp
  rw [show (-(1 / 2) : ℂ) = -1 / 2 by norm_num]
  linear_combination -h3

/-! ### The reciprocal-modulus transformation (Exercise 9.2-2) -/

/-- **Exercise 9.2-2**, first kind: if `0 < φ, φ₁ < π/2`, `k > 0` and `sin φ₁ = k sin φ`, then
`F(φ₁, 1/k) = k F(φ, k)`. -/
theorem legendreF_inv {φ φ₁ k : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) (h0' : 0 < φ₁)
    (h1' : φ₁ < π / 2) (hk : 0 < k) (hs : Real.sin φ₁ = k * Real.sin φ) :
    legendreF φ₁ k⁻¹ = k * legendreF φ k := by
  have hs1 : Real.sin φ₁ < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl h1'
  have hsp : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hsp1 : 0 < Real.sin φ₁ := by rw [hs]; positivity
  have hkφ : k ^ 2 * Real.sin φ ^ 2 < 1 := by
    rw [← mul_pow, ← hs]; nlinarith
  have hkφ₁ : k⁻¹ ^ 2 * Real.sin φ₁ ^ 2 < 1 := by
    rw [hs, ← mul_pow, ← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
    have hs1' : Real.sin φ < 1 := by
      rw [← Real.sin_pi_div_two]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl h1
    nlinarith
  have F1 := legendreF_eq_of_mul_lt h0' h1' hkφ₁
  have F0 := legendreF_eq_of_mul_lt h0 h1 hkφ
  have ec : Real.cos φ₁ ^ 2 = 1 - k ^ 2 * Real.sin φ ^ 2 := by
    rw [Real.cos_sq', hs]; ring
  have eΔ : 1 - k⁻¹ ^ 2 * Real.sin φ₁ ^ 2 = Real.cos φ ^ 2 := by
    rw [hs, Real.cos_sq']; field_simp
  rw [ec, eΔ, hs, carlsonRF_comm_left (ofReal_mem_slitPlane.2 (by nlinarith))
    (ofReal_mem_slitPlane.2 (by nlinarith [Real.cos_sq_add_sin_sq φ])) one_mem_slitPlane] at F1
  apply ofReal_injective
  rw [F1]
  simp only [ofReal_mul]
  rw [F0]
  ring

/-- **Exercise 9.2-2**, second kind: if `0 < φ, φ₁ < π/2`, `k > 0` and `sin φ₁ = k sin φ`, then
`k E(φ₁, 1/k) = E(φ, k) + (k² - 1) F(φ, k)`. -/
theorem legendreE_inv {φ φ₁ k : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) (h0' : 0 < φ₁)
    (h1' : φ₁ < π / 2) (hk : 0 < k) (hs : Real.sin φ₁ = k * Real.sin φ) :
    k * legendreE φ₁ k⁻¹ = legendreE φ k + (k ^ 2 - 1) * legendreF φ k := by
  have hs1 : Real.sin φ₁ < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl h1'
  have hs1' : Real.sin φ < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl h1
  have hsp : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hsp1 : 0 < Real.sin φ₁ := by rw [hs]; positivity
  have hkφ : k ^ 2 * Real.sin φ ^ 2 < 1 := by
    rw [← mul_pow, ← hs]; nlinarith
  have hkφ₁ : k⁻¹ ^ 2 * Real.sin φ₁ ^ 2 < 1 := by
    rw [hs, ← mul_pow, ← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]; nlinarith
  have E1 := legendreE_eq_of_mul_lt h0' h1' hkφ₁
  have E0 := legendreE_eq_of_mul_lt h0 h1 hkφ
  have F0 := legendreF_eq_of_mul_lt h0 h1 hkφ
  set c := Real.cos φ ^ 2
  set Δ := 1 - k ^ 2 * Real.sin φ ^ 2
  have hc : 0 < c := by
    have := Real.cos_sq_add_sin_sq φ; simp only [c]; nlinarith
  have hΔ : 0 < Δ := by simp only [Δ]; linarith
  have ec : Real.cos φ₁ ^ 2 = Δ := by rw [Real.cos_sq', hs]; ring
  have eΔ : 1 - k⁻¹ ^ 2 * Real.sin φ₁ ^ 2 = c := by
    rw [hs]; simp only [c, Real.cos_sq']; field_simp
  rw [ec, eΔ, hs] at E1
  have mc : (c : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hc
  have mΔ : (Δ : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hΔ
  have T1 := carlsonR_table_9_3_1_row1 mc mΔ one_mem_slitPlane
  have T2 := carlsonR_table_9_3_1_row1 mΔ mc one_mem_slitPlane
  rw [carlsonRG_comm_left mc mΔ one_mem_slitPlane, carlsonRF_comm_left mc mΔ one_mem_slitPlane]
    at T2
  have ecc : (c : ℂ) = 1 - (Real.sin φ : ℂ) ^ 2 := by
    simp only [c, Real.cos_sq']; push_cast; ring
  have eΔΔ : (Δ : ℂ) = 1 - (k : ℂ) ^ 2 * (Real.sin φ : ℂ) ^ 2 := by simp only [Δ]; push_cast; ring
  set R1 := carlsonR (-1 / 2) ![-1 / 2, 1 / 2, 3 / 2] ![(c : ℂ), (Δ : ℂ), 1]
  set R0 := carlsonR (-1 / 2) ![-1 / 2, 1 / 2, 3 / 2] ![(Δ : ℂ), (c : ℂ), 1]
  set RF := carlsonRF (c : ℂ) (Δ : ℂ) 1
  have hkey : (Real.sin φ : ℂ) ^ 2 * ((k : ℂ) ^ 2 * R1 - R0 - ((k : ℂ) ^ 2 - 1) * RF) = 0 := by
    linear_combination T1 - T2 + (R1 - RF) * eΔΔ - (R0 - RF) * ecc
  have hs0 : (Real.sin φ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (ofReal_ne_zero.2 hsp.ne')
  have hkey' := (mul_eq_zero.1 hkey).resolve_left hs0
  apply ofReal_injective
  simp only [ofReal_mul, ofReal_add, ofReal_sub, ofReal_pow, ofReal_one]
  rw [E1, E0, F0]
  simp only [ofReal_mul]
  linear_combination (Real.sin φ : ℂ) * hkey'

end Carlson
