/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Mapping

/-!
# Elliptic functions by inversion (Carlson's Examples 8.2-2 and 8.2-3)

Theorem 8.2-1 applies to the two classical elliptic cases.

**Weierstrass** (Example 8.2-2). For real `x₁ > x₂ > x₃`, the map
`u(z) = R_F(z - x₁, z - x₂, z - x₃)` is one-to-one from the upper half-plane onto the open
rectangle with vertices `0`, `u(x₃) = -i K₃`, `u(x₂) = K₁ - i K₃`, `u(x₁) = K₁`. Here
`K₁ = (π/2) R_K(x₁ - x₂, x₁ - x₃)` and `K₃ = (π/2) R_K(x₁ - x₃, x₂ - x₃)` are the half-periods
(8.2-8), (8.2-9). The inverse `z(u)` is holomorphic on the rectangle and satisfies Carlson's
differential equations (8.2-11), (8.2-12): `dz/du = -2 ∏ (z - xᵢ)^{1/2}` and
`(dz/du)² = 4 (z - x₁)(z - x₂)(z - x₃)`.

**Jacobi** (Example 8.2-3). For `0 < k < 1`, Carlson's
`v(y) = ∫₀^y ((1 - t²)(1 - k² t²))^{-1/2} dt` is a Schwarz–Christoffel map with nodes
`±1, ±1/k`. It maps the upper half-plane one-to-one onto the open rectangle
`-K < re v < K`, `0 < im v < K'`, where `2K = π R_K(1 - k², 1)` (8.2-20) and
`K' = (π/2) R_K(k², 1)` (8.2-21). The inverse `sn` is holomorphic on the rectangle and satisfies
`(sn')² = (1 - sn²)(1 - k² sn²)`. On `0 < y < 1`, `v(y) = y R_F(1 - y², 1 - k² y², 1)` (8.2-18).

The continuation of the inverse functions to doubly periodic meromorphic functions on `ℂ` by
repeated Schwarz reflection is not formalized here.

## Main results

* `Carlson.bijOn_carlsonRF_sub`, `Carlson.scPolygon_weierstrass`: Example 8.2-2.
* `Carlson.hasDerivAt_weierstrassInv`, `Carlson.sq_deriv_weierstrassInv`: (8.2-11), (8.2-12).
* `Carlson.bijOn_snV`, `Carlson.snV_ofReal`: Example 8.2-3.
* `Carlson.hasDerivAt_jacobiSn`, `Carlson.sq_deriv_jacobiSn`: the differential equation of `sn`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.2.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology
@[expose] public noncomputable section

namespace Carlson

/-- `im (e^{iθ} w) = cos θ im w + sin θ re w`. -/
theorem im_exp_mul_I_mul (θ : ℝ) (w : ℂ) :
    (exp (θ * I) * w).im = Real.cos θ * w.im + Real.sin θ * w.re := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [mul_im, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, add_im, mul_im, zero_add]

theorem im_exp_neg_mul_I_mul (θ : ℝ) (w : ℂ) :
    (exp (-(θ : ℂ) * I) * w).im = Real.cos θ * w.im - Real.sin θ * w.re := by
  rw [show -(θ : ℂ) = ((-θ : ℝ) : ℂ) by push_cast; ring, im_exp_mul_I_mul, Real.cos_neg,
    Real.sin_neg]
  ring

/-- The derivative of the inverse of a Schwarz–Christoffel map with all `bᵢ = 1/2`. -/
theorem inv_neg_mul_prod_cpow_neg_half {ι : Type*} [Fintype ι] (a : ℂ) (w : ι → ℂ) :
    (-a * ∏ i, w i ^ (-((1 / 2 : ℝ) : ℂ)))⁻¹ = -a⁻¹ * ∏ i, w i ^ (1 / 2 : ℂ) := by
  rw [mul_inv, neg_inv, ← Finset.prod_inv_distrib]
  congr 2
  funext i
  rw [cpow_neg, inv_inv]
  norm_num

theorem sq_prod_cpow_half {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    (∏ i, w i ^ (1 / 2 : ℂ)) ^ 2 = ∏ i, w i := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [one_div]
  exact cpow_nat_inv_pow _ two_ne_zero

/-! ### The Weierstrass case -/

section Weierstrass

variable {x₁ x₂ x₃ : ℝ}

/-- The nodes `x₁, x₂, x₃` of Carlson's Example 8.2-2. -/
def weierstrassNodes (x₁ x₂ x₃ : ℝ) : Fin 3 → ℝ := ![x₁, x₂, x₃]

theorem weierstrassParams (h₂₁ : x₂ < x₁) (h₃₂ : x₃ < x₂) :
    SchwarzChristoffelParams (1 / 2) (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) where
  injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [weierstrassNodes] at hij ⊢ <;> linarith
  pos := fun _ => by norm_num
  lt_one := fun _ => by norm_num
  a_pos := by norm_num
  sum_eq := by simp; norm_num

/-- `R_F(z - x₁, z - x₂, z - x₃)` is the Schwarz–Christoffel map of Example 8.2-2. -/
theorem carlsonRF_sub_eq_scMap (h₂₁ : x₂ < x₁) (h₃₂ : x₃ < x₂) {z : ℂ} (hz : 0 < z.im) :
    carlsonRF (z - x₁) (z - x₂) (z - x₃) =
      scMap (1 / 2) (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) z := by
  rw [scMap_eq_carlsonR (weierstrassParams h₂₁ h₃₂) hz, carlsonRF]
  congr 1
  · push_cast; ring
  · funext i; push_cast; ring
  · funext i; fin_cases i <;> simp [weierstrassNodes]

private theorem scAngle_weierstrass (σ : ℝ) :
    scAngle (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) σ =
      π * (1 - ((if σ < x₁ then 1 / 2 else 0) + (if σ < x₂ then 1 / 2 else 0) +
        (if σ < x₃ then 1 / 2 else 0))) := by
  unfold scAngle
  rw [Finset.sum_filter, Fin.sum_univ_three]
  simp [weierstrassNodes]

/-- The real half-period `K₁ = (1/2) ∫_{x₁}^∞ ((t - x₁)(t - x₂)(t - x₃))^{-1/2} dt`. -/
def weierstrassK₁ (x₁ x₂ x₃ : ℝ) : ℝ :=
  1 / 2 * ∫ t in Ioi x₁, ((t - x₁) * (t - x₂) * (t - x₃)) ^ (-1 / 2 : ℝ)

/-- The imaginary half-period `K₃ = (1/2) ∫_{-∞}^{x₃} ((x₁ - t)(x₂ - t)(x₃ - t))^{-1/2} dt`. -/
def weierstrassK₃ (x₁ x₂ x₃ : ℝ) : ℝ :=
  1 / 2 * ∫ t in Iio x₃, ((x₁ - t) * (x₂ - t) * (x₃ - t)) ^ (-1 / 2 : ℝ)

theorem weierstrassK₁_eq (h₂₁ : x₂ < x₁) (h₃₂ : x₃ < x₂) :
    (weierstrassK₁ x₁ x₂ x₃ : ℂ) = π / 2 * TwoVariable.carlsonRK (x₁ - x₂ : ℝ) (x₁ - x₃ : ℝ) :=
  half_integral_Ioi_rsqrt_cubic h₂₁ (by linarith)

theorem weierstrassK₃_eq (h₂₁ : x₂ < x₁) (h₃₂ : x₃ < x₂) :
    (weierstrassK₃ x₁ x₂ x₃ : ℂ) = π / 2 * TwoVariable.carlsonRK (x₁ - x₃ : ℝ) (x₂ - x₃ : ℝ) :=
  half_integral_Iio_rsqrt_cubic (by linarith) h₃₂

private theorem scDensity_weierstrass (σ : ℝ) :
    scDensity (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) σ =
      (|σ - x₁| * |σ - x₂| * |σ - x₃|) ^ (-1 / 2 : ℝ) := by
  rw [scDensity, Fin.prod_univ_three, Real.mul_rpow (by positivity) (abs_nonneg _),
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  simp only [weierstrassNodes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

variable (h₂₁ : x₂ < x₁) (h₃₂ : x₃ < x₂)
include h₂₁ h₃₂

/-- The vertex `u(x₁) = K₁` (8.2-8). -/
theorem scMap_weierstrass_x₁ :
    scMap (1 / 2) (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) x₁ = weierstrassK₁ x₁ x₂ x₃ := by
  rw [scMap_of_scAngle_Ioi (c := π) fun σ hσ => by
    have hσ : x₁ < σ := hσ
    rw [scAngle_weierstrass]
    split_ifs <;> first | (exfalso; linarith) | ring]
  rw [exp_pi_mul_I, weierstrassK₁]
  have : ∫ σ in Ioi x₁, scDensity (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) σ =
      ∫ t in Ioi x₁, ((t - x₁) * (t - x₂) * (t - x₃)) ^ (-1 / 2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun σ hσ => ?_
    have hσ : x₁ < σ := hσ
    rw [scDensity_weierstrass, abs_of_pos (by linarith), abs_of_pos (by linarith),
      abs_of_pos (by linarith)]
  rw [this]
  push_cast
  ring

/-- The vertex `u(x₃) = -i K₃` (8.2-9). -/
theorem scMap_weierstrass_x₃ :
    scMap (1 / 2) (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) x₃ =
      -I * weierstrassK₃ x₁ x₂ x₃ := by
  rw [scMap_of_scAngle_Iio (weierstrassParams h₂₁ h₃₂) (c := -(π / 2)) fun σ hσ => by
    have hσ : σ < x₃ := hσ
    rw [scAngle_weierstrass]
    split_ifs <;> first | (exfalso; linarith) | ring]
  rw [show ((-(π / 2) : ℝ) : ℂ) * I = -(π / 2 * I) by push_cast; ring, exp_neg,
    exp_pi_div_two_mul_I, weierstrassK₃]
  have : ∫ σ in Iio x₃, scDensity (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) σ =
      ∫ t in Iio x₃, ((x₁ - t) * (x₂ - t) * (x₃ - t)) ^ (-1 / 2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Iio fun σ hσ => ?_
    have hσ : σ < x₃ := hσ
    rw [scDensity_weierstrass, abs_of_neg (by linarith), abs_of_neg (by linarith),
      abs_of_neg (by linarith)]
    ring_nf
  rw [this, inv_I]
  push_cast
  ring

theorem scMap_weierstrass_x₂_re :
    (scMap (1 / 2) (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) x₂).re =
      weierstrassK₁ x₁ x₂ x₃ := by
  have h := scMap_sub_of_scAngle (weierstrassParams h₂₁ h₃₂) (c := π / 2) h₂₁.le fun σ hσ => by
    have := hσ.1; have := hσ.2
    rw [scAngle_weierstrass]
    split_ifs <;> first | (exfalso; linarith) | ring
  push_cast at h
  rw [exp_pi_div_two_mul_I, scMap_weierstrass_x₁ h₂₁ h₃₂] at h
  have := congrArg re h
  simp at this
  linarith

theorem scMap_weierstrass_x₂_im :
    (scMap (1 / 2) (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) x₂).im =
      -weierstrassK₃ x₁ x₂ x₃ := by
  have h := scMap_sub_of_scAngle (weierstrassParams h₂₁ h₃₂) (c := 0) h₃₂.le fun σ hσ => by
    have := hσ.1; have := hσ.2
    rw [scAngle_weierstrass]
    split_ifs <;> first | (exfalso; linarith) | ring
  rw [ofReal_zero, zero_mul, exp_zero, scMap_weierstrass_x₃ h₂₁ h₃₂] at h
  have := congrArg im h
  simp at this
  linarith

/-- **The Weierstrass rectangle** (Carlson's Figure 8.2-1): the polygon of
`u(z) = R_F(z - x₁, z - x₂, z - x₃)` is the open rectangle `0 < re u < K₁`, `-K₃ < im u < 0`. -/
theorem scPolygon_weierstrass :
    scPolygon (1 / 2) (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) =
      {ζ | 0 < ζ.re ∧ ζ.re < weierstrassK₁ x₁ x₂ x₃ ∧ -weierstrassK₃ x₁ x₂ x₃ < ζ.im ∧
        ζ.im < 0} := by
  have hθ₁ : scAngle (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) x₁ = π := by
    rw [scAngle_weierstrass]
    split_ifs <;> first | (exfalso; linarith) | ring
  have hθ₂ : scAngle (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) x₂ = π / 2 := by
    rw [scAngle_weierstrass]
    split_ifs <;> first | (exfalso; linarith) | ring
  have hθ₃ : scAngle (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) x₃ = 0 := by
    rw [scAngle_weierstrass]
    split_ifs <;> first | (exfalso; linarith) | ring
  have hx₁ := scMap_weierstrass_x₁ h₂₁ h₃₂
  have hx₂r := scMap_weierstrass_x₂_re h₂₁ h₃₂
  have hx₂i := scMap_weierstrass_x₂_im h₂₁ h₃₂
  have hx₃ := scMap_weierstrass_x₃ h₂₁ h₃₂
  ext ζ
  simp only [scPolygon, Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, mem_ofPred_eq]
  simp only [weierstrassNodes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [im_exp_mul_I_mul, im_exp_neg_mul_I_mul, im_exp_neg_mul_I_mul, im_exp_neg_mul_I_mul]
  simp only [weierstrassNodes] at hθ₁ hθ₂ hθ₃ hx₁ hx₂r hx₂i hx₃
  rw [hθ₁, hθ₂, hθ₃, hx₁, show π * (1 / 2 : ℝ) = π / 2 by ring]
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, hx₂r, hx₂i, hx₃, mul_re, mul_im, neg_re,
    neg_im, I_re, I_im, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two,
    Real.cos_zero, Real.sin_zero]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- **Carlson's Example 8.2-2**: for real `x₁ > x₂ > x₃`, `u(z) = R_F(z - x₁, z - x₂, z - x₃)` maps
the open upper half-plane one-to-one onto the open rectangle `0 < re u < K₁`,
`-K₃ < im u < 0`. -/
theorem bijOn_carlsonRF_sub :
    BijOn (fun z : ℂ => carlsonRF (z - x₁) (z - x₂) (z - x₃)) {z | 0 < z.im}
      {ζ | 0 < ζ.re ∧ ζ.re < weierstrassK₁ x₁ x₂ x₃ ∧ -weierstrassK₃ x₁ x₂ x₃ < ζ.im ∧
        ζ.im < 0} := by
  rw [← scPolygon_weierstrass h₂₁ h₃₂]
  refine (bijOn_scMap (weierstrassParams h₂₁ h₃₂) (by norm_num)).congr fun z hz => ?_
  exact (carlsonRF_sub_eq_scMap h₂₁ h₃₂ hz).symm

/-- The inverse `z(u)` of Example 8.2-2, from the rectangle to the upper half-plane. -/
def weierstrassInv (x₁ x₂ x₃ : ℝ) : ℂ → ℂ :=
  scMapInv (1 / 2) (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃)

/-- **Carlson's (8.2-11)**: on the rectangle, `dz/du = -2 ∏ (z - xᵢ)^{1/2}`. -/
theorem hasDerivAt_weierstrassInv {ζ : ℂ}
    (hζ : ζ ∈ scPolygon (1 / 2) (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃)) :
    HasDerivAt (weierstrassInv x₁ x₂ x₃)
      (-2 * ∏ i, (weierstrassInv x₁ x₂ x₃ ζ - weierstrassNodes x₁ x₂ x₃ i) ^ (1 / 2 : ℂ)) ζ := by
  have hp := weierstrassParams h₂₁ h₃₂
  have hz := scMapInv_mem hp (by norm_num) hζ
  have h := hasDerivAt_scMapInv hp (by norm_num) hz
  rw [scMap_scMapInv hp (by norm_num) hζ] at h
  unfold weierstrassInv
  convert h using 1
  rw [scIntegrand, show ((1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) from rfl]
  have := inv_neg_mul_prod_cpow_neg_half ((1 / 2 : ℝ) : ℂ)
    (fun i => scMapInv (1 / 2) (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃) ζ -
      weierstrassNodes x₁ x₂ x₃ i)
  rw [this]
  push_cast
  norm_num

/-- **Carlson's (8.2-12)**: `(dz/du)² = 4 (z - x₁)(z - x₂)(z - x₃)`. -/
theorem sq_deriv_weierstrassInv {ζ : ℂ}
    (hζ : ζ ∈ scPolygon (1 / 2) (fun _ => 1 / 2) (weierstrassNodes x₁ x₂ x₃)) :
    deriv (weierstrassInv x₁ x₂ x₃) ζ ^ 2 =
      4 * ((weierstrassInv x₁ x₂ x₃ ζ - x₁) * (weierstrassInv x₁ x₂ x₃ ζ - x₂) *
        (weierstrassInv x₁ x₂ x₃ ζ - x₃)) := by
  rw [(hasDerivAt_weierstrassInv h₂₁ h₃₂ hζ).deriv, mul_pow, sq_prod_cpow_half,
    Fin.prod_univ_three]
  simp only [weierstrassNodes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

end Weierstrass

/-! ### The Jacobian case -/

section Jacobi

variable {k : ℝ}

/-- The nodes `-1/k, -1, 1, 1/k` of Carlson's Example 8.2-3. -/
def snNodes (k : ℝ) : Fin 4 → ℝ := ![-(1 / k), -1, 1, 1 / k]

theorem one_lt_one_div_of_lt_one (hk0 : 0 < k) (hk1 : k < 1) : 1 < 1 / k := by
  rw [lt_div_iff₀ hk0]; linarith

theorem snParams (hk0 : 0 < k) (hk1 : k < 1) :
    SchwarzChristoffelParams 1 (fun _ => 1 / 2) (snNodes k) where
  injective := by
    have h := one_lt_one_div_of_lt_one hk0 hk1
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [snNodes, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢ <;> first | rfl | (exfalso; linarith)
  pos := fun _ => by norm_num
  lt_one := fun _ => by norm_num
  a_pos := one_pos
  sum_eq := by simp; norm_num

private theorem scAngle_sn (σ : ℝ) :
    scAngle (fun _ => 1 / 2) (snNodes k) σ =
      π * (1 - ((if σ < -(1 / k) then 1 / 2 else 0) + (if σ < -1 then 1 / 2 else 0) +
        (if σ < 1 then 1 / 2 else 0) + (if σ < 1 / k then 1 / 2 else 0))) := by
  unfold scAngle
  rw [Finset.sum_filter, Fin.sum_univ_four]
  simp [snNodes]

/-- The density of the `sn` map: `∏ |σ - xᵢ|^{-1/2} = k |(σ² - 1)(1 - k² σ²)|^{-1/2}`. -/
private theorem scDensity_sn (hk0 : 0 < k) (σ : ℝ) :
    scDensity (fun _ => 1 / 2) (snNodes k) σ =
      k * |(σ ^ 2 - 1) * (1 - k ^ 2 * σ ^ 2)| ^ (-1 / 2 : ℝ) := by
  have hprod : ∏ i, |σ - snNodes k i| = |(σ ^ 2 - 1) * (1 - k ^ 2 * σ ^ 2)| / k ^ 2 := by
    rw [← Finset.abs_prod, Fin.prod_univ_four]
    simp only [snNodes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [show (σ - -(1 / k)) * (σ - -1) * (σ - 1) * (σ - 1 / k) =
      -((σ ^ 2 - 1) * (1 - k ^ 2 * σ ^ 2)) / k ^ 2 by field_simp; ring, abs_div, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < k ^ 2)]
  rw [scDensity, show (fun i : Fin 4 => |σ - snNodes k i| ^ (-(1 / 2 : ℝ))) =
    fun i => |σ - snNodes k i| ^ (-1 / 2 : ℝ) by funext i; norm_num,
    Real.finsetProd_rpow _ _ (fun i _ => abs_nonneg _), hprod,
    Real.div_rpow (abs_nonneg _) (by positivity),
    show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by positivity : (0 : ℝ) ≤ k ^ 2),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq hk0.le]
  field_simp

/-- The complete elliptic integral `K = ∫₀¹ ((1 - t²)(1 - k² t²))^{-1/2} dt`. -/
def snK (k : ℝ) : ℝ := ∫ t in Ioo (0 : ℝ) 1, ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ)

/-- The complementary integral `K' = ∫₁^{1/k} ((t² - 1)(1 - k² t²))^{-1/2} dt`. -/
def snK' (k : ℝ) : ℝ :=
  ∫ t in Ioo (1 : ℝ) (1 / k), ((t ^ 2 - 1) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ)

theorem snK_eq (hk0 : 0 < k) (hk1 : k < 1) :
    (snK k : ℂ) = π / 2 * TwoVariable.carlsonRK (1 - k ^ 2 : ℝ) 1 :=
  integral_Ioo_rsqrt_sn_complete (by nlinarith)

theorem snK'_eq (hk0 : 0 < k) (hk1 : k < 1) :
    (snK' k : ℂ) = π / 2 * TwoVariable.carlsonRK (k ^ 2 : ℝ) 1 :=
  integral_Ioo_rsqrt_sn_imag hk0 hk1

/-- Integrals of even functions over reflected intervals. -/
theorem integral_Ioo_neg_of_even {f : ℝ → ℝ} (hf : ∀ t, f (-t) = f t) {c d : ℝ} (hcd : c ≤ d) :
    ∫ t in Ioo (-d) (-c), f t = ∫ t in Ioo c d, f t := by
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le hcd,
    ← intervalIntegral.integral_comp_neg]
  simp only [hf]

private theorem integral_density_sn_Ioo (hk0 : 0 < k) (hk1 : k < 1) {c d : ℝ}
    (hsub : Ioo c d ⊆ Ioo (-1) 1) :
    ∫ σ in Ioo c d, scDensity (fun _ => 1 / 2) (snNodes k) σ =
      k * ∫ t in Ioo c d, ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
  have hσ' := hsub hσ
  have h1 : σ ^ 2 < 1 := by nlinarith [hσ'.1, hσ'.2]
  have h2 : k ^ 2 * σ ^ 2 < 1 := by nlinarith [sq_nonneg σ]
  rw [scDensity_sn hk0, abs_of_neg (by nlinarith)]
  ring_nf

private theorem integral_density_sn_Ioo' (hk0 : 0 < k) (hk1 : k < 1) {c d : ℝ}
    (hsub : Ioo c d ⊆ Ioo 1 (1 / k) ∪ Ioo (-(1 / k)) (-1)) :
    ∫ σ in Ioo c d, scDensity (fun _ => 1 / 2) (snNodes k) σ =
      k * ∫ t in Ioo c d, ((t ^ 2 - 1) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
  have hkσ : ∀ τ, |τ| < 1 / k → k ^ 2 * τ ^ 2 < 1 := by
    intro τ hτ
    have : k * |τ| < 1 := by rwa [lt_div_iff₀ hk0, mul_comm] at hτ
    have h0 : 0 ≤ k * |τ| := by positivity
    have : (k * |τ|) ^ 2 < 1 := by nlinarith
    rwa [mul_pow, sq_abs] at this
  have hpos : 0 < (σ ^ 2 - 1) * (1 - k ^ 2 * σ ^ 2) := by
    rcases hsub hσ with h | h
    · have h1 : 1 < σ ^ 2 := by nlinarith [h.1]
      have h2 := hkσ σ (by rw [abs_of_pos (by linarith [h.1])]; exact h.2)
      exact mul_pos (by linarith) (by linarith)
    · have h1 : 1 < σ ^ 2 := by nlinarith [h.2]
      have h2 := hkσ σ (by rw [abs_of_neg (by linarith [h.2])]; linarith [h.1])
      exact mul_pos (by linarith) (by linarith)
  rw [scDensity_sn hk0, abs_of_pos hpos]

variable (hk0 : 0 < k) (hk1 : k < 1)
include hk0 hk1

/-- The base point `w(0)` of the `sn` map. -/
abbrev snW₀ (k : ℝ) : ℂ := scMap 1 (fun _ => 1 / 2) (snNodes k) 0

/-- Carlson's `v(y) = (w(y) - w(0))/k`, which is `∫₀^y ((1 - t²)(1 - k² t²))^{-1/2} dt`. -/
def snV (k : ℝ) (y : ℂ) : ℂ := (scMap 1 (fun _ => 1 / 2) (snNodes k) y - snW₀ k) / k

omit hk0 hk1 in
/-- The open rectangle `-K < re v < K`, `0 < im v < K'` of Carlson's Figure 8.2-2. -/
def snRect (k : ℝ) : Set ℂ := {v | -snK k < v.re ∧ v.re < snK k ∧ 0 < v.im ∧ v.im < snK' k}

private theorem sn_side_values :
    (scMap 1 (fun _ => 1 / 2) (snNodes k) 1).re = (snW₀ k).re + k * snK k ∧
    (scMap 1 (fun _ => 1 / 2) (snNodes k) (-1 : ℝ)).re = (snW₀ k).re - k * snK k ∧
    (scMap 1 (fun _ => 1 / 2) (snNodes k) (-1 : ℝ)).im = (snW₀ k).im ∧
    (scMap 1 (fun _ => 1 / 2) (snNodes k) (-(1 / k) : ℝ)).re =
      (scMap 1 (fun _ => 1 / 2) (snNodes k) (-1 : ℝ)).re ∧
    (scMap 1 (fun _ => 1 / 2) (snNodes k) (1 / k : ℝ)).im = 0 ∧
    (snW₀ k).im = -(k * snK' k) := by
  have hp := snParams hk0 hk1
  have hk := one_lt_one_div_of_lt_one hk0 hk1
  -- the four sides and the last side
  have s1 := scMap_sub_of_scAngle hp (s := 0) (t := 1) (c := 0) zero_le_one fun σ hσ => by
    have := hσ.1; have := hσ.2
    rw [scAngle_sn]; split_ifs <;> first | (exfalso; linarith) | ring
  have s2 := scMap_sub_of_scAngle hp (s := -1) (t := 0) (c := 0) (by norm_num) fun σ hσ => by
    have := hσ.1; have := hσ.2
    rw [scAngle_sn]; split_ifs <;> first | (exfalso; linarith) | ring
  have s3 := scMap_sub_of_scAngle hp (s := 1) (t := 1 / k) (c := π / 2) hk.le fun σ hσ => by
    have := hσ.1; have := hσ.2
    rw [scAngle_sn]; split_ifs <;> first | (exfalso; linarith) | ring
  have s4 := scMap_sub_of_scAngle hp (s := -(1 / k)) (t := -1) (c := -(π / 2)) (by linarith)
    fun σ hσ => by
      have := hσ.1; have := hσ.2
      rw [scAngle_sn]; split_ifs <;> first | (exfalso; linarith) | ring
  have s5 := scMap_of_scAngle_Ioi (a := 1) (b := fun _ => 1 / 2) (x := snNodes k) (t := 1 / k)
    (c := π) fun σ hσ => by
      have : 1 / k < σ := hσ
      rw [scAngle_sn]; split_ifs <;> first | (exfalso; linarith) | ring
  rw [integral_density_sn_Ioo hk0 hk1 (fun σ hσ => ⟨by linarith [hσ.1], hσ.2⟩)] at s1
  rw [integral_density_sn_Ioo hk0 hk1 (fun σ hσ => ⟨hσ.1, by linarith [hσ.2]⟩),
    show Ioo (-1 : ℝ) 0 = Ioo (-1) (-0) by rw [neg_zero],
    integral_Ioo_neg_of_even (fun t => by ring_nf) zero_le_one] at s2
  rw [integral_density_sn_Ioo' hk0 hk1 (fun σ hσ => Or.inl hσ)] at s3
  rw [integral_density_sn_Ioo' hk0 hk1 (fun σ hσ => Or.inr hσ),
    integral_Ioo_neg_of_even (fun t => by ring_nf) hk.le] at s4
  push_cast at s1 s2 s3 s4 s5
  rw [exp_pi_div_two_mul_I] at s3
  rw [show (-(↑π / 2) * I : ℂ) = -(↑π / 2 * I) by ring, exp_neg, exp_pi_div_two_mul_I,
    inv_I] at s4
  rw [exp_pi_mul_I] at s5
  simp only [zero_mul, exp_zero, mul_one, one_mul] at s1 s2
  have e1 := congrArg re s1; have f1 := congrArg im s1
  have e2 := congrArg re s2; have f2 := congrArg im s2
  have e3 := congrArg re s3; have f3 := congrArg im s3
  have e4 := congrArg re s4
  have f5 := congrArg im s5
  simp only [sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, neg_re,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add, neg_zero,
    sub_self, neg_mul, one_mul, neg_neg] at e1 f1 e2 f2 e3 f3 e4 f5
  unfold snK snK'
  simp only [snW₀] at *
  push_cast
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- `W₀ + k v` lies in the `sn` polygon exactly when `v` lies in Carlson's rectangle. -/
theorem add_mul_mem_scPolygon_sn_iff (v : ℂ) :
    snW₀ k + k * v ∈ scPolygon 1 (fun _ => 1 / 2) (snNodes k) ↔ v ∈ snRect k := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sn_side_values hk0 hk1
  have hk := one_lt_one_div_of_lt_one hk0 hk1
  have hθ0 : scAngle (fun _ => 1 / 2) (snNodes k) (-(1 / k)) = -(π / 2) := by
    rw [scAngle_sn]; split_ifs <;> first | (exfalso; linarith) | ring
  have hθ1 : scAngle (fun _ => 1 / 2) (snNodes k) (-1) = 0 := by
    rw [scAngle_sn]; split_ifs <;> first | (exfalso; linarith) | ring
  have hθ2 : scAngle (fun _ => 1 / 2) (snNodes k) 1 = π / 2 := by
    rw [scAngle_sn]; split_ifs <;> first | (exfalso; linarith) | ring
  have hθ3 : scAngle (fun _ => 1 / 2) (snNodes k) (1 / k) = π := by
    rw [scAngle_sn]; split_ifs <;> first | (exfalso; linarith) | ring
  have hf3 : ((2 : Fin 3).succ : Fin 4) = 3 := rfl
  simp only [scPolygon, Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, mem_ofPred_eq, snRect]
  simp only [snNodes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, hf3] at hθ0 hθ1 hθ2 hθ3 ⊢
  rw [im_exp_mul_I_mul, im_exp_neg_mul_I_mul, im_exp_neg_mul_I_mul, im_exp_neg_mul_I_mul,
    im_exp_neg_mul_I_mul, hθ0, hθ1, hθ2, hθ3, show π * (1 : ℝ) = π by ring]
  simp only [sub_re, sub_im, add_re, add_im, re_ofReal_mul, im_ofReal_mul, Real.cos_pi,
    Real.sin_pi, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two,
    Real.cos_zero, Real.sin_zero]
  have hre1 : (scMap 1 (fun _ => 1 / 2) ![-(1 / k), -1, 1, 1 / k] ((1 : ℝ) : ℂ)).re =
      (snW₀ k).re + k * snK k := by simpa [snNodes] using h1
  rw [show ((-1 : ℝ) : ℂ) = -1 by push_cast; rfl] at h2 h3 h4
  simp only [snNodes] at h1 h2 h3 h4 h5 h6
  push_cast at h1 h2 h3 h4 h5 h6 ⊢
  rw [h1, h4, h2, h3, h5, h6]
  simp only [zero_mul, add_zero, sub_zero, zero_sub]
  clear h1 h2 h3 h4 h5 h6 hθ0 hθ1 hθ2 hθ3 hre1
  generalize snK k = K
  generalize snK' k = K'
  generalize (snW₀ k).re = R
  have key : ∀ X : ℝ, 0 < k * X ↔ 0 < X := fun X => mul_pos_iff_of_pos_left hk0
  rw [show -1 * (-(k * K') + k * v.im) = k * (K' - v.im) by ring,
    show -(-1 * (R + k * v.re - (R - k * K))) = k * (v.re + K) by ring,
    show 1 * (-(k * K') + k * v.im - -(k * K')) = k * v.im by ring,
    show -(1 * (R + k * v.re - (R + k * K))) = k * (K - v.re) by ring, key, key, key, key]
  constructor
  · rintro ⟨a1, a2, a3, a4, -⟩
    exact ⟨by linarith, by linarith, a3, by linarith⟩
  · rintro ⟨a1, a2, a3, a4⟩
    exact ⟨by linarith, by linarith, a3, by linarith, by linarith⟩

/-- **Carlson's Example 8.2-3**: `v(y) = (w(y) - w(0))/k` maps the open upper half-plane
one-to-one onto the open rectangle `-K < re v < K`, `0 < im v < K'`. -/
theorem bijOn_snV : BijOn (snV k) {z | 0 < z.im} (snRect k) := by
  have hp := snParams hk0 hk1
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hbij := bijOn_scMap hp le_rfl
  have hsnV : ∀ z, snW₀ k + k * snV k z = scMap 1 (fun _ => 1 / 2) (snNodes k) z := by
    intro z; rw [snV]; field_simp; ring
  refine ⟨fun z hz => ?_, fun u hu v hv huv => ?_, fun w hw => ?_⟩
  · rw [← add_mul_mem_scPolygon_sn_iff hk0 hk1, hsnV]
    exact hbij.mapsTo hz
  · have : scMap 1 (fun _ => 1 / 2) (snNodes k) u = scMap 1 (fun _ => 1 / 2) (snNodes k) v := by
      rw [← hsnV, ← hsnV, huv]
    exact hbij.injOn hu hv this
  · rw [← add_mul_mem_scPolygon_sn_iff hk0 hk1] at hw
    obtain ⟨z, hz, hzw⟩ := hbij.surjOn hw
    refine ⟨z, hz, ?_⟩
    rw [snV, hzw]
    field_simp
    ring

omit hk0 hk1 in
/-- **Jacobi's elliptic sine** on Carlson's rectangle: the inverse of `v`. -/
def jacobiSn (k : ℝ) (v : ℂ) : ℂ := scMapInv 1 (fun _ => 1 / 2) (snNodes k) (snW₀ k + k * v)

theorem jacobiSn_mem {v : ℂ} (hv : v ∈ snRect k) : 0 < (jacobiSn k v).im :=
  scMapInv_mem (snParams hk0 hk1) le_rfl ((add_mul_mem_scPolygon_sn_iff hk0 hk1 v).mpr hv)

theorem snV_jacobiSn {v : ℂ} (hv : v ∈ snRect k) : snV k (jacobiSn k v) = v := by
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  rw [snV, jacobiSn, scMap_scMapInv (snParams hk0 hk1) le_rfl
    ((add_mul_mem_scPolygon_sn_iff hk0 hk1 v).mpr hv)]
  field_simp
  ring

theorem jacobiSn_snV {z : ℂ} (hz : 0 < z.im) : jacobiSn k (snV k z) = z := by
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  rw [jacobiSn, show snW₀ k + k * snV k z = scMap 1 (fun _ => 1 / 2) (snNodes k) z by
    rw [snV]; field_simp; ring]
  exact scMapInv_scMap (snParams hk0 hk1) le_rfl hz

/-- The derivative of `sn`: `sn' = -k ∏ (sn - xᵢ)^{1/2}`. -/
theorem hasDerivAt_jacobiSn {v : ℂ} (hv : v ∈ snRect k) :
    HasDerivAt (jacobiSn k) (-k * ∏ i, (jacobiSn k v - snNodes k i) ^ (1 / 2 : ℂ)) v := by
  have hp := snParams hk0 hk1
  have hmem := (add_mul_mem_scPolygon_sn_iff hk0 hk1 v).mpr hv
  have hz := scMapInv_mem hp le_rfl hmem
  have h := hasDerivAt_scMapInv hp le_rfl hz
  rw [scMap_scMapInv hp le_rfl hmem] at h
  have hlin : HasDerivAt (fun v : ℂ => snW₀ k + k * v) k v := by
    simpa using ((hasDerivAt_id v).const_mul (k : ℂ)).const_add (snW₀ k)
  have := h.comp v hlin
  unfold jacobiSn
  convert this using 1
  · rfl
  rw [scIntegrand]
  have hinv := inv_neg_mul_prod_cpow_neg_half ((1 : ℝ) : ℂ)
    (fun i => scMapInv 1 (fun _ => 1 / 2) (snNodes k) (snW₀ k + k * v) - snNodes k i)
  rw [hinv]
  push_cast
  ring

/-- **The differential equation of `sn`**: `(sn')² = (1 - sn²)(1 - k² sn²)`. -/
theorem sq_deriv_jacobiSn {v : ℂ} (hv : v ∈ snRect k) :
    deriv (jacobiSn k) v ^ 2 = (1 - jacobiSn k v ^ 2) * (1 - k ^ 2 * jacobiSn k v ^ 2) := by
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  rw [(hasDerivAt_jacobiSn hk0 hk1 hv).deriv, mul_pow, sq_prod_cpow_half, Fin.prod_univ_four]
  simp only [snNodes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  field_simp
  ring

/-- **Carlson's (8.2-15), (8.2-18)** on the real axis: for `0 < y < 1`,
`v(y) = ∫₀^y ((1 - t²)(1 - k² t²))^{-1/2} dt = y R_F(1 - y², 1 - k² y², 1)`, so that `y = sn v`
extends Carlson's definition `z^{-1/2} = sn u` to the boundary. -/
theorem snV_ofReal {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    snV k y = y * carlsonRF ((1 - y ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ) 1 := by
  have hp := snParams hk0 hk1
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hk' := one_lt_one_div_of_lt_one hk0 hk1
  have hs := scMap_sub_of_scAngle hp (s := 0) (t := y) (c := 0) hy0.le fun σ hσ => by
    have := hσ.1; have := hσ.2
    rw [scAngle_sn]; split_ifs <;> first | (exfalso; linarith) | ring
  rw [integral_density_sn_Ioo hk0 hk1 (fun σ hσ => ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)]
    at hs
  push_cast at hs
  simp only [zero_mul, exp_zero, one_mul] at hs
  rw [snV, snW₀, hs, mul_div_cancel_left₀ _ hk,
    ← integral_Ioo_rsqrt_sn_incomplete (by nlinarith) hy0 hy1]

/-- The half-periods of `sn` as complete elliptic integrals: `K = (π/2) R_K(1 - k², 1)` and
`K' = (π/2) R_K(k², 1)` (8.2-20), (8.2-21). -/
theorem snK_snK'_eq :
    (snK k : ℂ) = π / 2 * TwoVariable.carlsonRK (1 - k ^ 2 : ℝ) 1 ∧
      (snK' k : ℂ) = π / 2 * TwoVariable.carlsonRK (k ^ 2 : ℝ) 1 :=
  ⟨snK_eq hk0 hk1, snK'_eq hk0 hk1⟩

end Jacobi

end Carlson
