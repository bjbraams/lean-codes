/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.RF
public import Carlson.R.IntegralEvaluation
public import Carlson.R.IntegerParameters
public import Carlson.R.SlitDeriv
public import Carlson.R.Homogeneity
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# The Schwarz–Christoffel mapping and elliptic integrals (Carlson §8.2)

Carlson's Theorem 8.2-1 writes the Schwarz–Christoffel map of the upper half-plane onto a convex
polygon as `w(z) = R_{-a}(b; z - x)`, with real nodes `xᵢ`, `a + 1 = ∑ bᵢ`, `0 < a ≤ 1` and
`0 < bᵢ < 1`. This module proves the analytic facts behind that theorem:

* the differential equation `dw/dz = -a ∏ (z - xᵢ)^{-bᵢ}` (8.2-1), from the translation
  identity of Theorem 5.9-2 and the elementary value (5.9-22), which is proved here on the whole
  slit domain;
* the integral representation `w(z) = a ∫_z^∞ ∏ (t - xᵢ)^{-bᵢ} dt` (8.2-2), (8.2-3), from
  Formula 8.1-2;
* the phase of the boundary derivative on the real axis, which is constant between consecutive
  nodes and drops by `π bᵢ` at `xᵢ`: the polygon's turning angles.

The boundary values and the one-to-one and onto property are proved in
`Carlson.Elliptic.VertexLimits`, `Carlson.Elliptic.Polygon` and `Carlson.Elliptic.Mapping`.

For the elliptic case it proves the half-periods of Examples 8.2-2 and 8.2-3 as complete
elliptic integrals `R_K`, with the lemniscatic case, the reductions of `R_F` to `arcsin` and
`artanh` that give `sn` for `k = 0` and `k = 1`, the incomplete integral (8.2-18) of `sn`, and
the half-periods (8.2-20), (8.2-21) of `sn`.

## Main results

* `Carlson.regCarlsonR_neg_sum_of_slit`: (5.9-22) on the slit domain.
* `Carlson.hasDerivAt_carlsonR_sub`: the differential equation (8.2-1).
* `Carlson.carlsonR_sub_eq_integral`: the integral representation (8.2-2), (8.2-3).
* `Carlson.prod_ofReal_sub_cpow`: the phase of the boundary derivative.
* `Carlson.integral_Ioi_rsqrt_cubic`, `Carlson.half_integral_Ioi_rsqrt_cubic`,
  `Carlson.half_integral_Iio_rsqrt_cubic`, `Carlson.carlsonRK_lemniscatic`: (8.2-8)–(8.2-10).
* `Carlson.integral_Ioo_rsqrt_sn`, `Carlson.integral_Ioo_rsqrt_sn_complete`: (8.2-20).
* `Carlson.integral_Ioo_rsqrt_sn_imag`: (8.2-21).
* `Carlson.carlsonRF_sub_one_self_self`, `Carlson.carlsonRF_sub_one_sub_one_self`: (8.2-14),
  (8.2-16).
* `Carlson.integral_Ioo_rsqrt_sn_incomplete`, `Carlson.carlsonRF_sn`: (8.2-18).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.2.
-/

open Complex Set Filter Dirichlet MeasureTheory
open scoped Real Topology
@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- Carlson's (5.9-22) on the whole slit domain:
`R_{-c}(b; z)/Γ(c) = ∏ zᵢ^{-bᵢ}/Γ(c)`, `c = ∑ bᵢ`. -/
theorem regCarlsonR_neg_sum_of_slit (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR (-(∑ i, b i)) b z = (∏ i, z i ^ (-b i)) * (Gamma (∑ i, b i))⁻¹ := by
  have hF := analyticOnNhd_regCarlsonR (-(∑ i, b i)) b
  have hG : AnalyticOnNhd ℂ (fun w : ι → ℂ => (∏ i, w i ^ (-b i)) * (Gamma (∑ i, b i))⁻¹)
      carlsonRSlitDomain := by
    intro w hw
    refine AnalyticAt.mul ?_ analyticAt_const
    refine Finset.analyticAt_fun_prod (𝕜 := ℂ) _ fun i _ => ?_
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt w).cpow
      analyticAt_const (hw i)
  refine eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hF hG (fun w hw => ?_) hz
  have h := regCarlsonR_neg_sum_sub_nat 0 b hw
  simpa [regCarlsonRPolynomial_zero] using h

/-- **The Schwarz–Christoffel differential equation** (8.2-1): if `a + 1 = ∑ bᵢ` and `a + 1` is
not a pole of `Γ`, then `w(z) = R_{-a}(b; z - x)` satisfies `dw/dz = -a ∏ (z - xᵢ)^{-bᵢ}` wherever
all `z - xᵢ` lie in the slit plane (in particular on the upper half-plane for real `xᵢ`). -/
theorem hasDerivAt_carlsonR_sub (a : ℂ) (b x : ι → ℂ) (hsum : a + 1 = ∑ i, b i)
    (hΓ : ∀ m : ℕ, a + 1 ≠ -m) {z : ℂ} (hz : ∀ i, z - x i ∈ slitPlane) :
    HasDerivAt (fun z => carlsonR (-a) b (fun i => z - x i))
      (-a * ∏ i, (z - x i) ^ (-b i)) z := by
  have hs : (fun i => z + -x i) ∈ carlsonRSlitDomain := fun i => by
    simpa [sub_eq_add_neg] using hz i
  have h := (hasDerivAt_regCarlsonR_translate (-a) b (fun i => -x i) hs).const_mul
    (Gamma (∑ i, b i))
  have hsum' : -a - 1 = -(∑ i, b i) := by rw [← hsum]; ring
  rw [hsum', regCarlsonR_neg_sum_of_slit b hs] at h
  unfold carlsonR
  simp_rw [sub_eq_add_neg]
  convert h using 1
  have hG : Gamma (∑ i, b i) ≠ 0 := by rw [← hsum]; exact Gamma_ne_zero hΓ
  field_simp

/-- **Carlson's (8.2-2), (8.2-3)**: for `re a > 0` and `a + 1 = ∑ bᵢ`, the Schwarz–Christoffel map
is `w(z) = a ∫_z^∞ ∏ (t - xᵢ)^{-bᵢ} dt` along the horizontal ray `t = z + s`, `s > 0`. -/
theorem carlsonR_sub_eq_integral {a : ℂ} (ha : 0 < a.re) (b x : ι → ℂ)
    (hsum : a + 1 = ∑ i, b i) {z : ℂ} (hz : ∀ i, z - x i ∈ slitPlane) :
    carlsonR (-a) b (fun i => z - x i) =
      a * ∫ s in Ioi (0 : ℝ), ∏ i, (z + s - x i) ^ (-b i) := by
  have h := integral_Ioi_ray_eq_regCarlsonR (a := a) (a' := 1) (b := b) (z := fun i => -x i)
    (w := fun _ => 1) (x := z) ha one_pos hsum (fun _ => one_ne_zero)
    (fun i => by simpa [sub_eq_add_neg] using hz i)
    (fun i s _ => by rw [arg_one, zero_add]; exact arg_mem_Ioc _)
  simp only [sub_self, cpow_zero, one_mul, one_cpow, Finset.prod_const_one, mul_one, Gamma_one,
    div_one] at h
  have hint : (fun s : ℝ => ∏ i, (-x i + (z + s)) ^ (-b i)) =
      fun s : ℝ => ∏ i, (z + s - x i) ^ (-b i) := by
    funext s; congr 1; funext i; ring_nf
  rw [hint] at h
  rw [h, carlsonR, ← hsum, Gamma_add_one _ (by rintro rfl; simp at ha)]
  simp_rw [sub_eq_add_neg]
  ring

/-- **The polygon of the Schwarz–Christoffel map** (Carlson §8.2): on the real axis the principal
(upper-edge) value of `∏ (t - xᵢ)^{-bᵢ}` is
`∏ |t - xᵢ|^{-bᵢ} · exp(-π i ∑_{xᵢ > t} bᵢ)`. For real `bᵢ` its phase is constant between
consecutive nodes and drops by `π bᵢ` as `t` passes `xᵢ`. -/
theorem prod_ofReal_sub_cpow (b : ι → ℂ) (x : ι → ℝ) (t : ℝ) :
    ∏ i, (((t - x i : ℝ)) : ℂ) ^ (-b i) =
      (∏ i, ((|t - x i| : ℝ) : ℂ) ^ (-b i)) *
        exp (-(π * I) * ∑ i ∈ Finset.univ.filter (fun i => t < x i), b i) := by
  classical
  have hfac : ∀ i, (((t - x i : ℝ)) : ℂ) ^ (-b i) =
      ((|t - x i| : ℝ) : ℂ) ^ (-b i) * (if t < x i then exp (-(π * I) * b i) else 1) := by
    intro i
    split_ifs with hlt
    · rw [ofReal_cpow_of_nonpos (by linarith), abs_of_neg (by linarith)]
      push_cast; ring_nf
    · rw [abs_of_nonneg (by linarith [not_lt.mp hlt]), mul_one]
  simp_rw [hfac, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.mul_sum, exp_sum, Finset.prod_ite, Finset.prod_const_one, mul_one]


/-- `Γ(1/2)² = π`. -/
private theorem Gamma_one_half_sq : Gamma (1 / 2 : ℂ) * Gamma (1 / 2) = π := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal,
    Real.Gamma_one_half_eq, ← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]

open TwoVariable in
/-- The complete elliptic integral on a ray: for `p, q > 0`,
`∫₀^∞ (s (s + p)(s + q))^{-1/2} ds = π R_K(p, q)`. -/
theorem integral_Ioi_rsqrt_cubic {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ((∫ s in Ioi (0 : ℝ), (s * (s + p) * (s + q)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      π * carlsonRK p q := by
  have hz : pair (p : ℂ) q ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr hp
    · exact ofReal_mem_slitPlane.mpr hq
  have h := carlsonRPositiveRayIntegral_eq_gamma_mul_regCarlsonR (a := 1 / 2) (a' := 1 / 2)
    (b := pair (1 / 2) (1 / 2)) (by norm_num) (by norm_num) (by simp [pair]) hz
  unfold carlsonRPositiveRayIntegral at h
  rw [← integral_complex_ofReal]
  have hpt : ∀ s ∈ Ioi (0 : ℝ), (((s * (s + p) * (s + q)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      (s : ℂ) ^ ((1 / 2 : ℂ) - 1) *
        ∏ i, (pair (p : ℂ) q i + s) ^ (-pair (1 / 2 : ℂ) (1 / 2) i) := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    rw [Fin.prod_univ_two, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hs'.le (by positivity)]
    push_cast
    rw [ofReal_cpow hs'.le, ofReal_cpow (by positivity), ofReal_cpow (by positivity)]
    simp only [pair]
    push_cast
    norm_num
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, h, Gamma_one_half_sq, carlsonRK, carlsonR,
    sum_pair, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Gamma_one, one_mul,
    show (-(1 / 2) : ℂ) = -1 / 2 by ring]

/-- Translation of an integral over a half-line. -/
theorem integral_Ioi_eq_integral_Ioi_add (f : ℝ → ℝ) (c : ℝ) :
    ∫ t in Ioi c, f t = ∫ s in Ioi (0 : ℝ), f (s + c) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (f := fun s => s + c) (f' := fun _ => 1)
    (fun s _ => ((hasDerivAt_id s).add_const c).hasDerivWithinAt) (add_left_injective c).injOn f
  rw [image_add_const_Ioi, zero_add] at h
  simpa using h

/-- Reflection of an integral over a half-line. -/
theorem integral_Iio_eq_integral_Ioi_sub (f : ℝ → ℝ) (c : ℝ) :
    ∫ t in Iio c, f t = ∫ s in Ioi (0 : ℝ), f (c - s) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (f := fun s => c - s) (f' := fun _ => -1)
    (fun s _ => ((hasDerivAt_id s).const_sub c).hasDerivWithinAt)
    (fun a _ b _ hab => by simpa using hab) f
  rw [show (fun s => c - s) '' Ioi (0 : ℝ) = Iio c by
    ext t; simp only [mem_image, mem_Ioi, mem_Iio]
    exact ⟨fun ⟨s, hs, hst⟩ => by linarith, fun ht => ⟨c - t, by linarith, by ring⟩⟩] at h
  simpa using h

/-- **Carlson's (8.2-8)**: for real `x₁ > x₂, x₃`, the real half-period of the Weierstrass-type
map is `(1/2) ∫_{x₁}^∞ ((t - x₁)(t - x₂)(t - x₃))^{-1/2} dt = (π/2) R_K(x₁ - x₂, x₁ - x₃)`. -/
theorem half_integral_Ioi_rsqrt_cubic {x₁ x₂ x₃ : ℝ} (h₂ : x₂ < x₁) (h₃ : x₃ < x₁) :
    (((1 / 2) * ∫ t in Ioi x₁, ((t - x₁) * (t - x₂) * (t - x₃)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      π / 2 * TwoVariable.carlsonRK (x₁ - x₂ : ℝ) (x₁ - x₃ : ℝ) := by
  rw [integral_Ioi_eq_integral_Ioi_add]
  have h := integral_Ioi_rsqrt_cubic (p := x₁ - x₂) (q := x₁ - x₃) (by linarith) (by linarith)
  have hfun : (fun s : ℝ => ((s + x₁ - x₁) * (s + x₁ - x₂) * (s + x₁ - x₃)) ^ (-1 / 2 : ℝ)) =
      fun s : ℝ => (s * (s + (x₁ - x₂)) * (s + (x₁ - x₃))) ^ (-1 / 2 : ℝ) := by
    funext s; ring_nf
  rw [ofReal_mul, hfun, h, show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by norm_num]
  ring

/-- **Carlson's (8.2-9)**, as a real integral: for real `x₃ < x₁, x₂`,
`(1/2) ∫_{-∞}^{x₃} ((x₁ - t)(x₂ - t)(x₃ - t))^{-1/2} dt = (π/2) R_K(x₁ - x₃, x₂ - x₃)`; the
imaginary half-period is `-i` times this. -/
theorem half_integral_Iio_rsqrt_cubic {x₁ x₂ x₃ : ℝ} (h₁ : x₃ < x₁) (h₂ : x₃ < x₂) :
    (((1 / 2) * ∫ t in Iio x₃, ((x₁ - t) * (x₂ - t) * (x₃ - t)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      π / 2 * TwoVariable.carlsonRK (x₁ - x₃ : ℝ) (x₂ - x₃ : ℝ) := by
  rw [integral_Iio_eq_integral_Ioi_sub]
  have h := integral_Ioi_rsqrt_cubic (p := x₁ - x₃) (q := x₂ - x₃) (by linarith) (by linarith)
  have hfun : (fun s : ℝ => ((x₁ - (x₃ - s)) * (x₂ - (x₃ - s)) * (x₃ - (x₃ - s))) ^ (-1 / 2 : ℝ)) =
      fun s : ℝ => (s * (s + (x₁ - x₃)) * (s + (x₂ - x₃))) ^ (-1 / 2 : ℝ) := by
    funext s; ring_nf
  rw [ofReal_mul, hfun, h, show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by norm_num]
  ring

open TwoVariable in
/-- Homogeneity of `R_K` under positive real scaling: `R_K(λx, λy) = λ^{-1/2} R_K(x, y)`. -/
theorem carlsonRK_mul_of_pos {l : ℝ} (hl : 0 < l) {x y : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) : carlsonRK (l * x) (l * y) = (l : ℂ) ^ (-1 / 2 : ℂ) * carlsonRK x y := by
  have hz : pair x y ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hx
    · exact hy
  have h := regCarlsonR_smul_of_pos (-1 / 2) (pair (1 / 2) (1 / 2)) hl hz
  have hp : (fun i => (l : ℂ) * pair x y i) = pair (l * x) (l * y) := by
    funext i; fin_cases i <;> rfl
  rw [hp] at h
  unfold carlsonRK carlsonR
  rw [h]; ring

open TwoVariable in
/-- **Carlson's (8.2-10)**, the lemniscatic case `x₂ = 0`, `x₃ = -x₁`:
`(π/2) R_K(x₁, 2x₁) = (π/2) x₁^{-1/2} R_K(1, 2)`. -/
theorem carlsonRK_lemniscatic {x₁ : ℝ} (h : 0 < x₁) :
    carlsonRK (x₁ : ℂ) (2 * x₁ : ℝ) = (x₁ : ℂ) ^ (-1 / 2 : ℂ) * carlsonRK 1 2 := by
  have := carlsonRK_mul_of_pos h (x := 1) (y := 2) (by simp) (ofReal_mem_slitPlane.mpr two_pos)
  simpa [mul_comm] using this

open TwoVariable in
/-- **Carlson's (8.2-20)**: for real `k` with `k² < 1`, the real half-period of `sn` is
`∫₀¹ (s (1 - s)(1 - k² s))^{-1/2} ds = π R_K(1 - k², 1)`. -/
theorem integral_Ioo_rsqrt_sn {k : ℝ} (hk : k ^ 2 < 1) :
    ((∫ s in Ioo (0 : ℝ) 1, (s * (1 - s) * (1 - k ^ 2 * s)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      π * carlsonRK (1 - k ^ 2 : ℝ) 1 := by
  have hz : pair ((1 - k ^ 2 : ℝ) : ℂ) 1 ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr (by linarith)
    · simp [pair]
  have h := carlsonRUnitIntervalIntegral_eq_gamma_mul_regCarlsonR (a := 1 / 2) (a' := 1 / 2)
    (b := pair (1 / 2) (1 / 2)) (by norm_num) (by norm_num) (by simp [pair]) hz
  unfold carlsonRUnitIntervalIntegral at h
  rw [← integral_complex_ofReal]
  have hpt : ∀ s ∈ Ioo (0 : ℝ) 1, (((s * (1 - s) * (1 - k ^ 2 * s)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      (s : ℂ) ^ ((1 / 2 : ℂ) - 1) * (1 - s : ℂ) ^ ((1 / 2 : ℂ) - 1) *
        ∏ i, ((1 - s : ℂ) + (s : ℂ) * pair ((1 - k ^ 2 : ℝ) : ℂ) 1 i) ^
          (-pair (1 / 2 : ℂ) (1 / 2) i) := by
    intro s hs
    have h1 : 0 < 1 - s := by linarith [hs.2]
    have h2 : 0 < 1 - k ^ 2 * s := by nlinarith [hs.1, hs.2, sq_nonneg k]
    rw [Fin.prod_univ_two, Real.mul_rpow (by nlinarith [hs.1]) h2.le,
      Real.mul_rpow hs.1.le h1.le, ofReal_mul, ofReal_mul, ofReal_cpow hs.1.le, ofReal_cpow h1.le,
      ofReal_cpow h2.le]
    simp only [pair, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    rw [show (1 : ℂ) - s + s * 1 = 1 by ring, one_cpow, mul_one,
      show (1 : ℂ) - s + s * (1 - k ^ 2) = 1 - k ^ 2 * s by ring]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, h, Gamma_one_half_sq, carlsonRK, carlsonR,
    sum_pair, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Gamma_one, one_mul,
    show (-(1 / 2) : ℂ) = -1 / 2 by ring]

/-- **Carlson's (8.2-14)**: for real `z > 1`, `R_F(z - 1, z, z) = R_C(z - 1, z) = arcsin(z^{-1/2})`;
this is the case `k = 0` of `sn`, which is `sin`. -/
theorem carlsonRF_sub_one_self_self {z : ℝ} (hz : 1 < z) :
    carlsonRF ((z - 1 : ℝ) : ℂ) z z = (Real.arcsin (z ^ (-1 / 2 : ℝ)) : ℂ) := by
  have hz0 : 0 < z := by linarith
  have h1 : 0 < z - 1 := by linarith
  rw [carlsonRF_self_right (ofReal_mem_slitPlane.mpr h1) (ofReal_mem_slitPlane.mpr hz0),
    TwoVariable.carlsonRC_of_lt h1 (by linarith), show z - (z - 1) = 1 by ring, Real.sqrt_one,
    div_one, Real.arccos_eq_arcsin (Real.sqrt_nonneg _), Real.sq_sqrt (div_nonneg h1.le hz0.le)]
  congr 2
  rw [show 1 - (z - 1) / z = z⁻¹ by field_simp; ring, Real.sqrt_inv,
    show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hz0.le, ← Real.sqrt_eq_rpow]

/-- **Carlson's (8.2-16)**: for real `z > 1`, `R_F(z - 1, z - 1, z) = R_C(z, z - 1) =
artanh(z^{-1/2})`; this is the case `k = 1` of `sn`, which is `tanh`. -/
theorem carlsonRF_sub_one_sub_one_self {z : ℝ} (hz : 1 < z) :
    carlsonRF ((z - 1 : ℝ) : ℂ) ((z - 1 : ℝ) : ℂ) z = (Real.artanh (z ^ (-1 / 2 : ℝ)) : ℂ) := by
  have hz0 : 0 < z := by linarith
  have h1 : 0 < z - 1 := by linarith
  have hs1 := ofReal_mem_slitPlane.mpr h1
  have hs0 := ofReal_mem_slitPlane.mpr hz0
  rw [carlsonRF_comm_right hs1 hs0 hs1, carlsonRF_comm_left hs0 hs1 hs1,
    carlsonRF_self_right hs0 hs1, TwoVariable.carlsonRC_of_gt h1 (by linarith),
    show z - (z - 1) = 1 by ring, Real.sqrt_one, div_one]
  congr 1
  have hq : z ^ (-1 / 2 : ℝ) = (Real.sqrt z)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hz0.le, ← Real.sqrt_eq_rpow]
  have hsz : 1 < Real.sqrt z := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt zero_le_one hz
  have hmem : (Real.sqrt z)⁻¹ ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [inv_pos.mpr (by linarith : (0 : ℝ) < Real.sqrt z)], inv_le_one_of_one_le₀ hsz.le⟩
  rw [hq, Real.artanh_eq_half_log hmem]
  have hsq : Real.sqrt (z - 1) ^ 2 = (Real.sqrt z + 1) * (Real.sqrt z - 1) := by
    rw [Real.sq_sqrt h1.le]; ring_nf; rw [Real.sq_sqrt hz0.le]
  have hA : 0 < (Real.sqrt z + 1) / Real.sqrt (z - 1) := by positivity
  have hratio : (1 + (Real.sqrt z)⁻¹) / (1 - (Real.sqrt z)⁻¹) =
      ((Real.sqrt z + 1) / Real.sqrt (z - 1)) ^ 2 := by
    have hsz0 : Real.sqrt z ≠ 0 := by linarith
    have hsz1 : Real.sqrt z - 1 ≠ 0 := by linarith
    rw [div_pow, hsq]
    field_simp
  rw [hratio, Real.log_pow]
  push_cast; ring

/-- **Carlson's (8.2-18)**, first form: for real `k² < 1` and `0 < y < 1`, the incomplete elliptic
integral of the first kind is
`∫₀^y ((1 - t²)(1 - k² t²))^{-1/2} dt = y R_F(1 - y², 1 - k² y², 1)`. -/
theorem integral_Ioo_rsqrt_sn_incomplete {k y : ℝ} (hk : k ^ 2 < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    ((∫ t in Ioo (0 : ℝ) y, ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      y * carlsonRF ((1 - y ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ) 1 := by
  set g : ℝ → ℝ := fun t => ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ)
  set φ : ℝ → ℝ := fun s => y * Real.sqrt s
  set N : Fin 3 → ℂ := ![((1 - y ^ 2 : ℝ) : ℂ), ((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ), 1]
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
    · show ((1 - y ^ 2 : ℝ) : ℂ) ∈ slitPlane
      exact ofReal_mem_slitPlane.mpr (by nlinarith)
    · show ((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ) ∈ slitPlane
      have hky := mul_nonneg (sq_nonneg k) (sq_nonneg y)
      have hy2 : y ^ 2 < 1 := by nlinarith
      exact ofReal_mem_slitPlane.mpr (by nlinarith)
    · simp [N]
  have h := carlsonRUnitIntervalIntegral_eq_gamma_mul_regCarlsonR (a := 1 / 2) (a' := 1)
    (b := fun _ : Fin 3 => (1 / 2 : ℂ)) (by norm_num) (by norm_num) (by simp; norm_num) hz
  unfold carlsonRUnitIntervalIntegral at h
  rw [← integral_complex_ofReal]
  have hpt : ∀ s ∈ Ioo (0 : ℝ) 1, ((|y * (1 / (2 * Real.sqrt s))| • g (φ s) : ℝ) : ℂ) =
      (y / 2 : ℂ) * ((s : ℂ) ^ ((1 / 2 : ℂ) - 1) * (1 - s : ℂ) ^ ((1 : ℂ) - 1) *
        ∏ i, ((1 - s : ℂ) + (s : ℂ) * N i) ^ (-(fun _ : Fin 3 => (1 / 2 : ℂ)) i)) := by
    intro s hs
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.1.le
    have h1 : 0 < 1 - y ^ 2 * s := by nlinarith [hs.1, hs.2]
    have h2 : 0 < 1 - k ^ 2 * y ^ 2 * s := by
      nlinarith [hs.1, hs.2, sq_nonneg k, sq_nonneg y, mul_nonneg (sq_nonneg k) (sq_nonneg y)]
    have hg : g (φ s) =
        (1 - y ^ 2 * s) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * y ^ 2 * s) ^ (-1 / 2 : ℝ) := by
      simp only [g, φ]
      rw [show (1 - (y * Real.sqrt s) ^ 2) = 1 - y ^ 2 * s by rw [mul_pow, hsq],
        show (1 - k ^ 2 * (y * Real.sqrt s) ^ 2) = 1 - k ^ 2 * y ^ 2 * s by rw [mul_pow, hsq]; ring,
        Real.mul_rpow h1.le h2.le]
    have habs : |y * (1 / (2 * Real.sqrt s))| = y / 2 * s ^ (-1 / 2 : ℝ) := by
      rw [abs_of_pos (by have := Real.sqrt_pos.mpr hs.1; positivity),
        show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow]
      ring
    rw [hg, habs, smul_eq_mul, ofReal_mul, ofReal_mul, ofReal_mul, ofReal_cpow hs.1.le,
      ofReal_cpow h1.le, ofReal_cpow h2.le]
    simp only [N, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast
    rw [show (1 : ℂ) - s + s * 1 = 1 by ring, one_cpow, mul_one, sub_self, cpow_zero, mul_one,
      show (1 : ℂ) - s + s * (1 - y ^ 2) = 1 - y ^ 2 * s by ring,
      show (1 : ℂ) - s + s * (1 - k ^ 2 * y ^ 2) = 1 - k ^ 2 * y ^ 2 * s by ring]
    norm_num
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul, h, carlsonRF_eq,
    Gamma_one, show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
  simp only [N]
  ring_nf

/-- **Carlson's (8.2-18)**, second form: `R_F(y⁻² - 1, y⁻² - k², y⁻²) = y R_F(1 - y², 1 - k²y², 1)`
for `0 < y < 1` and `k² < 1`, by homogeneity. -/
theorem carlsonRF_sn {k y : ℝ} (hk : k ^ 2 < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    carlsonRF (((y ^ 2)⁻¹ - 1 : ℝ) : ℂ) (((y ^ 2)⁻¹ - k ^ 2 : ℝ) : ℂ) (((y ^ 2)⁻¹ : ℝ) : ℂ) =
      y * carlsonRF ((1 - y ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ) 1 := by
  set N : Fin 3 → ℂ := ![((1 - y ^ 2 : ℝ) : ℂ), ((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ), 1]
  have hz : N ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · show ((1 - y ^ 2 : ℝ) : ℂ) ∈ slitPlane
      exact ofReal_mem_slitPlane.mpr (by nlinarith)
    · show ((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ) ∈ slitPlane
      have hky := mul_nonneg (sq_nonneg k) (sq_nonneg y)
      have hy2 : y ^ 2 < 1 := by nlinarith
      exact ofReal_mem_slitPlane.mpr (by nlinarith)
    · simp [N]
  have hl : 0 < (y ^ 2)⁻¹ := by positivity
  have h := regCarlsonR_smul_of_pos (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) hl hz
  have hy2 : (y ^ 2)⁻¹ * y ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  have hvec : (fun i => (((y ^ 2)⁻¹ : ℝ) : ℂ) * N i) =
      ![(((y ^ 2)⁻¹ - 1 : ℝ) : ℂ), (((y ^ 2)⁻¹ - k ^ 2 : ℝ) : ℂ), (((y ^ 2)⁻¹ : ℝ) : ℂ)] := by
    funext i; fin_cases i
    · show (((y ^ 2)⁻¹ : ℝ) : ℂ) * ((1 - y ^ 2 : ℝ) : ℂ) = (((y ^ 2)⁻¹ - 1 : ℝ) : ℂ)
      rw [← ofReal_mul]; congr 1; rw [mul_sub, mul_one, hy2]
    · show (((y ^ 2)⁻¹ : ℝ) : ℂ) * ((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ) = (((y ^ 2)⁻¹ - k ^ 2 : ℝ) : ℂ)
      rw [← ofReal_mul]; congr 1
      rw [mul_sub, mul_one, show (y ^ 2)⁻¹ * (k ^ 2 * y ^ 2) = k ^ 2 * ((y ^ 2)⁻¹ * y ^ 2) by ring,
        hy2, mul_one]
    · show (((y ^ 2)⁻¹ : ℝ) : ℂ) * 1 = (((y ^ 2)⁻¹ : ℝ) : ℂ)
      rw [mul_one]
  rw [hvec] at h
  have hpow : ((((y ^ 2)⁻¹ : ℝ) : ℂ)) ^ (-1 / 2 : ℂ) = y := by
    rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hl.le]
    congr 1
    rw [Real.inv_rpow (by positivity), show (-1 / 2 : ℝ) = -(1 / 2) by ring,
      Real.rpow_neg (by positivity), inv_inv, ← Real.sqrt_eq_rpow, Real.sqrt_sq hy0.le]
  rw [carlsonRF_eq, carlsonRF_eq, h, hpow]
  simp only [N]
  ring

open TwoVariable in
/-- **Carlson's (8.2-21)**, as a real integral: for `0 < k < 1`, the imaginary half-period of `sn`
is `∫₁^{1/k} ((t² - 1)(1 - k² t²))^{-1/2} dt = (π/2) R_K(k², 1)`. The substitution
`t = √(1 - (1 - k²) u)/k` reduces it to (8.2-20) with the complementary modulus. -/
theorem integral_Ioo_rsqrt_sn_imag {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ((∫ t in Ioo (1 : ℝ) (1 / k), ((t ^ 2 - 1) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      π / 2 * carlsonRK (k ^ 2 : ℝ) 1 := by
  set g : ℝ → ℝ := fun t => ((t ^ 2 - 1) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ)
  set c : ℝ := 1 - k ^ 2 with hc
  have hc0 : 0 < c := by nlinarith
  have hc1 : c < 1 := by nlinarith
  set S : ℝ → ℝ := fun u => 1 - c * u
  set φ : ℝ → ℝ := fun u => Real.sqrt (S u) / k
  have hS : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < S u := fun u hu => by
    simp only [S]; nlinarith [hu.1, hu.2]
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt φ (1 / (2 * Real.sqrt (S u)) * (-c) / k) (Ioo 0 1) u := by
    intro u hu
    have h1 : HasDerivAt S (-c) u := by
      simpa using ((hasDerivAt_id u).const_mul c).const_sub 1
    exact (((Real.hasDerivAt_sqrt (hS u hu).ne').comp u h1).div_const k).hasDerivWithinAt
  have hinj : InjOn φ (Ioo 0 1) := by
    intro u hu v hv huv
    have h1 : Real.sqrt (S u) = Real.sqrt (S v) := by
      have := congrArg (· * k) huv
      simpa [φ, div_mul_cancel₀ _ hk0.ne'] using this
    rw [Real.sqrt_inj (hS u hu).le (hS v hv).le] at h1
    simp only [S] at h1
    have := mul_left_cancel₀ hc0.ne' (by linarith : c * u = c * v)
    exact this
  have himg : φ '' Ioo 0 1 = Ioo 1 (1 / k) := by
    ext t; constructor
    · rintro ⟨u, hu, rfl⟩
      have hSu := hS u hu
      have hlt : S u < 1 := by simp only [S]; nlinarith [hu.1]
      have hgt : k ^ 2 < S u := by simp only [S, c]; nlinarith [hu.2]
      constructor
      · rw [lt_div_iff₀ hk0, one_mul, show k = Real.sqrt (k ^ 2) by rw [Real.sqrt_sq hk0.le]]
        exact Real.sqrt_lt_sqrt (sq_nonneg k) hgt
      · show Real.sqrt (S u) / k < 1 / k
        rw [div_lt_div_iff_of_pos_right hk0, Real.sqrt_lt' one_pos]
        simpa using hlt
    · rintro ⟨ht1, htk⟩
      have hkt : k * t < 1 := by rwa [lt_div_iff₀ hk0, mul_comm] at htk
      have hkt0 : 0 < k * t := by nlinarith
      refine ⟨(1 - k ^ 2 * t ^ 2) / c, ⟨div_pos (by nlinarith) hc0, ?_⟩, ?_⟩
      · have ht2 : 1 < t ^ 2 := by nlinarith
        have : k ^ 2 < k ^ 2 * t ^ 2 := by nlinarith [pow_pos hk0 2]
        rw [div_lt_one hc0]; simp only [c]; linarith
      · show Real.sqrt (1 - c * ((1 - k ^ 2 * t ^ 2) / c)) / k = t
        rw [mul_div_cancel₀ _ hc0.ne', show 1 - (1 - k ^ 2 * t ^ 2) = (k * t) ^ 2 by ring,
          Real.sqrt_sq hkt0.le]
        field_simp
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  rw [himg] at hsub
  rw [hsub]
  have hpt : ∀ u ∈ Ioo (0 : ℝ) 1, |1 / (2 * Real.sqrt (S u)) * (-c) / k| • g (φ u) =
      1 / 2 * (u * (1 - u) * (1 - Real.sqrt c ^ 2 * u)) ^ (-1 / 2 : ℝ) := by
    intro u hu
    have hSu := hS u hu
    have hsq : Real.sqrt (S u) ^ 2 = S u := Real.sq_sqrt hSu.le
    have hu1 : 0 < 1 - u := by linarith [hu.2]
    have hA : (φ u ^ 2 - 1) * (1 - k ^ 2 * φ u ^ 2) = (c / k) ^ 2 * (u * (1 - u)) := by
      simp only [φ, div_pow, hsq]
      simp only [S, c]
      field_simp
      ring
    have huu : 0 < u * (1 - u) := mul_pos hu.1 hu1
    have hneg : ∀ X : ℝ, 0 ≤ X → X ^ (-1 / 2 : ℝ) = 1 / Real.sqrt X := fun X hX => by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hX, ← Real.sqrt_eq_rpow, one_div]
    simp only [g]
    rw [hA, Real.sq_sqrt hc0.le, smul_eq_mul, hneg _ (by positivity), hneg _ (by positivity),
      Real.sqrt_mul' _ huu.le, Real.sqrt_sq (by positivity),
      show u * (1 - u) * (1 - c * u) = u * (1 - u) * S u by rfl, Real.sqrt_mul huu.le,
      abs_of_neg (by
        have := Real.sqrt_pos.mpr hSu
        have : 0 < 1 / (2 * Real.sqrt (S u)) := by positivity
        have : 1 / (2 * Real.sqrt (S u)) * (-c) < 0 := by nlinarith
        exact div_neg_of_neg_of_pos this hk0)]
    have := Real.sqrt_pos.mpr hSu
    have := Real.sqrt_pos.mpr huu
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul, ofReal_mul,
    integral_Ioo_rsqrt_sn (k := Real.sqrt c) (by rw [Real.sq_sqrt hc0.le]; exact hc1),
    Real.sq_sqrt hc0.le, show 1 - c = k ^ 2 by simp only [c]; ring]
  push_cast
  ring

open TwoVariable in
/-- **Carlson's (8.2-20)** in Legendre's form: for `k² < 1`, the complete elliptic integral
`K = ∫₀¹ ((1 - t²)(1 - k² t²))^{-1/2} dt` is `(π/2) R_K(1 - k², 1)`; the substitution `t = √s`
reduces it to `integral_Ioo_rsqrt_sn`. -/
theorem integral_Ioo_rsqrt_sn_complete {k : ℝ} (hk : k ^ 2 < 1) :
    ((∫ t in Ioo (0 : ℝ) 1, ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      π / 2 * carlsonRK (1 - k ^ 2 : ℝ) 1 := by
  set g : ℝ → ℝ := fun t => ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ)
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt Real.sqrt (1 / (2 * Real.sqrt s)) (Ioo 0 1) s := fun s hs =>
    (Real.hasDerivAt_sqrt hs.1.ne').hasDerivWithinAt
  have hinj : InjOn Real.sqrt (Ioo 0 1) := fun u hu v hv huv =>
    (Real.sqrt_inj hu.1.le hv.1.le).mp huv
  have himg : Real.sqrt '' Ioo 0 1 = Ioo 0 1 := by
    ext t; constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Real.sqrt_pos.mpr hs.1, by rw [Real.sqrt_lt' one_pos]; simpa using hs.2⟩
    · rintro ⟨ht0, ht1⟩
      exact ⟨t ^ 2, ⟨by positivity, by nlinarith⟩, Real.sqrt_sq ht0.le⟩
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  rw [himg] at hsub
  rw [hsub]
  have hpt : ∀ s ∈ Ioo (0 : ℝ) 1, |1 / (2 * Real.sqrt s)| • g (Real.sqrt s) =
      1 / 2 * (s * (1 - s) * (1 - k ^ 2 * s)) ^ (-1 / 2 : ℝ) := by
    intro s hs
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.1.le
    have h1 : 0 < 1 - s := by linarith [hs.2]
    have h2 : 0 < 1 - k ^ 2 * s := by nlinarith [hs.1, hs.2, sq_nonneg k]
    have hr := Real.sqrt_pos.mpr hs.1
    simp only [g, hsq]
    rw [abs_of_pos (by positivity), smul_eq_mul, Real.mul_rpow h1.le h2.le,
      Real.mul_rpow (mul_nonneg hs.1.le h1.le) h2.le, Real.mul_rpow hs.1.le h1.le,
      show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul, ofReal_mul,
    integral_Ioo_rsqrt_sn hk]
  push_cast
  ring

end Carlson
