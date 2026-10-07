/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.IntegralExercises
public import Carlson.Elliptic.LegendreStandard
public import Carlson.R.ContourRepresentation

/-!
# Applications of elliptic integrals (Carlson §9.4)

Formulas of Carlson's §9.4 and Exercises 9.3-2 and 9.4-1 that express quantities from geometry,
potential theory and mechanics by symmetric elliptic integrals. The integrals are stated for
real data; the physical derivations (energy equations, Laplace's equation in ellipsoidal
coordinates) are reduced to the integral or differential identities they rest on.

## Main results

* `Carlson.integral_rsqrt_quadratic_mul_quadratic`: `∫₀^x [(at² + c)(αt² + γ)]^{-1/2} dt` as an
  `R_F`, Exercise 9.8-3 with `y = 0`.
* `Carlson.integral_Ioo_rsqrt_one_sub_mul_sq`: (8.2-20) for a real parameter `m < 1` in place
  of `k²`.
* `Carlson.integral_pendulum`, `Carlson.integral_pendulum_separatrix`,
  `Carlson.carlsonRC_inv_sq_eq_artanh`, `Carlson.integral_pendulum_rotation`: the simple pendulum,
  (9.4-21), (9.4-25) and (9.4-26).
* `Carlson.integral_anharmonic`, `Carlson.integral_anharmonic_period`: the anharmonic
  oscillator, (9.4-17) and (9.4-18).
* `Carlson.ellipse_perimeter`: the perimeter of an ellipse, (9.4-5).
* `Carlson.hyperbola_arc_length`: the arc length of a hyperbola, Exercise 9.4-1.
* `Carlson.hasDerivAt_carlsonRF_add`, `Carlson.hasDerivAt_ellipsoid_potential`,
  `Carlson.tendsto_sqrt_mul_ellipsoid_potential`: the potential of a charged conducting
  ellipsoid, (9.4-9) and (9.4-10).
* `Carlson.integral_mutual_inductance`: the mutual inductance of two coaxial circles,
  Exercise 9.3-2.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology

@[expose] public noncomputable section

namespace Carlson

open TwoVariable

/-- `x^{-1/2}` for real `x > 0`, as a complex power and as an inverse square root. -/
private theorem ofReal_cpow_neg_half' {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-1 / 2 : ℂ) = ((Real.sqrt x)⁻¹ : ℝ) := by
  rw [show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx.le,
    Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]

/-- `x^{-1/2}` for real `x ≥ 0`, as a complex power of a real number. -/
private theorem ofReal_cpow_neg_half'' {x : ℝ} (hx : 0 ≤ x) :
    (((x ^ (-1 / 2 : ℝ) : ℝ)) : ℂ) = (x : ℂ) ^ (-1 / 2 : ℂ) := by
  rw [ofReal_cpow hx]; push_cast; ring_nf

/-- **Exercise 9.8-3 with `y = 0`**, and the integral behind (9.4-17) and (9.4-21): for real
`x > 0` with `at² + c`, `αt² + γ` positive on `[0, x]`,
`∫₀^x [(at² + c)(αt² + γ)]^{-1/2} dt = R_F(U², U² + aγ, U² + cα)` with `U² = cγ/x²`. -/
theorem integral_rsqrt_quadratic_mul_quadratic {a c α γ x : ℝ} (hx : 0 < x)
    (hpos : ∀ t ∈ Icc 0 x, 0 < a * t ^ 2 + c ∧ 0 < α * t ^ 2 + γ) :
    ((∫ t in Ioo 0 x, ((a * t ^ 2 + c) * (α * t ^ 2 + γ)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      carlsonRF ((c * γ / x ^ 2 : ℝ) : ℂ) ((c * γ / x ^ 2 + a * γ : ℝ) : ℂ)
        ((c * γ / x ^ 2 + c * α : ℝ) : ℂ) := by
  obtain ⟨hc, hγ⟩ := hpos 0 ⟨le_rfl, hx.le⟩
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add] at hc hγ
  obtain ⟨hcx, hγx⟩ := hpos x ⟨hx.le, le_rfl⟩
  have hseg : ∀ {A B : ℝ}, (∀ t ∈ Icc 0 x, 0 < B * t ^ 2 + A) →
      ∀ s ∈ Icc (0 : ℝ) (x ^ 2), (A : ℂ) + B * (s : ℂ) ∈ slitPlane := fun {A B} h s hs => by
    have ht : Real.sqrt s ∈ Icc 0 x := ⟨Real.sqrt_nonneg _, by
      rw [← Real.sqrt_sq hx.le]; exact Real.sqrt_le_sqrt hs.2⟩
    have := h _ ht
    rw [Real.sq_sqrt hs.1] at this
    rw [← ofReal_mul, ← ofReal_add]
    exact ofReal_mem_slitPlane.2 (by linarith)
  have H := integral_cpow_mul_affine_sq_cpow (α := 1 / 2) (β := -1 / 2) (δ := -1 / 2)
    (A := c) (B := a) (C := γ) (D := α) hx (by norm_num)
    (hseg fun t ht => (hpos t ht).1) (hseg fun t ht => (hpos t ht).2)
  norm_num at H
  have hb : (![1 / 2, 1 / 2, 1 / 2] : Fin 3 → ℂ) = fun _ => 1 / 2 := by
    funext i; fin_cases i <;> rfl
  set u : ℝ := (c + a * x ^ 2) / c
  set v : ℝ := (γ + α * x ^ 2) / γ
  have hu : 0 < u := div_pos (by linarith) hc
  have hv : 0 < v := div_pos (by linarith) hγ
  have hreg : regCarlsonR (-(1 / 2)) ![1 / 2, 1 / 2, 1 / 2]
      ![((c : ℂ) + a * (x : ℂ) ^ 2) / c, ((γ : ℂ) + α * (x : ℂ) ^ 2) / γ, 1] =
      carlsonRF u v 1 / Gamma (3 / 2) := by
    rw [carlsonRF_eq, hb, show (-(1 / 2) : ℂ) = -1 / 2 by ring]
    rw [mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos (by norm_num))]
    simp [u, v]
  have hs : ∀ {r : ℝ}, 0 < r → (r : ℂ) ∈ slitPlane := fun hr => ofReal_mem_slitPlane.2 hr
  have hl : 0 < c * γ / x ^ 2 := by positivity
  have hRF : carlsonRF ((c * γ / x ^ 2 : ℝ) : ℂ) ((c * γ / x ^ 2 + a * γ : ℝ) : ℂ)
      ((c * γ / x ^ 2 + c * α : ℝ) : ℂ) =
      ((c * γ / x ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) * carlsonRF u v 1 := by
    rw [← carlsonRF_comm_right (hs hu) (hs hv) one_mem_slitPlane,
      ← carlsonRF_comm_left (hs hu) one_mem_slitPlane (hs hv),
      ← carlsonRF_mul_of_pos hl one_mem_slitPlane (hs hu) (hs hv)]
    have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
    have hγ0 : (γ : ℂ) ≠ 0 := ofReal_ne_zero.2 hγ.ne'
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
    congr 1 <;> push_cast [u, v] <;> field_simp
  rw [hRF, ← integral_complex_ofReal]
  rw [setIntegral_congr_fun measurableSet_Ioo (g := fun t : ℝ =>
    ((c : ℂ) + a * (t : ℂ) ^ 2) ^ (-(1 / 2) : ℂ) * ((γ : ℂ) + α * (t : ℂ) ^ 2) ^ (-(1 / 2) : ℂ))
    fun t ht => by
      obtain ⟨h1, h2⟩ := hpos t (Ioo_subset_Icc_self ht)
      simp only
      rw [Real.mul_rpow h1.le h2.le, ofReal_mul, ofReal_cpow h1.le, ofReal_cpow h2.le]
      congr 1 <;> congr 1 <;> push_cast <;> ring]
  rw [H, hreg, Gamma_three_halves]
  have hx2 : ((x : ℂ) ^ 2) ^ (1 / 2 : ℂ) = x := by
    rw [← ofReal_pow, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (sq_nonneg x), ← Real.sqrt_eq_rpow, Real.sqrt_sq hx.le]
  rw [hx2, show (-(1 / 2) : ℂ) = -1 / 2 by ring, ofReal_cpow_neg_half' hc,
    ofReal_cpow_neg_half' hγ, ofReal_cpow_neg_half' hl, Real.sqrt_div' _ (sq_nonneg x),
    Real.sqrt_sq hx.le, Real.sqrt_mul hc.le]
  have hG : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hsc : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  have hsγ : Real.sqrt γ ≠ 0 := (Real.sqrt_pos.2 hγ).ne'
  push_cast
  field_simp

/-- `Γ(1/2)² = π`. -/
private theorem Gamma_one_half_mul_self : Gamma (1 / 2 : ℂ) * Gamma (1 / 2) = π := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal,
    Real.Gamma_one_half_eq, ← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]

/-- **Carlson's (8.2-20)** with a real parameter `m < 1` in place of `k²`:
`∫₀¹ (s (1 - s)(1 - ms))^{-1/2} ds = π R_K(1 - m, 1)`. -/
theorem integral_Ioo_rsqrt_one_sub_mul {m : ℝ} (hm : m < 1) :
    ((∫ s in Ioo (0 : ℝ) 1, (s * (1 - s) * (1 - m * s)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      π * carlsonRK (1 - m : ℝ) 1 := by
  have hz : pair ((1 - m : ℝ) : ℂ) 1 ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr (by linarith)
    · simp [pair]
  have h := carlsonRUnitIntervalIntegral_eq_Gamma_mul_regCarlsonR (a := 1 / 2) (a' := 1 / 2)
    (b := pair (1 / 2) (1 / 2)) (by norm_num) (by norm_num) (by simp [pair]) hz
  unfold carlsonRUnitIntervalIntegral at h
  rw [← integral_complex_ofReal]
  have hpt : ∀ s ∈ Ioo (0 : ℝ) 1, (((s * (1 - s) * (1 - m * s)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      (s : ℂ) ^ ((1 / 2 : ℂ) - 1) * (1 - s : ℂ) ^ ((1 / 2 : ℂ) - 1) *
        ∏ i, ((1 - s : ℂ) + (s : ℂ) * pair ((1 - m : ℝ) : ℂ) 1 i) ^
          (-pair (1 / 2 : ℂ) (1 / 2) i) := by
    intro s hs
    have h1 : 0 < 1 - s := by linarith [hs.2]
    have h2 : 0 < 1 - m * s := by nlinarith [mul_pos hs.1 (sub_pos.2 hm)]
    rw [Fin.prod_univ_two, Real.mul_rpow (by nlinarith [hs.1]) h2.le,
      Real.mul_rpow hs.1.le h1.le, ofReal_mul, ofReal_mul, ofReal_cpow hs.1.le, ofReal_cpow h1.le,
      ofReal_cpow h2.le]
    simp only [pair, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    rw [show (1 : ℂ) - s + s * 1 = 1 by ring, one_cpow, mul_one,
      show (1 : ℂ) - s + s * (1 - m) = 1 - m * s by ring]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, h, Gamma_one_half_mul_self, carlsonRK, carlsonR,
    sum_pair, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Gamma_one, one_mul,
    show (-(1 / 2) : ℂ) = -1 / 2 by ring]

/-- **Carlson's (8.2-20)** in Legendre's form with a real parameter `m < 1`:
`∫₀¹ ((1 - t²)(1 - mt²))^{-1/2} dt = (π/2) R_K(1 - m, 1)`. -/
theorem integral_Ioo_rsqrt_one_sub_mul_sq {m : ℝ} (hm : m < 1) :
    ((∫ t in Ioo (0 : ℝ) 1, ((1 - t ^ 2) * (1 - m * t ^ 2)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      π / 2 * carlsonRK (1 - m : ℝ) 1 := by
  set g : ℝ → ℝ := fun t => ((1 - t ^ 2) * (1 - m * t ^ 2)) ^ (-1 / 2 : ℝ)
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
      1 / 2 * (s * (1 - s) * (1 - m * s)) ^ (-1 / 2 : ℝ) := by
    intro s hs
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.1.le
    have h1 : 0 < 1 - s := by linarith [hs.2]
    have h2 : 0 < 1 - m * s := by nlinarith [mul_pos hs.1 (sub_pos.2 hm)]
    have hr := Real.sqrt_pos.mpr hs.1
    simp only [g, hsq]
    rw [abs_of_pos (by positivity), smul_eq_mul, Real.mul_rpow h1.le h2.le,
      Real.mul_rpow (mul_nonneg hs.1.le h1.le) h2.le, Real.mul_rpow hs.1.le h1.le,
      show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul, ofReal_mul,
    integral_Ioo_rsqrt_one_sub_mul hm]
  push_cast
  ring

/-! ### The simple pendulum (Example 9.4-5) -/

/-- **Carlson's (9.4-21)**: the time along the pendulum's swing,
`ωt = ∫₀^x [(1 - u²)(1 - k²u²)]^{-1/2} du = R_F(x^{-2} - 1, x^{-2} - k², x^{-2})`,
for `0 < x < 1` and `k²x² < 1`. -/
theorem integral_pendulum {k x : ℝ} (hx : 0 < x) (hx1 : x < 1) (hkx : k ^ 2 * x ^ 2 < 1) :
    ((∫ u in Ioo 0 x, ((1 - u ^ 2) * (1 - k ^ 2 * u ^ 2)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      carlsonRF ((x⁻¹ ^ 2 - 1 : ℝ) : ℂ) ((x⁻¹ ^ 2 - k ^ 2 : ℝ) : ℂ) ((x⁻¹ ^ 2 : ℝ) : ℂ) := by
  have hpos : ∀ t ∈ Icc 0 x, 0 < -1 * t ^ 2 + 1 ∧ 0 < -k ^ 2 * t ^ 2 + 1 := fun t ht => by
    have h2 : t ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ ht.1 ht.2 2
    constructor <;> nlinarith [sq_nonneg k]
  have H := integral_rsqrt_quadratic_mul_quadratic hx hpos
  have hs : ∀ {r : ℝ}, 0 < r → (r : ℂ) ∈ slitPlane := fun hr => ofReal_mem_slitPlane.2 hr
  have hx2 : 1 < x⁻¹ ^ 2 := by
    rw [inv_pow]; exact (one_lt_inv₀ (by positivity)).2 (by nlinarith)
  have hk2 : k ^ 2 < x⁻¹ ^ 2 := by
    rw [inv_pow, ← one_div, lt_div_iff₀ (by positivity)]; exact hkx
  have e : (∫ u in Ioo 0 x, ((1 - u ^ 2) * (1 - k ^ 2 * u ^ 2)) ^ (-1 / 2 : ℝ)) =
      ∫ u in Ioo 0 x, ((-1 * u ^ 2 + 1) * (-k ^ 2 * u ^ 2 + 1)) ^ (-1 / 2 : ℝ) := by
    congr 1; funext u; congr 1; ring
  have h0 : (0 : ℝ) < x⁻¹ ^ 2 := by positivity
  have h1 : (0 : ℝ) < x⁻¹ ^ 2 - 1 := by linarith
  have h2 : (0 : ℝ) < x⁻¹ ^ 2 - k ^ 2 := by linarith
  rw [← carlsonRF_comm_right (hs h1) (hs h2) (hs h0), ← carlsonRF_comm_left (hs h1) (hs h0) (hs h2),
    e, H]
  congr 1 <;> push_cast <;> ring

/-- **Carlson's (9.4-25)**, the separatrix `k = 1` of the pendulum:
`∫₀^x (1 - u²)^{-1} du = R_C(x^{-2}, x^{-2} - 1)` for `0 < x < 1`. -/
theorem integral_pendulum_separatrix {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ((∫ u in Ioo 0 x, (1 - u ^ 2)⁻¹ : ℝ) : ℂ) =
      carlsonRC ((x⁻¹ ^ 2 : ℝ) : ℂ) ((x⁻¹ ^ 2 - 1 : ℝ) : ℂ) := by
  have hpos : ∀ t ∈ Icc 0 x, 0 < -1 * t ^ 2 + 1 ∧ 0 < -1 * t ^ 2 + 1 := fun t ht => by
    have h2 : t ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ ht.1 ht.2 2
    constructor <;> nlinarith
  have H := integral_rsqrt_quadratic_mul_quadratic hx hpos
  have hs : ∀ {r : ℝ}, 0 < r → (r : ℂ) ∈ slitPlane := fun hr => ofReal_mem_slitPlane.2 hr
  have hx2 : 1 < x⁻¹ ^ 2 := by
    rw [inv_pow]; exact (one_lt_inv₀ (by positivity)).2 (by nlinarith)
  have e : (∫ u in Ioo 0 x, (1 - u ^ 2)⁻¹) =
      ∫ u in Ioo 0 x, ((-1 * u ^ 2 + 1) * (-1 * u ^ 2 + 1)) ^ (-1 / 2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hp : 0 < -1 * u ^ 2 + 1 := (hpos u (Ioo_subset_Icc_self hu)).1
    rw [← sq, ← Real.rpow_natCast (-1 * u ^ 2 + 1) 2, ← Real.rpow_mul hp.le]
    norm_num [Real.rpow_neg_one]
    ring_nf
  rw [e, H, ← carlsonRF_self_right (hs (by linarith)) (hs (by linarith))]
  congr 1 <;> push_cast <;> ring

/-- The separatrix time (9.4-25) in closed form: `R_C(x^{-2}, x^{-2} - 1) = artanh x` for
`0 < x < 1`. -/
theorem carlsonRC_inv_sq_eq_artanh {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    carlsonRC ((x⁻¹ ^ 2 : ℝ) : ℂ) ((x⁻¹ ^ 2 - 1 : ℝ) : ℂ) = (Real.artanh x : ℂ) := by
  have hx2 : 1 < x⁻¹ ^ 2 := by
    rw [inv_pow]; exact (one_lt_inv₀ (by positivity)).2 (by nlinarith)
  rw [carlsonRC_of_gt (by linarith) (by linarith), show x⁻¹ ^ 2 - (x⁻¹ ^ 2 - 1) = 1 by ring,
    Real.sqrt_one, div_one, Real.artanh]
  congr 2
  have h1 : 0 < 1 - x := by linarith
  have h2 : 0 < 1 - x ^ 2 := by nlinarith
  rw [Real.sqrt_sq (by positivity), show x⁻¹ ^ 2 - 1 = (1 - x ^ 2) / x ^ 2 by field_simp,
    Real.sqrt_div' _ (sq_nonneg x), Real.sqrt_sq hx.le, eq_comm,
    Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
  have hs := Real.mul_self_sqrt h2.le
  field_simp
  nlinarith [hs]

/-- **Carlson's (9.4-26)**: for `k > 1` the pendulum rotates, and the quarter period is
`∫₀^{1/k} [(1 - u²)(1 - k²u²)]^{-1/2} du = (π/2) R_K(k² - 1, k²)`. -/
theorem integral_pendulum_rotation {k : ℝ} (hk : 1 < k) :
    ((∫ u in Ioo 0 k⁻¹, ((1 - u ^ 2) * (1 - k ^ 2 * u ^ 2)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      π / 2 * carlsonRK ((k ^ 2 - 1 : ℝ) : ℂ) ((k ^ 2 : ℝ) : ℂ) := by
  have hk0 : 0 < k := by linarith
  set g : ℝ → ℝ := fun u => ((1 - u ^ 2) * (1 - k ^ 2 * u ^ 2)) ^ (-1 / 2 : ℝ)
  have hsub : ∫ v in (0 : ℝ)..1, g (k⁻¹ * v) = k * ∫ u in (0 : ℝ)..k⁻¹, g u := by
    rw [intervalIntegral.integral_comp_mul_left g (inv_ne_zero hk0.ne'), mul_zero, mul_one,
      inv_inv, smul_eq_mul]
  have hm : k⁻¹ ^ 2 < 1 := by
    rw [inv_pow]; exact inv_lt_one_of_one_lt₀ (by nlinarith)
  have H := integral_Ioo_rsqrt_one_sub_mul_sq hm
  have hcongr : ∫ v in Ioo (0 : ℝ) 1, ((1 - v ^ 2) * (1 - k⁻¹ ^ 2 * v ^ 2)) ^ (-1 / 2 : ℝ) =
      ∫ v in (0 : ℝ)..1, g (k⁻¹ * v) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun v _ => ?_
    simp only [g]
    congr 1
    field_simp
  rw [hcongr, hsub, intervalIntegral.integral_of_le (by positivity),
    integral_Ioc_eq_integral_Ioo] at H
  have hs : ∀ {r : ℝ}, 0 < r → (r : ℂ) ∈ slitPlane := fun hr => ofReal_mem_slitPlane.2 hr
  have hK := carlsonRK_mul_of_pos (by positivity : (0 : ℝ) < k ^ 2) (hs (sub_pos.2 hm))
    one_mem_slitPlane
  have hk2 : ((k ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = ((k⁻¹ : ℝ) : ℂ) := by
    rw [ofReal_cpow_neg_half' (by positivity), Real.sqrt_sq hk0.le]
  rw [hk2] at hK
  have hk0' : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk0.ne'
  have e1 : ((k ^ 2 : ℝ) : ℂ) * ((1 - k⁻¹ ^ 2 : ℝ) : ℂ) = ((k ^ 2 - 1 : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [e1, mul_one] at hK
  rw [hK]
  rw [ofReal_mul] at H
  set I := ∫ u in Ioo 0 k⁻¹, g u
  have : (I : ℂ) = (k : ℂ)⁻¹ * (k * I) := by field_simp
  rw [this, H]
  push_cast
  ring

/-! ### The anharmonic oscillator (Example 9.4-4) -/

/-- **Carlson's (9.4-17)**: for the oscillator with potential `kx²/2 + βx⁴`, amplitude `A` and
`σ = βA⁴/E ≥ 0`, the time to reach `0 < x < A` is
`ωt = A^{-1} ∫₀^x [(1 - u²/A²)(1 + σu²/A²)]^{-1/2} du = R_F(A²/x² - 1, A²/x², A²/x² + σ)`. -/
theorem integral_anharmonic {A σ x : ℝ} (hA : 0 < A) (hσ : 0 ≤ σ) (hx : 0 < x) (hxA : x < A) :
    ((A⁻¹ * ∫ u in Ioo 0 x, ((1 - u ^ 2 / A ^ 2) * (1 + σ * u ^ 2 / A ^ 2)) ^ (-1 / 2 : ℝ) :
        ℝ) : ℂ) =
      carlsonRF ((A ^ 2 / x ^ 2 - 1 : ℝ) : ℂ) ((A ^ 2 / x ^ 2 : ℝ) : ℂ)
        ((A ^ 2 / x ^ 2 + σ : ℝ) : ℂ) := by
  have hpos : ∀ t ∈ Icc 0 x, 0 < -(A ^ 2)⁻¹ * t ^ 2 + 1 ∧ 0 < σ / A ^ 2 * t ^ 2 + 1 :=
    fun t ht => by
      have h2 : t ^ 2 < A ^ 2 := pow_lt_pow_left₀ (ht.2.trans_lt hxA) ht.1 two_ne_zero
      constructor
      · have : t ^ 2 / A ^ 2 < 1 := (div_lt_one (by positivity)).2 h2
        rw [neg_mul, ← div_eq_inv_mul]
        linarith
      · positivity
  have H := integral_rsqrt_quadratic_mul_quadratic hx hpos
  have hs : ∀ {r : ℝ}, 0 < r → (r : ℂ) ∈ slitPlane := fun hr => ofReal_mem_slitPlane.2 hr
  have hxA2 : x ^ 2 < A ^ 2 := pow_lt_pow_left₀ hxA hx.le two_ne_zero
  have h1 : 0 < 1 / x ^ 2 - 1 / A ^ 2 := by
    rw [sub_pos]; exact one_div_lt_one_div_of_lt (by positivity) hxA2
  have hK := carlsonRF_mul_of_pos (by positivity : (0 : ℝ) < A ^ 2) (hs h1)
    (hs (by positivity : (0 : ℝ) < 1 / x ^ 2))
    (hs (by positivity : (0 : ℝ) < 1 / x ^ 2 + σ / A ^ 2))
  have hA2 : ((A ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = ((A⁻¹ : ℝ) : ℂ) := by
    rw [ofReal_cpow_neg_half' (by positivity), Real.sqrt_sq hA.le]
  rw [hA2, carlsonRF_comm_left (hs (by positivity)) (hs h1) (hs (by positivity))] at hK
  have e : (∫ u in Ioo 0 x, ((1 - u ^ 2 / A ^ 2) * (1 + σ * u ^ 2 / A ^ 2)) ^ (-1 / 2 : ℝ)) =
      ∫ u in Ioo 0 x, ((-(A ^ 2)⁻¹ * u ^ 2 + 1) * (σ / A ^ 2 * u ^ 2 + 1)) ^ (-1 / 2 : ℝ) := by
    congr 1; funext u; congr 1; ring
  rw [e, ofReal_mul, H]
  have e' : carlsonRF ((1 * 1 / x ^ 2 : ℝ) : ℂ) ((1 * 1 / x ^ 2 + -(A ^ 2)⁻¹ * 1 : ℝ) : ℂ)
      ((1 * 1 / x ^ 2 + 1 * (σ / A ^ 2) : ℝ) : ℂ) =
      carlsonRF ((1 / x ^ 2 : ℝ) : ℂ) ((1 / x ^ 2 - 1 / A ^ 2 : ℝ) : ℂ)
        ((1 / x ^ 2 + σ / A ^ 2 : ℝ) : ℂ) := by
    congr 1 <;> push_cast <;> ring
  rw [e', ← hK]
  have hA0 : (A : ℂ) ≠ 0 := ofReal_ne_zero.2 hA.ne'
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  congr 1 <;> push_cast <;> field_simp

/-- **Carlson's (9.4-18)**: the period of the anharmonic oscillator,
`ωT = 4 ∫₀¹ [(1 - v²)(1 + σv²)]^{-1/2} dv = 2π R_K(1, 1 + σ)`, for `σ > -1`. -/
theorem integral_anharmonic_period {σ : ℝ} (hσ : -1 < σ) :
    ((4 * ∫ v in Ioo 0 1, ((1 - v ^ 2) * (1 + σ * v ^ 2)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      2 * π * carlsonRK 1 ((1 + σ : ℝ) : ℂ) := by
  have H := integral_Ioo_rsqrt_one_sub_mul_sq (m := -σ) (by linarith)
  have e : (∫ v in Ioo (0 : ℝ) 1, ((1 - v ^ 2) * (1 + σ * v ^ 2)) ^ (-1 / 2 : ℝ)) =
      ∫ v in Ioo (0 : ℝ) 1, ((1 - v ^ 2) * (1 - -σ * v ^ 2)) ^ (-1 / 2 : ℝ) := by
    congr 1; funext v; congr 1; ring
  rw [ofReal_mul, e, H, carlsonRK_comm (ofReal_mem_slitPlane.2 (by linarith)) one_mem_slitPlane,
    show (1 - -σ : ℝ) = 1 + σ by ring]
  push_cast
  ring

/-! ### Ellipses (Example 9.4-1) -/

/-- The quarter perimeter of an ellipse when `α ≤ β`, from (9.2-15). -/
private theorem integral_ellipse_quarter_of_le {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ((∫ θ in (0 : ℝ)..π / 2,
        (α ^ 2 * Real.sin θ ^ 2 + β ^ 2 * Real.cos θ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
      π / 2 * carlsonRE ((α ^ 2 : ℝ) : ℂ) ((β ^ 2 : ℝ) : ℂ) := by
  have hβ : 0 < β := hα.trans_le hαβ
  have h1 : 0 ≤ 1 - α ^ 2 / β ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact pow_le_pow_left₀ hα.le hαβ 2
  rw [carlsonRE_eq_legendreEc (by positivity) (pow_le_pow_left₀ hα.le hαβ 2),
    Real.sqrt_sq hβ.le]
  unfold legendreEc legendreE
  rw [Real.sq_sqrt h1]
  have e : (∫ θ in (0 : ℝ)..π / 2,
      (α ^ 2 * Real.sin θ ^ 2 + β ^ 2 * Real.cos θ ^ 2) ^ (1 / 2 : ℝ)) =
      β * ∫ θ in (0 : ℝ)..π / 2, (1 - (1 - α ^ 2 / β ^ 2) * Real.sin θ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext θ
    have hw : 0 ≤ 1 - (1 - α ^ 2 / β ^ 2) * Real.sin θ ^ 2 := by
      have := Real.sin_sq_le_one θ
      have : 0 ≤ α ^ 2 / β ^ 2 := by positivity
      nlinarith
    rw [show α ^ 2 * Real.sin θ ^ 2 + β ^ 2 * Real.cos θ ^ 2 =
      β ^ 2 * (1 - (1 - α ^ 2 / β ^ 2) * Real.sin θ ^ 2) by
        rw [Real.cos_sq']; field_simp; ring,
      Real.mul_rpow (sq_nonneg β) hw, ← Real.sqrt_eq_rpow, Real.sqrt_sq hβ.le]
  rw [e]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp

/-- **Carlson's (9.4-5)**: the perimeter of the ellipse `x²/α² + y²/β² = 1` is
`S = 4 ∫₀^{π/2} (α² sin² θ + β² cos² θ)^{1/2} dθ = 2π R_E(α², β²)`. -/
theorem ellipse_perimeter {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ((4 * ∫ θ in (0 : ℝ)..π / 2,
        (α ^ 2 * Real.sin θ ^ 2 + β ^ 2 * Real.cos θ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
      2 * π * carlsonRE ((α ^ 2 : ℝ) : ℂ) ((β ^ 2 : ℝ) : ℂ) := by
  rcases le_total α β with h | h
  · rw [ofReal_mul, integral_ellipse_quarter_of_le hα h]
    push_cast; ring
  · have e : (∫ θ in (0 : ℝ)..π / 2,
        (α ^ 2 * Real.sin θ ^ 2 + β ^ 2 * Real.cos θ ^ 2) ^ (1 / 2 : ℝ)) =
        ∫ θ in (0 : ℝ)..π / 2, (β ^ 2 * Real.sin θ ^ 2 + α ^ 2 * Real.cos θ ^ 2) ^ (1 / 2 : ℝ) := by
      have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 2)
        (fun θ => (β ^ 2 * Real.sin θ ^ 2 + α ^ 2 * Real.cos θ ^ 2) ^ (1 / 2 : ℝ)) (π / 2)
      rw [sub_self, sub_zero] at this
      rw [← this]
      congr 1; funext θ
      rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
      ring_nf
    rw [e, ofReal_mul, integral_ellipse_quarter_of_le hβ h,
      carlsonRE_comm (ofReal_mem_slitPlane.2 (by positivity))
        (ofReal_mem_slitPlane.2 (by positivity))]
    push_cast; ring

/-- The branch `x = α (1 + t²/β²)^{1/2}` of the hyperbola `x²/α² - y²/β² = 1`, as a function
of `y = t`, has slope `αt / (β² (1 + t²/β²)^{1/2})`. -/
theorem hasDerivAt_hyperbola {α β : ℝ} (hβ : β ≠ 0) (t : ℝ) :
    HasDerivAt (fun t => α * Real.sqrt (1 + t ^ 2 / β ^ 2))
      (α * t / (β ^ 2 * Real.sqrt (1 + t ^ 2 / β ^ 2))) t := by
  have hw : 0 < 1 + t ^ 2 / β ^ 2 := by positivity
  have := ((hasDerivAt_pow 2 t).div_const (β ^ 2)).const_add 1 |>.sqrt hw.ne' |>.const_mul α
  convert this using 1
  have := Real.sqrt_pos.2 hw
  simp only [Nat.cast_ofNat]
  field_simp
  ring

/-- **Exercise 9.4-1**: the arc of the hyperbola `x²/α² - y²/β² = 1` from `(α, 0)` to `(x, y)`,
`y > 0`, has length
`s = ∫₀^y [1 + (dx/dt)²]^{1/2} dt = R_{-1/2}(1/2, -1/2, 3/2; y^{-2} + β^{-2},
y^{-2} + β^{-2} + α²β^{-4}, y^{-2})`, where `x(t) = α (1 + t²/β²)^{1/2}`
(`Carlson.hasDerivAt_hyperbola`). -/
theorem hyperbola_arc_length {α β y : ℝ} (hβ : 0 < β) (hy : 0 < y) :
    ((∫ t in Ioo 0 y,
        Real.sqrt (1 + (α * t / (β ^ 2 * Real.sqrt (1 + t ^ 2 / β ^ 2))) ^ 2) : ℝ) : ℂ) =
      carlsonR (-1 / 2) ![1 / 2, -1 / 2, 3 / 2]
        ![((y⁻¹ ^ 2 + β⁻¹ ^ 2 : ℝ) : ℂ), ((y⁻¹ ^ 2 + β⁻¹ ^ 2 + α ^ 2 * β⁻¹ ^ 4 : ℝ) : ℂ),
          ((y⁻¹ ^ 2 : ℝ) : ℂ)] := by
  have hs : ∀ {r : ℝ}, 0 < r → (r : ℂ) ∈ slitPlane := fun hr => ofReal_mem_slitPlane.2 hr
  have hseg : ∀ {B : ℝ}, 0 ≤ B → ∀ s ∈ Icc (0 : ℝ) (y ^ 2),
      ((β ^ 4 : ℝ) : ℂ) + (B : ℂ) * (s : ℂ) ∈ slitPlane := fun hB s hs' => by
    rw [← ofReal_mul, ← ofReal_add]
    exact ofReal_mem_slitPlane.2 (by nlinarith [hs'.1, pow_pos hβ 4, mul_nonneg hB hs'.1])
  have H := integral_cpow_mul_affine_sq_cpow (α := 1 / 2) (β := 1 / 2) (δ := -1 / 2)
    (A := ((β ^ 4 : ℝ) : ℂ)) (B := ((α ^ 2 + β ^ 2 : ℝ) : ℂ)) (C := ((β ^ 4 : ℝ) : ℂ))
    (D := ((β ^ 2 : ℝ) : ℂ)) hy (by norm_num) (hseg (by positivity)) (hseg (by positivity))
  norm_num at H
  -- the integrand
  rw [← integral_complex_ofReal, setIntegral_congr_fun measurableSet_Ioo (g := fun t : ℝ =>
    ((β : ℂ) ^ 4 + ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * (t : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
      ((β : ℂ) ^ 4 + (β : ℂ) ^ 2 * (t : ℂ) ^ 2) ^ (-(1 / 2) : ℂ)) fun t _ => by
    have hw : 0 < 1 + t ^ 2 / β ^ 2 := by positivity
    have hsw := Real.sq_sqrt hw.le
    have hN : 0 ≤ β ^ 4 + (α ^ 2 + β ^ 2) * t ^ 2 := by positivity
    have hD : 0 < β ^ 4 + β ^ 2 * t ^ 2 := by positivity
    have e : 1 + (α * t / (β ^ 2 * Real.sqrt (1 + t ^ 2 / β ^ 2))) ^ 2 =
        (β ^ 4 + (α ^ 2 + β ^ 2) * t ^ 2) / (β ^ 4 + β ^ 2 * t ^ 2) := by
      rw [div_pow, mul_pow, mul_pow, hsw]; field_simp; ring
    simp only
    rw [e, Real.sqrt_div hN, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, div_eq_mul_inv,
      ← Real.rpow_neg hD.le,
      ofReal_mul, ofReal_cpow hN, ofReal_cpow hD.le]
    push_cast
    ring_nf]
  rw [H]
  -- the right side
  have hb4 : ((β : ℂ) ^ 4) ^ (1 / 2 : ℂ) * ((β : ℂ) ^ 4) ^ (-(1 / 2) : ℂ) = 1 := by
    rw [← cpow_add _ _ (pow_ne_zero 4 (ofReal_ne_zero.2 hβ.ne')), add_neg_cancel, cpow_zero]
  have hy2 : ((y : ℂ) ^ 2) ^ (1 / 2 : ℂ) = y := by
    rw [← ofReal_pow, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (sq_nonneg y), ← Real.sqrt_eq_rpow, Real.sqrt_sq hy.le]
  rw [mul_assoc (_ * _ * _) (((β : ℂ) ^ 4) ^ (1 / 2 : ℂ)), hb4, mul_one, hy2]
  set wB : Fin 3 → ℂ := ![((y⁻¹ ^ 2 + β⁻¹ ^ 2 : ℝ) : ℂ),
    ((y⁻¹ ^ 2 + β⁻¹ ^ 2 + α ^ 2 * β⁻¹ ^ 4 : ℝ) : ℂ), ((y⁻¹ ^ 2 : ℝ) : ℂ)]
  have hwB : wB ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> exact hs (by positivity)
  set z : Fin 3 → ℂ := ![((1 + (α ^ 2 + β ^ 2) * y ^ 2 / β ^ 4 : ℝ) : ℂ),
    ((1 + y ^ 2 / β ^ 2 : ℝ) : ℂ), 1]
  have hz : z ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hs (by positivity)
    · exact hs (by positivity)
    · exact one_mem_slitPlane
  have hsw := regCarlsonR_comp_equiv (Equiv.swap (0 : Fin 3) 1) (-1 / 2) hwB
    ![-1 / 2, 1 / 2, 3 / 2]
  have hb' : (![-1 / 2, 1 / 2, 3 / 2] : Fin 3 → ℂ) ∘ (Equiv.swap (0 : Fin 3) 1).symm =
      ![1 / 2, -1 / 2, 3 / 2] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  have hβ0 : (β : ℂ) ≠ 0 := ofReal_ne_zero.2 hβ.ne'
  have hwz : wB ∘ Equiv.swap (0 : Fin 3) 1 = fun i => ((y⁻¹ ^ 2 : ℝ) : ℂ) * z i := by
    funext i; fin_cases i <;> simp [wB, z, Equiv.swap_apply_def] <;> (field_simp; try ring)
  have hsm := regCarlsonR_smul_of_pos (-1 / 2) ![-1 / 2, 1 / 2, 3 / 2]
    (by positivity : (0 : ℝ) < y⁻¹ ^ 2) hz
  rw [hb', hwz, hsm, ofReal_cpow_neg_half' (by positivity), Real.sqrt_sq (by positivity),
    inv_inv] at hsw
  have hzH : (![((β : ℂ) ^ 4 + ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * (y : ℂ) ^ 2) / (β : ℂ) ^ 4,
      ((β : ℂ) ^ 4 + (β : ℂ) ^ 2 * (y : ℂ) ^ 2) / (β : ℂ) ^ 4, 1] : Fin 3 → ℂ) = z := by
    funext i; fin_cases i <;> simp [z] <;> field_simp
  have hbH : (![-(1 / 2), 1 / 2, 3 / 2] : Fin 3 → ℂ) = ![-1 / 2, 1 / 2, 3 / 2] := by
    funext i; fin_cases i <;> norm_num
  rw [hzH, hbH, show (-(1 / 2) : ℂ) = -1 / 2 by ring]
  unfold carlsonR
  rw [← hsw, show ∑ i, (![1 / 2, -1 / 2, 3 / 2] : Fin 3 → ℂ) i = 3 / 2 by
    simp [Fin.sum_univ_three]; norm_num, Gamma_three_halves]
  ring

/-! ### The potential of a charged conducting ellipsoid (Example 9.4-3) -/

/-- The derivative of `R_F` along the diagonal: on the slit plane,
`d/dλ R_F(λ + x, λ + y, λ + z) = -(1/2) (λ + x)^{-1/2} (λ + y)^{-1/2} (λ + z)^{-1/2}`. -/
theorem hasDerivAt_carlsonRF_add {x y z l : ℂ} (hx : l + x ∈ slitPlane) (hy : l + y ∈ slitPlane)
    (hz : l + z ∈ slitPlane) :
    HasDerivAt (fun l => carlsonRF (l + x) (l + y) (l + z))
      (-1 / 2 * ((l + x) ^ (-1 / 2 : ℂ) * (l + y) ^ (-1 / 2 : ℂ) * (l + z) ^ (-1 / 2 : ℂ))) l := by
  have h := hasDerivAt_carlsonR_sub (1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) ![-x, -y, -z]
    (by simp; norm_num) (fun m hm => by
      have := congrArg re hm; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    (fun i => by fin_cases i <;> simpa)
  convert h using 1
  · funext q
    unfold carlsonRF
    congr 1
    · norm_num
    · funext i; fin_cases i <;> simp
  · simp [Fin.prod_univ_three]
    ring_nf

/-- **Carlson's (9.4-9), (9.4-10)**: the potential `V(λ) = R_F(λ + α², λ + β², λ + γ²)` of a
charged conducting ellipsoid with semiaxes `α, β, γ`, as a function of the ellipsoidal coordinate
`λ ≥ 0`, satisfies `[(λ + α²)(λ + β²)(λ + γ²)]^{1/2} dV/dλ = -1/2`; hence it solves Laplace's
equation (9.4-9) in the form `d/dλ ([(λ + α²)(λ + β²)(λ + γ²)]^{1/2} dV/dλ) = 0`. -/
theorem hasDerivAt_ellipsoid_potential {α β γ l : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hl : 0 ≤ l) :
    HasDerivAt (fun l : ℝ => carlsonRF ((l + α ^ 2 : ℝ) : ℂ) ((l + β ^ 2 : ℝ) : ℂ)
        ((l + γ ^ 2 : ℝ) : ℂ))
      ((-1 / 2 * ((l + α ^ 2) * (l + β ^ 2) * (l + γ ^ 2)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) l := by
  have hs : ∀ {r : ℝ}, 0 < r → (r : ℂ) ∈ slitPlane := fun hr => ofReal_mem_slitPlane.2 hr
  have h := hasDerivAt_carlsonRF_add (l := (l : ℂ)) (x := ((α ^ 2 : ℝ) : ℂ))
    (y := ((β ^ 2 : ℝ) : ℂ)) (z := ((γ ^ 2 : ℝ) : ℂ))
    (by rw [← ofReal_add]; exact hs (by positivity))
    (by rw [← ofReal_add]; exact hs (by positivity))
    (by rw [← ofReal_add]; exact hs (by positivity))
  have h' := h.comp_ofReal
  convert h' using 1
  · funext q; push_cast; rfl
  · rw [ofReal_mul, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    push_cast
    rw [ofReal_cpow_neg_half'' (by positivity : 0 ≤ l + α ^ 2),
      ofReal_cpow_neg_half'' (by positivity : 0 ≤ l + β ^ 2),
      ofReal_cpow_neg_half'' (by positivity : 0 ≤ l + γ ^ 2)]
    push_cast
    ring

/-- **The boundary condition in (9.4-10)**: `λ^{1/2} R_F(λ + α², λ + β², λ + γ²) → 1` as
`λ → ∞`, so `V(λ) = Q R_F(λ + α², λ + β², λ + γ²)` behaves like `Q/r` at large distances. -/
theorem tendsto_sqrt_mul_ellipsoid_potential (α β γ : ℝ) :
    Tendsto (fun l : ℝ => (Real.sqrt l : ℂ) *
        carlsonRF ((l + α ^ 2 : ℝ) : ℂ) ((l + β ^ 2 : ℝ) : ℂ) ((l + γ ^ 2 : ℝ) : ℂ))
      atTop (𝓝 1) := by
  set g : ℂ → ℂ := fun q => carlsonRF (1 + α ^ 2 * q) (1 + β ^ 2 * q) (1 + γ ^ 2 * q)
  have hg : ContinuousAt g 0 := by
    refine (analyticAt_carlsonRF_comp (by fun_prop) (by fun_prop) (by fun_prop) ?_ ?_
      ?_).continuousAt
    all_goals simp
  have hg0 : g 0 = 1 := by simp [g, carlsonRF_self one_mem_slitPlane]
  have hinv : Tendsto (fun l : ℝ => ((l⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
    rwa [ofReal_zero] at this
  have hlim := (hg.tendsto.comp hinv)
  rw [hg0] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with l hl
  have hs : ∀ {r : ℝ}, 0 < r → (r : ℂ) ∈ slitPlane := fun hr => ofReal_mem_slitPlane.2 hr
  have hm := carlsonRF_mul_of_pos hl (x := 1 + α ^ 2 * ((l⁻¹ : ℝ) : ℂ))
    (y := 1 + β ^ 2 * ((l⁻¹ : ℝ) : ℂ)) (z := 1 + γ ^ 2 * ((l⁻¹ : ℝ) : ℂ))
    (by rw [show (1 : ℂ) + α ^ 2 * ((l⁻¹ : ℝ) : ℂ) = ((1 + α ^ 2 * l⁻¹ : ℝ) : ℂ) by push_cast; ring]
        exact hs (by positivity))
    (by rw [show (1 : ℂ) + β ^ 2 * ((l⁻¹ : ℝ) : ℂ) = ((1 + β ^ 2 * l⁻¹ : ℝ) : ℂ) by push_cast; ring]
        exact hs (by positivity))
    (by rw [show (1 : ℂ) + γ ^ 2 * ((l⁻¹ : ℝ) : ℂ) = ((1 + γ ^ 2 * l⁻¹ : ℝ) : ℂ) by push_cast; ring]
        exact hs (by positivity))
  have hl0 : (l : ℂ) ≠ 0 := ofReal_ne_zero.2 hl.ne'
  have e : ∀ c : ℝ, (l : ℂ) * (1 + (c : ℂ) ^ 2 * ((l⁻¹ : ℝ) : ℂ)) = ((l + c ^ 2 : ℝ) : ℂ) := by
    intro c; push_cast; field_simp
  rw [e, e, e, ofReal_cpow_neg_half' hl] at hm
  simp only [Function.comp, g]
  rw [hm]
  have hsl : (Real.sqrt l : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 hl).ne'
  push_cast
  field_simp

/-! ### Mutual inductance of coaxial circles (Exercise 9.3-2) -/

/-- The Euler integral for `R̃_{-3/2}(3/2, 3/2; P, Q)`:
`∫₀¹ (s(1 - s))^{1/2} (sP + (1 - s)Q)^{-3/2} ds = (π/4) R̃_{-3/2}(3/2, 3/2; P, Q)`. -/
private theorem integral_euler_three_halves {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) :
    ((∫ s in Ioo (0 : ℝ) 1, Real.sqrt (s * (1 - s)) * (s * P + (1 - s) * Q) ^ (-3 / 2 : ℝ) :
        ℝ) : ℂ) = π / 4 * regCarlsonR (-3 / 2) (pair (3 / 2) (3 / 2)) (pair P Q) := by
  have hb : pair (3 / 2 : ℂ) (3 / 2) ∈ mvBetaConvergent := by
    intro i; fin_cases i <;> simp [pair]
  have hz : pair (P : ℂ) (Q : ℂ) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · simpa [Dirichlet.carlsonRightHalfPlane] using hP
    · simpa [Dirichlet.carlsonRightHalfPlane] using hQ
  rw [regCarlsonR_eq_regCarlsonRIntegral _ hb hz, regCarlsonRIntegral,
    regCarlsonDirichletAverage_pair_eq, Dirichlet.regEulerIntegral]
  have hG : Gamma (3 / 2 : ℂ) * Gamma (3 / 2) = π / 4 := by
    rw [Gamma_three_halves]
    linear_combination (1 / 4 : ℂ) * Gamma_one_half_mul_self
  rw [hG, ← mul_assoc, mul_inv_cancel₀ (by
    exact div_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero) (by norm_num)), one_mul,
    ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have h1 : 0 < 1 - u := by linarith [hu.2]
  have hw : 0 < u * P + (1 - u) * Q := by nlinarith [hu.1, hu.2]
  rw [Real.sqrt_mul hu.1.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  push_cast
  rw [ofReal_cpow hu.1.le, ofReal_cpow h1.le,
    show (u : ℂ) * P + (1 - u) * Q = ((u * P + (1 - u) * Q : ℝ) : ℂ) by push_cast; ring,
    ofReal_cpow hw.le]
  push_cast
  ring_nf

/-- **Exercise 9.3-2**: for coaxial circles of radii `a, b > 0` whose centers are a distance `h`
apart, with `r_±² = h² + (a ± b)²` and `r_- > 0`,
`∫₀^{2π} (h² + a² + b² - 2ab cos θ)^{-1/2} cos θ dθ = πab R_{-3/2}(3/2, 3/2; r_+², r_-²)`.
Hence the mutual inductance `M = (2πab/c²) ∫₀^{2π} (…)^{-1/2} cos θ dθ` equals
`2(πa²/c)(πb²/c) R_{-3/2}(3/2, 3/2; r_+², r_-²)`. -/
theorem integral_mutual_inductance {a b h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < h ^ 2 + (a - b) ^ 2) :
    ((∫ θ in (0 : ℝ)..2 * π,
        (h ^ 2 + a ^ 2 + b ^ 2 - 2 * a * b * Real.cos θ) ^ (-1 / 2 : ℝ) * Real.cos θ : ℝ) : ℂ) =
      π * a * b * carlsonR (-3 / 2) (pair (3 / 2) (3 / 2))
        (pair ((h ^ 2 + (a + b) ^ 2 : ℝ) : ℂ) ((h ^ 2 + (a - b) ^ 2 : ℝ) : ℂ)) := by
  set A := h ^ 2 + a ^ 2 + b ^ 2
  set w : ℝ → ℝ := fun θ => A - 2 * a * b * Real.cos θ
  have hw : ∀ θ, 0 < w θ := fun θ => by
    have := Real.cos_le_one θ
    have : 0 < a * b := mul_pos ha hb
    simp only [w, A]; nlinarith
  have hwc : Continuous w := by simp only [w]; fun_prop
  have hwd : ∀ θ, HasDerivAt w (2 * a * b * Real.sin θ) θ := fun θ => by
    have := ((Real.hasDerivAt_cos θ).const_mul (2 * a * b)).const_sub A
    convert this using 1; ring
  set g : ℝ → ℝ := fun θ => Real.sin θ ^ 2 * w θ ^ (-3 / 2 : ℝ)
  have hgc : Continuous g := by
    simp only [g]
    exact (Real.continuous_sin.pow 2).mul
      (hwc.rpow_const fun θ => Or.inl (hw θ).ne')
  -- Step 1: integration by parts
  have hIBP : (∫ θ in (0 : ℝ)..2 * π, w θ ^ (-1 / 2 : ℝ) * Real.cos θ) =
      a * b * ∫ θ in (0 : ℝ)..2 * π, g θ := by
    have hu : ∀ θ ∈ uIcc 0 (2 * π), HasDerivAt (fun θ => w θ ^ (-1 / 2 : ℝ))
        (2 * a * b * Real.sin θ * (-1 / 2) * w θ ^ ((-1 / 2 : ℝ) - 1)) θ := fun θ _ =>
      (hwd θ).rpow_const (Or.inl (hw θ).ne')
    have hv : ∀ θ ∈ uIcc 0 (2 * π), HasDerivAt Real.sin (Real.cos θ) θ := fun θ _ =>
      Real.hasDerivAt_sin θ
    have hu' : IntervalIntegrable (fun θ => 2 * a * b * Real.sin θ * (-1 / 2) *
        w θ ^ ((-1 / 2 : ℝ) - 1)) volume 0 (2 * π) :=
      (((continuous_const.mul Real.continuous_sin).mul continuous_const).mul
        (hwc.rpow_const fun θ => Or.inl (hw θ).ne')).intervalIntegrable _ _
    have hv' : IntervalIntegrable Real.cos volume 0 (2 * π) :=
      Real.continuous_cos.intervalIntegrable _ _
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv', Real.sin_two_pi,
      Real.sin_zero, mul_zero, mul_zero, sub_zero, zero_sub, ← intervalIntegral.integral_neg,
      ← intervalIntegral.integral_const_mul]
    congr 1; funext θ
    simp only [g]
    norm_num
    ring
  -- Step 2: the reflection `θ ↦ 2π - θ`
  have hsym : (∫ θ in (0 : ℝ)..2 * π, g θ) = 2 * ∫ θ in (0 : ℝ)..π, g θ := by
    have h2 := intervalIntegral.integral_comp_sub_left (a := 0) (b := π) g (2 * π)
    rw [show 2 * π - π = π by ring, sub_zero] at h2
    have hg : (fun θ => g (2 * π - θ)) = g := by
      funext θ; simp only [g, w, Real.sin_two_pi_sub, Real.cos_two_pi_sub, neg_sq]
    rw [hg] at h2
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := π)
      (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _), ← h2]
    ring
  -- Step 3: the substitution `s = (1 - cos θ)/2`
  set P := h ^ 2 + (a + b) ^ 2
  set Q := h ^ 2 + (a - b) ^ 2
  have hP : 0 < P := by positivity
  set G : ℝ → ℝ := fun s => 4 * (Real.sqrt (s * (1 - s)) * (s * P + (1 - s) * Q) ^ (-3 / 2 : ℝ))
  set φ : ℝ → ℝ := fun θ => (1 - Real.cos θ) / 2
  have hφd : ∀ θ ∈ Ioo 0 π, HasDerivWithinAt φ (Real.sin θ / 2) (Ioo 0 π) θ := fun θ _ => by
    have := ((Real.hasDerivAt_cos θ).const_sub 1).div_const 2
    exact (by convert this using 1; ring : HasDerivAt φ (Real.sin θ / 2) θ).hasDerivWithinAt
  have hφinj : InjOn φ (Ioo 0 π) := fun u hu v hv huv => by
    have : Real.cos u = Real.cos v := by simp only [φ] at huv; linarith
    exact Real.injOn_cos (Ioo_subset_Icc_self hu) (Ioo_subset_Icc_self hv) this
  have hφimg : φ '' Ioo 0 π = Ioo 0 1 := by
    ext s; constructor
    · rintro ⟨θ, hθ, rfl⟩
      have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
      have := Real.sin_sq_add_cos_sq θ
      have hc : Real.cos θ ^ 2 < 1 := by nlinarith
      constructor <;> simp only [φ] <;> nlinarith [sq_nonneg (Real.cos θ - 1),
        sq_nonneg (Real.cos θ + 1)]
    · rintro ⟨hs0, hs1⟩
      refine ⟨Real.arccos (1 - 2 * s), ⟨Real.arccos_pos.2 (by linarith),
        Real.arccos_lt_pi.2 (by linarith)⟩, ?_⟩
      simp only [φ]
      rw [Real.cos_arccos (by linarith) (by linarith)]
      ring
  have hsub : (∫ θ in (0 : ℝ)..π, g θ) = ∫ s in Ioo (0 : ℝ) 1, G s := by
    rw [← hφimg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hφd hφinj,
      intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have e1 : φ θ * (1 - φ θ) = (Real.sin θ / 2) ^ 2 := by
      simp only [φ]; have := Real.sin_sq_add_cos_sq θ; nlinarith
    have e2 : φ θ * P + (1 - φ θ) * Q = w θ := by simp only [φ, w, P, Q, A]; ring
    simp only [G, g, smul_eq_mul]
    rw [e1, e2, Real.sqrt_sq (by positivity), abs_of_pos (by positivity)]
    ring
  -- Step 4: the Euler integral
  have hE := integral_euler_three_halves hP hr
  have hint : (∫ θ in (0 : ℝ)..2 * π,
      (h ^ 2 + a ^ 2 + b ^ 2 - 2 * a * b * Real.cos θ) ^ (-1 / 2 : ℝ) * Real.cos θ) =
      8 * a * b * ∫ s in Ioo (0 : ℝ) 1,
        Real.sqrt (s * (1 - s)) * (s * P + (1 - s) * Q) ^ (-3 / 2 : ℝ) := by
    rw [show (fun θ => (h ^ 2 + a ^ 2 + b ^ 2 - 2 * a * b * Real.cos θ) ^ (-1 / 2 : ℝ) *
      Real.cos θ) = fun θ => w θ ^ (-1 / 2 : ℝ) * Real.cos θ from rfl, hIBP, hsym, hsub]
    simp only [G]
    rw [integral_const_mul]
    ring
  rw [hint]
  push_cast
  rw [hE]
  unfold carlsonR
  rw [sum_pair, show (3 / 2 : ℂ) + 3 / 2 = 2 + 1 by norm_num, Gamma_add_one _ two_ne_zero,
    Gamma_two']
  ring

end Carlson
