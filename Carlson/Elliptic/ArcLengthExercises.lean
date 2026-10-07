/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.IntegralExercises
public import Carlson.Elliptic.Addition
public import Carlson.Elliptic.SchwarzChristoffel
public import Carlson.TwoVariable.QuadraticHybrid

/-!
# Arc-length exercises of Carlson's Section 8.3

The lemniscate arc length and the solution of `|dx/dt|^p + |x|^p = c^p` as R-functions, by the
substitutions `s = t²` and `u = s^p` in Formula 8.1-1 on a real segment.

## Main results

* `Carlson.integral_lemniscate_eq_carlsonRF`, `Carlson.four_mul_integral_lemniscate`:
  Exercise 8.3-7, the arc length `∫₀^r (1 - t⁴)^{-1/2} dt = R_F(r⁻² + 1, r⁻², r⁻² - 1)` and the
  perimeter `P = 2π R_K(1, 2)`. The periodicity of the lemniscatic sine is not formalized.
* `Carlson.integral_rpow_sub_abs_rpow`, `Carlson.hasDerivAt_integral_rpow_sub_abs_rpow`,
  `Carlson.integral_rpow_sub_rpow_quarter_period`: Exercise 8.3-8, the time
  `t = x R_{-1/p}(1/p, 1; c^p - |x|^p, c^p)` along the solution and the quarter-period
  `(π/p) csc(π/p)`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.3.
-/

open Complex MeasureTheory Set
open scoped Real

@[expose] public noncomputable section

namespace Carlson

/-- The lemniscate integrand after the substitution `s = t²`. -/
private theorem lemniscate_integrand {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (((1 - t ^ 4) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      1 / 2 * (((2 * t : ℝ) : ℂ) * (((t ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1) *
        ((1 - t ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1) * ((1 + t ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) := by
  have h1 : 0 < 1 - t ^ 2 := by nlinarith
  have h2 : 0 < 1 + t ^ 2 := by positivity
  have ht : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  rw [show 1 - t ^ 4 = (1 - t ^ 2) * (1 + t ^ 2) by ring, Real.mul_rpow h1.le h2.le, ofReal_mul,
    ofReal_cpow h1.le, ofReal_cpow h2.le, ofReal_pow, ofReal_sq_cpow ht0,
    show 2 * ((1 / 2 : ℂ) - 1) = -1 by ring, cpow_neg_one]
  push_cast
  field_simp
  ring_nf

/-- `r R_F(1 - r², 1 + r², 1)` as the lemniscate integral `∫₀^r (1 - t⁴)^{-1/2} dt`. -/
private theorem integral_lemniscate_eq_mul_carlsonRF {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((∫ t in Ioo 0 r, (1 - t ^ 4) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      r * carlsonRF ((1 - r ^ 2 : ℝ) : ℂ) ((1 + r ^ 2 : ℝ) : ℂ) 1 := by
  set b : Fin 3 → ℂ := fun _ => 1 / 2
  set z : Fin 3 → ℂ := ![1, 1, 1]
  set w : Fin 3 → ℂ := ![-1, 1, 0]
  set G : ℝ → ℂ := fun s => ((s - 0 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1) *
    ((r ^ 2 - s : ℝ) : ℂ) ^ ((1 : ℂ) - 1) * ∏ i, (z i + w i * (s : ℂ)) ^ (-b i)
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hseg : ∀ i, ∀ s ∈ Icc (0 : ℝ) (r ^ 2), z i + w i * (s : ℂ) ∈ slitPlane := by
    intro i s hs
    fin_cases i
    · simpa [z, w, sub_eq_add_neg] using
        ofReal_mem_slitPlane.mpr (by linarith [hs.2] : (0 : ℝ) < 1 - s)
    · simpa [z, w] using ofReal_mem_slitPlane.mpr (by linarith [hs.1] : (0 : ℝ) < 1 + s)
    · simp [z, w]
  have H := integral_Ioo_real_segment_eq_regCarlsonR (a := 1 / 2) (a' := 1) (b := b)
    (by norm_num) (by norm_num) (by simp [b]; norm_num) (by positivity) hseg
  have hsub := integral_Ioo_sq_eq G le_rfl hr0
  rw [← integral_complex_ofReal]
  have hI : ∫ t in Ioo 0 r, (((1 - t ^ 4) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      1 / 2 * ∫ t in Ioo 0 r, ((2 * t : ℝ) : ℂ) * G (t ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [lemniscate_integrand ht.1 (ht.2.trans hr1)]
    have hcs : ((r ^ 2 - t ^ 2 : ℝ) : ℂ) ^ ((1 : ℂ) - 1) = 1 := by simp
    simp only [G, b, z, w, sub_zero, hcs, mul_one, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_mul,
      add_zero, one_cpow]
    push_cast
    ring_nf
  rw [hI, ← hsub, show (0 : ℝ) ^ 2 = 0 by norm_num, H]
  have hn : (fun i => (z i + w i * ((r ^ 2 : ℝ) : ℂ)) / (z i + w i * ((0 : ℝ) : ℂ))) =
      ![((1 - r ^ 2 : ℝ) : ℂ), ((1 + r ^ 2 : ℝ) : ℂ), 1] := by
    funext i; fin_cases i <;> (simp [z, w]; try ring)
  have hsq : ((r ^ 2 - 0 : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + 1 - 1) = (r : ℂ) := by
    rw [sub_zero, add_sub_cancel_right, ofReal_pow, ofReal_sq_cpow hr0]; norm_num
  rw [hn, hsq, carlsonRF_eq, show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num,
    Gamma_add_one _ (by norm_num), show (-1 / 2 : ℂ) = -(1 / 2) by ring]
  simp [b, z, Gamma_one, Fin.prod_univ_three]
  ring

/-- **Exercise 8.3-7**: the arc length from the origin to the point at distance `r` on the
lemniscate `r² = cos 2θ` is
`s = ∫₀^r (1 - t⁴)^{-1/2} dt = R_F(r⁻² + 1, r⁻², r⁻² - 1)`, for `0 < r < 1`. -/
theorem integral_lemniscate_eq_carlsonRF {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((∫ t in Ioo 0 r, (1 - t ^ 4) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      carlsonRF (((r ^ 2)⁻¹ + 1 : ℝ) : ℂ) (((r ^ 2)⁻¹ : ℝ) : ℂ) (((r ^ 2)⁻¹ - 1 : ℝ) : ℂ) := by
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hl : 0 < (r ^ 2)⁻¹ := by positivity
  have hl1 : 1 < (r ^ 2)⁻¹ := by rw [lt_inv_comm₀ one_pos (by positivity), inv_one]; exact hr2
  have hA : (((r ^ 2)⁻¹ + 1 : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr (by linarith)
  have hB : (((r ^ 2)⁻¹ : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hl
  have hC : (((r ^ 2)⁻¹ - 1 : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr (by linarith)
  have hrot : carlsonRF (((r ^ 2)⁻¹ + 1 : ℝ) : ℂ) (((r ^ 2)⁻¹ : ℝ) : ℂ)
      (((r ^ 2)⁻¹ - 1 : ℝ) : ℂ) = carlsonRF (((r ^ 2)⁻¹ - 1 : ℝ) : ℂ)
        (((r ^ 2)⁻¹ + 1 : ℝ) : ℂ) (((r ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [← carlsonRF_perm (finRotate 3) hC hA hB]
    unfold carlsonRF; congr 1; funext i; fin_cases i <;> rfl
  have hscale := carlsonRF_mul_of_pos hl (x := ((1 - r ^ 2 : ℝ) : ℂ)) (y := ((1 + r ^ 2 : ℝ) : ℂ))
    (z := 1) (ofReal_mem_slitPlane.mpr (by linarith)) (ofReal_mem_slitPlane.mpr (by positivity))
    (by simp)
  have hpow : (((r ^ 2)⁻¹ : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = r := by
    rw [show (r ^ 2)⁻¹ = r⁻¹ ^ 2 by rw [inv_pow], ofReal_pow,
      ofReal_sq_cpow (inv_pos.mpr hr0), show 2 * (-1 / 2 : ℂ) = -1 by ring, cpow_neg_one]
    push_cast; exact inv_inv _
  have hr0' : r ^ 2 ≠ 0 := by positivity
  rw [hrot, integral_lemniscate_eq_mul_carlsonRF hr0 hr1, ← hpow, ← hscale]
  have hr : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  congr 1 <;> push_cast <;> field_simp

open TwoVariable in
/-- **Exercise 8.3-7**, the perimeter of the lemniscate `r² = cos 2θ`:
`P = 4 ∫₀¹ (1 - t⁴)^{-1/2} dt = 2π R_K(1, 2)`. -/
theorem four_mul_integral_lemniscate :
    ((4 * ∫ t in Ioo (0 : ℝ) 1, (1 - t ^ 4) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      2 * π * carlsonRK 1 2 := by
  set G : ℝ → ℂ := fun s => (s : ℂ) ^ ((1 / 2 : ℂ) - 1) * (1 - s : ℂ) ^ ((1 / 2 : ℂ) - 1) *
    ∏ i, ((1 - s : ℂ) + (s : ℂ) * pair (2 : ℂ) 1 i) ^ (-pair (1 / 2 : ℂ) (1 / 2) i)
  have hz : pair (2 : ℂ) 1 ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr (by norm_num : (0 : ℝ) < 2)
    · simp [pair]
  have h := carlsonRUnitIntervalIntegral_eq_Gamma_mul_regCarlsonR (a := 1 / 2) (a' := 1 / 2)
    (b := pair (1 / 2) (1 / 2)) (by norm_num) (by norm_num) (by simp [pair]) hz
  unfold carlsonRUnitIntervalIntegral at h
  have hsub := integral_Ioo_sq_eq G le_rfl one_pos
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, one_pow] at hsub
  have hI : ∫ t in Ioo (0 : ℝ) 1, (((1 - t ^ 4) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      1 / 2 * ∫ t in Ioo (0 : ℝ) 1, ((2 * t : ℝ) : ℂ) * G (t ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [lemniscate_integrand ht.1 ht.2]
    simp only [G, Fin.prod_univ_two, pair, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    push_cast
    rw [show (1 : ℂ) - (t : ℂ) ^ 2 + (t : ℂ) ^ 2 * 1 = 1 by ring, one_cpow, mul_one,
      show (1 : ℂ) - (t : ℂ) ^ 2 + (t : ℂ) ^ 2 * 2 = 1 + (t : ℂ) ^ 2 by ring]
  have hG : Gamma (1 / 2 : ℂ) * Gamma (1 / 2) = π := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal,
      Real.Gamma_one_half_eq, ← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [ofReal_mul, ← integral_complex_ofReal, hI, ← hsub, h, hG,
    carlsonRK_comm (ξ := 1) (η := 2) (by simp) (by simp),
    carlsonRK, carlsonR, sum_pair, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Gamma_one, one_mul,
    show (-(1 / 2) : ℂ) = -1 / 2 by ring]
  push_cast
  ring

/-- The substitution `u = s^p`, `p > 0`, on `(0, X)`. -/
theorem integral_Ioo_rpow_eq (G : ℝ → ℂ) {p X : ℝ} (hp : 0 < p) (hX : 0 < X) :
    ∫ u in Ioo 0 (X ^ p), G u = ∫ s in Ioo 0 X, ((p * s ^ (p - 1) : ℝ) : ℂ) * G (s ^ p) := by
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 X) measurableSet_Ioo
    (f := fun s => s ^ p) (f' := fun s => p * s ^ (p - 1))
    (fun s hs => (Real.hasDerivAt_rpow_const (Or.inl hs.1.ne')).hasDerivWithinAt)
    (fun a ha b hb hab => by
      have := congrArg (· ^ p⁻¹) hab
      simpa [Real.rpow_rpow_inv ha.1.le hp.ne', Real.rpow_rpow_inv hb.1.le hp.ne'] using this) G
  rw [show (fun s : ℝ => s ^ p) '' Ioo 0 X = Ioo 0 (X ^ p) by
    ext u; simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
      exact ⟨Real.rpow_pos_of_pos h1 p, Real.rpow_lt_rpow h1.le h2 hp⟩
    · rintro ⟨h1, h2⟩
      refine ⟨u ^ p⁻¹, ⟨Real.rpow_pos_of_pos h1 _, ?_⟩, Real.rpow_inv_rpow h1.le hp.ne'⟩
      rw [← Real.rpow_rpow_inv hX.le hp.ne']
      exact Real.rpow_lt_rpow h1.le h2 (inv_pos.mpr hp)] at hsub
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  have : 0 ≤ p * s ^ (p - 1) := mul_nonneg hp.le (Real.rpow_nonneg hs.1.le _)
  simp [abs_of_nonneg this, Complex.real_smul]

/-- Exercise 8.3-8 for `0 < x < c`, in regularized form. -/
private theorem integral_Ioo_rpow_sub_rpow {p c x : ℝ} (hp : 0 < p) (hx : 0 < x) (hxc : x < c) :
    ((∫ s in Ioo 0 x, (c ^ p - s ^ p) ^ (-1 / p) : ℝ) : ℂ) =
      x * (Gamma (1 / p + 1) * regCarlsonR (-(1 / p)) ![1 / (p : ℂ), 1]
        ![((c ^ p - x ^ p : ℝ) : ℂ), ((c ^ p : ℝ) : ℂ)]) := by
  have hc : 0 < c := hx.trans hxc
  have hp0 : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  have hcp : 0 < c ^ p := Real.rpow_pos_of_pos hc p
  have hxp : x ^ p < c ^ p := Real.rpow_lt_rpow hx.le hxc hp
  set b : Fin 2 → ℂ := ![1 / (p : ℂ), 1]
  set z : Fin 2 → ℂ := ![((c ^ p : ℝ) : ℂ), 1]
  set w : Fin 2 → ℂ := ![-1, 0]
  set G : ℝ → ℂ := fun u => ((u - 0 : ℝ) : ℂ) ^ (1 / (p : ℂ) - 1) *
    ((x ^ p - u : ℝ) : ℂ) ^ ((1 : ℂ) - 1) * ∏ i, (z i + w i * (u : ℂ)) ^ (-b i)
  have hseg : ∀ i, ∀ u ∈ Icc (0 : ℝ) (x ^ p), z i + w i * (u : ℂ) ∈ slitPlane := by
    intro i u hu
    fin_cases i
    · simpa [z, w, sub_eq_add_neg] using
        ofReal_mem_slitPlane.mpr (by linarith [hu.2] : (0 : ℝ) < c ^ p - u)
    · simp [z, w]
  have H := integral_Ioo_real_segment_eq_regCarlsonR (a := 1 / (p : ℂ)) (a' := 1) (b := b)
    (by simp; positivity) (by norm_num) (by simp [b]) (Real.rpow_pos_of_pos hx p) hseg
  have hsub := integral_Ioo_rpow_eq G hp hx
  rw [← integral_complex_ofReal]
  have hI : ∫ s in Ioo 0 x, (((c ^ p - s ^ p) ^ (-1 / p) : ℝ) : ℂ) =
      1 / (p : ℂ) * ∫ s in Ioo 0 x, ((p * s ^ (p - 1) : ℝ) : ℂ) * G (s ^ p) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    have hs0 := hs.1
    have hsp : s ^ p < c ^ p := Real.rpow_lt_rpow hs0.le (hs.2.trans hxc) hp
    have hcs : ((x ^ p - s ^ p : ℝ) : ℂ) ^ ((1 : ℂ) - 1) = 1 := by simp
    simp only [G, b, z, w, sub_zero, hcs, mul_one, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, add_zero, one_cpow]
    have e1 : (((s ^ p : ℝ) : ℂ)) ^ (1 / (p : ℂ) - 1) = ((s ^ (1 - p) : ℝ) : ℂ) := by
      rw [show (1 / (p : ℂ) - 1) = ((1 / p - 1 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow (Real.rpow_nonneg hs0.le _), ← Real.rpow_mul hs0.le]
      congr 2; field_simp
    have e2 : ((c ^ p : ℝ) : ℂ) + -1 * ((s ^ p : ℝ) : ℂ) = ((c ^ p - s ^ p : ℝ) : ℂ) := by
      push_cast; ring
    have e3 : (((c ^ p - s ^ p : ℝ) : ℂ)) ^ (-(1 / (p : ℂ))) =
        (((c ^ p - s ^ p) ^ (-1 / p) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by linarith)]; push_cast; ring_nf
    have e4 : s ^ (p - 1) * s ^ (1 - p) = 1 := by
      rw [← Real.rpow_add hs0]; simp
    rw [e1, e2, e3]
    calc _ = (1 / (p : ℂ)) * p * ((s ^ (p - 1) * s ^ (1 - p) : ℝ) : ℂ) *
        (((c ^ p - s ^ p) ^ (-1 / p) : ℝ) : ℂ) := by rw [e4]; field_simp; push_cast; ring
      _ = _ := by push_cast; ring
  rw [hI, ← hsub, H]
  have hcpow : ∀ q : ℝ, ((c ^ p : ℝ) : ℂ) ^ (q : ℂ) = ((c ^ (p * q) : ℝ) : ℂ) := fun q => by
    rw [← ofReal_cpow hcp.le, Real.rpow_mul hc.le]
  have hn : (fun i => (z i + w i * ((x ^ p : ℝ) : ℂ)) / (z i + w i * ((0 : ℝ) : ℂ))) =
      fun i => ((c ^ p : ℝ) : ℂ)⁻¹ * ![((c ^ p - x ^ p : ℝ) : ℂ), ((c ^ p : ℝ) : ℂ)] i := by
    have : ((c ^ p : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hcp.ne'
    funext i; fin_cases i <;> (simp [z, w]; try field_simp; try ring)
  have hsl : ![((c ^ p - x ^ p : ℝ) : ℂ), ((c ^ p : ℝ) : ℂ)] ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr (by simpa using hxp)
    · exact ofReal_mem_slitPlane.mpr hcp
  have hhom := regCarlsonR_smul_of_pos (-(1 / (p : ℂ))) b (inv_pos.mpr hcp) hsl
  simp only [ofReal_inv] at hhom
  rw [hn, hhom]
  have hx1 : ((x ^ p - 0 : ℝ) : ℂ) ^ (1 / (p : ℂ) + 1 - 1) = x := by
    rw [sub_zero, add_sub_cancel_right, show (1 / (p : ℂ)) = ((1 / p : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le, mul_one_div_cancel hp.ne',
      Real.rpow_one]
  have hc1 : ((c ^ p : ℝ) : ℂ)⁻¹ ^ (-(1 / (p : ℂ))) = c := by
    rw [inv_cpow _ _ (by simpa using (arg_ofReal_of_nonneg hcp.le).trans_ne Real.pi_ne_zero.symm),
      ← cpow_neg, neg_neg, show (1 / (p : ℂ)) = ((1 / p : ℝ) : ℂ) by push_cast; ring, hcpow,
      mul_one_div_cancel hp.ne', Real.rpow_one]
  have hc2 : (z 0 + w 0 * ((0 : ℝ) : ℂ)) ^ (-b 0) = (c : ℂ)⁻¹ := by
    simp only [ofReal_zero, mul_zero, add_zero, b, z, Matrix.cons_val_zero]
    rw [show -(1 / (p : ℂ)) = ((-(1 / p) : ℝ) : ℂ) by push_cast; ring, hcpow,
      show p * -(1 / p) = -1 by field_simp, Real.rpow_neg_one, ofReal_inv]
  rw [hx1, hc1, Fin.prod_univ_two, hc2, Gamma_add_one _ (one_div_ne_zero hp0)]
  simp only [w, b, z, Matrix.cons_val_one, Matrix.cons_val_fin_one, ofReal_zero, mul_zero,
    add_zero, one_cpow, Gamma_one]
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  field_simp

/-- **Exercise 8.3-8**: for real `p, c > 0` and `|x| < c`,
`∫₀^x (c^p - |s|^p)^{-1/p} ds = x R_{-1/p}(1/p, 1; c^p - |x|^p, c^p)`. The left side is the time
`t(x)` along the solution of `|dx/dt|^p + |x|^p = c^p` with `dx/dt = c` at `t = 0`
(see `hasDerivAt_integral_rpow_sub_abs_rpow`). -/
theorem integral_rpow_sub_abs_rpow {p c x : ℝ} (hp : 0 < p) (hx : |x| < c) :
    ((∫ s in (0)..x, (c ^ p - |s| ^ p) ^ (-1 / p) : ℝ) : ℂ) =
      x * carlsonR (-(1 / p)) ![1 / (p : ℂ), 1]
        ![((c ^ p - |x| ^ p : ℝ) : ℂ), ((c ^ p : ℝ) : ℂ)] := by
  have hpos : ∀ y : ℝ, 0 < y → y < c →
      ((∫ s in (0)..y, (c ^ p - |s| ^ p) ^ (-1 / p) : ℝ) : ℂ) =
        y * carlsonR (-(1 / p)) ![1 / (p : ℂ), 1]
          ![((c ^ p - |y| ^ p : ℝ) : ℂ), ((c ^ p : ℝ) : ℂ)] := by
    intro y hy hyc
    rw [intervalIntegral.integral_of_le hy.le, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo (g := fun s => (c ^ p - s ^ p) ^ (-1 / p))
        fun s hs => by simp [abs_of_pos hs.1],
      integral_Ioo_rpow_sub_rpow hp hy hyc, abs_of_pos hy, carlsonR]
    simp [Fin.sum_univ_two]
  rcases lt_trichotomy x 0 with hneg | rfl | hpos'
  · have h := hpos (-x) (by linarith) (by rw [abs_of_neg hneg] at hx; exact hx)
    rw [abs_neg] at h
    have hsymm : ∫ s in (0)..x, (c ^ p - |s| ^ p) ^ (-1 / p) =
        -∫ s in (0)..(-x), (c ^ p - |s| ^ p) ^ (-1 / p) := by
      rw [← intervalIntegral.integral_symm, ← neg_zero,
        ← intervalIntegral.integral_comp_neg (fun s => (c ^ p - |s| ^ p) ^ (-1 / p))]
      simp [abs_neg]
    rw [hsymm, ofReal_neg, h]
    push_cast; ring
  · simp
  · exact hpos x hpos' (lt_of_le_of_lt (le_abs_self x) hx)

/-- **Exercise 8.3-8**, the differential equation: `t(x) = ∫₀^x (c^p - |s|^p)^{-1/p} ds` has
derivative `(c^p - |x|^p)^{-1/p}` for `|x| < c`, so its inverse `x(t)` satisfies
`dx/dt = (c^p - |x|^p)^{1/p}`, hence `|dx/dt|^p + |x|^p = c^p` and `dx/dt = c` at `t = 0`. -/
theorem hasDerivAt_integral_rpow_sub_abs_rpow {p c x : ℝ} (hp : 0 < p) (hx : |x| < c) :
    HasDerivAt (fun y => ∫ s in (0)..y, (c ^ p - |s| ^ p) ^ (-1 / p))
      ((c ^ p - |x| ^ p) ^ (-1 / p)) x := by
  set f : ℝ → ℝ := fun s => (c ^ p - |s| ^ p) ^ (-1 / p)
  have hcont : ∀ s, |s| < c → ContinuousAt f s := by
    intro s hs
    have hlt : |s| ^ p < c ^ p := Real.rpow_lt_rpow (abs_nonneg s) hs hp
    exact (continuousAt_const.sub ((Real.continuousAt_rpow_const _ _ (Or.inr hp.le)).comp
      continuous_abs.continuousAt)).rpow_const (Or.inl (by simp; linarith))
  have hsub : uIcc 0 x ⊆ {s | |s| < c} := by
    intro s hs
    refine lt_of_le_of_lt (abs_le.mpr ?_) hx
    rcases mem_uIcc.mp hs with h | h
    · constructor <;> linarith [le_abs_self x, neg_abs_le x]
    · constructor <;> linarith [le_abs_self x, neg_abs_le x]
  have hopen : IsOpen {s : ℝ | |s| < c} := isOpen_lt continuous_abs continuous_const
  have hco : ContinuousOn f {s : ℝ | |s| < c} := fun s hs => (hcont s hs).continuousWithinAt
  exact intervalIntegral.integral_hasDerivAt_right (hco.mono hsub).intervalIntegrable
    (hco.stronglyMeasurableAtFilter hopen x hx) (hcont x hx)

/-- **Exercise 8.3-8**, the period: for `p > 1` and `c > 0` the quarter-period of the solution
of `|dx/dt|^p + |x|^p = c^p` is `∫₀^c (c^p - s^p)^{-1/p} ds = (π/p) csc(π/p)`, independent of
`c`; the solution has period `4 (π/p) csc(π/p)`. -/
theorem integral_rpow_sub_rpow_quarter_period {p c : ℝ} (hp : 1 < p) (hc : 0 < c) :
    ∫ s in Ioo 0 c, (c ^ p - s ^ p) ^ (-1 / p) = π / p / Real.sin (π / p) := by
  have hp0 : 0 < p := one_pos.trans hp
  have hpC : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp0.ne'
  have hcp : 0 < c ^ p := Real.rpow_pos_of_pos hc p
  set b : Fin 1 → ℂ := fun _ => 1
  set z : Fin 1 → ℂ := fun _ => 1
  set w : Fin 1 → ℂ := fun _ => 0
  set G : ℝ → ℂ := fun u => ((u - 0 : ℝ) : ℂ) ^ (1 / (p : ℂ) - 1) *
    ((c ^ p - u : ℝ) : ℂ) ^ ((1 - 1 / (p : ℂ)) - 1) * ∏ i, (z i + w i * (u : ℂ)) ^ (-b i)
  have H := integral_Ioo_real_segment_eq_regCarlsonR (a := 1 / (p : ℂ)) (a' := 1 - 1 / (p : ℂ))
    (b := b) (z := z) (w := w) (by simp; positivity)
    (by simp; exact inv_lt_one_of_one_lt₀ hp)
    (by simp [b]) hcp (fun i u _ => by simp [z, w])
  have hsub := integral_Ioo_rpow_eq G hp0 hc
  apply ofReal_injective
  rw [← integral_complex_ofReal]
  have hI : ∫ s in Ioo 0 c, (((c ^ p - s ^ p) ^ (-1 / p) : ℝ) : ℂ) =
      1 / (p : ℂ) * ∫ s in Ioo 0 c, ((p * s ^ (p - 1) : ℝ) : ℂ) * G (s ^ p) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    have hs0 := hs.1
    have hsp : s ^ p < c ^ p := Real.rpow_lt_rpow hs0.le hs.2 hp0
    simp only [G, b, z, w, sub_zero, Finset.univ_unique, Finset.prod_singleton, zero_mul,
      add_zero, one_cpow, mul_one]
    have e1 : (((s ^ p : ℝ) : ℂ)) ^ (1 / (p : ℂ) - 1) = ((s ^ (1 - p) : ℝ) : ℂ) := by
      rw [show (1 / (p : ℂ) - 1) = ((1 / p - 1 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow (Real.rpow_nonneg hs0.le _), ← Real.rpow_mul hs0.le]
      congr 2; field_simp
    have e3 : (((c ^ p - s ^ p : ℝ) : ℂ)) ^ (1 - 1 / (p : ℂ) - 1) =
        (((c ^ p - s ^ p) ^ (-1 / p) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by linarith)]; push_cast; ring_nf
    have e4 : s ^ (p - 1) * s ^ (1 - p) = 1 := by
      rw [← Real.rpow_add hs0]; simp
    rw [e1, e3]
    calc _ = (1 / (p : ℂ)) * p * ((s ^ (p - 1) * s ^ (1 - p) : ℝ) : ℂ) *
        (((c ^ p - s ^ p) ^ (-1 / p) : ℝ) : ℂ) := by rw [e4]; field_simp; push_cast; ring
      _ = _ := by push_cast; ring
  rw [hI, ← hsub, H]
  have hn : (fun i => (z i + w i * ((c ^ p : ℝ) : ℂ)) / (z i + w i * ((0 : ℝ) : ℂ))) =
      fun _ => (1 : ℂ) := by funext i; simp [z, w]
  rw [hn, regCarlsonR_const_node _ _ (by simp)]
  simp only [b, z, w, ofReal_zero, mul_zero, add_zero, one_cpow, Finset.prod_const_one, mul_one,
    Finset.univ_unique, Finset.sum_singleton, Gamma_one, inv_one,
    show 1 / (p : ℂ) + (1 - 1 / (p : ℂ)) - 1 = 0 by ring, cpow_zero]
  rw [Gamma_mul_Gamma_one_sub]
  push_cast
  field_simp

end Carlson
