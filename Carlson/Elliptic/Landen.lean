/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Addition

/-!
# Landen's transformation (Carlson §9.5)

**Theorem 9.5-1.** Let `x, y, z > 0`, `u = (x + y)/2`, and let `v, w > 0` satisfy
`v² + w² = z² + xy` and `vw = zu`, which is Carlson's (9.5-2) in squared form. Then for every
complex `t`,
`R_t(1/2, 1/2, -t; x², y², z²) = R_t(t + 1, -t, -t; u², v², w²)`.
It is stated in regularized form: both Dirichlet parameter vectors sum to `1 - t`. For `re t < 0`
the substitution `r = s(s + xy)/(s + u²)` transforms the single-integral representation (6.8-6)
of the left side into that of the right side. Both sides are entire in `t`.

The same substitution works when `v², w²` are complex conjugates in the slit plane, since then
`(s + v²)^t (s + w²)^t = |s + v²|^{2t}`; this covers `z` between `x` and `y`.

The case `t = -1/2` is Landen's transformation of `R_F` (9.5-4),
`R_F(x², y², z²) = R_F(u², v², w²)`. With `(z - x)(z - y) ≥ 0`, Carlson's explicit
`v ± w = (z ± x)^{1/2}(z ± y)^{1/2}` gives admissible `v, w`.

## Main results

* `Carlson.regCarlsonR_landen`: Theorem 9.5-1.
* `Carlson.carlsonRF_landen`, `Carlson.carlsonRF_landen_explicit`: (9.5-4).
* `Carlson.regCarlsonR_landen_of_cpow`, `Carlson.regCarlsonR_landen_conj`,
  `Carlson.carlsonRF_landen_conj`: Theorem 9.5-1 and (9.5-4) when `z` lies between `x` and `y`,
  so that `v², w²` are complex conjugates.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §9.5.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology
@[expose] public noncomputable section

namespace Carlson

section Substitution

variable {x y z v w : ℝ}

/-- Landen's substitution `r = s(s + xy)/(s + u²)`, `u = (x + y)/2`. -/
def landenSub (x y s : ℝ) : ℝ := s * (s + x * y) / (s + ((x + y) / 2) ^ 2)

variable (hx : 0 < x) (hy : 0 < y)
include hx hy

theorem landenSub_add_sq_left {s : ℝ} (hs : 0 < s) :
    x ^ 2 + landenSub x y s = (s + x * ((x + y) / 2)) ^ 2 / (s + ((x + y) / 2) ^ 2) := by
  unfold landenSub
  have : 0 < s + ((x + y) / 2) ^ 2 := by positivity
  field_simp
  ring

theorem landenSub_add_sq_right {s : ℝ} (hs : 0 < s) :
    y ^ 2 + landenSub x y s = (s + y * ((x + y) / 2)) ^ 2 / (s + ((x + y) / 2) ^ 2) := by
  unfold landenSub
  have : 0 < s + ((x + y) / 2) ^ 2 := by positivity
  field_simp
  ring

theorem landenSub_add_sq_third (hv2 : v ^ 2 + w ^ 2 = z ^ 2 + x * y)
    (hvw : v * w = z * ((x + y) / 2)) {s : ℝ} (hs : 0 < s) :
    z ^ 2 + landenSub x y s = (s + v ^ 2) * (s + w ^ 2) / (s + ((x + y) / 2) ^ 2) := by
  unfold landenSub
  have : 0 < s + ((x + y) / 2) ^ 2 := by positivity
  rw [eq_div_iff this.ne', add_mul, div_mul_cancel₀ _ this.ne']
  have hvw2 : v ^ 2 * w ^ 2 = z ^ 2 * ((x + y) / 2) ^ 2 := by rw [← mul_pow, hvw]; ring
  linear_combination (-s) * hv2 - hvw2

theorem hasDerivAt_landenSub {s : ℝ} (hs : 0 < s) :
    HasDerivAt (landenSub x y)
      ((s + x * ((x + y) / 2)) * (s + y * ((x + y) / 2)) / (s + ((x + y) / 2) ^ 2) ^ 2) s := by
  have hA : s + ((x + y) / 2) ^ 2 ≠ 0 := by positivity
  have h := (((hasDerivAt_id' s).mul ((hasDerivAt_id' s).add_const (x * y)))).div
    ((hasDerivAt_id' s).add_const (((x + y) / 2) ^ 2)) hA
  unfold landenSub
  convert h using 1
  simp only [Pi.mul_apply]
  field_simp
  ring

theorem landenSub_pos {s : ℝ} (hs : 0 < s) : 0 < landenSub x y s := by
  unfold landenSub; positivity

theorem injOn_landenSub : InjOn (landenSub x y) (Ioi 0) := by
  intro s₁ h₁ s₂ h₂ h
  have h₁ : (0 : ℝ) < s₁ := h₁
  have h₂ : (0 : ℝ) < s₂ := h₂
  set m := ((x + y) / 2) ^ 2
  have hm : 0 < m := by positivity
  unfold landenSub at h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have hP : 0 < s₁ * s₂ + m * (s₁ + s₂) + x * y * m := by positivity
  have : (s₁ - s₂) * (s₁ * s₂ + m * (s₁ + s₂) + x * y * m) = 0 := by linear_combination h
  have := (mul_eq_zero.mp this).resolve_right hP.ne'
  linarith

theorem image_landenSub : landenSub x y '' Ioi 0 = Ioi 0 := by
  ext r; constructor
  · rintro ⟨s, hs, rfl⟩; exact landenSub_pos hx hy hs
  · intro hr
    have hr : (0 : ℝ) < r := hr
    set m := ((x + y) / 2) ^ 2
    have hm : 0 < m := by positivity
    set D := Real.sqrt ((r - x * y) ^ 2 + 4 * r * m)
    have hD2 : D ^ 2 = (r - x * y) ^ 2 + 4 * r * m := Real.sq_sqrt (by positivity)
    have hDgt : |r - x * y| < D := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
    set s := ((r - x * y) + D) / 2
    have hs : 0 < s := by
      have := neg_abs_le (r - x * y)
      simp only [s]; linarith
    refine ⟨s, hs, ?_⟩
    unfold landenSub
    rw [div_eq_iff (by positivity)]
    simp only [s]
    linear_combination (1 / 4 : ℝ) * hD2

end Substitution

/-! ### Theorem 9.5-1 -/

private theorem cpow_ofReal_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (t : ℂ) :
    ((a / b : ℝ) : ℂ) ^ t = (a : ℂ) ^ t * ((b : ℂ) ^ t)⁻¹ := by
  rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg ha (inv_nonneg.mpr hb.le), ofReal_inv,
    inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hb.le]; exact Real.pi_pos.ne)]

/-- The positive-ray integrand of the left side of Theorem 9.5-1. -/
private def landenLeft (x y z : ℝ) (t : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ ((1 : ℂ) - 1) * ∏ i, ((![((x ^ 2 : ℝ) : ℂ), ((y ^ 2 : ℝ) : ℂ), ((z ^ 2 : ℝ) : ℂ)] :
    Fin 3 → ℂ) i + r) ^ (-(![1 / 2, 1 / 2, -t] : Fin 3 → ℂ) i)

/-- The positive-ray integrand of the right side of Theorem 9.5-1. -/
private def landenRight (u v w : ℝ) (t : ℂ) (s : ℝ) : ℂ :=
  (s : ℂ) ^ ((1 : ℂ) - 1) * ∏ i, ((![((u ^ 2 : ℝ) : ℂ), ((v ^ 2 : ℝ) : ℂ), ((w ^ 2 : ℝ) : ℂ)] :
    Fin 3 → ℂ) i + s) ^ (-(![t + 1, -t, -t] : Fin 3 → ℂ) i)

private theorem landen_pointwise {x y z v w : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hv2 : v ^ 2 + w ^ 2 = z ^ 2 + x * y) (hvw : v * w = z * ((x + y) / 2)) (t : ℂ)
    {s : ℝ} (hs : 0 < s) :
    |(s + x * ((x + y) / 2)) * (s + y * ((x + y) / 2)) / (s + ((x + y) / 2) ^ 2) ^ 2| •
      landenLeft x y z t (landenSub x y s) = landenRight ((x + y) / 2) v w t s := by
  set u := (x + y) / 2
  set A := s + u ^ 2
  set B := s + x * u
  set C := s + y * u
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hC : 0 < C := by positivity
  have hV : 0 < s + v ^ 2 := by positivity
  have hW : 0 < s + w ^ 2 := by positivity
  have e1 := landenSub_add_sq_left hx hy hs
  have e2 := landenSub_add_sq_right hx hy hs
  have e3 := landenSub_add_sq_third hx hy hv2 hvw hs
  simp only [landenLeft, landenRight, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sub_self,
    cpow_zero, one_mul]
  rw [show ((x ^ 2 : ℝ) : ℂ) + (landenSub x y s : ℂ) = ((B ^ 2 / A : ℝ) : ℂ) by
      rw [← e1]; push_cast; ring,
    show ((y ^ 2 : ℝ) : ℂ) + (landenSub x y s : ℂ) = ((C ^ 2 / A : ℝ) : ℂ) by
      rw [← e2]; push_cast; ring,
    show ((z ^ 2 : ℝ) : ℂ) + (landenSub x y s : ℂ) = (((s + v ^ 2) * (s + w ^ 2) / A : ℝ) : ℂ) by
      rw [← e3]; push_cast; ring,
    show ((u ^ 2 : ℝ) : ℂ) + (s : ℂ) = ((A : ℝ) : ℂ) by simp only [A]; push_cast; ring,
    show ((v ^ 2 : ℝ) : ℂ) + (s : ℂ) = ((s + v ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show ((w ^ 2 : ℝ) : ℂ) + (s : ℂ) = ((s + w ^ 2 : ℝ) : ℂ) by push_cast; ring]
  -- the two factors with exponent `-1/2`
  have hhalf : ∀ P : ℝ, 0 < P → ((P ^ 2 / A : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) =
      (((Real.sqrt A / P) : ℝ) : ℂ) := by
    intro P hP
    rw [show -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity), Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      Real.sqrt_div' _ hA.le, Real.sqrt_sq hP.le, inv_div]
  rw [neg_neg, hhalf B hB, hhalf C hC,
    cpow_ofReal_div (a := (s + v ^ 2) * (s + w ^ 2)) (by positivity) hA, ofReal_mul,
    mul_cpow_ofReal_nonneg hV.le hW.le]
  rw [abs_of_pos (by positivity), real_smul]
  have hsA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA.le
  have hAt : ((A : ℝ) : ℂ) ^ (-(t + 1)) = (((A : ℝ) : ℂ) ^ t)⁻¹ * ((A⁻¹ : ℝ) : ℂ) := by
    rw [show -(t + 1) = -t + (-1) by ring, cpow_add _ _ (by exact_mod_cast hA.ne'), cpow_neg,
      cpow_neg_one, ofReal_inv]
  rw [hAt]
  have hAc : ((A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hBc : ((B : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hCc : ((C : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hAt0 : ((A : ℝ) : ℂ) ^ t ≠ 0 := by
    rw [cpow_def_of_ne_zero hAc]; exact exp_ne_zero _
  have hsAc : ((Real.sqrt A : ℝ) : ℂ) * (Real.sqrt A : ℝ) = (A : ℂ) := by exact_mod_cast hsA
  generalize ((s + v ^ 2 : ℝ) : ℂ) ^ t = Vt
  generalize ((s + w ^ 2 : ℝ) : ℂ) ^ t = Wt
  generalize ((A : ℝ) : ℂ) ^ t = At at hAt0 ⊢
  push_cast
  field_simp
  linear_combination (Vt * Wt) * hsAc

/-- The substitution identity of the positive-ray integrals. -/
private theorem landen_integral {x y z v w : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hv2 : v ^ 2 + w ^ 2 = z ^ 2 + x * y) (hvw : v * w = z * ((x + y) / 2)) (t : ℂ) :
    ∫ r in Ioi (0 : ℝ), landenLeft x y z t r =
      ∫ s in Ioi (0 : ℝ), landenRight ((x + y) / 2) v w t s := by
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun s hs => (hasDerivAt_landenSub hx hy hs).hasDerivWithinAt) (injOn_landenSub hx hy)
    (landenLeft x y z t)
  rw [image_landenSub hx hy] at hsub
  rw [hsub]
  exact setIntegral_congr_fun measurableSet_Ioi fun s hs =>
    landen_pointwise hx hy hv2 hvw t hs

/-- The exponent–parameter point `(t, b(t))` of Theorem 9.5-1. -/
private def landenPoint (b : ℂ → Fin 3 → ℂ) (t : ℂ) : Option (Fin 3) → ℂ :=
  fun o => Option.elim o t (b t)

private theorem analyticOnNhd_landen {b : ℂ → Fin 3 → ℂ} (hb : ∀ i, AnalyticOnNhd ℂ (b · i) univ)
    {Z : Fin 3 → ℂ} (hZ : Z ∈ carlsonRSlitDomain) :
    AnalyticOnNhd ℂ (fun t => regCarlsonR t (b t) Z) univ := by
  have h := analyticOnNhd_regCarlsonR_exponent_parameters hZ
  have hp : AnalyticOnNhd ℂ (landenPoint b) univ := by
    intro t _
    refine analyticAt_pi_iff.mpr fun o => ?_
    cases o with
    | none => exact analyticAt_id
    | some i => exact hb i t (mem_univ t)
  exact fun t _ => (h (landenPoint b t) (mem_univ _)).comp (hp t (mem_univ t))

/-- **Carlson's Theorem 9.5-1 (Landen's transformation)** in regularized form: for positive
`x, y, z, v, w` with `v² + w² = z² + xy` and `vw = zu`, `u = (x + y)/2`, and every complex `t`,
`R_t(1/2, 1/2, -t; x², y², z²) = R_t(t + 1, -t, -t; u², v², w²)`. -/
theorem regCarlsonR_landen {x y z v w : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hv : 0 < v)
    (hw : 0 < w) (hv2 : v ^ 2 + w ^ 2 = z ^ 2 + x * y) (hvw : v * w = z * ((x + y) / 2)) (t : ℂ) :
    regCarlsonR t ![1 / 2, 1 / 2, -t] ![((x ^ 2 : ℝ) : ℂ), ((y ^ 2 : ℝ) : ℂ), ((z ^ 2 : ℝ) : ℂ)] =
      regCarlsonR t ![t + 1, -t, -t]
        ![((((x + y) / 2) ^ 2 : ℝ) : ℂ), ((v ^ 2 : ℝ) : ℂ), ((w ^ 2 : ℝ) : ℂ)] := by
  set Z : Fin 3 → ℂ := ![((x ^ 2 : ℝ) : ℂ), ((y ^ 2 : ℝ) : ℂ), ((z ^ 2 : ℝ) : ℂ)]
  set W : Fin 3 → ℂ := ![((((x + y) / 2) ^ 2 : ℝ) : ℂ), ((v ^ 2 : ℝ) : ℂ), ((w ^ 2 : ℝ) : ℂ)]
  have hs : ∀ r : ℝ, 0 < r → ((r : ℂ)) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  have hZ : Z ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hs _ (by positivity)
    · exact hs _ (by positivity)
    · exact hs _ (by positivity)
  have hW : W ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hs _ (by positivity)
    · exact hs _ (by positivity)
    · exact hs _ (by positivity)
  -- equality for `re t < 0`
  have hneg : ∀ t : ℂ, t.re < 0 → regCarlsonR t ![1 / 2, 1 / 2, -t] Z =
      regCarlsonR t ![t + 1, -t, -t] W := by
    intro t ht
    have hL := carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR (a := 1) (a' := -t)
      (b := ![1 / 2, 1 / 2, -t]) (z := Z) (by norm_num) (by simpa using ht)
      (by simp [Fin.sum_univ_three]; try ring) hZ
    have hR := carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR (a := 1) (a' := -t)
      (b := ![t + 1, -t, -t]) (z := W) (by norm_num) (by simpa using ht)
      (by simp [Fin.sum_univ_three]; try ring) hW
    have hI := landen_integral hx hy hv2 hvw t
    unfold carlsonRPositiveRayIntegral at hL hR
    have hG : Gamma 1 * Gamma (-t) ≠ 0 := by
      rw [Gamma_one, one_mul]
      refine Gamma_ne_zero fun m hm => ?_
      have := congrArg re hm
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [neg_neg] at hL hR
    have : (Gamma 1 * Gamma (-t)) * regCarlsonR t ![1 / 2, 1 / 2, -t] Z =
        (Gamma 1 * Gamma (-t)) * regCarlsonR t ![t + 1, -t, -t] W := by
      rw [← hL, ← hR]
      exact hI
    exact mul_left_cancel₀ hG this
  -- continuation in `t`
  have hF := analyticOnNhd_landen (b := fun t => ![1 / 2, 1 / 2, -t])
    (fun i => by fin_cases i <;> simp <;> fun_prop) hZ
  have hG := analyticOnNhd_landen (b := fun t => ![t + 1, -t, -t])
    (fun i => by fin_cases i <;> simp <;> fun_prop) hW
  have hev : (fun t => regCarlsonR t ![1 / 2, 1 / 2, -t] Z) =ᶠ[𝓝 (-1)]
      fun t => regCarlsonR t ![t + 1, -t, -t] W := by
    have : ∀ᶠ t : ℂ in 𝓝 (-1), t.re < 0 :=
      (continuous_re.tendsto (-1)).eventually (eventually_lt_nhds (by simp))
    filter_upwards [this] with t ht
    exact hneg t ht
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_univ (mem_univ _) hev
    (mem_univ t)

/-- **Landen's transformation of `R_F`** (9.5-4): for positive `x, y, z, v, w` with
`v² + w² = z² + xy` and `vw = z(x + y)/2`, `R_F(x², y², z²) = R_F(u², v², w²)`, `u = (x + y)/2`. -/
theorem carlsonRF_landen {x y z v w : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hv : 0 < v)
    (hw : 0 < w) (hv2 : v ^ 2 + w ^ 2 = z ^ 2 + x * y) (hvw : v * w = z * ((x + y) / 2)) :
    carlsonRF ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ) =
      carlsonRF ((((x + y) / 2) ^ 2 : ℝ) : ℂ) ((v ^ 2 : ℝ) : ℂ) ((w ^ 2 : ℝ) : ℂ) := by
  have h := regCarlsonR_landen hx hy hz hv hw hv2 hvw (-1 / 2)
  rw [carlsonRF_eq, carlsonRF_eq]
  congr 1
  convert h using 2 <;> (funext i; fin_cases i <;> simp <;> norm_num)

/-- Carlson's explicit parameters (9.5-2): if `(z - x)(z - y) ≥ 0`, then
`v = ((z + x)^{1/2}(z + y)^{1/2} + (z - x)^{1/2}(z - y)^{1/2})/2` and
`w = ((z + x)^{1/2}(z + y)^{1/2} - (z - x)^{1/2}(z - y)^{1/2})/2` are admissible in (9.5-4). -/
theorem carlsonRF_landen_explicit {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hzxy : 0 ≤ (z - x) * (z - y)) :
    carlsonRF ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ) =
      carlsonRF ((((x + y) / 2) ^ 2 : ℝ) : ℂ)
        ((((Real.sqrt ((z + x) * (z + y)) + Real.sqrt ((z - x) * (z - y))) / 2) ^ 2 : ℝ) : ℂ)
        ((((Real.sqrt ((z + x) * (z + y)) - Real.sqrt ((z - x) * (z - y))) / 2) ^ 2 : ℝ) : ℂ) := by
  set P := Real.sqrt ((z + x) * (z + y))
  set Q := Real.sqrt ((z - x) * (z - y))
  have hP2 : P ^ 2 = (z + x) * (z + y) := Real.sq_sqrt (by positivity)
  have hQ2 : Q ^ 2 = (z - x) * (z - y) := Real.sq_sqrt hzxy
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have hPQ : Q < P := Real.sqrt_lt_sqrt hzxy (by nlinarith)
  refine carlsonRF_landen hx hy hz (by linarith) (by linarith) ?_ ?_
  · linear_combination (1 / 2 : ℝ) * hP2 + (1 / 2 : ℝ) * hQ2
  · linear_combination (1 / 4 : ℝ) * hP2 - (1 / 4 : ℝ) * hQ2

/-! ### Complex conjugate nodes: the case `x < z < y` -/

open ComplexConjugate in
/-- For `z` in the slit plane, `z^t z̄^t = |z|^{2t}`. -/
theorem cpow_mul_conj_cpow {z : ℂ} (hz : z ∈ slitPlane) (t : ℂ) :
    z ^ t * (conj z) ^ t = ((normSq z : ℝ) : ℂ) ^ t := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hc0 : conj z ≠ 0 := (map_ne_zero _).2 hz0
  have hn : 0 < normSq z := normSq_pos.2 hz0
  rw [cpow_def_of_ne_zero hz0, cpow_def_of_ne_zero hc0,
    cpow_def_of_ne_zero (ofReal_ne_zero.2 hn.ne'), ← exp_add, log_conj _ (slitPlane_arg_ne_pi hz),
    ← add_mul, add_conj, ← ofReal_log hn.le, log_re, normSq_eq_norm_sq, Real.log_pow]
  push_cast
  ring

/-- The positive-ray integrand of the right side of Theorem 9.5-1 with complex nodes `V, W`. -/
private def landenRightC (u : ℝ) (V W : ℂ) (t : ℂ) (s : ℝ) : ℂ :=
  (s : ℂ) ^ ((1 : ℂ) - 1) * ∏ i, ((![((u ^ 2 : ℝ) : ℂ), V, W] : Fin 3 → ℂ) i + s) ^
    (-(![t + 1, -t, -t] : Fin 3 → ℂ) i)

private theorem landen_pointwise_gen {x y z : ℝ} {V W : ℂ} (hx : 0 < x) (hy : 0 < y) (t : ℂ)
    (hP : ∀ s : ℝ, 0 < s → (V + s) ^ t * (W + s) ^ t =
      ((s ^ 2 + (z ^ 2 + x * y) * s + (z * ((x + y) / 2)) ^ 2 : ℝ) : ℂ) ^ t)
    {s : ℝ} (hs : 0 < s) :
    |(s + x * ((x + y) / 2)) * (s + y * ((x + y) / 2)) / (s + ((x + y) / 2) ^ 2) ^ 2| •
      landenLeft x y z t (landenSub x y s) = landenRightC ((x + y) / 2) V W t s := by
  set u := (x + y) / 2
  set A := s + u ^ 2
  set B := s + x * u
  set C := s + y * u
  set P := s ^ 2 + (z ^ 2 + x * y) * s + (z * u) ^ 2
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hC : 0 < C := by positivity
  have hP0 : 0 < P := by positivity
  have e1 := landenSub_add_sq_left hx hy hs
  have e2 := landenSub_add_sq_right hx hy hs
  have e3 : z ^ 2 + landenSub x y s = P / A := by
    simp only [landenSub, P, A, u]; field_simp; ring
  simp only [landenLeft, landenRightC, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sub_self,
    cpow_zero, one_mul]
  rw [show ((x ^ 2 : ℝ) : ℂ) + (landenSub x y s : ℂ) = ((B ^ 2 / A : ℝ) : ℂ) by
      rw [← e1]; push_cast; ring,
    show ((y ^ 2 : ℝ) : ℂ) + (landenSub x y s : ℂ) = ((C ^ 2 / A : ℝ) : ℂ) by
      rw [← e2]; push_cast; ring,
    show ((z ^ 2 : ℝ) : ℂ) + (landenSub x y s : ℂ) = ((P / A : ℝ) : ℂ) by
      rw [← e3]; push_cast; ring,
    show ((u ^ 2 : ℝ) : ℂ) + (s : ℂ) = ((A : ℝ) : ℂ) by simp only [A]; push_cast; ring]
  have hhalf : ∀ Q : ℝ, 0 < Q → ((Q ^ 2 / A : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) =
      (((Real.sqrt A / Q) : ℝ) : ℂ) := by
    intro Q hQ
    rw [show -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity), Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      Real.sqrt_div' _ hA.le, Real.sqrt_sq hQ.le, inv_div]
  have hPs : (V + s) ^ t * (W + s) ^ t = ((P : ℝ) : ℂ) ^ t := hP s hs
  rw [hhalf B hB, hhalf C hC, cpow_ofReal_div (a := P) hP0.le hA, neg_neg, ← hPs]
  rw [abs_of_pos (by positivity), real_smul]
  have hsA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA.le
  have hAt : ((A : ℝ) : ℂ) ^ (-(t + 1)) = (((A : ℝ) : ℂ) ^ t)⁻¹ * ((A⁻¹ : ℝ) : ℂ) := by
    rw [show -(t + 1) = -t + (-1) by ring, cpow_add _ _ (by exact_mod_cast hA.ne'), cpow_neg,
      cpow_neg_one, ofReal_inv]
  rw [hAt]
  have hAc : ((A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hBc : ((B : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hCc : ((C : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hAt0 : ((A : ℝ) : ℂ) ^ t ≠ 0 := by
    rw [cpow_def_of_ne_zero hAc]; exact exp_ne_zero _
  have hsAc : ((Real.sqrt A : ℝ) : ℂ) * (Real.sqrt A : ℝ) = (A : ℂ) := by exact_mod_cast hsA
  generalize (V + s) ^ t = Vt
  generalize (W + s) ^ t = Wt
  generalize ((A : ℝ) : ℂ) ^ t = At at hAt0 ⊢
  push_cast
  field_simp
  linear_combination (Vt * Wt) * hsAc

/-- **Carlson's Theorem 9.5-1 with general nodes**: for positive `x, y, z` and nodes `V, W` in
the slit plane with `(s + V)^t (s + W)^t = (s² + (z² + xy)s + z²u²)^t` for all `s > 0` and all
complex `t` (so `V + W = z² + xy`, `VW = z²u²`), `R_t(1/2, 1/2, -t; x², y², z²) =
R_t(t + 1, -t, -t; u², V, W)` in regularized form. -/
theorem regCarlsonR_landen_of_cpow {x y z : ℝ} {V W : ℂ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hV : V ∈ slitPlane) (hW : W ∈ slitPlane)
    (hP : ∀ t : ℂ, ∀ s : ℝ, 0 < s → (V + s) ^ t * (W + s) ^ t =
      ((s ^ 2 + (z ^ 2 + x * y) * s + (z * ((x + y) / 2)) ^ 2 : ℝ) : ℂ) ^ t) (t : ℂ) :
    regCarlsonR t ![1 / 2, 1 / 2, -t] ![((x ^ 2 : ℝ) : ℂ), ((y ^ 2 : ℝ) : ℂ), ((z ^ 2 : ℝ) : ℂ)] =
      regCarlsonR t ![t + 1, -t, -t] ![((((x + y) / 2) ^ 2 : ℝ) : ℂ), V, W] := by
  set Z : Fin 3 → ℂ := ![((x ^ 2 : ℝ) : ℂ), ((y ^ 2 : ℝ) : ℂ), ((z ^ 2 : ℝ) : ℂ)]
  set N : Fin 3 → ℂ := ![((((x + y) / 2) ^ 2 : ℝ) : ℂ), V, W]
  have hs : ∀ r : ℝ, 0 < r → ((r : ℂ)) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  have hZ : Z ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hs _ (by positivity)
    · exact hs _ (by positivity)
    · exact hs _ (by positivity)
  have hN : N ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hs _ (by positivity)
    · exact hV
    · exact hW
  have hneg : ∀ t : ℂ, t.re < 0 → regCarlsonR t ![1 / 2, 1 / 2, -t] Z =
      regCarlsonR t ![t + 1, -t, -t] N := by
    intro t ht
    have hL := carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR (a := 1) (a' := -t)
      (b := ![1 / 2, 1 / 2, -t]) (z := Z) (by norm_num) (by simpa using ht)
      (by simp [Fin.sum_univ_three]; try ring) hZ
    have hR := carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR (a := 1) (a' := -t)
      (b := ![t + 1, -t, -t]) (z := N) (by norm_num) (by simpa using ht)
      (by simp [Fin.sum_univ_three]; try ring) hN
    have hI : ∫ r in Ioi (0 : ℝ), landenLeft x y z t r =
        ∫ s in Ioi (0 : ℝ), landenRightC ((x + y) / 2) V W t s := by
      have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
        (fun s hs => (hasDerivAt_landenSub hx hy hs).hasDerivWithinAt) (injOn_landenSub hx hy)
        (landenLeft x y z t)
      rw [image_landenSub hx hy] at hsub
      rw [hsub]
      exact setIntegral_congr_fun measurableSet_Ioi fun s hs =>
        landen_pointwise_gen hx hy t (hP t) hs
    unfold carlsonRPositiveRayIntegral at hL hR
    have hG : Gamma 1 * Gamma (-t) ≠ 0 := by
      rw [Gamma_one, one_mul]
      refine Gamma_ne_zero fun m hm => ?_
      have := congrArg re hm
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [neg_neg] at hL hR
    have : (Gamma 1 * Gamma (-t)) * regCarlsonR t ![1 / 2, 1 / 2, -t] Z =
        (Gamma 1 * Gamma (-t)) * regCarlsonR t ![t + 1, -t, -t] N := by
      rw [← hL, ← hR]
      exact hI
    exact mul_left_cancel₀ hG this
  have hF := analyticOnNhd_landen (b := fun t => ![1 / 2, 1 / 2, -t])
    (fun i => by fin_cases i <;> simp <;> fun_prop) hZ
  have hG := analyticOnNhd_landen (b := fun t => ![t + 1, -t, -t])
    (fun i => by fin_cases i <;> simp <;> fun_prop) hN
  have hev : (fun t => regCarlsonR t ![1 / 2, 1 / 2, -t] Z) =ᶠ[𝓝 (-1)]
      fun t => regCarlsonR t ![t + 1, -t, -t] N := by
    have : ∀ᶠ t : ℂ in 𝓝 (-1), t.re < 0 :=
      (continuous_re.tendsto (-1)).eventually (eventually_lt_nhds (by simp))
    filter_upwards [this] with t ht
    exact hneg t ht
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_univ (mem_univ _) hev
    (mem_univ t)

open ComplexConjugate in
/-- **Carlson's Theorem 9.5-1 with complex conjugate `v², w²`**: for positive `x, y, z` and `V`
in the slit plane with `2 re V = z² + xy` and `|V| = zu`, `u = (x + y)/2`,
`R_t(1/2, 1/2, -t; x², y², z²) = R_t(t + 1, -t, -t; u², V, V̄)` in regularized form. This is the
case `z` between `x` and `y`, where Carlson's `v, w` of (9.5-2) are complex conjugates. -/
theorem regCarlsonR_landen_conj {x y z : ℝ} {V : ℂ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hV : V ∈ slitPlane) (hre : 2 * V.re = z ^ 2 + x * y)
    (hnorm : normSq V = (z * ((x + y) / 2)) ^ 2) (t : ℂ) :
    regCarlsonR t ![1 / 2, 1 / 2, -t] ![((x ^ 2 : ℝ) : ℂ), ((y ^ 2 : ℝ) : ℂ), ((z ^ 2 : ℝ) : ℂ)] =
      regCarlsonR t ![t + 1, -t, -t] ![((((x + y) / 2) ^ 2 : ℝ) : ℂ), V, conj V] := by
  have hVc : conj V ∈ slitPlane := by
    rcases mem_slitPlane_iff.1 hV with h | h
    · exact mem_slitPlane_iff.2 (Or.inl (by simpa using h))
    · exact mem_slitPlane_iff.2 (Or.inr (by simpa using h))
  refine regCarlsonR_landen_of_cpow hx hy hz hV hVc (fun t s hs => ?_) t
  have hVs : V + s ∈ slitPlane := by
    rcases mem_slitPlane_iff.1 hV with h | h
    · exact mem_slitPlane_iff.2 (Or.inl (by simp; linarith))
    · exact mem_slitPlane_iff.2 (Or.inr (by simpa using h))
  rw [show conj V + (s : ℂ) = conj (V + s) by simp, cpow_mul_conj_cpow hVs]
  congr 2
  rw [normSq_apply] at hnorm ⊢
  simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
  nlinarith [hre, hnorm]

open ComplexConjugate in
/-- **Landen's transformation of `R_F` (9.5-4) with `x < z < y`**: Carlson's
`v ± w = (z ± x)^{1/2}(z ± y)^{1/2}` are then the complex conjugates
`v, w = ((z + x)^{1/2}(z + y)^{1/2} ± i (z - x)^{1/2}(y - z)^{1/2})/2`, and
`R_F(x², y², z²) = R_F(u², v², w²)`, `u = (x + y)/2`. -/
theorem carlsonRF_landen_conj {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxz : x < z)
    (hzy : z < y) :
    carlsonRF ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ) =
      carlsonRF ((((x + y) / 2) ^ 2 : ℝ) : ℂ)
        ((((√((z + x) * (z + y)) : ℂ) + I * √((z - x) * (y - z))) / 2) ^ 2)
        ((((√((z + x) * (z + y)) : ℂ) - I * √((z - x) * (y - z))) / 2) ^ 2) := by
  set a := √((z + x) * (z + y))
  set b := √((z - x) * (y - z))
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have ha2 : a ^ 2 = (z + x) * (z + y) := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = (z - x) * (y - z) := Real.sq_sqrt (by nlinarith)
  set v : ℂ := ((a : ℂ) + I * b) / 2
  have hvc : ((a : ℂ) - I * b) / 2 = conj v := by
    simp only [v, map_div₀, map_add, map_mul, conj_ofReal, conj_I, map_ofNat]; ring
  have hvre : 0 < v.re := by simp [v]; positivity
  have hV : v ^ 2 ∈ slitPlane := sq_mem_slitPlane_of_re_pos hvre
  have hre : 2 * (v ^ 2).re = z ^ 2 + x * y := by
    simp only [v, sq, mul_re, div_re, add_re, ofReal_re, mul_im, I_re, I_im, ofReal_im,
      div_im, add_im]
    norm_num
    nlinarith [ha2, hb2]
  have hnorm : normSq (v ^ 2) = (z * ((x + y) / 2)) ^ 2 := by
    rw [map_pow, normSq_apply]
    simp only [v, div_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, div_im, add_im,
      mul_im]
    norm_num
    nlinarith [ha2, hb2]
  have h := regCarlsonR_landen_conj hx hy hz hV hre hnorm (-1 / 2)
  rw [hvc, ← map_pow, carlsonRF_eq, carlsonRF_eq]
  congr 1
  convert h using 2 <;> (funext i; fin_cases i <;> simp <;> norm_num)

end Carlson
