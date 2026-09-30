/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Standard

/-!
# The addition and duplication theorems for `R_F` (Carlson §9.6, §9.7)

**The addition theorem** (Theorem 9.7-1). For positive `x, y, z, λ, μ` with
`λμ - xy - xz - yz = 2 (xyz)^{1/2} (λ + μ + x + y + z)^{1/2}`,
`R_F(x + λ, y + λ, z + λ) + R_F(x + μ, y + μ, z + μ) = R_F(x, y, z)`.

Euler's differential equation `dλ/√P(λ) + dμ/√P(μ) = 0`, with `P(t) = (t + x)(t + y)(t + z)`,
has the algebraic solution `(λμ - f)² = 4g(λ + μ + e)`, where `e, f, g` are the elementary
symmetric functions of `x, y, z`. On the branch `λμ > f`, `μ` is an explicit function of `λ`,
and `μ → ∞` as `λ → 0`. Along this branch
`R_F(x + λ, …) + R_F(x + μ, …) = (1/2) ∫_λ^∞ P^{-1/2} + (1/2) ∫_μ^∞ P^{-1/2}`
has zero derivative and tends to `R_F(x, y, z)` as `λ → 0`.

**The duplication theorem** (Theorem 9.6-1) is the case `λ = μ = √x√y + √x√z + √y√z`:
`R_F(x, y, z) = 2 R_F(x + λ, y + λ, z + λ)`. It extends from positive reals to the whole slit
domain by uniqueness of holomorphic functions, one variable at a time. Iterating it gives
Carlson's Algorithm 9.6-2.

## Main results

* `Carlson.carlsonRF_add_carlsonRF`: Theorem 9.7-1.
* `Carlson.carlsonRF_duplication_ofReal`, `Carlson.carlsonRF_duplication`: Theorem 9.6-1.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §9.6, §9.7.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology
@[expose] public noncomputable section

namespace Carlson

/-- The cubic `P(t) = (t + x)(t + y)(t + z)` of the addition theorem. -/
def rfCubic (x y z t : ℝ) : ℝ := (t + x) * (t + y) * (t + z)

/-- The integrand `P(t)^{-1/2}` of `R_F` on a half-line. -/
def rfKernel (x y z t : ℝ) : ℝ := (Real.sqrt (rfCubic x y z t))⁻¹

section Positive

variable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
include hx hy hz

theorem rfCubic_pos {t : ℝ} (ht : 0 ≤ t) : 0 < rfCubic x y z t := by
  unfold rfCubic; positivity

omit hx hy hz in
theorem rfCubic_eq (t : ℝ) : rfCubic x y z t =
    t ^ 3 + (x + y + z) * t ^ 2 + (x * y + x * z + y * z) * t + x * y * z := by
  unfold rfCubic; ring

/-- `P(t)^{-1/2}` is integrable on `(0, ∞)`. -/
theorem integrableOn_rfKernel : IntegrableOn (rfKernel x y z) (Ioi 0) := by
  set m := min x (min y z)
  have hm : 0 < m := lt_min hx (lt_min hy hz)
  have hbd : IntegrableOn (fun t : ℝ => (t + m) ^ (-3 / 2 : ℝ)) (Ioi 0) := by
    have h := integrableOn_Ioi_rpow_of_lt (a := -3 / 2) (c := m) (by norm_num) hm
    rw [← (measurePreserving_add_right volume m).integrableOn_comp_preimage
      (measurableEmbedding_addRight m)] at h
    simpa [Function.comp_def] using h
  refine hbd.mono' ?_ ?_
  · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
    intro t ht
    have := rfCubic_pos hx hy hz (le_of_lt (show (0 : ℝ) < t from ht))
    refine ((Real.continuous_sqrt.continuousAt.comp ?_).inv₀ ?_).continuousWithinAt
    · unfold rfCubic; fun_prop
    · exact (Real.sqrt_pos.mpr this).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht : (0 : ℝ) < t := ht
    have hP := rfCubic_pos hx hy hz ht.le
    rw [rfKernel, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hP))]
    have hle : (t + m) ^ 3 ≤ rfCubic x y z t := by
      unfold rfCubic
      have h1 : t + m ≤ t + x := by linarith [min_le_left x (min y z)]
      have h2 : t + m ≤ t + y := by
        linarith [min_le_left y z, min_le_right x (min y z)]
      have h3 : t + m ≤ t + z := by
        linarith [min_le_right y z, min_le_right x (min y z)]
      have h0 : 0 ≤ t + m := by linarith
      calc (t + m) ^ 3 = (t + m) * (t + m) * (t + m) := by ring
        _ ≤ (t + x) * (t + y) * (t + z) := by
          apply mul_le_mul (mul_le_mul h1 h2 h0 (by linarith)) h3 h0 (by positivity)
    have htm : 0 < t + m := by linarith
    rw [show (-3 / 2 : ℝ) = -(3 / 2) by ring, Real.rpow_neg htm.le, Real.sqrt_eq_rpow]
    refine inv_anti₀ (by positivity) ?_
    calc (t + m) ^ (3 / 2 : ℝ) = ((t + m) ^ 3) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul htm.le]; norm_num
      _ ≤ rfCubic x y z t ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)

theorem continuousAt_rfKernel {t : ℝ} (ht : 0 ≤ t) : ContinuousAt (rfKernel x y z) t := by
  have hP := rfCubic_pos hx hy hz ht
  refine (Real.continuous_sqrt.continuousAt.comp ?_).inv₀ (Real.sqrt_pos.mpr hP).ne'
  unfold rfCubic; fun_prop

/-- `R_F` of shifted positive arguments as a real half-line integral:
`R_F(x + λ, y + λ, z + λ) = (1/2) ∫_λ^∞ P(t)^{-1/2} dt`. -/
theorem carlsonRF_add_eq_integral {l : ℝ} (hl : 0 ≤ l) :
    carlsonRF ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) =
      ((1 / 2 * ∫ t in Ioi l, rfKernel x y z t : ℝ) : ℂ) := by
  have hs : ∀ r : ℝ, 0 < r → ((r : ℝ) : ℂ) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  rw [carlsonRF_eq_integral (hs _ (by linarith)) (hs _ (by linarith)) (hs _ (by linarith)),
    ← integral_Ioi_zero_add (rfKernel x y z) l, ofReal_mul, ← integral_complex_ofReal]
  push_cast
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : (0 : ℝ) < t := ht
  have hc : ∀ r : ℝ, 0 < r → ((r : ℂ)) ^ (-1 / 2 : ℂ) = (((Real.sqrt r)⁻¹ : ℝ) : ℂ) := by
    intro r hr
    rw [show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hr.le,
      Real.rpow_neg hr.le, Real.sqrt_eq_rpow]
  rw [show (x : ℂ) + l + t = ((x + l + t : ℝ) : ℂ) by push_cast; ring,
    show (y : ℂ) + l + t = ((y + l + t : ℝ) : ℂ) by push_cast; ring,
    show (z : ℂ) + l + t = ((z + l + t : ℝ) : ℂ) by push_cast; ring,
    hc _ (by linarith), hc _ (by linarith), hc _ (by linarith), rfKernel, rfCubic]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  push_cast
  rw [show t + l + x = x + l + t by ring, show t + l + y = y + l + t by ring,
    show t + l + z = z + l + t by ring]
  simp only [mul_inv]

end Positive

/-! ### Euler's algebraic solution -/

section Euler

variable {e f g : ℝ}

/-- **The branch lemma**: on `(λμ - f)² = 4g(λ + μ + e)` with `λμ > f`,
`λ²μ - fλ - 2g = 2√g √P(λ)`, where `P(λ) = λ³ + eλ² + fλ + g`. -/
theorem sq_mul_sub_eq_two_sqrt (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 < g) {l m : ℝ} (hl : 0 < l)
    (hQ : (l * m - f) ^ 2 = 4 * g * (l + m + e)) (hpos : 0 < l * m - f) :
    l ^ 2 * m - f * l - 2 * g = 2 * (Real.sqrt g * Real.sqrt (l ^ 3 + e * l ^ 2 + f * l + g)) := by
  set X := l ^ 2 * m - f * l - 2 * g
  set P := l ^ 3 + e * l ^ 2 + f * l + g
  have hX2 : X ^ 2 = 4 * g * P := by simp only [X, P]; linear_combination l ^ 2 * hQ
  have hPg : g < P := by
    have : 0 < l ^ 3 + e * l ^ 2 + f * l := by positivity
    simp only [P]; linarith
  have hX : 0 ≤ X := by
    by_contra hc
    push Not at hc
    have h1 : 0 < X + 2 * g := by
      have : X + 2 * g = l * (l * m - f) := by simp only [X]; ring
      rw [this]; positivity
    have h2 : X ^ 2 < 4 * g * g := by nlinarith
    nlinarith
  rw [← Real.sqrt_mul hg.le, ← Real.sqrt_sq hX, hX2,
    show 4 * g * P = 2 ^ 2 * (g * P) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]

/-- The explicit branch `μ(λ) = λ^{-2} (fλ + 2g + 2√g √P(λ))` (Carlson's (9.7-12)). -/
def eulerMu (e f g l : ℝ) : ℝ :=
  (f * l + 2 * g + 2 * (Real.sqrt g * Real.sqrt (l ^ 3 + e * l ^ 2 + f * l + g))) / l ^ 2

variable (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 < g)
include he hf hg

theorem eulerMu_spec {l : ℝ} (hl : 0 < l) :
    0 < eulerMu e f g l ∧ 0 < l * eulerMu e f g l - f ∧
      (l * eulerMu e f g l - f) ^ 2 = 4 * g * (l + eulerMu e f g l + e) := by
  set S := Real.sqrt g * Real.sqrt (l ^ 3 + e * l ^ 2 + f * l + g)
  have hS0 : 0 ≤ S := by positivity
  have hS : S ^ 2 = g * (l ^ 3 + e * l ^ 2 + f * l + g) := by
    simp only [S]; rw [mul_pow, Real.sq_sqrt hg.le, Real.sq_sqrt (by positivity)]
  set M := eulerMu e f g l
  have hl2 : l ^ 2 ≠ 0 := by positivity
  have hM : l ^ 2 * M = f * l + 2 * g + 2 * S := by
    simp only [M, eulerMu]; rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ hl2
  have hlM : l * M - f = 2 * (g + S) / l := by
    field_simp; linear_combination hM
  refine ⟨by simp only [M, eulerMu]; positivity, by rw [hlM]; positivity, ?_⟩
  have key : l ^ 2 * ((l * M - f) ^ 2 - 4 * g * (l + M + e)) = 0 := by
    linear_combination 4 * hS + (4 * S + (l ^ 2 * M - (f * l + 2 * g + 2 * S))) * hM
  have := (mul_eq_zero.mp key).resolve_left hl2
  linarith

/-- Every solution on the branch `λμ > f` is `μ = μ(λ)`. -/
theorem eq_eulerMu {l m : ℝ} (hl : 0 < l) (hQ : (l * m - f) ^ 2 = 4 * g * (l + m + e))
    (hpos : 0 < l * m - f) : m = eulerMu e f g l := by
  have h := sq_mul_sub_eq_two_sqrt he hf hg hl hQ hpos
  unfold eulerMu
  rw [eq_div_iff (by positivity)]
  linarith

end Euler

/-! ### The addition theorem -/

theorem continuousAt_rfKernel' {x y z t : ℝ} (hP : 0 < rfCubic x y z t) :
    ContinuousAt (rfKernel x y z) t := by
  refine (Real.continuous_sqrt.continuousAt.comp ?_).inv₀ (Real.sqrt_pos.mpr hP).ne'
  unfold rfCubic; fun_prop

section AdditionProof

variable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
include hx hy hz

/-- The tail integral `F(λ) = ∫_λ^∞ P^{-1/2}`, written with a primitive so that it is defined
and differentiable near `0`. -/
private def tailF (x y z l : ℝ) : ℝ :=
  (∫ t in Ioi 0, rfKernel x y z t) - ∫ t in (0 : ℝ)..l, rfKernel x y z t

private theorem tailF_eq {l : ℝ} (hl : 0 ≤ l) :
    tailF x y z l = ∫ t in Ioi l, rfKernel x y z t := by
  have hint := integrableOn_rfKernel hx hy hz
  have hsplit := setIntegral_union (s := Ioc 0 l) (t := Ioi l) (f := rfKernel x y z)
    (Set.disjoint_left.mpr fun σ h1 h2 => not_lt.mpr h1.2 h2) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hl))
  rw [Ioc_union_Ioi_eq_Ioi hl] at hsplit
  rw [tailF, hsplit, intervalIntegral.integral_of_le hl]
  ring

private theorem hasDerivAt_tailF {l : ℝ} (hl : 0 ≤ l) :
    HasDerivAt (tailF x y z) (-rfKernel x y z l) l := by
  have hU : IsOpen {t : ℝ | 0 < rfCubic x y z t} :=
    isOpen_lt continuous_const (by unfold rfCubic; fun_prop)
  have hcont : ContinuousOn (rfKernel x y z) {t : ℝ | 0 < rfCubic x y z t} := fun t ht =>
    (continuousAt_rfKernel' ht).continuousWithinAt
  have hii : IntervalIntegrable (rfKernel x y z) volume 0 l := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [uIcc_of_le hl] at ht
    exact (continuousAt_rfKernel hx hy hz ht.1).continuousWithinAt
  have h := intervalIntegral.integral_hasDerivAt_right hii
    (hcont.stronglyMeasurableAtFilter hU l (rfCubic_pos hx hy hz hl))
    (continuousAt_rfKernel hx hy hz hl)
  unfold tailF
  exact h.const_sub (∫ t in Ioi 0, rfKernel x y z t)

private theorem hasDerivAt_tailF_add_eulerMu {l : ℝ} (hl : 0 < l) :
    HasDerivAt (fun l => tailF x y z l + tailF x y z
      (eulerMu (x + y + z) (x * y + x * z + y * z) (x * y * z) l)) 0 l := by
  set e := x + y + z
  set f := x * y + x * z + y * z
  set g := x * y * z
  have he : 0 ≤ e := by positivity
  have hf : 0 ≤ f := by positivity
  have hg : 0 < g := by positivity
  set μ := eulerMu e f g
  have hd : DifferentiableAt ℝ μ l := by
    have hP : l ^ 3 + e * l ^ 2 + f * l + g ≠ 0 := by positivity
    have hl2 : l ^ 2 ≠ 0 := by positivity
    show DifferentiableAt ℝ (fun l => (f * l + 2 * g +
      2 * (Real.sqrt g * Real.sqrt (l ^ 3 + e * l ^ 2 + f * l + g))) / l ^ 2) l
    refine DifferentiableAt.div ?_ (by fun_prop) hl2
    refine ((differentiableAt_id.const_mul f).add_const _).add (DifferentiableAt.const_mul ?_ _)
    exact (differentiableAt_const _).mul (DifferentiableAt.sqrt (by fun_prop) hP)
  set D := deriv μ l
  have hD : HasDerivAt μ D l := hd.hasDerivAt
  obtain ⟨hμ0, hpos, hQ⟩ := eulerMu_spec he hf hg hl
  -- the derivative of the algebraic relation vanishes
  have hq0 : HasDerivAt (fun t => (t * μ t - f) * (t * μ t - f) - 4 * g * (t + μ t + e)) 0 l := by
    refine (hasDerivAt_const l (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hl] with t ht
    have := (eulerMu_spec he hf hg ht).2.2
    simp only [μ]
    linear_combination this
  have hq1 : HasDerivAt (fun t => (t * μ t - f) * (t * μ t - f) - 4 * g * (t + μ t + e))
      (2 * (l * μ l - f) * (1 * μ l + l * D) - 4 * g * (1 + D + 0)) l := by
    have h1 := ((hasDerivAt_id' l).mul hD).sub_const f
    have h2 := (((hasDerivAt_id' l).add hD).add_const e).const_mul (4 * g)
    convert (h1.mul h1).sub h2 using 1
    simp only [Pi.mul_apply]
    ring
  have hE := hq1.unique hq0
  have hA := sq_mul_sub_eq_two_sqrt he hf hg hl hQ hpos
  have hA' := sq_mul_sub_eq_two_sqrt he hf hg hμ0 (m := l)
    (by rw [mul_comm]; linarith [hQ]) (by rw [mul_comm]; exact hpos)
  set Pl := l ^ 3 + e * l ^ 2 + f * l + g
  set Pm := μ l ^ 3 + e * μ l ^ 2 + f * μ l + g
  have hPl : 0 < Pl := by positivity
  have hPm : 0 < Pm := by positivity
  have hsg := Real.sqrt_pos.mpr hg
  have hsl := Real.sqrt_pos.mpr hPl
  have hsm := Real.sqrt_pos.mpr hPm
  -- `D √P(λ) = -√P(μ)`
  have hDD : D * Real.sqrt Pl = -Real.sqrt Pm := by
    have : Real.sqrt g * (D * Real.sqrt Pl + Real.sqrt Pm) = 0 := by
      linear_combination (1 / 4 : ℝ) * hE - (1 / 2 : ℝ) * D * hA - (1 / 2 : ℝ) * hA'
    have := (mul_eq_zero.mp this).resolve_left hsg.ne'
    linarith
  have hk : ∀ t : ℝ, 0 < t → rfKernel x y z t = (Real.sqrt (t ^ 3 + e * t ^ 2 + f * t + g))⁻¹ :=
    fun t _ => by rw [rfKernel, rfCubic_eq]
  have hsum := (hasDerivAt_tailF hx hy hz hl.le).add
    ((hasDerivAt_tailF hx hy hz hμ0.le).comp l hD)
  refine hsum.congr_deriv ?_
  rw [hk l hl, hk (μ l) hμ0]
  have hD2 : D = -Real.sqrt Pm / Real.sqrt Pl := by rw [eq_div_iff hsl.ne']; linarith
  rw [hD2]
  show -(Real.sqrt Pl)⁻¹ + -(Real.sqrt Pm)⁻¹ * (-Real.sqrt Pm / Real.sqrt Pl) = 0
  have : (Real.sqrt Pm)⁻¹ * (Real.sqrt Pm / Real.sqrt Pl) = (Real.sqrt Pl)⁻¹ := by
    field_simp
  rw [neg_div, mul_neg]
  simp only [neg_mul, neg_neg, this]
  ring

/-- **Carlson's Theorem 9.7-1 (addition theorem)**: for positive `x, y, z, λ, μ` with
`λμ - xy - xz - yz = 2 (xyz)^{1/2} (λ + μ + x + y + z)^{1/2}`,
`R_F(x + λ, y + λ, z + λ) + R_F(x + μ, y + μ, z + μ) = R_F(x, y, z)`. -/
theorem carlsonRF_add_carlsonRF {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (h13 : l * m - x * y - x * z - y * z =
      2 * Real.sqrt (x * y * z) * Real.sqrt (l + m + x + y + z)) :
    carlsonRF ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
      carlsonRF ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) =
        carlsonRF (x : ℂ) (y : ℂ) (z : ℂ) := by
  set e := x + y + z
  set f := x * y + x * z + y * z
  set g := x * y * z
  have he : 0 ≤ e := by positivity
  have hf : 0 ≤ f := by positivity
  have hg : 0 < g := by positivity
  have hsum : 0 < l + m + e := by positivity
  have hpos : 0 < l * m - f := by
    have : 0 < 2 * Real.sqrt g * Real.sqrt (l + m + x + y + z) := by
      have := Real.sqrt_pos.mpr hg
      have : 0 < Real.sqrt (l + m + x + y + z) := Real.sqrt_pos.mpr (by positivity)
      positivity
    simp only [f]; linarith
  have hQ : (l * m - f) ^ 2 = 4 * g * (l + m + e) := by
    have h13' : l * m - f = 2 * Real.sqrt g * Real.sqrt (l + m + e) := by
      have h1 : l * m - f = l * m - x * y - x * z - y * z := by simp only [f]; ring
      have h2 : l + m + e = l + m + x + y + z := by simp only [e]; ring
      rw [h1, h2, h13]
    rw [h13', mul_pow, mul_pow, Real.sq_sqrt hg.le, Real.sq_sqrt hsum.le]
    ring
  have hmμ := eq_eulerMu he hf hg hl hQ hpos
  set G := fun l => tailF x y z l + tailF x y z (eulerMu e f g l)
  set I₀ := ∫ t in Ioi 0, rfKernel x y z t
  -- `G` is constant on `(0, ∞)`
  have hconst : ∀ a b : ℝ, 0 < a → a ≤ b → G b = G a := by
    intro a b ha hab
    have hderiv : ∀ t, 0 < t → HasDerivAt G 0 t := fun t ht =>
      hasDerivAt_tailF_add_eulerMu hx hy hz ht
    refine constant_of_has_deriv_right_zero (fun t ht => ?_) (fun t ht => ?_) b ⟨hab, le_rfl⟩
    · exact (hderiv t (by linarith [ht.1])).continuousAt.continuousWithinAt
    · exact (hderiv t (by linarith [ht.1])).hasDerivWithinAt
  -- the limit at `0`
  have hint := integrableOn_rfKernel hx hy hz
  have hμinf : Tendsto (eulerMu e f g) (𝓝[>] 0) atTop := by
    have h1 : Tendsto (fun a : ℝ => 2 * g * (a⁻¹) ^ 2) (𝓝[>] 0) atTop :=
      Tendsto.const_mul_atTop (by positivity)
        ((tendsto_pow_atTop two_ne_zero).comp tendsto_inv_nhdsGT_zero)
    refine tendsto_atTop_mono' _ ?_ h1
    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    unfold eulerMu
    rw [le_div_iff₀ (by positivity), inv_pow, mul_assoc, inv_mul_cancel₀ (by positivity)]
    have : 0 ≤ Real.sqrt g * Real.sqrt (a ^ 3 + e * a ^ 2 + f * a + g) := by positivity
    have : 0 ≤ f * a := by positivity
    linarith
  have hlim : Tendsto G (𝓝[>] 0) (𝓝 (I₀ + 0)) := by
    refine Tendsto.add ?_ ?_
    · have := (hasDerivAt_tailF hx hy hz le_rfl).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [tailF, I₀] using this
    · have h := intervalIntegral_tendsto_integral_Ioi 0 hint hμinf
      have := h.const_sub I₀
      simpa [tailF, I₀] using this
  have hGl : G l = I₀ := by
    have hev : G =ᶠ[𝓝[>] 0] fun _ => G l := by
      filter_upwards [Ioo_mem_nhdsGT hl] with a ha
      exact (hconst a l ha.1 ha.2.le).symm
    have := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
    simpa using this.symm
  simp only [G] at hGl
  rw [← hmμ, tailF_eq hx hy hz hl.le, tailF_eq hx hy hz hm.le] at hGl
  rw [carlsonRF_add_eq_integral hx hy hz hl.le, carlsonRF_add_eq_integral hx hy hz hm.le]
  have h0 := carlsonRF_add_eq_integral hx hy hz (le_refl (0 : ℝ))
  simp only [add_zero] at h0
  rw [h0, ← ofReal_add]
  congr 1
  rw [← mul_add, hGl]

end AdditionProof

/-! ### The duplication theorem -/

/-- **Carlson's Theorem 9.6-1 for positive reals**: with `λ = √x√y + √x√z + √y√z`,
`R_F(x, y, z) = 2 R_F(x + λ, y + λ, z + λ)`. It is the case `λ = μ` of the addition theorem. -/
theorem carlsonRF_duplication_ofReal {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    carlsonRF (x : ℂ) (y : ℂ) (z : ℂ) = 2 * carlsonRF
      ((x + (√x * √y + √x * √z + √y * √z) : ℝ) : ℂ)
      ((y + (√x * √y + √x * √z + √y * √z) : ℝ) : ℂ)
      ((z + (√x * √y + √x * √z + √y * √z) : ℝ) : ℂ) := by
  set L := √x * √y + √x * √z + √y * √z
  have hL : 0 < L := by positivity
  have h13 : L * L - x * y - x * z - y * z =
      2 * Real.sqrt (x * y * z) * Real.sqrt (L + L + x + y + z) := by
    have hxs := Real.sq_sqrt hx.le
    have hys := Real.sq_sqrt hy.le
    have hzs := Real.sq_sqrt hz.le
    have hs : L + L + x + y + z = (√x + √y + √z) ^ 2 := by
      simp only [L]; nlinarith [hxs, hys, hzs]
    rw [hs, Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul hx.le]
    simp only [L]
    nlinarith [hxs, hys, hzs]
  have h := carlsonRF_add_carlsonRF hx hy hz hL hL h13
  rw [← h]
  ring

/-- Principal square roots of slit-plane numbers have positive real part. -/
theorem re_cpow_half_pos {x : ℂ} (hx : x ∈ slitPlane) : 0 < (x ^ (1 / 2 : ℂ)).re := by
  have hx0 : x ≠ 0 := slitPlane_ne_zero hx
  have harg : arg x ∈ Ioo (-π) π :=
    ⟨neg_pi_lt_arg x, lt_of_le_of_ne (arg_le_pi x) (mem_slitPlane_iff_arg.mp hx).1⟩
  rw [cpow_def_of_ne_zero hx0, exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have : (log x * (1 / 2)).im = arg x / 2 := by simp [log_im]; ring
    rw [this]; linarith [harg.1]
  · have : (log x * (1 / 2)).im = arg x / 2 := by simp [log_im]; ring
    rw [this]; linarith [harg.2]

theorem cpow_half_sq (x : ℂ) : (x ^ (1 / 2 : ℂ)) ^ 2 = x := by
  rw [one_div]; exact cpow_nat_inv_pow x two_ne_zero

/-- A product of two numbers with positive real parts lies in the slit plane. -/
theorem mul_mem_slitPlane_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    a * b ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra h
  push Not at h
  obtain ⟨hre, him⟩ := h
  simp only [mul_re, mul_im] at hre him
  have : a.re * (a.re * b.re - a.im * b.im) = b.re * (a.re ^ 2 + a.im ^ 2) := by
    linear_combination (-a.im) * him
  have hpos : 0 < b.re * (a.re ^ 2 + a.im ^ 2) := by positivity
  nlinarith

/-- Carlson's `λ = √x√y + √x√z + √y√z` with principal square roots. -/
def dupLambda (x y z : ℂ) : ℂ :=
  x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) + x ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) +
    y ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ)

theorem add_dupLambda (x y z : ℂ) :
    x + dupLambda x y z =
      (x ^ (1 / 2 : ℂ) + y ^ (1 / 2 : ℂ)) * (x ^ (1 / 2 : ℂ) + z ^ (1 / 2 : ℂ)) := by
  have := cpow_half_sq x
  unfold dupLambda
  linear_combination -this

theorem add_dupLambda_mem {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : x + dupLambda x y z ∈ slitPlane := by
  rw [add_dupLambda]
  refine mul_mem_slitPlane_of_re_pos ?_ ?_
  · rw [add_re]; linarith [re_cpow_half_pos hx, re_cpow_half_pos hy]
  · rw [add_re]; linarith [re_cpow_half_pos hx, re_cpow_half_pos hz]

theorem dupLambda_comm_left (x y z : ℂ) : dupLambda y x z = dupLambda x y z := by
  unfold dupLambda; ring

theorem dupLambda_comm_right (x y z : ℂ) : dupLambda x z y = dupLambda x y z := by
  unfold dupLambda; ring

/-- The duplication defect `R_F(x, y, z) - 2 R_F(x + λ, y + λ, z + λ)`. -/
private def dupDefect (x y z : ℂ) : ℂ :=
  carlsonRF x y z - 2 * carlsonRF (x + dupLambda x y z) (y + dupLambda x y z)
    (z + dupLambda x y z)

private theorem dupDefect_comm_left {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : dupDefect y x z = dupDefect x y z := by
  unfold dupDefect
  rw [dupLambda_comm_left, carlsonRF_comm_left hx hy hz,
    carlsonRF_comm_left (add_dupLambda_mem hx hy hz)
      (by rw [← dupLambda_comm_left]; exact add_dupLambda_mem hy hx hz)
      (by rw [← dupLambda_comm_right, ← dupLambda_comm_left, ← dupLambda_comm_right];
          exact add_dupLambda_mem hz hy hx)]

private theorem dupDefect_comm_right {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : dupDefect x z y = dupDefect x y z := by
  unfold dupDefect
  rw [dupLambda_comm_right, carlsonRF_comm_right hx hy hz,
    carlsonRF_comm_right (add_dupLambda_mem hx hy hz)
      (by rw [← dupLambda_comm_left]; exact add_dupLambda_mem hy hx hz)
      (by rw [← dupLambda_comm_right, ← dupLambda_comm_left, ← dupLambda_comm_right];
          exact add_dupLambda_mem hz hy hx)]

/-- `x ↦ R_F(f₁ x, f₂ x, f₃ x)` is analytic where the arguments are analytic and in the slit
plane. -/
theorem analyticAt_carlsonRF_comp {f₁ f₂ f₃ : ℂ → ℂ} {p : ℂ} (h₁ : AnalyticAt ℂ f₁ p)
    (h₂ : AnalyticAt ℂ f₂ p) (h₃ : AnalyticAt ℂ f₃ p) (m₁ : f₁ p ∈ slitPlane)
    (m₂ : f₂ p ∈ slitPlane) (m₃ : f₃ p ∈ slitPlane) :
    AnalyticAt ℂ (fun q => carlsonRF (f₁ q) (f₂ q) (f₃ q)) p := by
  simp_rw [carlsonRF_eq]
  refine analyticAt_const.mul (analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const ?_ ?_)
  · refine analyticAt_pi_iff.mpr fun i => ?_
    fin_cases i <;> simpa
  · intro i; fin_cases i <;> simpa

private theorem analyticOnNhd_dupDefect {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    AnalyticOnNhd ℂ (fun x => dupDefect x y z) slitPlane := by
  intro x hx
  have hs : AnalyticAt ℂ (fun w : ℂ => w ^ (1 / 2 : ℂ)) x :=
    analyticAt_id.cpow analyticAt_const hx
  have hL : AnalyticAt ℂ (fun w => dupLambda w y z) x := by
    unfold dupLambda
    exact ((hs.mul analyticAt_const).add (hs.mul analyticAt_const)).add analyticAt_const
  unfold dupDefect
  refine (analyticAt_carlsonRF_comp analyticAt_id analyticAt_const analyticAt_const hx hy hz).sub
    (analyticAt_const.mul (analyticAt_carlsonRF_comp (analyticAt_id.add hL)
      (analyticAt_const.add hL) (analyticAt_const.add hL) (add_dupLambda_mem hx hy hz) ?_ ?_))
  · rw [← dupLambda_comm_left]; exact add_dupLambda_mem hy hx hz
  · rw [← dupLambda_comm_right, ← dupLambda_comm_left, ← dupLambda_comm_right]
    exact add_dupLambda_mem hz hy hx

/-- Extension in the first variable from the positive reals to the slit plane. -/
private theorem dupDefect_extend {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (h : ∀ x : ℝ, 0 < x → dupDefect x y z = 0) {x : ℂ} (hx : x ∈ slitPlane) :
    dupDefect x y z = 0 := by
  have hEq : ∀ᶠ t : ℝ in 𝓝 1, (fun x => dupDefect x y z) (t : ℂ) = (fun _ => (0 : ℂ)) (t : ℂ) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact h t ht
  have := (analyticOnNhd_dupDefect hy hz).eqOn_of_eventuallyEq_ofReal analyticOnNhd_const
    (starConvex_one_slitPlane.isPathConnected (by simp)).isConnected.isPreconnected (by simp) hEq
  exact this hx

/-- The principal square root of a nonnegative real number is its real square root. -/
theorem ofReal_cpow_half {r : ℝ} (hr : 0 ≤ r) : ((r : ℂ)) ^ (1 / 2 : ℂ) = (√r : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hr,
    Real.sqrt_eq_rpow]

/-- **Carlson's Theorem 9.6-1 (duplication theorem)**: for `x, y, z` in the slit plane and
`λ = x^{1/2} y^{1/2} + x^{1/2} z^{1/2} + y^{1/2} z^{1/2}` with principal square roots,
`R_F(x, y, z) = 2 R_F(x + λ, y + λ, z + λ)`. -/
theorem carlsonRF_duplication {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    carlsonRF x y z = 2 * carlsonRF (x + dupLambda x y z) (y + dupLambda x y z)
      (z + dupLambda x y z) := by
  have hpos : ∀ r : ℝ, 0 < r → ((r : ℂ)) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  -- positive reals
  have h1 : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → dupDefect a b c = 0 := by
    intro a b c ha hb hc
    have hL : dupLambda a b c = ((√a * √b + √a * √c + √b * √c : ℝ) : ℂ) := by
      unfold dupLambda
      rw [ofReal_cpow_half ha.le, ofReal_cpow_half hb.le, ofReal_cpow_half hc.le]
      push_cast; ring
    unfold dupDefect
    rw [hL, carlsonRF_duplication_ofReal ha hb hc]
    push_cast
    ring
  -- extend in `x`, then `y`, then `z`
  have h2 : ∀ x' : ℂ, x' ∈ slitPlane → ∀ b c : ℝ, 0 < b → 0 < c → dupDefect x' b c = 0 :=
    fun x' hx' b c hb hc => dupDefect_extend (hpos b hb) (hpos c hc)
      (fun a ha => h1 a b c ha hb hc) hx'
  have h3 : ∀ x' y' : ℂ, x' ∈ slitPlane → y' ∈ slitPlane → ∀ c : ℝ, 0 < c →
      dupDefect x' y' c = 0 := by
    intro x' y' hx' hy' c hc
    rw [dupDefect_comm_left hy' hx' (hpos c hc)]
    exact dupDefect_extend hx' (hpos c hc) (fun b hb => by
      rw [dupDefect_comm_left hx' (hpos b hb) (hpos c hc)]; exact h2 x' hx' b c hb hc) hy'
  have h4 : dupDefect x y z = 0 := by
    rw [dupDefect_comm_right hx hz hy, dupDefect_comm_left hz hx hy]
    refine dupDefect_extend hx hy (fun c hc => ?_) hz
    rw [dupDefect_comm_left hx (hpos c hc) hy, dupDefect_comm_right hx hy (hpos c hc)]
    exact h3 x y hx hy c hc
  unfold dupDefect at h4
  linear_combination h4

/-! ### The duplication algorithm -/

/-- Homogeneity of `R_F` under positive real scaling: `R_F(λx, λy, λz) = λ^{-1/2} R_F(x, y, z)`. -/
theorem carlsonRF_mul_of_pos {l : ℝ} (hl : 0 < l) {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    carlsonRF (l * x) (l * y) (l * z) = (l : ℂ) ^ (-1 / 2 : ℂ) * carlsonRF x y z := by
  have hs : (![x, y, z] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  have h := regCarlsonR_smul_of_pos (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) hl hs
  have hp : (fun i => (l : ℂ) * (![x, y, z] : Fin 3 → ℂ) i) = ![l * x, l * y, l * z] := by
    funext i; fin_cases i <;> rfl
  rw [hp] at h
  unfold carlsonRF carlsonR
  rw [h]; ring

/-- One step of Carlson's Algorithm 9.6-2 on the square roots of the arguments of `R_F`:
`x' = (1/2)(x + y)^{1/2}(x + z)^{1/2}` and cyclically. -/
def dupStep (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (1 / 2 * √(p.1 + p.2.1) * √(p.1 + p.2.2), 1 / 2 * √(p.2.1 + p.1) * √(p.2.1 + p.2.2),
    1 / 2 * √(p.2.2 + p.1) * √(p.2.2 + p.2.1))

/-- The sequence of Carlson's Algorithm 9.6-2. -/
def dupSeq (x y z : ℝ) (n : ℕ) : ℝ × ℝ × ℝ := dupStep^[n] (x, y, z)

private def PosTriple (p : ℝ × ℝ × ℝ) : Prop := 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2

private theorem sq_dupStep_fst (p : ℝ × ℝ × ℝ) (hp : PosTriple p) :
    (dupStep p).1 ^ 2 = (p.1 + p.2.1) * (p.1 + p.2.2) / 4 := by
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [dupStep]
  rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  ring

private theorem sq_dupStep_snd (p : ℝ × ℝ × ℝ) (hp : PosTriple p) :
    (dupStep p).2.1 ^ 2 = (p.2.1 + p.1) * (p.2.1 + p.2.2) / 4 := by
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [dupStep]
  rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  ring

private theorem sq_dupStep_thd (p : ℝ × ℝ × ℝ) (hp : PosTriple p) :
    (dupStep p).2.2 ^ 2 = (p.2.2 + p.1) * (p.2.2 + p.2.1) / 4 := by
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [dupStep]
  rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  ring

private theorem dupStep_pos {p : ℝ × ℝ × ℝ} (hp : PosTriple p) : PosTriple (dupStep p) := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, ?_⟩ <;> simp only [dupStep] <;>
    exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by linarith)))
      (Real.sqrt_pos.mpr (by linarith))

/-- `R_F` is invariant under a step of the algorithm. -/
private theorem carlsonRF_dupStep {p : ℝ × ℝ × ℝ} (hp : PosTriple p) :
    carlsonRF (((dupStep p).1 ^ 2 : ℝ) : ℂ) (((dupStep p).2.1 ^ 2 : ℝ) : ℂ)
      (((dupStep p).2.2 ^ 2 : ℝ) : ℂ) =
      carlsonRF ((p.1 ^ 2 : ℝ) : ℂ) ((p.2.1 ^ 2 : ℝ) : ℂ) ((p.2.2 ^ 2 : ℝ) : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := hp
  set a := p.1; set b := p.2.1; set c := p.2.2
  have hd := carlsonRF_duplication_ofReal (pow_pos h1 2) (pow_pos h2 2) (pow_pos h3 2)
  rw [Real.sqrt_sq h1.le, Real.sqrt_sq h2.le, Real.sqrt_sq h3.le] at hd
  have hs : ∀ r : ℝ, 0 < r → ((r : ℂ)) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  have hpos := dupStep_pos (p := p) ⟨h1, h2, h3⟩
  have hm := carlsonRF_mul_of_pos (l := 4) (by norm_num) (hs _ (pow_pos hpos.1 2))
    (hs _ (pow_pos hpos.2.1 2)) (hs _ (pow_pos hpos.2.2 2))
  have e1 : ((a ^ 2 + (a * b + a * c + b * c) : ℝ) : ℂ) = 4 * (((dupStep p).1 ^ 2 : ℝ) : ℂ) := by
    rw [sq_dupStep_fst p ⟨h1, h2, h3⟩]; push_cast; ring
  have e2 : ((b ^ 2 + (a * b + a * c + b * c) : ℝ) : ℂ) =
      4 * (((dupStep p).2.1 ^ 2 : ℝ) : ℂ) := by
    rw [sq_dupStep_snd p ⟨h1, h2, h3⟩]; push_cast; ring
  have e3 : ((c ^ 2 + (a * b + a * c + b * c) : ℝ) : ℂ) =
      4 * (((dupStep p).2.2 ^ 2 : ℝ) : ℂ) := by
    rw [sq_dupStep_thd p ⟨h1, h2, h3⟩]; push_cast; ring
  have h4 : ((4 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = 1 / 2 := by
    rw [show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by norm_num),
      Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    push_cast; ring
  rw [hd, e1, e2, e3]
  push_cast at hm ⊢
  rw [hm]
  push_cast at h4
  rw [h4]
  ring

private def triMin (p : ℝ × ℝ × ℝ) : ℝ := min p.1 (min p.2.1 p.2.2)
private def triMax (p : ℝ × ℝ × ℝ) : ℝ := max p.1 (max p.2.1 p.2.2)
private def triSpread (p : ℝ × ℝ × ℝ) : ℝ :=
  |p.1 ^ 2 - p.2.1 ^ 2| + |p.1 ^ 2 - p.2.2 ^ 2| + |p.2.1 ^ 2 - p.2.2 ^ 2|

private theorem sqrt_mul_bounds {m M u v : ℝ} (hm : 0 ≤ m) (hu : 2 * m ≤ u) (huM : u ≤ 2 * M)
    (hv : 2 * m ≤ v) (hvM : v ≤ 2 * M) : m ≤ 1 / 2 * √u * √v ∧ 1 / 2 * √u * √v ≤ M := by
  have hu0 : 0 ≤ u := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hsu := Real.sqrt_nonneg u
  have hsv := Real.sqrt_nonneg v
  have hsu2 := Real.sq_sqrt hu0
  have hsv2 := Real.sq_sqrt hv0
  have hM : 0 ≤ M := by linarith
  constructor
  · have h1 : √(2 * m) ≤ √u := Real.sqrt_le_sqrt hu
    have h2 : √(2 * m) ≤ √v := Real.sqrt_le_sqrt hv
    have h3 : √(2 * m) * √(2 * m) = 2 * m := Real.mul_self_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg (2 * m)]
  · have h1 : √u ≤ √(2 * M) := Real.sqrt_le_sqrt huM
    have h2 : √v ≤ √(2 * M) := Real.sqrt_le_sqrt hvM
    have h3 : √(2 * M) * √(2 * M) = 2 * M := Real.mul_self_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg (2 * M)]

private theorem dupStep_bounds {p : ℝ × ℝ × ℝ} (hp : PosTriple p) :
    triMin p ≤ triMin (dupStep p) ∧ triMax (dupStep p) ≤ triMax p := by
  obtain ⟨h1, h2, h3⟩ := hp
  set m := triMin p; set M := triMax p
  have hm0 : 0 ≤ m := le_min h1.le (le_min h2.le h3.le)
  have ha : m ≤ p.1 := min_le_left _ _
  have hb : m ≤ p.2.1 := (min_le_right _ _).trans (min_le_left _ _)
  have hc : m ≤ p.2.2 := (min_le_right _ _).trans (min_le_right _ _)
  have ha' : p.1 ≤ M := le_max_left _ _
  have hb' : p.2.1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hc' : p.2.2 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have b1 := sqrt_mul_bounds hm0 (u := p.1 + p.2.1) (v := p.1 + p.2.2) (M := M)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have b2 := sqrt_mul_bounds hm0 (u := p.2.1 + p.1) (v := p.2.1 + p.2.2) (M := M)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have b3 := sqrt_mul_bounds hm0 (u := p.2.2 + p.1) (v := p.2.2 + p.2.1) (M := M)
    (by linarith) (by linarith) (by linarith) (by linarith)
  exact ⟨le_min b1.1 (le_min b2.1 b3.1), max_le b1.2 (max_le b2.2 b3.2)⟩

private theorem triSpread_dupStep {p : ℝ × ℝ × ℝ} (hp : PosTriple p) :
    triSpread (dupStep p) = triSpread p / 4 := by
  simp only [triSpread]
  rw [sq_dupStep_fst p hp, sq_dupStep_snd p hp, sq_dupStep_thd p hp]
  rw [show (p.1 + p.2.1) * (p.1 + p.2.2) / 4 - (p.2.1 + p.1) * (p.2.1 + p.2.2) / 4 =
      (p.1 ^ 2 - p.2.1 ^ 2) / 4 by ring,
    show (p.1 + p.2.1) * (p.1 + p.2.2) / 4 - (p.2.2 + p.1) * (p.2.2 + p.2.1) / 4 =
      (p.1 ^ 2 - p.2.2 ^ 2) / 4 by ring,
    show (p.2.1 + p.1) * (p.2.1 + p.2.2) / 4 - (p.2.2 + p.1) * (p.2.2 + p.2.1) / 4 =
      (p.2.1 ^ 2 - p.2.2 ^ 2) / 4 by ring]
  simp only [abs_div, abs_of_pos (show (0 : ℝ) < 4 by norm_num)]
  ring

private theorem triMax_sq_sub_triMin_sq_le (p : ℝ × ℝ × ℝ) :
    triMax p ^ 2 - triMin p ^ 2 ≤ triSpread p := by
  have hMc : triMax p = p.1 ∨ triMax p = p.2.1 ∨ triMax p = p.2.2 := by
    unfold triMax
    rcases max_choice p.1 (max p.2.1 p.2.2) with h | h <;> rw [h]
    · exact Or.inl rfl
    · rcases max_choice p.2.1 p.2.2 with h' | h' <;> rw [h'] <;> simp
  have hmc : triMin p = p.1 ∨ triMin p = p.2.1 ∨ triMin p = p.2.2 := by
    unfold triMin
    rcases min_choice p.1 (min p.2.1 p.2.2) with h | h <;> rw [h]
    · exact Or.inl rfl
    · rcases min_choice p.2.1 p.2.2 with h' | h' <;> rw [h'] <;> simp
  have e1 := abs_nonneg (p.1 ^ 2 - p.2.1 ^ 2)
  have e2 := abs_nonneg (p.1 ^ 2 - p.2.2 ^ 2)
  have e3 := abs_nonneg (p.2.1 ^ 2 - p.2.2 ^ 2)
  have g1 := le_abs_self (p.1 ^ 2 - p.2.1 ^ 2)
  have g2 := le_abs_self (p.1 ^ 2 - p.2.2 ^ 2)
  have g3 := le_abs_self (p.2.1 ^ 2 - p.2.2 ^ 2)
  have g1' := neg_abs_le (p.1 ^ 2 - p.2.1 ^ 2)
  have g2' := neg_abs_le (p.1 ^ 2 - p.2.2 ^ 2)
  have g3' := neg_abs_le (p.2.1 ^ 2 - p.2.2 ^ 2)
  unfold triSpread
  rcases hMc with h | h | h <;> rcases hmc with h' | h' | h' <;> rw [h, h'] <;> linarith

/-- **Carlson's Algorithm 9.6-2**: for positive `x₀, y₀, z₀`, the iteration
`x_{n+1} = (1/2)(x_n + y_n)^{1/2}(x_n + z_n)^{1/2}` (and cyclically) converges to a common limit
`L > 0`, and `R_F(x₀², y₀², z₀²) = 1/L`. -/
theorem tendsto_dupSeq {x₀ y₀ z₀ : ℝ} (hx : 0 < x₀) (hy : 0 < y₀) (hz : 0 < z₀) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (fun n => (dupSeq x₀ y₀ z₀ n).1) atTop (𝓝 L) ∧
      Tendsto (fun n => (dupSeq x₀ y₀ z₀ n).2.1) atTop (𝓝 L) ∧
      Tendsto (fun n => (dupSeq x₀ y₀ z₀ n).2.2) atTop (𝓝 L) ∧
      carlsonRF ((x₀ ^ 2 : ℝ) : ℂ) ((y₀ ^ 2 : ℝ) : ℂ) ((z₀ ^ 2 : ℝ) : ℂ) = ((L⁻¹ : ℝ) : ℂ) := by
  set q := dupSeq x₀ y₀ z₀
  have hsucc : ∀ n, q (n + 1) = dupStep (q n) := fun n =>
    Function.iterate_succ_apply' dupStep n (x₀, y₀, z₀)
  have hpos : ∀ n, PosTriple (q n) := by
    intro n; induction n with
    | zero => exact ⟨hx, hy, hz⟩
    | succ n ih => rw [hsucc]; exact dupStep_pos ih
  set mn := fun n => triMin (q n)
  set mx := fun n => triMax (q n)
  have hmn_mono : Monotone mn := monotone_nat_of_le_succ fun n => by
    simp only [mn]; rw [hsucc]; exact (dupStep_bounds (hpos n)).1
  have hmx_anti : Antitone mx := antitone_nat_of_succ_le fun n => by
    simp only [mx]; rw [hsucc]; exact (dupStep_bounds (hpos n)).2
  have hle : ∀ n, mn n ≤ mx n := fun n =>
    (min_le_left _ _).trans (le_max_left _ _)
  have hmn0 : 0 < mn 0 := lt_min hx (lt_min hy hz)
  obtain ⟨mL, hmL⟩ : ∃ l, Tendsto mn atTop (𝓝 l) :=
    ⟨_, tendsto_atTop_ciSup hmn_mono ⟨mx 0, fun _ ⟨n, hn⟩ => hn ▸ (hle n).trans (hmx_anti
      (Nat.zero_le n))⟩⟩
  obtain ⟨ML, hML⟩ : ∃ l, Tendsto mx atTop (𝓝 l) :=
    ⟨_, tendsto_atTop_ciInf hmx_anti ⟨mn 0, fun _ ⟨n, hn⟩ => hn ▸ (hmn_mono (Nat.zero_le n)).trans
      (hle n)⟩⟩
  have hmLpos : 0 < mL := lt_of_lt_of_le hmn0 (hmn_mono.ge_of_tendsto hmL 0)
  -- the spread tends to zero
  have hspread : ∀ n, triSpread (q n) = triSpread (q 0) / 4 ^ n := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [hsucc, triSpread_dupStep (hpos n), ih, pow_succ]; field_simp
  have hsp0 : Tendsto (fun n => triSpread (q n)) atTop (𝓝 0) := by
    rw [show (fun n => triSpread (q n)) = fun n => triSpread (q 0) / 4 ^ n from funext hspread]
    have : Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [div_eq_mul_inv, inv_pow] using this.const_mul (triSpread (q 0))
  have hgap : Tendsto (fun n => mx n ^ 2 - mn n ^ 2) atTop (𝓝 (ML ^ 2 - mL ^ 2)) :=
    (hML.pow 2).sub (hmL.pow 2)
  have hgap0 : ML ^ 2 - mL ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto hgap hsp0 (Filter.Eventually.of_forall fun n =>
      triMax_sq_sub_triMin_sq_le (q n))
  have hMLm : mL ≤ ML := le_of_tendsto_of_tendsto hmL hML (Filter.Eventually.of_forall hle)
  have hEq : ML = mL := by nlinarith
  subst hEq
  -- each coordinate is squeezed
  have hsq : ∀ f : ℝ × ℝ × ℝ → ℝ, (∀ n, triMin (q n) ≤ f (q n) ∧ f (q n) ≤ triMax (q n)) →
      Tendsto (fun n => f (q n)) atTop (𝓝 ML) := fun f hf =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le hmL hML (fun n => (hf n).1) (fun n => (hf n).2)
  have h1 := hsq Prod.fst fun n => ⟨min_le_left _ _, le_max_left _ _⟩
  have h2 := hsq (fun p => p.2.1) fun n =>
    ⟨(min_le_right _ _).trans (min_le_left _ _), (le_max_left _ _).trans (le_max_right _ _)⟩
  have h3 := hsq (fun p => p.2.2) fun n =>
    ⟨(min_le_right _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  refine ⟨ML, hmLpos, h1, h2, h3, ?_⟩
  -- the invariant and its limit
  have hinv : ∀ n, carlsonRF (((q n).1 ^ 2 : ℝ) : ℂ) (((q n).2.1 ^ 2 : ℝ) : ℂ)
      (((q n).2.2 ^ 2 : ℝ) : ℂ) = carlsonRF ((x₀ ^ 2 : ℝ) : ℂ) ((y₀ ^ 2 : ℝ) : ℂ)
        ((z₀ ^ 2 : ℝ) : ℂ) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [hsucc, carlsonRF_dupStep (hpos n), ih]
  have hML2 : (((ML ^ 2 : ℝ) : ℂ)) ∈ slitPlane := ofReal_mem_slitPlane.mpr (by positivity)
  have hcont : ContinuousAt (fun w : Fin 3 → ℂ => carlsonRF (w 0) (w 1) (w 2))
      ![((ML ^ 2 : ℝ) : ℂ), ((ML ^ 2 : ℝ) : ℂ), ((ML ^ 2 : ℝ) : ℂ)] := by
    have hs : (![((ML ^ 2 : ℝ) : ℂ), ((ML ^ 2 : ℝ) : ℂ), ((ML ^ 2 : ℝ) : ℂ)] : Fin 3 → ℂ) ∈
        carlsonRSlitDomain := by intro i; fin_cases i <;> exact hML2
    have := (analyticOnNhd_regCarlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) _ hs).continuousAt
    have hc2 : ContinuousAt (fun w : Fin 3 → ℂ =>
        Gamma (3 / 2) * regCarlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) w) _ :=
      continuousAt_const.mul this
    refine hc2.congr (Filter.Eventually.of_forall fun w => ?_)
    show Gamma (3 / 2) * regCarlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) w =
      carlsonRF (w 0) (w 1) (w 2)
    rw [carlsonRF_eq]
    congr 2
    funext i; fin_cases i <;> rfl
  have hvec : Tendsto (fun n => (![(((q n).1 ^ 2 : ℝ) : ℂ), (((q n).2.1 ^ 2 : ℝ) : ℂ),
      (((q n).2.2 ^ 2 : ℝ) : ℂ)] : Fin 3 → ℂ)) atTop
      (𝓝 ![((ML ^ 2 : ℝ) : ℂ), ((ML ^ 2 : ℝ) : ℂ), ((ML ^ 2 : ℝ) : ℂ)]) := by
    rw [tendsto_pi_nhds]
    intro i; fin_cases i
    · exact (continuous_ofReal.tendsto _).comp (h1.pow 2)
    · exact (continuous_ofReal.tendsto _).comp (h2.pow 2)
    · exact (continuous_ofReal.tendsto _).comp (h3.pow 2)
  have hlim := hcont.tendsto.comp hvec
  simp only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, hinv] at hlim
  have hval := tendsto_nhds_unique tendsto_const_nhds hlim
  have hML2' : 0 < ML ^ 2 := pow_pos hmLpos 2
  rw [hval, carlsonRF_self (by rw [ofReal_re]; exact hML2')]
  rw [show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hML2'.le,
    Real.rpow_neg hML2'.le, ← Real.sqrt_eq_rpow, Real.sqrt_sq hmLpos.le]

end Carlson
