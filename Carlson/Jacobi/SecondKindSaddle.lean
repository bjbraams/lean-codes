/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SecondKindBounds
public import Carlson.Jacobi.SaddleGeometry
public import SeveralComplexVariables.ContourIntegral
public import Carlson.Jacobi.SecondKindInfinity

/-!
# Deformation of the Euler integral onto the saddle curve

The second-kind Jacobi functions have an Euler representation over the unit interval once the
degree-shifted parameters lie in the right half-plane. The substitution
`t = ρ s / ((1 - s) + ρ s)` is a real change of variables for `ρ > 0`. The transformed integral
is holomorphic in `ρ` on the convex domain where `ρ` and `ρ / c` lie in the right half-plane,
with `c² (z - r) = z - s`, so the identity theorem extends the equality to complex `ρ`. At
`ρ = c` the transformed integrand runs along Carlson's saddle curve, where the per-degree
factor is bounded by `1 / (4 μ(z))`. This replaces the contour deformation of the
saddle-point argument without Cauchy's theorem at the singular endpoints.

## Main results

* `integral_jacobiMobiusIntegrand_ofReal`: the real change of variables.
* `analyticOnNhd_integral_jacobiMobiusIntegrand`: holomorphy in the Möbius parameter.
* `integral_jacobiMobiusIntegrand_eq`: the deformed integral equals the Euler integral.
* `jacobiSecondKind_eq_integral_mobius`: the second-kind functions on the saddle curve.
* `norm_jacobiMobiusKernel_le`: the sharp per-degree factor `1 / (4 μ(z))`.
* `exists_bound_jacobiSecondKind_of_isCompact`: degree-uniform bounds on compact sets.
* `exists_bound_jacobiSecondKind_exterior`: the bound `C (1/σ + ε)ⁿ` on closed elliptic
  exteriors, the upper half of Theorem 7.5-2 for `q̂ₙ`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  §7.4, the saddle-point argument for Theorem 7.4-3.
-/

@[expose] public noncomputable section
open Complex Set Filter Polynomial MeasureTheory
open scoped Topology Interval ComplexConjugate

namespace Carlson.TwoVariable

/-- The Euler integrand of the second-kind functions after the Möbius substitution
`t = ρ s / ((1 - s) + ρ s)`. For real `ρ > 0` this is a real change of variables; the
integrand is holomorphic in `ρ`. -/
def jacobiMobiusIntegrand (a b : ℂ) (m : ℕ) (A B ρ : ℂ) (s : ℝ) : ℂ :=
  ρ ^ (a + 1) * complexJacobiWeight a b s * ((1 - s) + ρ * s) ^ ((m : ℂ) - a - b - 2) *
    (ρ * s * A + (1 - s) * B) ^ (-(m : ℤ))

/-- For real positive `ρ` the Möbius substitution leaves the Euler integral unchanged. -/
theorem integral_jacobiMobiusIntegrand_ofReal {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (m : ℕ) {A B : ℂ} (hAB : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * A + (1 - t) * B ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ s in (0 : ℝ)..1, jacobiMobiusIntegrand a b m A B ρ s =
      ∫ t in (0 : ℝ)..1, complexJacobiWeight a b t * ((t : ℂ) * A + (1 - t) * B) ^ (-(m : ℤ)) := by
  set D : ℝ → ℝ := fun s => 1 + (ρ - 1) * s
  have hD (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : 0 < D s := by
    simp only [D]
    rcases le_total ρ 1 with h | h <;> nlinarith [hs.1, hs.2]
  set f : ℝ → ℝ := fun s => ρ * s / D s
  set f' : ℝ → ℝ := fun s => ρ / D s ^ 2
  have hf (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) 1) : HasDerivAt f (f' s) s := by
    rw [uIcc_of_le zero_le_one] at hs
    have h1 : HasDerivAt (fun s => ρ * s) ρ s := by simpa using (hasDerivAt_id s).const_mul ρ
    have h2 : HasDerivAt D (ρ - 1) s := by
      have := ((hasDerivAt_id s).const_mul (ρ - 1)).const_add 1
      rw [mul_one] at this
      exact this
    convert h1.div h2 (hD s hs).ne' using 1
    simp only [f', D]; ring
  have hf' : ContinuousOn f' (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro s hs; exact pow_ne_zero _ (hD s hs).ne'
  set g : ℝ → ℂ := fun t => complexJacobiWeight a b t * ((t : ℂ) * A + (1 - t) * B) ^ (-(m : ℤ))
  have hwc : Continuous (fun t : ℝ => complexJacobiWeight a b t) := by
    simpa only [sub_add_cancel] using
      (continuous_complexJacobiWeight_succ (α := a - 1) (β := b - 1)
        (by simp only [sub_re, one_re]; linarith) (by simp only [sub_re, one_re]; linarith))
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := by
    apply hwc.continuousOn.mul
    apply ContinuousOn.zpow₀ (by fun_prop)
    intro t ht; exact Or.inl (hAB t ht)
  have hfimg : f '' uIcc (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [uIcc_of_le zero_le_one] at hs
    have hDs := hD s hs
    refine ⟨div_nonneg (mul_nonneg hρ.le hs.1) hDs.le, (div_le_one hDs).mpr ?_⟩
    simp only [D]; nlinarith [hs.2]
  have hsub := intervalIntegral.integral_deriv_smul_comp' hf hf' (hg.mono hfimg)
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 1 := by simp [f, D, hρ.ne']
  rw [hf0, hf1] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le zero_le_one] at hs
  have hDs := hD s hs
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  simp only [g, f, f', jacobiMobiusIntegrand, complexJacobiWeight, real_smul,
    Function.comp_apply]
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst h0; simp [zero_cpow ha0]
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · subst h1
    have hD1 : D 1 = ρ := by simp [D]
    simp [hD1, hρ.ne', zero_cpow hb0]
  have hs0 : (0 : ℝ) < s := h0
  have hs1 : (0 : ℝ) < 1 - s := by linarith
  have hρ0 : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.ne'
  have hD0 : (D s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hDs.ne'
  have hDC : ((1 : ℂ) - s) + ρ * s = (D s : ℂ) := by simp only [D]; push_cast; ring
  set L : ℂ := (ρ : ℂ) * s * A + (1 - s) * B
  have hx1 : (1 : ℂ) - ((ρ * s / D s : ℝ) : ℂ) = (((1 - s) / D s : ℝ) : ℂ) := by
    push_cast; field_simp; simp only [D]; push_cast; ring
  have hxL : ((ρ * s / D s : ℝ) : ℂ) * A + (((1 - s) / D s : ℝ) : ℂ) * B = L / D s := by
    push_cast; field_simp; rfl
  have hdiv (x : ℝ) (hx : 0 ≤ x) (c : ℂ) :
      (((x / D s : ℝ)) : ℂ) ^ c = (x : ℂ) ^ c * ((D s : ℂ) ^ c)⁻¹ := by
    rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hx (inv_nonneg.mpr hDs.le),
      ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hDs.le]; exact Real.pi_pos.ne)]
  rw [hx1, hxL, hdiv _ (mul_nonneg hρ.le hs0.le), hdiv _ hs1.le, ofReal_mul,
    mul_cpow_ofReal_nonneg hρ.le hs0.le, hDC, ofReal_sub, ofReal_one]
  rw [cpow_add _ _ hρ0, cpow_one, cpow_sub _ _ hD0, cpow_sub _ _ hD0, cpow_sub _ _ hD0,
    cpow_natCast, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast, div_zpow]
  have hDa : (D s : ℂ) ^ a ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  have hDb : (D s : ℂ) ^ b ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  simp only [zpow_neg, zpow_natCast, ofReal_div, ofReal_pow]
  field_simp

/-- A root `c` of `c² A = B` in the right half-plane keeps the Möbius resolvent away from
zero whenever `ρ / c` also lies in the right half-plane. -/
theorem mobius_resolvent_ne_zero {A B c ρ : ℂ} (hA : A ≠ 0) (hc : 0 < c.re)
    (hcAB : c ^ 2 * A = B) (hρc : 0 < (ρ / c).re) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ρ * s * A + (1 - s) * B ≠ 0 := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have he : ρ * s * A + (1 - s) * B = A * c * ((s : ℂ) * (ρ / c) + (1 - s) * c) := by
    rw [← hcAB]; field_simp
  rw [he]
  refine mul_ne_zero (mul_ne_zero hA hc0) (fun h => ?_)
  have hre := congrArg re h
  simp only [add_re, mul_re, ofReal_re, ofReal_im, sub_re, one_re, sub_im, one_im, zero_mul,
    sub_zero, zero_re, sub_self] at hre
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst h0; simp at hre; linarith
  · nlinarith [hs.2, mul_pos h0 hρc]

/-- The Möbius-transformed Euler integral is holomorphic in `ρ` on the domain where both
`ρ` and `ρ / c` lie in the right half-plane. -/
theorem analyticOnNhd_integral_jacobiMobiusIntegrand {a b : ℂ} (ha : -1 < a.re)
    (hb : -1 < b.re) (m : ℕ) {A B c : ℂ} (hA : A ≠ 0) (hc : 0 < c.re)
    (hcAB : c ^ 2 * A = B) :
    AnalyticOnNhd ℂ (fun ρ => ∫ s in (0 : ℝ)..1, jacobiMobiusIntegrand a b m A B ρ s)
      {ρ | 0 < ρ.re ∧ 0 < (ρ / c).re} := by
  set U := {ρ : ℂ | 0 < ρ.re ∧ 0 < (ρ / c).re}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_const (continuous_re.comp (continuous_id.div_const c)))
  set W : Set (ℂ × ℂ) := {p | (1 - p.2) + p.1 * p.2 ∈ slitPlane ∧
    p.1 * p.2 * A + (1 - p.2) * B ≠ 0}
  set H : ℂ × ℂ → ℂ := fun p => ((1 - p.2) + p.1 * p.2) ^ ((m : ℂ) - a - b - 2) *
    ((p.1 * p.2 * A + (1 - p.2) * B) ^ m)⁻¹
  have hH : AnalyticOnNhd ℂ H W := by
    rintro ⟨ρ, w⟩ ⟨h1, h2⟩
    apply AnalyticAt.mul
    · exact AnalyticAt.cpow ((analyticAt_const.sub analyticAt_snd).add
        (analyticAt_fst.mul analyticAt_snd)) analyticAt_const h1
    · exact (AnalyticAt.pow (((analyticAt_fst.mul analyticAt_snd).mul analyticAt_const).add
        ((analyticAt_const.sub analyticAt_snd).mul analyticAt_const)) m).inv (pow_ne_zero _ h2)
  have hW : ∀ ρ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (ρ, (t : ℂ)) ∈ W := by
    intro ρ hρ t ht
    refine ⟨Or.inl ?_, mobius_resolvent_ne_zero hA hc hcAB hρ.2 ht⟩
    simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero]
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1; simpa using hρ.1
    · nlinarith [ht.1, hρ.1]
  have hint := analyticOnNhd_integral_mul_compact_kernel (μ := volume) isCompact_Icc
    ((integrableOn_Icc_iff_integrableOn_Ioc).mpr (intervalIntegrable_complexJacobiWeight ha hb).1)
    continuous_ofReal.continuousOn hU hH hW
  have hpow : AnalyticOnNhd ℂ (fun ρ : ℂ => ρ ^ (a + 1)) U := fun ρ hρ =>
    AnalyticAt.cpow analyticAt_id analyticAt_const (Or.inl hρ.1)
  refine (hpow.mul hint).congr hU ?_
  intro ρ hρ
  simp only [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
  simp only [jacobiMobiusIntegrand, H, zpow_neg, zpow_natCast]
  ring

/-- Deformation of the Euler integral: for every `ρ` with `ρ` and `ρ / c` in the right
half-plane, the Möbius-transformed integral equals the Euler integral over the unit interval.
The proof uses a real change of variables for `ρ > 0` and the identity theorem. -/
theorem integral_jacobiMobiusIntegrand_eq {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (m : ℕ) {A B c : ℂ} (hA : A ≠ 0) (hc : 0 < c.re) (hcAB : c ^ 2 * A = B)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hρc : 0 < (ρ / c).re) :
    ∫ s in (0 : ℝ)..1, jacobiMobiusIntegrand a b m A B ρ s =
      ∫ t in (0 : ℝ)..1, complexJacobiWeight a b t * ((t : ℂ) * A + (1 - t) * B) ^ (-(m : ℤ)) := by
  set U := {ρ : ℂ | 0 < ρ.re ∧ 0 < (ρ / c).re}
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hreal (x : ℝ) (hx : 0 < x) : (x : ℂ) ∈ U := by
    refine ⟨by simpa using hx, ?_⟩
    rw [div_re]
    simp only [ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos hx hc) (normSq_pos.mpr hc0)
  have hAB : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * A + (1 - t) * B ≠ 0 := by
    intro t ht
    simpa using mobius_resolvent_ne_zero hA hc hcAB (hreal 1 one_pos).2 ht
  have hconv : Convex ℝ U := by
    refine (convex_halfSpace_re_gt 0).inter ?_
    intro x hx y hy p q hp hq hpq
    change 0 < (x / c).re at hx
    change 0 < (y / c).re at hy
    change 0 < ((p • x + q • y) / c).re
    have he : ((p • x + q • y) / c).re = p * (x / c).re + q * (y / c).re := by
      rw [real_smul, real_smul, add_div, add_re, mul_div_assoc, mul_div_assoc, re_ofReal_mul,
        re_ofReal_mul]
    rw [he]
    rcases eq_or_lt_of_le hp with h | h
    · subst h; simp only [zero_add] at hpq; subst hpq; simpa using hy
    · positivity
  have hf := analyticOnNhd_integral_jacobiMobiusIntegrand (by linarith) (by linarith) m hA hc
    hcAB (a := a) (b := b)
  have heq : EqOn (fun ρ => ∫ s in (0 : ℝ)..1, jacobiMobiusIntegrand a b m A B ρ s)
      (fun _ => ∫ t in (0 : ℝ)..1,
        complexJacobiWeight a b t * ((t : ℂ) * A + (1 - t) * B) ^ (-(m : ℤ))) U := by
    apply hf.eqOn_of_preconnected_of_mem_closure analyticOnNhd_const hconv.isPreconnected
      (hreal 1 one_pos) (z₀ := 1)
    have ht : Tendsto (fun k : ℕ => ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 1) := by
      have := ((tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ))
      simpa [Function.comp_def] using (continuous_ofReal.tendsto _).comp this
    apply mem_closure_of_tendsto ht
    refine Eventually.of_forall (fun k => ⟨?_, ?_⟩)
    · exact integral_jacobiMobiusIntegrand_ofReal ha hb m hAB (by positivity)
    · simp only [mem_singleton_iff, ofReal_eq_one]
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  exact heq ⟨hρ, hρc⟩


/-- Off the segment, the ratio of the two endpoint differences lies in the slit plane. -/
theorem div_mem_slitPlane_of_not_mem_segment {r s z : ℂ} (hz : z ∉ segment ℝ r s) :
    (z - s) / (z - r) ∈ slitPlane := by
  have hzr : z - r ≠ 0 := sub_ne_zero.mpr (fun h => hz (h ▸ left_mem_segment ℝ r s))
  rw [mem_slitPlane_iff]
  by_contra h
  simp only [not_or, not_lt, not_not] at h
  obtain ⟨hre, him⟩ := h
  set w := (z - s) / (z - r)
  have hw : w = (w.re : ℂ) := by apply Complex.ext <;> simp [him]
  have hzw : z - s = w.re * (z - r) := by
    rw [← hw]; simp only [w]; rw [div_mul_cancel₀ _ hzr]
  have h1 : (1 - w.re) ≠ 0 := by linarith
  have h1' : (1 : ℂ) - w.re ≠ 0 := by exact_mod_cast h1
  apply hz
  refine ⟨-w.re / (1 - w.re), 1 / (1 - w.re), ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (by linarith) (by linarith)
  · exact div_nonneg zero_le_one (by linarith)
  · field_simp; ring
  · simp only [real_smul]
    push_cast
    field_simp
    linear_combination -hzw

/-- The principal square root of the endpoint ratio, which determines Carlson's saddle curve. -/
def jacobiSaddleRatio (r s z : ℂ) : ℂ := ((z - s) / (z - r)) ^ (1 / 2 : ℂ)

/-- The square of the saddle ratio recovers the endpoint ratio. -/
theorem jacobiSaddleRatio_sq_mul {r s z : ℂ} (hzr : z ≠ r) :
    jacobiSaddleRatio r s z ^ 2 * (z - r) = z - s := by
  have h : jacobiSaddleRatio r s z ^ 2 = (z - s) / (z - r) := by
    simp only [jacobiSaddleRatio, one_div]
    exact cpow_nat_inv_pow _ two_ne_zero
  rw [h]; field_simp [sub_ne_zero.mpr hzr]

/-- Off the segment the saddle ratio lies in the open right half-plane. -/
theorem re_jacobiSaddleRatio_pos {r s z : ℂ} (hz : z ∉ segment ℝ r s) :
    0 < (jacobiSaddleRatio r s z).re := by
  have hw := div_mem_slitPlane_of_not_mem_segment hz
  have hw0 : (z - s) / (z - r) ≠ 0 := slitPlane_ne_zero hw
  simp only [jacobiSaddleRatio, cpow_def_of_ne_zero hw0, exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have harg := mem_slitPlane_iff_arg.mp hw
  have h1 := neg_pi_lt_arg ((z - s) / (z - r))
  have h2 := lt_of_le_of_ne (arg_le_pi ((z - s) / (z - r))) harg.1
  simp only [mul_im, log_re, log_im, div_ofNat_re, div_ofNat_im]
  norm_num
  constructor <;> linarith

/-- The Euler representation of the second-kind functions, deformed onto the saddle curve. -/
theorem jacobiSecondKind_eq_integral_mobius (α β r s : ℂ) (n : ℕ) (hα : 0 < (α + n).re)
    (hβ : 0 < (β + n).re) {z : ℂ} (hz : z ∉ segment ℝ r s) :
    jacobiSecondKind α β r s n z =
      (Gamma (α + n + 1 + (β + n + 1)) / (Gamma (α + n + 1) * Gamma (β + n + 1))) *
        ∫ t in (0 : ℝ)..1, jacobiMobiusIntegrand (α + n) (β + n) (n + 1) (z - r) (z - s)
          (jacobiSaddleRatio r s z) t := by
  have hzr : z ≠ r := fun h => hz (h ▸ left_mem_segment ℝ r s)
  have hc := re_jacobiSaddleRatio_pos hz
  have hc0 : jacobiSaddleRatio r s z ≠ 0 := fun h => by simp [h] at hc
  rw [jacobiSecondKind_eq_complexEulerIntegral_on_segment r s n
    (by simp only [add_re, one_re] at *; linarith)
    (by simp only [add_re, one_re] at *; linarith) hz,
    integral_jacobiMobiusIntegrand_eq hα hβ (n + 1) (sub_ne_zero.mpr hzr) hc
      (jacobiSaddleRatio_sq_mul hzr) hc (by rw [div_self hc0]; simp)]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  congr 1
  push_cast
  ring_nf

/-- The per-degree factor of the deformed Euler integrand. -/
def jacobiMobiusKernel (A B ρ : ℂ) (s : ℝ) : ℂ :=
  ρ * s * (1 - s) / (((1 - s) + ρ * s) * (ρ * s * A + (1 - s) * B))

/-- Raising the degree multiplies the deformed Euler integrand by the kernel. -/
theorem jacobiMobiusIntegrand_add_nat (a b : ℂ) (m k : ℕ) (A B ρ : ℂ) (hρ : 0 < ρ.re)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hL : ρ * s * A + (1 - s) * B ≠ 0) :
    jacobiMobiusIntegrand (a + k) (b + k) (m + k) A B ρ s =
      jacobiMobiusIntegrand a b m A B ρ s * jacobiMobiusKernel A B ρ s ^ k := by
  have hρ0 : ρ ≠ 0 := fun h => by simp [h] at hρ
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.1.ne'
  have hs1 : (1 : ℂ) - s ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith [hs.2])
  have hD : (1 - (s : ℂ)) + ρ * s ≠ 0 := by
    intro h
    have := congrArg re h
    simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero,
      zero_re] at this
    nlinarith [hs.1, hs.2, mul_pos hρ hs.1]
  simp only [jacobiMobiusIntegrand, jacobiMobiusKernel]
  rw [complexJacobiWeight_add_nat a b s k hs0 hs1,
    show a + k + 1 = (a + 1) + (k : ℂ) by ring, cpow_add _ _ hρ0, cpow_natCast,
    show ((m + k : ℕ) : ℂ) - (a + k) - (b + k) - 2 = ((m : ℂ) - a - b - 2) - k by push_cast; ring,
    cpow_sub _ _ hD, cpow_natCast,
    show (-((m + k : ℕ) : ℤ)) = -(m : ℤ) + -(k : ℤ) by push_cast; ring, zpow_add₀ hL,
    zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, div_pow]
  generalize (1 - (s : ℂ)) + ρ * s = D at hD ⊢
  generalize ρ * s * A + (1 - s) * B = L at hL ⊢
  rw [show ρ * s * (1 - s) = ρ * (s * (1 - s)) by ring]
  simp only [mul_pow]
  field_simp

/-- Along the principal saddle curve the per-degree factor is bounded by the reciprocal of
four times the elliptic mean radius. -/
theorem norm_jacobiMobiusKernel_le {r s z : ℂ} (hz : z ∉ segment ℝ r s) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖jacobiMobiusKernel (z - r) (z - s) (jacobiSaddleRatio r s z) t‖ ≤
      1 / (4 * jacobiEllipseRadius r s z) := by
  have hzr : z ≠ r := fun h => hz (h ▸ left_mem_segment ℝ r s)
  set c := jacobiSaddleRatio r s z
  have hc : 0 < c.re := re_jacobiSaddleRatio_pos hz
  have hc0 : c ≠ 0 := fun h => by
    have : c.re = 0 := by rw [h]; simp
    linarith
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (z - r) (by norm_num : 0 < (2 : ℕ))
  have ha0 : a ≠ 0 := by
    rintro rfl; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at ha
    exact sub_ne_zero.mpr hzr ha.symm
  set b := a * c with hbdef
  have hb : b ^ 2 = z - s := by
    simp only [hbdef, mul_pow, ha, mul_comm _ (c ^ 2)]
    exact jacobiSaddleRatio_sq_mul hzr
  have hab : 0 < (a * conj b).re := by
    have : (a * conj b).re = normSq a * c.re := by
      simp only [hbdef, map_mul, mul_re, mul_im, conj_re, conj_im, normSq_apply]; ring
    rw [this]; exact mul_pos (normSq_pos.mpr ha0) hc
  have hbound := norm_jacobiEulerKernel_mobius_le hab ht
  rw [jacobiEllipseRadius_eq_sq_of_re_mul_conj_nonneg r s z a b ha hb hab.le,
    show 4 * (‖a + b‖ ^ 2 / 4) = ‖a + b‖ ^ 2 by ring]
  convert hbound using 2
  have hL : c * t * (z - r) + (1 - t) * (z - s) ≠ 0 :=
    mobius_resolvent_ne_zero (sub_ne_zero.mpr hzr) hc (jacobiSaddleRatio_sq_mul hzr)
      (by rw [div_self hc0]; simp) (Ioo_subset_Icc_self ht)
  have hD : (1 - (t : ℂ)) + c * t ≠ 0 := by
    intro h
    have := congrArg re h
    simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero,
      zero_re] at this
    nlinarith [ht.1, ht.2, mul_pos hc ht.1]
  have hD' : a * (1 - (t : ℂ)) + b * t ≠ 0 := by
    rw [show a * (1 - (t : ℂ)) + b * t = a * ((1 - t) + c * t) by rw [hbdef]; ring]
    exact mul_ne_zero ha0 hD
  simp only [jacobiMobiusKernel]
  rw [← ha, ← hb]
  rw [← ha, ← hb] at hL
  rw [hbdef] at hD' ⊢
  field_simp
  ring

/-- The saddle ratio depends continuously on the evaluation point off the segment. -/
theorem continuousAt_jacobiSaddleRatio {r s z : ℂ} (hz : z ∉ segment ℝ r s) :
    ContinuousAt (jacobiSaddleRatio r s) z := by
  have hzr : z - r ≠ 0 := sub_ne_zero.mpr (fun h => hz (h ▸ left_mem_segment ℝ r s))
  have hf : ContinuousAt (fun z : ℂ => (z - s) / (z - r)) z :=
    (continuousAt_id.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const) hzr
  exact ContinuousAt.comp' (g := fun w : ℂ => w ^ (1 / 2 : ℂ))
    (continuousAt_cpow_const (div_mem_slitPlane_of_not_mem_segment hz)) hf

/-- The deformed Euler integrand at a fixed base degree is jointly continuous off the
segment. -/
theorem continuousAt_jacobiMobiusIntegrand_saddle {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (m : ℕ) {r s z : ℂ} (hz : z ∉ segment ℝ r s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun p : ℂ × ℝ => jacobiMobiusIntegrand a b m (p.1 - r) (p.1 - s)
      (jacobiSaddleRatio r s p.1) p.2) (z, t) := by
  have hzr : z ≠ r := fun h => hz (h ▸ left_mem_segment ℝ r s)
  have hc := re_jacobiSaddleRatio_pos hz
  have hcz : ContinuousAt (fun p : ℂ × ℝ => jacobiSaddleRatio r s p.1) (z, t) :=
    ContinuousAt.comp' (g := jacobiSaddleRatio r s) (continuousAt_jacobiSaddleRatio hz)
      continuousAt_fst
  have ht' : ContinuousAt (fun p : ℂ × ℝ => (p.2 : ℂ)) (z, t) :=
    continuous_ofReal.continuousAt.comp continuousAt_snd
  have hw : Continuous (fun t : ℝ => complexJacobiWeight a b t) := by
    simpa only [sub_add_cancel] using
      (continuous_complexJacobiWeight_succ (α := a - 1) (β := b - 1)
        (by simp only [sub_re, one_re]; linarith) (by simp only [sub_re, one_re]; linarith))
  have hD : (1 - (t : ℂ)) + jacobiSaddleRatio r s z * t ∈ slitPlane := by
    left
    simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero]
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1; simpa using hc
    · nlinarith [ht.1, hc]
  have hL := mobius_resolvent_ne_zero (sub_ne_zero.mpr hzr) hc (jacobiSaddleRatio_sq_mul hzr)
    (by rw [div_self (fun h => by simp [h] at hc)]; simp) ht
  simp only [jacobiMobiusIntegrand]
  refine ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_) ?_
  · exact hcz.cpow continuousAt_const (Or.inl hc)
  · exact hw.continuousAt.comp continuousAt_snd
  · exact ((continuousAt_const.sub ht').add (hcz.mul ht')).cpow continuousAt_const hD
  · exact ContinuousAt.zpow₀ (((hcz.mul ht').mul (continuousAt_fst.sub continuousAt_const)).add
      ((continuousAt_const.sub ht').mul (continuousAt_fst.sub continuousAt_const))) _ (Or.inl hL)

/-- On a compact set off the segment the second-kind functions satisfy one degree-uniform
bound retaining the sharp saddle factor `1 / (4 μ(z))` at each degree, for arbitrary
complex parameters. -/
theorem exists_bound_jacobiSecondKind_of_isCompact (α β r s : ℂ) {L : Set ℂ}
    (hL : IsCompact L) (hLseg : ∀ z ∈ L, z ∉ segment ℝ r s) {N : ℕ}
    (hα : 0 < (α + N).re) (hβ : 0 < (β + N).re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ∀ z ∈ L,
      ‖jacobiSecondKind α β r s (N + k) z‖ ≤
        ‖betaShiftNormalization (α + N + 1) (β + N + 1) k‖ *
          (C * (1 / (4 * jacobiEllipseRadius r s z)) ^ k) := by
  set Φ : ℂ × ℝ → ℂ := fun p => jacobiMobiusIntegrand (α + N) (β + N) (N + 1) (p.1 - r)
    (p.1 - s) (jacobiSaddleRatio r s p.1) p.2
  have hΦ : ContinuousOn Φ (L ×ˢ Icc (0 : ℝ) 1) := fun p hp =>
    (continuousAt_jacobiMobiusIntegrand_saddle hα hβ (N + 1) (hLseg p.1 hp.1) hp.2 :
      ContinuousAt Φ (p.1, p.2)).continuousWithinAt
  obtain ⟨C, hC⟩ := (hL.prod isCompact_Icc).exists_bound_of_continuousOn hΦ
  refine ⟨|C|, abs_nonneg C, fun k z hz => ?_⟩
  have hzseg := hLseg z hz
  have hzr : z ≠ r := fun h => hzseg (h ▸ left_mem_segment ℝ r s)
  have hμ : 0 < jacobiEllipseRadius r s z := by
    have h1 := le_jacobiEllipseRadius r s z
    have h2 := (jacobiEllipseRadius_eq_min_iff r s z).not.mpr hzseg
    have h0 : 0 ≤ ‖r - s‖ / 4 := by positivity
    rcases eq_or_lt_of_le h1 with h | h
    · exact absurd h.symm h2
    · linarith
  have hαk : 0 < (α + (N + k : ℕ)).re := by
    simp only [add_re, natCast_re, Nat.cast_add] at *; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hβk : 0 < (β + (N + k : ℕ)).re := by
    simp only [add_re, natCast_re, Nat.cast_add] at *; have := Nat.cast_nonneg (α := ℝ) k; linarith
  rw [jacobiSecondKind_eq_integral_mobius α β r s (N + k) hαk hβk hzseg, norm_mul]
  have hG : Gamma (α + (N + k : ℕ) + 1 + (β + (N + k : ℕ) + 1)) /
      (Gamma (α + (N + k : ℕ) + 1) * Gamma (β + (N + k : ℕ) + 1)) =
      betaShiftNormalization (α + N + 1) (β + N + 1) k := by
    rw [show α + ((N + k : ℕ) : ℂ) + 1 = α + N + 1 + k by push_cast; ring,
      show β + ((N + k : ℕ) : ℂ) + 1 = β + N + 1 + k by push_cast; ring]
    rfl
  rw [hG]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hc := re_jacobiSaddleRatio_pos hzseg
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t => jacobiMobiusIntegrand (α + (N + k : ℕ)) (β + (N + k : ℕ)) (N + k + 1)
      (z - r) (z - s) (jacobiSaddleRatio r s z) t)
    (C := |C| * (1 / (4 * jacobiEllipseRadius r s z)) ^ k) ?_
  · simpa using hi
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1
    have hb0 : β + (N + k : ℕ) ≠ 0 := fun h => by rw [h] at hβk; simp at hβk
    simp only [jacobiMobiusIntegrand, complexJacobiWeight, ofReal_one, sub_self,
      zero_cpow hb0, mul_zero, zero_mul, norm_zero]
    positivity
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, h1⟩
  have hLne := mobius_resolvent_ne_zero (sub_ne_zero.mpr hzr) hc (jacobiSaddleRatio_sq_mul hzr)
    (by rw [div_self (fun h => by simp [h] at hc)]; simp) (Ioo_subset_Icc_self htI)
  have hfac := jacobiMobiusIntegrand_add_nat (α + N) (β + N) (N + 1) k (z - r) (z - s)
    (jacobiSaddleRatio r s z) hc htI hLne
  rw [show α + ((N + k : ℕ) : ℂ) = α + N + k by push_cast; ring,
    show β + ((N + k : ℕ) : ℂ) = β + N + k by push_cast; ring,
    show N + k + 1 = N + 1 + k by ring, hfac, norm_mul, norm_pow]
  exact mul_le_mul ((hC (z, t) ⟨hz, Ioo_subset_Icc_self htI⟩).trans (le_abs_self C))
    (pow_le_pow_left₀ (norm_nonneg _) (norm_jacobiMobiusKernel_le hzseg htI) k)
    (by positivity) (abs_nonneg C)

/-- Off the segment the mean radius exceeds its minimum. -/
theorem lt_jacobiEllipseRadius {r s z : ℂ} (hz : z ∉ segment ℝ r s) :
    ‖r - s‖ / 4 < jacobiEllipseRadius r s z :=
  lt_of_le_of_ne (le_jacobiEllipseRadius r s z)
    (fun h => hz ((jacobiEllipseRadius_eq_min_iff r s z).mp h.symm))

/-- Points with mean radius above the minimum avoid the segment. -/
theorem not_mem_segment_of_lt_jacobiEllipseRadius {r s z : ℂ}
    (h : ‖r - s‖ / 4 < jacobiEllipseRadius r s z) : z ∉ segment ℝ r s := fun hz => by
  rw [(jacobiEllipseRadius_eq_min_iff r s z).mpr hz] at h
  exact lt_irrefl _ h

/-- The mean radius is at most the semimajor axis. -/
theorem jacobiEllipseRadius_le_half (r s z : ℂ) :
    jacobiEllipseRadius r s z ≤ (‖z - r‖ + ‖z - s‖) / 2 := by
  have h := le_jacobiEllipseRadius r s z
  simp only [jacobiEllipseRadius] at h ⊢
  have hS : 0 ≤ ‖z - r‖ + ‖z - s‖ := by positivity
  have : Real.sqrt ((‖z - r‖ + ‖z - s‖) ^ 2 - ‖r - s‖ ^ 2) ≤ ‖z - r‖ + ‖z - s‖ := by
    rw [Real.sqrt_le_left hS]; nlinarith [sq_nonneg ‖r - s‖]
  linarith

/-- The distance to the focal segment is at least the mean radius minus the focal length. -/
theorem sub_le_norm_sub_of_mem_segment (r s z : ℂ) {w : ℂ} (hw : w ∈ segment ℝ r s) :
    jacobiEllipseRadius r s z - ‖r - s‖ ≤ ‖z - w‖ := by
  have hr : ‖w - r‖ ≤ ‖r - s‖ := by
    simpa [norm_sub_rev] using norm_sub_le_of_mem_segment hw
  have hs : ‖w - s‖ ≤ ‖r - s‖ := by
    simpa using norm_sub_le_of_mem_segment (segment_symm ℝ r s ▸ hw)
  have h1 : ‖z - r‖ ≤ ‖z - w‖ + ‖w - r‖ := by
    simpa using norm_sub_le (z - w) (r - w) |>.trans_eq' (by congr 1; ring) |>.trans
      (by rw [norm_sub_rev r w])
  have h2 : ‖z - s‖ ≤ ‖z - w‖ + ‖w - s‖ := by
    simpa using norm_sub_le (z - w) (s - w) |>.trans_eq' (by congr 1; ring) |>.trans
      (by rw [norm_sub_rev s w])
  have := jacobiEllipseRadius_le_half r s z
  linarith

/-- Each second-kind function is bounded on every closed elliptic exterior. -/
theorem exists_bound_jacobiSecondKind_of_le (α β r s : ℂ) (n : ℕ) {σ : ℝ}
    (hσ : ‖r - s‖ / 4 < σ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, σ ≤ jacobiEllipseRadius r s z →
      ‖jacobiSecondKind α β r s n z‖ ≤ M := by
  set g := fun w : ℂ => jacobiSecondKind α β (w * r) (w * s) n 1
  have hg := (analyticAt_jacobiSecondKind_infinity α β r s n).continuousAt
  obtain ⟨δ, hδ, hgδ⟩ := Metric.continuousAt_iff.mp hg 1 one_pos
  set R := max 1 (2 / δ)
  have hfar : ∀ z : ℂ, R ≤ ‖z‖ → z ∉ segment ℝ r s →
      ‖jacobiSecondKind α β r s n z‖ ≤ ‖g 0‖ + 1 := by
    intro z hz hzs
    have hz1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
    have hcov := jacobiSecondKind_affine α β r s z⁻¹ 0 n (inv_ne_zero hz0) hzs
    simp only [add_zero, inv_mul_cancel₀ hz0] at hcov
    have hq : jacobiSecondKind α β r s n z = z⁻¹ ^ (n + 1) * g z⁻¹ := by
      simp only [g]
      rw [hcov, zpow_neg, ← mul_assoc, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, inv_pow, inv_inv, inv_mul_cancel₀ (pow_ne_zero _ hz0), one_mul]
    have hsmall : dist z⁻¹ 0 < δ := by
      rw [dist_zero_right, norm_inv]
      have : 2 / δ ≤ ‖z‖ := (le_max_right _ _).trans hz
      rw [inv_lt_comm₀ (by linarith) hδ]
      calc δ⁻¹ < 2 / δ := by rw [div_eq_mul_inv]; linarith [inv_pos.mpr hδ]
        _ ≤ ‖z‖ := this
    have hgz : ‖g z⁻¹‖ ≤ ‖g 0‖ + 1 := by
      have := hgδ hsmall
      rw [dist_eq_norm] at this
      linarith [norm_sub_norm_le (g z⁻¹) (g 0)]
    rw [hq, norm_mul, norm_pow, norm_inv]
    calc
      _ ≤ 1 * (‖g 0‖ + 1) := by
        gcongr
        exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hz1)
      _ = _ := one_mul _
  set E := {z : ℂ | σ ≤ jacobiEllipseRadius r s z} ∩ Metric.closedBall 0 R
  have hE : IsCompact E := (isCompact_closedBall 0 R).inter_left
    (isClosed_le continuous_const (continuous_jacobiEllipseRadius r s))
  have hEseg : ∀ z ∈ E, z ∉ segment ℝ r s := fun z hz =>
    not_mem_segment_of_lt_jacobiEllipseRadius (hσ.trans_le hz.1)
  obtain ⟨M₂, hM₂⟩ := hE.exists_bound_of_continuousOn
    (fun z hz => ((analyticOnNhd_jacobiSecondKind α β r s n) z
      (hEseg z hz)).continuousAt.continuousWithinAt)
  refine ⟨max (|M₂|) (‖g 0‖ + 1), by positivity, fun z hz => ?_⟩
  by_cases hzR : ‖z‖ ≤ R
  · exact (hM₂ z ⟨hz, by simpa using hzR⟩).trans ((le_abs_self _).trans (le_max_left _ _))
  · exact (hfar z (le_of_not_ge hzR) (not_mem_segment_of_lt_jacobiEllipseRadius
      (hσ.trans_le hz))).trans (le_max_right _ _)

/-- The second-kind functions decay at the reciprocal elliptic rate on closed elliptic
exteriors: `‖qₙ(z)‖ ≤ C (1/σ + ε)ⁿ` whenever `μ(z) ≥ σ`. This is the upper half of Carlson's
Theorem 7.5-2 for `q̂ₙ(σ)`, for arbitrary complex parameters and endpoints. -/
theorem exists_bound_jacobiSecondKind_exterior (α β r s : ℂ) {σ ε : ℝ}
    (hσ : ‖r - s‖ / 4 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n z, σ ≤ jacobiEllipseRadius r s z →
      ‖jacobiSecondKind α β r s n z‖ ≤ C * (1 / σ + ε) ^ n := by
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  obtain ⟨N, hα, hβ, B, hB0, hbound⟩ := exists_jacobiWeight_shift_bound α β
  set T := σ + ‖r - s‖ + 1
  set K := {z : ℂ | σ ≤ jacobiEllipseRadius r s z ∧ jacobiEllipseRadius r s z ≤ T}
  have hKc : IsCompact K :=
    (isCompact_jacobiClosedEllipseDisk r s T).of_isClosed_subset
      ((isClosed_le continuous_const (continuous_jacobiEllipseRadius r s)).inter
        (isClosed_le (continuous_jacobiEllipseRadius r s) continuous_const)) (fun z hz => hz.2)
  have hKseg : ∀ z ∈ K, z ∉ segment ℝ r s := fun z hz =>
    not_mem_segment_of_lt_jacobiEllipseRadius (hσ.trans_le hz.1)
  obtain ⟨C₁, hC₁, hK⟩ := exists_bound_jacobiSecondKind_of_isCompact α β r s hKc hKseg hα hβ
  -- a uniform bound at degrees `N + k` with factor `(1 / (4σ))^k`
  have hshift : ∀ k z, σ ≤ jacobiEllipseRadius r s z →
      ‖jacobiSecondKind α β r s (N + k) z‖ ≤
        ‖betaShiftNormalization (α + N + 1) (β + N + 1) k‖ * ((C₁ + B) * (1 / (4 * σ)) ^ k) := by
    intro k z hz
    have hzs := not_mem_segment_of_lt_jacobiEllipseRadius (hσ.trans_le hz)
    by_cases hzT : jacobiEllipseRadius r s z ≤ T
    · have hμ : 0 < jacobiEllipseRadius r s z := hσ0.trans_le hz
      refine (hK k z ⟨hz, hzT⟩).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact mul_le_mul (by linarith) (pow_le_pow_left₀ (by positivity)
        (one_div_le_one_div_of_le (by positivity) (by linarith)) k)
        (pow_nonneg (by positivity) k) (by linarith)
    · have hdist : ∀ w ∈ segment ℝ r s, σ + 1 ≤ ‖z - w‖ := fun w hw => by
        have := sub_le_norm_sub_of_mem_segment r s z hw
        linarith
      refine (norm_jacobiSecondKind_add_le α β r s N k hα hβ hB0 (by linarith) hbound hzs
        hdist).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      have h1 : (σ + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have h2 : (σ + 1)⁻¹ ≤ σ⁻¹ := inv_anti₀ hσ0 (by linarith)
      calc
        B * (1 / 4 : ℝ) ^ k * (σ + 1)⁻¹ ^ (N + k + 1)
            = B * ((1 / 4 : ℝ) ^ k * (σ + 1)⁻¹ ^ k) * (σ + 1)⁻¹ ^ (N + 1) := by ring
        _ ≤ B * ((1 / 4 : ℝ) ^ k * σ⁻¹ ^ k) * 1 := by
          gcongr
          exact pow_le_one₀ (by positivity) h1
        _ = B * (1 / (4 * σ)) ^ k := by rw [mul_one, ← mul_pow]; ring_nf
        _ ≤ (C₁ + B) * (1 / (4 * σ)) ^ k := by gcongr; linarith
  -- geometric control of the beta normalization
  set t := 1 / (4 * (1 + ε * σ))
  have ht0 : 0 ≤ t := by positivity
  have ht4 : 4 * t < 1 := by
    simp only [t]
    rw [show 4 * (1 / (4 * (1 + ε * σ))) = 1 / (1 + ε * σ) by field_simp]
    rw [div_lt_one (by positivity)]
    nlinarith [mul_pos hε hσ0]
  have hsum := summable_norm_betaShiftNormalization_mul_pow (α + N + 1) (β + N + 1) ht0 ht4
  set S := ∑' k, ‖betaShiftNormalization (α + N + 1) (β + N + 1) k‖ * t ^ k
  have hS0 : 0 ≤ S := tsum_nonneg fun k => by positivity
  have hbs (k : ℕ) : ‖betaShiftNormalization (α + N + 1) (β + N + 1) k‖ * (1 / (4 * σ)) ^ k ≤
      S * (1 / σ + ε) ^ k := by
    have h := hsum.le_tsum k (fun j _ => by positivity)
    have he : 1 / (4 * σ) = t * (1 / σ + ε) := by simp only [t]; field_simp
    rw [he, mul_pow, ← mul_assoc]
    gcongr
  -- low degrees
  have hlow (n : ℕ) := exists_bound_jacobiSecondKind_of_le α β r s n hσ
  choose M hM0 hM using hlow
  set Msum := ∑ n ∈ Finset.range N, M n
  set q := 1 / σ + ε
  have hq : 0 < q := by positivity
  set m := min 1 q
  have hm : 0 < m := lt_min one_pos hq
  have hm1 : m ≤ 1 := min_le_left _ _
  have hMsum : 0 ≤ Msum := Finset.sum_nonneg (fun j _ => hM0 j)
  refine ⟨((C₁ + B) * S + Msum) / m ^ N, by positivity, fun n z hz => ?_⟩
  have hqn (j : ℕ) : m ^ j ≤ q ^ j := pow_le_pow_left₀ hm.le (min_le_right _ _) j
  rcases lt_or_ge n N with hn | hn
  · calc
      _ ≤ M n := hM n z hz
      _ ≤ Msum := Finset.single_le_sum (f := M) (fun j _ => hM0 j) (Finset.mem_range.mpr hn)
      _ = Msum * m ^ N / m ^ N := by field_simp
      _ ≤ Msum * q ^ n / m ^ N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          ((pow_le_pow_of_le_one hm.le hm1 hn.le).trans (hqn n))
          (Finset.sum_nonneg (fun j _ => hM0 j))) (pow_pos hm N).le
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        gcongr
        have : 0 ≤ (C₁ + B) * S := by positivity
        linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
  calc
    _ ≤ _ := hshift k z hz
    _ = (C₁ + B) * (‖betaShiftNormalization (α + N + 1) (β + N + 1) k‖ * (1 / (4 * σ)) ^ k) := by
      ring
    _ ≤ (C₁ + B) * (S * q ^ k) := mul_le_mul_of_nonneg_left (hbs k) (by linarith)
    _ = (C₁ + B) * S * (q ^ k * m ^ N) / m ^ N := by field_simp
    _ ≤ (C₁ + B) * S * q ^ (N + k) / m ^ N := by
      apply div_le_div_of_nonneg_right _ (pow_pos hm N).le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [pow_add, mul_comm]
      exact mul_le_mul_of_nonneg_right (hqn N) (pow_nonneg hq.le k)
    _ ≤ _ := by
      rw [div_mul_eq_mul_div]
      gcongr
      have : 0 ≤ Msum := Finset.sum_nonneg (fun j _ => hM0 j)
      linarith

end Carlson.TwoVariable
