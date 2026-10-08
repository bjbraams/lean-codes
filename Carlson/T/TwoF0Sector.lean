/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.T.TwoF0
public import ToMathlib.Analysis.SpecialFunctions.GammaRatio

/-!
# Carlson's `₂F₀` on the sector `|ph(-x)| < 3π/2`

Carlson's Theorem 5.12-6 continues `₂F₀(α, β; x)` from the half-plane `re x < 0` to the sector
`|ph(-x)| < 3π/2`, which covers real `x` of both signs twice. The continuation is multivalued,
so here it is a function of `ζ = log(-x)`: `x = -e^ζ` with `|im ζ| < 3π/2` and `ph(-x) = im ζ`.
It is given by the representation (5.12-12), in which both Euler measures are integrated along
the ray `{s e^{iφ} : s > 0}` at Carlson's angle `φ = -(1/3) ph(-x)`.

Carlson rotates the rays by Cauchy's integral theorem. Here the rotation is proved without
contours. For a complex direction `w` with `re w > 0` let `D(w)` be the remainder integral along
the rays `s w`, `t w`. It is holomorphic in `w` by dominated differentiation, and `D(ρ w) = D(w)`
for `ρ > 0` by the substitution `(s, t) ↦ (ρ s, ρ t)`. Hence `D' = 0`, and `D(e^{iθ})` is
constant on every interval of admissible angles. Independence of the number of explicit terms
is transferred from the half-plane by the identity theorem in `ζ`.

The remainder along the rotated rays is bounded by the total variations of the rotated Euler
measures, which gives the error bound (5.12-15) of Theorem 5.12-7 on the whole sector and the
asymptotic expansion (5.12-17) uniformly on closed subsectors.

## Main definitions

* `Carlson.twoF0DoubleRot`: the remainder double integral along rays in direction `w`.
* `Carlson.twoF0RepRot`: the representation (5.12-12) along rays in direction `w`.
* `Carlson.twoF0Angles`: the admissible angles for a given `ph(-x)`.
* `Carlson.carlson2F0Sector`: `₂F₀(α, β; -e^ζ)` for `|im ζ| < 3π/2`.

## Main results

* `Carlson.analyticOnNhd_twoF0DoubleRot`: holomorphy of the rotated integral in `(α, β, x, w)`.
* `Carlson.twoF0DoubleRot_angle_eq`: rotation invariance.
* `Carlson.carlson2F0Sector_eq_twoF0RepRot`: formula (5.12-12) in every admissible direction and
  with every admissible number of terms.
* `Carlson.analyticOnNhd_carlson2F0Sector`: Theorem 5.12-6.
* `Carlson.carlson2F0Sector_eq_carlson2F0`: agreement with Theorem 5.12-4 for `|ph(-x)| < π/2`.
* `Carlson.carlson2F0Sector_comm`: Theorem 5.12-2 on the sector.
* `Carlson.norm_carlson2F0Sector_sub_sum_le`: the error bound (5.12-15).
* `Carlson.norm_carlson2F0Sector_sub_sum_le_two_rpow`: the simplified bound (5.12-16).
* `Carlson.exists_norm_carlson2F0Sector_sub_sum_le`: the asymptotic expansion (5.12-17).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.12.
-/

open Complex MeasureTheory Filter Set
open scoped Topology Real
@[expose] public noncomputable section

namespace Carlson

/-- The complexified integrand is jointly analytic wherever both integration variables lie in
the slit plane. -/
theorem analyticAt_twoF0Integrand_of_mem_slitPlane (n : ℕ) (p : ℂ × ℂ × ℂ) {σ τ : ℂ}
    (hs' : σ ∈ slitPlane) (ht' : τ ∈ slitPlane) :
    AnalyticAt ℂ (twoF0Integrand n) (p, (σ, τ)) := by
  set q := (p, (σ, τ))
  have hα : AnalyticAt ℂ (fun v : (ℂ × ℂ × ℂ) × (ℂ × ℂ) => v.1.1) q :=
    ((ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)).comp
      (ContinuousLinearMap.fst ℂ (ℂ × ℂ × ℂ) (ℂ × ℂ))).analyticAt q
  have hβ : AnalyticAt ℂ (fun v : (ℂ × ℂ × ℂ) × (ℂ × ℂ) => v.1.2.1) q :=
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).comp
      (ContinuousLinearMap.fst ℂ (ℂ × ℂ × ℂ) (ℂ × ℂ))).analyticAt q
  have hx : AnalyticAt ℂ (fun v : (ℂ × ℂ × ℂ) × (ℂ × ℂ) => v.1.2.2) q :=
    (((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).comp
      (ContinuousLinearMap.fst ℂ (ℂ × ℂ × ℂ) (ℂ × ℂ))).analyticAt q
  have hσ : AnalyticAt ℂ (fun v : (ℂ × ℂ × ℂ) × (ℂ × ℂ) => v.2.1) q :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
      (ContinuousLinearMap.snd ℂ (ℂ × ℂ × ℂ) (ℂ × ℂ))).analyticAt q
  have hτ : AnalyticAt ℂ (fun v : (ℂ × ℂ × ℂ) × (ℂ × ℂ) => v.2.2) q :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
      (ContinuousLinearMap.snd ℂ (ℂ × ℂ × ℂ) (ℂ × ℂ))).analyticAt q
  have hG : ∀ {f : (ℂ × ℂ × ℂ) × (ℂ × ℂ) → ℂ}, AnalyticAt ℂ f q →
      AnalyticAt ℂ (fun v => (Gamma (f v + n))⁻¹) q := fun hf =>
    (analyticOnNhd_inv_Gamma _ (mem_univ _)).comp_of_eq (hf.add analyticAt_const) rfl
  have hE := (analyticOnNhd_expRemainder n _ (mem_univ _)).comp_of_eq
    ((hσ.mul hτ).mul hx) rfl
  unfold twoF0Integrand
  exact (((hG hα).mul ((hσ.cpow ((hα.add analyticAt_const).sub analyticAt_const) hs').mul
    hσ.neg.cexp)).mul ((hG hβ).mul ((hτ.cpow ((hβ.add analyticAt_const).sub analyticAt_const)
      ht').mul hτ.neg.cexp))).mul hE

/-- The integrand of the rotated remainder integral: both Euler rays are turned by the
direction `w`, so `s ↦ s w`, `t ↦ t w`, with Jacobian `w²`. -/
def twoF0RotIntegrand (n : ℕ) (v : ((ℂ × ℂ × ℂ) × ℂ) × (ℂ × ℂ)) : ℂ :=
  twoF0Integrand n (v.1.1, (v.2.1 * v.1.2, v.2.2 * v.1.2)) * v.1.2 ^ 2

/-- Carlson's remainder double integral along the rays `s w`, `t w` (`s, t > 0`), as in the
representation (5.12-12). -/
@[irreducible] def twoF0DoubleRot (n : ℕ) (α β x w : ℂ) : ℂ :=
  ∫ a, twoF0RotIntegrand n (((α, β, x), w), ((a.1 : ℂ), (a.2 : ℂ))) ∂quadrantMeasure

/-- The rotated integrand is analytic in all variables at positive real `(s, t)` when
`re w > 0`. -/
theorem analyticAt_twoF0RotIntegrand (n : ℕ) (P : (ℂ × ℂ × ℂ) × ℂ) (hw : 0 < P.2.re) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) :
    AnalyticAt ℂ (twoF0RotIntegrand n) (P, ((s : ℂ), (t : ℂ))) := by
  set q := (P, ((s : ℂ), (t : ℂ)))
  have hP1 : AnalyticAt ℂ (fun v : ((ℂ × ℂ × ℂ) × ℂ) × (ℂ × ℂ) => v.1.1) q :=
    ((ContinuousLinearMap.fst ℂ (ℂ × ℂ × ℂ) ℂ).comp
      (ContinuousLinearMap.fst ℂ ((ℂ × ℂ × ℂ) × ℂ) (ℂ × ℂ))).analyticAt q
  have hw' : AnalyticAt ℂ (fun v : ((ℂ × ℂ × ℂ) × ℂ) × (ℂ × ℂ) => v.1.2) q :=
    ((ContinuousLinearMap.snd ℂ (ℂ × ℂ × ℂ) ℂ).comp
      (ContinuousLinearMap.fst ℂ ((ℂ × ℂ × ℂ) × ℂ) (ℂ × ℂ))).analyticAt q
  have hσ : AnalyticAt ℂ (fun v : ((ℂ × ℂ × ℂ) × ℂ) × (ℂ × ℂ) => v.2.1) q :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
      (ContinuousLinearMap.snd ℂ ((ℂ × ℂ × ℂ) × ℂ) (ℂ × ℂ))).analyticAt q
  have hτ : AnalyticAt ℂ (fun v : ((ℂ × ℂ × ℂ) × ℂ) × (ℂ × ℂ) => v.2.2) q :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
      (ContinuousLinearMap.snd ℂ ((ℂ × ℂ × ℂ) × ℂ) (ℂ × ℂ))).analyticAt q
  have hsl : ∀ {r : ℝ}, 0 < r → (r : ℂ) * P.2 ∈ slitPlane := fun hr =>
    mem_slitPlane_iff.mpr (Or.inl (by rw [re_ofReal_mul]; exact mul_pos hr hw))
  have h := (analyticAt_twoF0Integrand_of_mem_slitPlane n P.1 (hsl hs) (hsl ht)).comp_of_eq
    (hP1.prod ((hσ.mul hw').prod (hτ.mul hw'))) rfl
  exact h.mul (hw'.pow 2)

/-- The one-dimensional majorant with exponential rate `c > 0` is integrable. -/
private theorem integrableOn_rpow_add_rpow_mul_exp_mul {A₀ A₁ c : ℝ} (h₀ : 0 < A₀) (h₁ : 0 < A₁)
    (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => (s ^ (A₀ - 1) + s ^ (A₁ - 1)) * Real.exp (-c * s)) (Ioi 0) := by
  have i₀ := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A₀ - 1) (b := c)
    (by linarith) one_pos hc
  have i₁ := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A₁ - 1) (b := c)
    (by linarith) one_pos hc
  refine (i₀.add i₁).congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, Real.rpow_one]; ring

/-- The norm of a power of a rotated positive number. -/
theorem norm_ofReal_mul_cpow {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : w ≠ 0) (c : ℂ) :
    ‖((s : ℂ) * w) ^ c‖ = s ^ c.re * (‖w‖ ^ c.re / Real.exp (arg w * c.im)) := by
  have hsw : (s : ℂ) * w ≠ 0 := mul_ne_zero (by exact_mod_cast hs.ne') hw
  rw [norm_cpow_of_ne_zero hsw, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le,
    Real.mul_rpow hs.le (norm_nonneg _), arg_real_mul _ hs]
  ring

/-- The domain of the rotated representation with `n` explicit terms: `re (α + n) > 0`,
`re (β + n) > 0`, `re w > 0` and `re (w² x) < 0`. -/
def twoF0RotDomain (n : ℕ) : Set ((ℂ × ℂ × ℂ) × ℂ) :=
  {P | 0 < (P.1.1 + n).re ∧ 0 < (P.1.2.1 + n).re ∧ 0 < P.2.re ∧ (P.2 ^ 2 * P.1.2.2).re < 0}

/-- The domain of the rotated representation is open. -/
theorem isOpen_twoF0RotDomain (n : ℕ) : IsOpen (twoF0RotDomain n) := by
  have c1 : Continuous fun P : (ℂ × ℂ × ℂ) × ℂ => (P.1.1 + n).re := by fun_prop
  have c2 : Continuous fun P : (ℂ × ℂ × ℂ) × ℂ => (P.1.2.1 + n).re := by fun_prop
  have c3 : Continuous fun P : (ℂ × ℂ × ℂ) × ℂ => P.2.re := by fun_prop
  have c4 : Continuous fun P : (ℂ × ℂ × ℂ) × ℂ => (P.2 ^ 2 * P.1.2.2).re := by fun_prop
  exact (isOpen_lt continuous_const c1).inter ((isOpen_lt continuous_const c2).inter
    ((isOpen_lt continuous_const c3).inter (isOpen_lt c4 continuous_const)))

set_option maxHeartbeats 2000000 in
/-- **Holomorphy of the rotated remainder integral** in `(α, β, x, w)`. -/
theorem analyticOnNhd_twoF0DoubleRot (n : ℕ) :
    AnalyticOnNhd ℂ (fun P : (ℂ × ℂ × ℂ) × ℂ => twoF0DoubleRot n P.1.1 P.1.2.1 P.1.2.2 P.2)
      (twoF0RotDomain n) := by
  set F : (ℂ × ℂ × ℂ) × ℂ → ℝ × ℝ → ℂ := fun P a =>
    twoF0RotIntegrand n (P, ((a.1 : ℂ), (a.2 : ℂ)))
  have hQ : quadrantMeasure = ((volume : Measure ℝ).prod volume).restrict
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := Measure.prod_restrict _ _
  have hmQ : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hfun : (fun P : (ℂ × ℂ × ℂ) × ℂ => twoF0DoubleRot n P.1.1 P.1.2.1 P.1.2.2 P.2) =
      fun P => ∫ a, F P a ∂quadrantMeasure := by
    funext P; rw [twoF0DoubleRot]
  rw [hfun]
  have hcont : ∀ P ∈ twoF0RotDomain n, ContinuousOn (F P) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    fun P hP a ha => ((analyticAt_twoF0RotIntegrand n P hP.2.2.1 ha.1 ha.2).continuousAt.comp_of_eq
      (show ContinuousAt (fun v : ℝ × ℝ => (P, ((v.1 : ℂ), (v.2 : ℂ)))) a by fun_prop)
        rfl).continuousWithinAt
  apply analyticOnNhd_integral_of_locally_dominated (isOpen_twoF0RotDomain n)
  · intro P hP
    rw [hQ]
    exact (hcont P hP).aestronglyMeasurable hmQ
  · intro P hP
    rw [hQ]
    refine ContinuousOn.aestronglyMeasurable ?_ hmQ
    have heq : ∀ a ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), fderiv ℂ (fun q => F q a) P =
        (fderiv ℂ (twoF0RotIntegrand n) (P, ((a.1 : ℂ), (a.2 : ℂ)))).comp
          (ContinuousLinearMap.inl ℂ ((ℂ × ℂ × ℂ) × ℂ) (ℂ × ℂ)) := fun a ha => by
      show fderiv ℂ (twoF0RotIntegrand n ∘ fun e => (e, ((a.1 : ℂ), (a.2 : ℂ)))) P = _
      exact ((analyticAt_twoF0RotIntegrand n P hP.2.2.1 ha.1 ha.2).differentiableAt.hasFDerivAt.comp
        P (hasFDerivAt_prodMk_left (𝕜 := ℂ) P ((a.1 : ℂ), (a.2 : ℂ)))).fderiv
    refine ContinuousOn.congr ?_ heq
    intro a ha
    exact (((analyticAt_twoF0RotIntegrand n P hP.2.2.1 ha.1 ha.2).fderiv.continuousAt.comp_of_eq
      (show ContinuousAt (fun v : ℝ × ℝ => (P, ((v.1 : ℂ), (v.2 : ℂ)))) a by fun_prop)
        rfl).clm_comp continuousAt_const).continuousWithinAt
  · rw [hQ]
    filter_upwards [self_mem_ae_restrict hmQ] with a ha
    intro P hP
    exact (analyticAt_twoF0RotIntegrand n P hP.2.2.1 ha.1 ha.2).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  · intro P hP
    set A := (P.1.1 + n).re
    set B := (P.1.2.1 + n).re
    set c := P.2.re / 2
    have hA : 0 < A := hP.1
    have hB : 0 < B := hP.2.1
    have hc : 0 < c := by simp only [c]; linarith [hP.2.2.1]
    have c1 : Continuous fun q : (ℂ × ℂ × ℂ) × ℂ => (q.1.1 + (n : ℂ)).re := by fun_prop
    have c2 : Continuous fun q : (ℂ × ℂ × ℂ) × ℂ => (q.1.2.1 + (n : ℂ)).re := by fun_prop
    have c3 : Continuous fun q : (ℂ × ℂ × ℂ) × ℂ => q.2.re := by fun_prop
    have c4 : Continuous fun q : (ℂ × ℂ × ℂ) × ℂ => (q.2 ^ 2 * q.1.2.2).re := by fun_prop
    have hev : ∀ᶠ q in 𝓝 P, A / 2 < (q.1.1 + (n : ℂ)).re ∧ (q.1.1 + (n : ℂ)).re < A + 1 ∧
        B / 2 < (q.1.2.1 + (n : ℂ)).re ∧ (q.1.2.1 + (n : ℂ)).re < B + 1 ∧ c < q.2.re ∧
        (q.2 ^ 2 * q.1.2.2).re < 0 := by
      filter_upwards [c1.continuousAt.eventually_const_lt (show A / 2 < A by linarith),
        c1.continuousAt.eventually_lt_const (show A < A + 1 by linarith),
        c2.continuousAt.eventually_const_lt (show B / 2 < B by linarith),
        c2.continuousAt.eventually_lt_const (show B < B + 1 by linarith),
        c3.continuousAt.eventually_const_lt (show c < P.2.re by simp only [c]; linarith [hP.2.2.1]),
        c4.continuousAt.eventually_lt_const hP.2.2.2] with q a b d e f g
      exact ⟨a, b, d, e, f, g⟩
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hev
    have hK := isCompact_closedBall P r
    set Φ : (ℂ × ℂ × ℂ) × ℂ → ℝ := fun q =>
      ‖(Gamma (q.1.1 + n))⁻¹‖ * (‖q.2‖ ^ (q.1.1 + (n : ℂ) - 1).re /
        Real.exp (arg q.2 * (q.1.1 + (n : ℂ) - 1).im)) *
      (‖(Gamma (q.1.2.1 + n))⁻¹‖ * (‖q.2‖ ^ (q.1.2.1 + (n : ℂ) - 1).re /
        Real.exp (arg q.2 * (q.1.2.1 + (n : ℂ) - 1).im))) * ‖q.2‖ ^ 2
    have hΦc : ContinuousOn Φ (Metric.closedBall P r) := by
      intro q hq
      obtain ⟨-, -, -, -, h5, -⟩ := hball hq
      have hq2 : q.2 ≠ 0 := fun h => by rw [h] at h5; simp at h5; linarith
      have hsl : q.2 ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by linarith))
      have harg : ContinuousAt (fun q : (ℂ × ℂ × ℂ) × ℂ => arg q.2) q :=
        (continuousAt_arg hsl).comp continuous_snd.continuousAt
      have hnorm : ContinuousAt (fun q : (ℂ × ℂ × ℂ) × ℂ => ‖q.2‖) q :=
        continuous_snd.norm.continuousAt
      have hpow : ∀ {g : (ℂ × ℂ × ℂ) × ℂ → ℂ}, Continuous g →
          ContinuousAt (fun q : (ℂ × ℂ × ℂ) × ℂ =>
            ‖q.2‖ ^ (g q).re / Real.exp (arg q.2 * (g q).im)) q := fun hg =>
        (hnorm.rpow (Complex.continuous_re.comp hg).continuousAt
          (Or.inl (norm_ne_zero_iff.mpr hq2))).div
          (Real.continuous_exp.continuousAt.comp (harg.mul
            (Complex.continuous_im.comp hg).continuousAt)) (Real.exp_pos _).ne'
      have hG1 : ContinuousAt (fun q : (ℂ × ℂ × ℂ) × ℂ => ‖(Gamma (q.1.1 + n))⁻¹‖) q :=
        (differentiable_one_div_Gamma.continuous.comp (by fun_prop)).norm.continuousAt
      have hG2 : ContinuousAt (fun q : (ℂ × ℂ × ℂ) × ℂ => ‖(Gamma (q.1.2.1 + n))⁻¹‖) q :=
        (differentiable_one_div_Gamma.continuous.comp (by fun_prop)).norm.continuousAt
      exact (((hG1.mul (hpow (by fun_prop))).mul (hG2.mul (hpow (by fun_prop)))).mul
        (hnorm.pow 2)).continuousWithinAt
    obtain ⟨M, hM⟩ := hK.bddAbove_image hΦc
    set bound : ℝ × ℝ → ℝ := fun a => max M 0 *
      (((a.1 ^ (A / 2 - 1) + a.1 ^ (A + 1 - 1)) * Real.exp (-c * a.1)) *
        ((a.2 ^ (B / 2 - 1) + a.2 ^ (B + 1 - 1)) * Real.exp (-c * a.2)))
    refine ⟨Metric.closedBall P r, bound, Metric.closedBall_mem_nhds P hr, ?_, ?_⟩
    · have := (integrableOn_rpow_add_rpow_mul_exp_mul (by linarith : 0 < A / 2)
        (by linarith : 0 < A + 1) hc).mul_prod (integrableOn_rpow_add_rpow_mul_exp_mul
          (by linarith : 0 < B / 2) (by linarith : 0 < B + 1) hc)
      exact this.const_mul _
    · filter_upwards [ae_quadrantMeasure] with a ha q hq
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hball hq
      have hq2 : q.2 ≠ 0 := fun h => by rw [h] at h5; simp at h5; linarith
      have hMq : Φ q ≤ max M 0 := (hM (mem_image_of_mem _ hq)).trans (le_max_left _ _)
      have hE : ‖expRemainder n ((a.1 : ℂ) * q.2 * ((a.2 : ℂ) * q.2) * q.1.2.2)‖ ≤ 1 := by
        refine norm_expRemainder_le n ?_
        have : ((a.1 : ℂ) * q.2 * ((a.2 : ℂ) * q.2) * q.1.2.2).re =
            a.1 * a.2 * (q.2 ^ 2 * q.1.2.2).re := by
          rw [show (a.1 : ℂ) * q.2 * ((a.2 : ℂ) * q.2) * q.1.2.2 =
            ((a.1 * a.2 : ℝ) : ℂ) * (q.2 ^ 2 * q.1.2.2) by push_cast; ring, re_ofReal_mul]
        rw [this]
        exact mul_nonpos_of_nonneg_of_nonpos (mul_pos ha.1 ha.2).le h6.le
      have hexp : ∀ {s : ℝ}, 0 < s → ‖exp (-((s : ℂ) * q.2))‖ ≤ Real.exp (-c * s) := by
        intro s hs
        rw [norm_exp, neg_re, re_ofReal_mul]
        exact Real.exp_le_exp.mpr (by nlinarith)
      simp only [F, twoF0RotIntegrand, twoF0Integrand, bound]
      simp only [norm_mul]
      rw [norm_ofReal_mul_cpow ha.1 hq2, norm_ofReal_mul_cpow ha.2 hq2, norm_pow]
      have hs := Real.rpow_le_rpow_add_rpow ha.1 (c₁ := A / 2 - 1) (c := (q.1.1 + (n : ℂ) - 1).re)
        (c₂ := A + 1 - 1) (by simp only [sub_re, one_re]; linarith)
        (by simp only [sub_re, one_re]; linarith)
      have ht := Real.rpow_le_rpow_add_rpow ha.2 (c₁ := B / 2 - 1)
        (c := (q.1.2.1 + (n : ℂ) - 1).re) (c₂ := B + 1 - 1)
        (by simp only [sub_re, one_re]; linarith) (by simp only [sub_re, one_re]; linarith)
      have e1 := hexp ha.1
      have e2 := hexp ha.2
      have p1 := Real.rpow_nonneg ha.1.le (q.1.1 + (n : ℂ) - 1).re
      have p2 := Real.rpow_nonneg ha.2.le (q.1.2.1 + (n : ℂ) - 1).re
      have hΦ0 : 0 ≤ Φ q := by positivity
      calc _ = Φ q * ((a.1 ^ (q.1.1 + (n : ℂ) - 1).re * ‖exp (-((a.1 : ℂ) * q.2))‖) *
              (a.2 ^ (q.1.2.1 + (n : ℂ) - 1).re * ‖exp (-((a.2 : ℂ) * q.2))‖)) *
              ‖expRemainder n ((a.1 : ℂ) * q.2 * ((a.2 : ℂ) * q.2) * q.1.2.2)‖ := by
            simp only [Φ]; ring
        _ ≤ max M 0 * ((((a.1 ^ (A / 2 - 1) + a.1 ^ (A + 1 - 1)) * Real.exp (-c * a.1))) *
              ((a.2 ^ (B / 2 - 1) + a.2 ^ (B + 1 - 1)) * Real.exp (-c * a.2))) * 1 := by
            have q1 := Real.rpow_nonneg ha.1.le (A / 2 - 1)
            have q2 := Real.rpow_nonneg ha.1.le (A + 1 - 1)
            have q3 := Real.rpow_nonneg ha.2.le (B / 2 - 1)
            have q4 := Real.rpow_nonneg ha.2.le (B + 1 - 1)
            gcongr
        _ = _ := by ring

/-- Along the unrotated rays the rotated integral is Carlson's remainder integral. -/
theorem twoF0DoubleRot_one (n : ℕ) (α β x : ℂ) : twoF0DoubleRot n α β x 1 =
    twoF0Double n α β x := by
  simp [twoF0DoubleRot, twoF0Double, twoF0RotIntegrand, twoF0Integrand, eulerDensity]

/-- **Radial invariance**: scaling the direction by a positive factor does not change the rotated
integral (substitution `s ↦ ρ s`, `t ↦ ρ t`). -/
theorem twoF0DoubleRot_ofReal_mul (n : ℕ) (α β x w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    twoF0DoubleRot n α β x (ρ * w) = twoF0DoubleRot n α β x w := by
  set Q : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 0
  have hmQ : MeasurableSet Q := measurableSet_Ioi.prod measurableSet_Ioi
  set H : ℝ × ℝ → ℂ := fun a => twoF0RotIntegrand n (((α, β, x), w), ((a.1 : ℂ), (a.2 : ℂ)))
  set H' : ℝ × ℝ → ℂ := fun a =>
    twoF0RotIntegrand n (((α, β, x), (ρ : ℂ) * w), ((a.1 : ℂ), (a.2 : ℂ)))
  have hQ : quadrantMeasure = (volume : Measure (ℝ × ℝ)).restrict Q := by
    rw [quadrantMeasure, Measure.prod_restrict, Measure.volume_eq_prod]
  have hmem : ∀ a : ℝ × ℝ, ρ • a ∈ Q ↔ a ∈ Q := fun a => by
    simp only [Q, mem_prod, mem_Ioi, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨pos_of_mul_pos_right h1 hρ.le, pos_of_mul_pos_right h2 hρ.le⟩
    · rintro ⟨h1, h2⟩; exact ⟨mul_pos hρ h1, mul_pos hρ h2⟩
  have key : ∀ a : ℝ × ℝ, Q.indicator H' a = ((ρ : ℂ) ^ 2) * Q.indicator H (ρ • a) := by
    intro a
    by_cases ha : a ∈ Q
    · rw [indicator_of_mem ha, indicator_of_mem ((hmem a).mpr ha)]
      simp only [H, H', twoF0RotIntegrand, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      push_cast
      rw [show (a.1 : ℂ) * (ρ * w) = ρ * a.1 * w by ring,
        show (a.2 : ℂ) * (ρ * w) = ρ * a.2 * w by ring]
      ring
    · rw [indicator_of_notMem ha, indicator_of_notMem (fun h => ha ((hmem a).mp h)), mul_zero]
  have h1 : twoF0DoubleRot n α β x (ρ * w) = ∫ a, Q.indicator H' a := by
    rw [twoF0DoubleRot, hQ, integral_indicator hmQ]
  have h2 : twoF0DoubleRot n α β x w = ∫ a, Q.indicator H a := by
    rw [twoF0DoubleRot, hQ, integral_indicator hmQ]
  rw [h1, h2, integral_congr_ae (Eventually.of_forall key), MeasureTheory.integral_const_mul,
    Measure.integral_comp_smul (volume : Measure (ℝ × ℝ)) (Q.indicator H) ρ]
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hfin, abs_of_pos (by positivity), Complex.real_smul]
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  push_cast
  field_simp

/-- The rotated integral is holomorphic in the direction. -/
theorem analyticAt_twoF0DoubleRot_dir (n : ℕ) {α β x w : ℂ}
    (h : ((α, β, x), w) ∈ twoF0RotDomain n) :
    AnalyticAt ℂ (fun u => twoF0DoubleRot n α β x u) w :=
  (analyticOnNhd_twoF0DoubleRot n _ h).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl

/-- The derivative of the rotated integral in the direction vanishes. -/
theorem deriv_twoF0DoubleRot_dir (n : ℕ) {α β x w : ℂ}
    (h : ((α, β, x), w) ∈ twoF0RotDomain n) :
    deriv (fun u => twoF0DoubleRot n α β x u) w = 0 := by
  set g := fun u => twoF0DoubleRot n α β x u
  have hg := (analyticAt_twoF0DoubleRot_dir n h).differentiableAt.hasDerivAt
  have he : HasDerivAt (fun u : ℂ => g (u * w)) (deriv g w * w) 1 := by
    have hg1 : HasDerivAt g (deriv g w) (1 * w) := by rwa [one_mul]
    exact hg1.comp (1 : ℂ) (hasDerivAt_mul_const w)
  have hr : HasDerivAt (fun y : ℝ => g ((y : ℂ) * w)) (deriv g w * w) 1 :=
    (by simpa using he : HasDerivAt (fun u : ℂ => g (u * w)) (deriv g w * w)
        ((1 : ℝ) : ℂ)).comp_ofReal
  have hc : HasDerivAt (fun y : ℝ => g ((y : ℂ) * w)) 0 1 := by
    apply (hasDerivAt_const (1 : ℝ) (g w)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
    exact twoF0DoubleRot_ofReal_mul n α β x w hy
  have h0 := hr.unique hc
  have hw : w ≠ 0 := fun h0 => by have := h.2.2.1; rw [h0] at this; simp at this
  exact (mul_eq_zero.mp h0).resolve_right hw

/-- The admissible directions for `x = -e^ζ` with `im ζ = v`: angles `θ` with `|θ| < π/2`
(convergence of the Euler measures) and `|2θ + v| < π/2` (so that `re (s t x) ≤ 0`). -/
def twoF0Angles (v : ℝ) : Set ℝ := {θ | |θ| < π / 2 ∧ |2 * θ + v| < π / 2}

/-- The admissible angles form an open interval. -/
theorem twoF0Angles_eq (v : ℝ) :
    twoF0Angles v = Ioo (-(π / 2)) (π / 2) ∩ Ioo ((-(π / 2) - v) / 2) ((π / 2 - v) / 2) := by
  ext θ
  simp only [twoF0Angles, mem_ofPred_eq, mem_inter_iff, mem_Ioo, abs_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h2⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h2⟩, by linarith, by linarith⟩

/-- An admissible angle gives a point of the rotated domain. -/
theorem mem_twoF0RotDomain_of_mem_twoF0Angles (n : ℕ) {α β ζ : ℂ} (hα : 0 < (α + n).re)
    (hβ : 0 < (β + n).re) {θ : ℝ} (hθ : θ ∈ twoF0Angles ζ.im) :
    ((α, β, -exp ζ), exp (θ * I)) ∈ twoF0RotDomain n := by
  obtain ⟨h1, h2⟩ := hθ
  refine ⟨hα, hβ, ?_, ?_⟩
  · have : (exp (θ * I)).re = Real.cos θ := by rw [exp_re]; simp
    rw [this]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp h1).1], (abs_lt.mp h1).2⟩
  · have : exp (θ * I) ^ 2 * -exp ζ = -exp (ζ + (2 * θ : ℝ) * I) := by
      rw [← exp_nat_mul, mul_neg, ← exp_add]; congr 2; push_cast; ring
    rw [this, neg_re, exp_re, neg_lt_zero]
    apply mul_pos (Real.exp_pos _)
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp h2).1], by linarith [(abs_lt.mp h2).2]⟩

/-- **Rotation invariance**: for `x = -e^ζ`, the rotated remainder integral takes the same value
for all admissible directions. -/
theorem twoF0DoubleRot_angle_eq (n : ℕ) {α β ζ : ℂ} (hα : 0 < (α + n).re)
    (hβ : 0 < (β + n).re) {θ₁ θ₂ : ℝ} (h₁ : θ₁ ∈ twoF0Angles ζ.im) (h₂ : θ₂ ∈ twoF0Angles ζ.im) :
    twoF0DoubleRot n α β (-exp ζ) (exp (θ₁ * I)) =
        twoF0DoubleRot n α β (-exp ζ) (exp (θ₂ * I)) := by
  set h : ℝ → ℂ := fun θ => twoF0DoubleRot n α β (-exp ζ) (exp (θ * I))
  have hopen : IsOpen (twoF0Angles ζ.im) := by
    rw [twoF0Angles_eq]; exact isOpen_Ioo.inter isOpen_Ioo
  have hconn : IsPreconnected (twoF0Angles ζ.im) := by
    rw [twoF0Angles_eq]; exact ((convex_Ioo _ _).inter (convex_Ioo _ _)).isPreconnected
  have hd : ∀ θ ∈ twoF0Angles ζ.im, HasDerivAt h 0 θ := by
    intro θ hθ
    have hg := (analyticAt_twoF0DoubleRot_dir n
      (mem_twoF0RotDomain_of_mem_twoF0Angles n hα hβ hθ)).differentiableAt.hasDerivAt
    rw [deriv_twoF0DoubleRot_dir n (mem_twoF0RotDomain_of_mem_twoF0Angles n hα hβ hθ)] at hg
    have he : HasDerivAt (fun u : ℂ => exp (u * I)) (exp ((θ : ℂ) * I) * I) (θ : ℂ) := by
      simpa using ((hasDerivAt_id (θ : ℂ)).mul_const I).cexp
    have := (hg.comp (θ : ℂ) he).comp_ofReal
    simpa using this
  exact hopen.is_const_of_deriv_eq_zero hconn
      (fun θ hθ => (hd θ hθ).differentiableAt.differentiableWithinAt)
    (fun θ hθ => (hd θ hθ).deriv) h₁ h₂

/-! ### The continuation to the sector `|ph(-x)| < 3π/2` -/

/-- Carlson's representation (5.12-12) along the rays in direction `w`, with `n` explicit terms. -/
def twoF0RepRot (n : ℕ) (α β x w : ℂ) : ℂ :=
  ∑ m ∈ Finset.range n, twoF0Term m α β x + twoF0Term n α β x * twoF0DoubleRot n α β x w

/-- Along the unrotated rays the rotated representation is (5.12-10). -/
theorem twoF0RepRot_one (n : ℕ) (α β x : ℂ) : twoF0RepRot n α β x 1 = twoF0Rep n α β x := by
  rw [twoF0RepRot, twoF0Rep, twoF0DoubleRot_one]

/-- Rotation invariance of the representation. -/
theorem twoF0RepRot_angle_eq (n : ℕ) {α β ζ : ℂ} (hα : 0 < (α + n).re) (hβ : 0 < (β + n).re)
    {θ₁ θ₂ : ℝ} (h₁ : θ₁ ∈ twoF0Angles ζ.im) (h₂ : θ₂ ∈ twoF0Angles ζ.im) :
    twoF0RepRot n α β (-exp ζ) (exp (θ₁ * I)) = twoF0RepRot n α β (-exp ζ) (exp (θ₂ * I)) := by
  rw [twoF0RepRot, twoF0RepRot, twoF0DoubleRot_angle_eq n hα hβ h₁ h₂]

/-- The terms of the `₂F₀` series are entire in `(α, β, x)`. -/
theorem analyticAt_twoF0Term {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ)
    {α β x : E → ℂ} {e : E} (hα : AnalyticAt ℂ α e) (hβ : AnalyticAt ℂ β e)
    (hx : AnalyticAt ℂ x e) : AnalyticAt ℂ (fun e => twoF0Term m (α e) (β e) (x e)) e := by
  unfold twoF0Term
  have h1 : AnalyticAt ℂ (fun e => (ascPochhammer ℂ m).eval (α e)) e :=
    (Differentiable.analyticAt (Polynomial.differentiable _) _).comp_of_eq hα rfl
  have h2 : AnalyticAt ℂ (fun e => (ascPochhammer ℂ m).eval (β e)) e :=
    (Differentiable.analyticAt (Polynomial.differentiable _) _).comp_of_eq hβ rfl
  exact ((h1.mul h2).mul (hx.pow m)).div_const

/-- The rotated representation is holomorphic in `(α, β, ζ)` for `x = -e^ζ` and a fixed
admissible direction. -/
theorem analyticAt_twoF0RepRot_exp (n : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {α β ζ : E → ℂ} {e : E} (hα : AnalyticAt ℂ α e) (hβ : AnalyticAt ℂ β e)
    (hζ : AnalyticAt ℂ ζ e) {θ : ℝ} (hαn : 0 < (α e + n).re) (hβn : 0 < (β e + n).re)
    (hθ : θ ∈ twoF0Angles (ζ e).im) :
    AnalyticAt ℂ (fun e => twoF0RepRot n (α e) (β e) (-exp (ζ e)) (exp (θ * I))) e := by
  have hx : AnalyticAt ℂ (fun e => -exp (ζ e)) e := hζ.cexp.neg
  have hD := (analyticOnNhd_twoF0DoubleRot n _
    (mem_twoF0RotDomain_of_mem_twoF0Angles n hαn hβn hθ)).comp_of_eq
      ((hα.prod (hβ.prod hx)).prod analyticAt_const) rfl
  unfold twoF0RepRot
  exact (Finset.analyticAt_fun_sum _ fun m _ => analyticAt_twoF0Term m hα hβ hx).add
    ((analyticAt_twoF0Term n hα hβ hx).mul hD)

/-- The strip `{ζ : |2θ + im ζ| < π/2}` of variables for which the direction `e^{iθ}` is
admissible. -/
theorem isPreconnected_twoF0Strip (θ : ℝ) :
    IsPreconnected {ζ : ℂ | |2 * θ + ζ.im| < π / 2} := by
  apply Convex.isPreconnected
  intro a ha b hb s t hs ht hst
  simp only [mem_ofPred_eq, add_im, smul_im, smul_eq_mul] at ha hb ⊢
  rw [abs_lt] at ha hb ⊢
  have : 2 * θ + (s * a.im + t * b.im) = s * (2 * θ + a.im) + t * (2 * θ + b.im) := by
    have : 2 * θ = (s + t) * (2 * θ) := by rw [hst, one_mul]
    linarith [this]
  rw [this]
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  rcases hs.lt_or_eq with hs' | hs'
  · have e1 := mul_pos hs' (sub_pos.mpr ha1)
    have e2 := mul_pos hs' (sub_pos.mpr ha2)
    have e3 := mul_nonneg ht (sub_pos.mpr hb1).le
    have e4 := mul_nonneg ht (sub_pos.mpr hb2).le
    constructor <;> nlinarith
  · subst hs'
    have ht1 : t = 1 := by linarith
    subst ht1
    constructor <;> linarith

/-- **Independence of the number of explicit terms** for the rotated representation. -/
theorem twoF0RepRot_eq_of_le {n k : ℕ} {α β ζ : ℂ} (hα : 0 < (α + n).re) (hβ : 0 < (β + n).re)
    {θ : ℝ} (hθ : θ ∈ twoF0Angles ζ.im) :
    twoF0RepRot n α β (-exp ζ) (exp (θ * I)) = twoF0RepRot (n + k) α β (-exp ζ) (exp (θ * I)) := by
  have hαk : 0 < (α + ((n + k : ℕ) : ℂ)).re := by
    push_cast; simp only [add_re, natCast_re] at hα ⊢; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hβk : 0 < (β + ((n + k : ℕ) : ℂ)).re := by
    push_cast; simp only [add_re, natCast_re] at hβ ⊢; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hθ' : |θ| < π / 2 := hθ.1
  set S : Set ℂ := {ζ : ℂ | |2 * θ + ζ.im| < π / 2}
  have hSo : IsOpen S := isOpen_lt (by fun_prop) continuous_const
  have hmem : ∀ ζ' ∈ S, θ ∈ twoF0Angles ζ'.im := fun ζ' h => ⟨hθ', h⟩
  have hf : ∀ m : ℕ, 0 < (α + m).re → 0 < (β + m).re → AnalyticOnNhd ℂ
      (fun ζ' => twoF0RepRot m α β (-exp ζ') (exp (θ * I))) S := fun m h1 h2 ζ' h =>
    analyticAt_twoF0RepRot_exp m analyticAt_const analyticAt_const analyticAt_id h1 h2 (hmem ζ' h)
  -- a point of the strip where the unrotated rays are also admissible
  set ζ₀ : ℂ := ((-θ : ℝ) : ℂ) * I
  have hζ₀ : ζ₀.im = -θ := by simp [ζ₀]
  have h0 : ∀ᶠ ζ' in 𝓝 ζ₀, ζ' ∈ S ∧ (0 : ℝ) ∈ twoF0Angles ζ'.im := by
    have hc : Continuous fun ζ' : ℂ => ζ'.im := Complex.continuous_im
    have hπ := Real.pi_pos
    have hθ2 := abs_lt.mp hθ'
    filter_upwards [(isOpen_lt (by fun_prop) continuous_const : IsOpen S).mem_nhds
        (show ζ₀ ∈ S by
          show |2 * θ + ζ₀.im| < π / 2
          rw [hζ₀, show 2 * θ + -θ = θ by ring]; exact hθ'),
      (isOpen_lt (hc.abs) continuous_const).mem_nhds
        (show ζ₀ ∈ {ζ' : ℂ | |ζ'.im| < π / 2} by
          show |ζ₀.im| < π / 2
          rw [hζ₀, abs_neg]; exact hθ')] with ζ' h1 h2
    refine ⟨h1, by simp; linarith [Real.pi_pos], ?_⟩
    simpa using h2
  have heq := (hf n hα hβ).eqOn_of_preconnected_of_eventuallyEq (hf (n + k) hαk hβk)
    (isPreconnected_twoF0Strip θ) (h0.self_of_nhds.1) (by
      filter_upwards [h0] with ζ' h
      rw [twoF0RepRot_angle_eq n hα hβ (hmem ζ' h.1) h.2,
        twoF0RepRot_angle_eq (n + k) hαk hβk (hmem ζ' h.1) h.2]
      simp only [ofReal_zero, zero_mul, exp_zero, twoF0RepRot_one]
      have hx : (-exp ζ').re ≤ 0 := by
        rw [neg_re, exp_re, neg_nonpos]
        exact mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [(abs_lt.mp h.2.2).1], by linarith [(abs_lt.mp h.2.2).2]⟩)
      rw [← carlson2F0_eq_twoF0Rep hα hβ hx, ← carlson2F0_eq_twoF0Rep hαk hβk hx])
  exact heq hθ.2

/-- The general form of independence of the number of explicit terms. -/
theorem twoF0RepRot_eq {n m : ℕ} {α β ζ : ℂ} (hαn : 0 < (α + n).re) (hβn : 0 < (β + n).re)
    (hαm : 0 < (α + m).re) (hβm : 0 < (β + m).re) {θ : ℝ} (hθ : θ ∈ twoF0Angles ζ.im) :
    twoF0RepRot n α β (-exp ζ) (exp (θ * I)) = twoF0RepRot m α β (-exp ζ) (exp (θ * I)) := by
  rcases le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact twoF0RepRot_eq_of_le hαn hβn hθ
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (twoF0RepRot_eq_of_le hαm hβm hθ).symm

/-- Carlson's angle `φ = -(1/3) ph(-x)`, for `ph(-x) = im ζ`. -/
def twoF0Angle (ζ : ℂ) : ℝ := -ζ.im / 3

/-- Carlson's angle is admissible throughout the sector `|ph(-x)| < 3π/2`. -/
theorem twoF0Angle_mem {ζ : ℂ} (hζ : |ζ.im| < 3 * π / 2) : twoF0Angle ζ ∈ twoF0Angles ζ.im := by
  have h := abs_lt.mp hζ
  constructor
  · rw [twoF0Angle, abs_lt]; constructor <;> linarith
  · rw [twoF0Angle, abs_lt]; constructor <;> linarith

/-- **Carlson's `₂F₀` on the sector `|ph(-x)| < 3π/2` (Theorem 5.12-6)**, as a function of
`ζ = log(-x)`: `x = -e^ζ` with `|im ζ| < 3π/2`, so that `ph(-x) = im ζ`. It is given by the
representation (5.12-12) along the rays at Carlson's angle `φ = -(im ζ)/3`. -/
@[irreducible] def carlson2F0Sector (α β ζ : ℂ) : ℂ :=
  twoF0RepRot (twoF0Depth α β) α β (-exp ζ) (exp (twoF0Angle ζ * I))

/-- **Formula (5.12-12)**: the sector function is represented along the rays in any admissible
direction, with any number `n` of explicit terms such that `re (α + n), re (β + n) > 0`. -/
theorem carlson2F0Sector_eq_twoF0RepRot {n : ℕ} {α β ζ : ℂ} (hα : 0 < (α + n).re)
    (hβ : 0 < (β + n).re) (hζ : |ζ.im| < 3 * π / 2) {θ : ℝ} (hθ : θ ∈ twoF0Angles ζ.im) :
    carlson2F0Sector α β ζ = twoF0RepRot n α β (-exp ζ) (exp (θ * I)) := by
  obtain ⟨hα', hβ'⟩ := re_add_twoF0Depth_pos α β
  rw [carlson2F0Sector, twoF0RepRot_angle_eq _ hα' hβ' (twoF0Angle_mem hζ) hθ]
  exact twoF0RepRot_eq hα' hβ' hα hβ hθ

/-- **Theorem 5.12-6**: the sector function agrees with the continued `₂F₀` of Theorem 5.12-4
for `|ph(-x)| < π/2`. -/
theorem carlson2F0Sector_eq_carlson2F0 (α β : ℂ) {ζ : ℂ} (hζ : |ζ.im| < π / 2) :
    carlson2F0Sector α β ζ = carlson2F0 α β (-exp ζ) := by
  obtain ⟨hα, hβ⟩ := re_add_twoF0Depth_pos α β
  have h0 : (0 : ℝ) ∈ twoF0Angles ζ.im := ⟨by simp; positivity, by simpa using hζ⟩
  have hx : (-exp ζ).re ≤ 0 := by
    rw [neg_re, exp_re, neg_nonpos]
    exact mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [(abs_lt.mp hζ).1], by linarith [(abs_lt.mp hζ).2]⟩)
  rw [carlson2F0Sector_eq_twoF0RepRot hα hβ (by linarith [Real.pi_pos]) h0,
    carlson2F0_eq_twoF0Rep hα hβ hx]
  simp [twoF0RepRot_one]

/-- The sector of `ζ = log(-x)` in which Carlson's continuation is defined. -/
def twoF0SectorDomain : Set (ℂ × ℂ × ℂ) := {p | |p.2.2.im| < 3 * π / 2}

/-- **Theorem 5.12-6** (holomorphy): `₂F₀(α, β; -e^ζ)` is holomorphic in `(α, β, ζ)` on
`ℂ² × {|im ζ| < 3π/2}`. -/
theorem analyticOnNhd_carlson2F0Sector :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => carlson2F0Sector p.1 p.2.1 p.2.2) twoF0SectorDomain := by
  intro p hp
  set N := twoF0Depth p.1 p.2.1
  obtain ⟨hα, hβ⟩ := re_add_twoF0Depth_pos p.1 p.2.1
  set θ := twoF0Angle p.2.2
  have hθ := twoF0Angle_mem hp
  have hα' : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.1) p := analyticAt_fst
  have hβ' : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.1) p :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).analyticAt p
  have hζ' : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.2) p :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).analyticAt p
  have hA := analyticAt_twoF0RepRot_exp N hα' hβ' hζ' hα hβ hθ
  refine hA.congr ?_
  have c1 : Continuous fun q : ℂ × ℂ × ℂ => (q.1 + (N : ℂ)).re := by fun_prop
  have c2 : Continuous fun q : ℂ × ℂ × ℂ => (q.2.1 + (N : ℂ)).re := by fun_prop
  have c3 : Continuous fun q : ℂ × ℂ × ℂ => |q.2.2.im| := by fun_prop
  have c4 : Continuous fun q : ℂ × ℂ × ℂ => |2 * θ + q.2.2.im| := by fun_prop
  filter_upwards [c1.continuousAt.eventually_const_lt hα, c2.continuousAt.eventually_const_lt hβ,
    c3.continuousAt.eventually_lt_const hp, c4.continuousAt.eventually_lt_const hθ.2]
        with q h1 h2 h3 h4
  exact (carlson2F0Sector_eq_twoF0RepRot h1 h2 h3 ⟨hθ.1, h4⟩).symm

/-- The sector domain is preconnected. -/
theorem isPreconnected_twoF0SectorDomain : IsPreconnected twoF0SectorDomain := by
  apply Convex.isPreconnected
  intro a ha b hb s t hs ht hst
  simp only [twoF0SectorDomain, mem_ofPred_eq, Prod.smul_snd, Prod.snd_add, add_im, smul_im,
    smul_eq_mul] at ha hb ⊢
  calc |s * a.2.2.im + t * b.2.2.im| ≤ s * |a.2.2.im| + t * |b.2.2.im| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
    _ < 3 * π / 2 := by
        rcases hs.lt_or_eq with hs' | hs'
        · have e1 := mul_lt_mul_of_pos_left ha hs'
          have e2 := mul_le_mul_of_nonneg_left hb.le ht
          have e3 : s * (3 * π / 2) + t * (3 * π / 2) = 3 * π / 2 := by
            rw [← add_mul, hst, one_mul]
          linarith
        · subst hs'; simp only [zero_mul, zero_add] at hst ⊢; subst hst; simpa using hb

/-- **Theorem 5.12-2 on the sector**: `₂F₀(α, β; x) = ₂F₀(β, α; x)`. -/
theorem carlson2F0Sector_comm (α β ζ : ℂ) (hζ : |ζ.im| < 3 * π / 2) :
    carlson2F0Sector α β ζ = carlson2F0Sector β α ζ := by
  have hf := analyticOnNhd_carlson2F0Sector
  have hg : AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => carlson2F0Sector p.2.1 p.1 p.2.2)
      twoF0SectorDomain := fun p hp =>
    (hf (p.2.1, p.1, p.2.2) hp).comp_of_eq
      ((((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
          (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).analyticAt p).prod
      (analyticAt_fst.prod
        (((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
          (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).analyticAt p)))
      rfl
  have h0 : ((α, β, (0 : ℂ)) : ℂ × ℂ × ℂ) ∈ twoF0SectorDomain := by
    show |(0 : ℂ).im| < 3 * π / 2; simp; positivity
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_twoF0SectorDomain h0 (by
    have c : Continuous fun q : ℂ × ℂ × ℂ => |q.2.2.im| := by fun_prop
    filter_upwards [c.continuousAt.eventually_lt_const (show |(0 : ℂ).im| < π / 2 by
      simp; positivity)] with q hq
    rw [carlson2F0Sector_eq_carlson2F0 _ _ hq, carlson2F0Sector_eq_carlson2F0 _ _ hq]
    exact carlson2F0_comm _ _ _ (by
      rw [neg_re, exp_re, neg_nonpos]
      exact mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [(abs_lt.mp hq).1], by linarith [(abs_lt.mp hq).2]⟩)))
  exact heq (show ((α, β, ζ) : ℂ × ℂ × ℂ) ∈ twoF0SectorDomain from hζ)

/-! ### Error bounds on the sector -/

/-- The total variation of the Euler measure along the ray in direction `e^{iθ}`. -/
def rotEulerVariation (a : ℂ) (θ : ℝ) : ℝ :=
  Real.Gamma a.re / ‖Gamma a‖ * (Real.exp (-(θ * a.im)) / Real.cos θ ^ a.re)

/-- The norm of the rotated remainder integral is at most the product of the total variations
of the two rotated Euler measures. -/
theorem norm_twoF0DoubleRot_le (n : ℕ) {α β x : ℂ} (hα : 0 < (α + n).re) (hβ : 0 < (β + n).re)
    {θ : ℝ} (hθ : |θ| < π / 2) (hx : (exp (θ * I) ^ 2 * x).re ≤ 0) :
    ‖twoF0DoubleRot n α β x (exp (θ * I))‖ ≤
      rotEulerVariation (α + n) θ * rotEulerVariation (β + n) θ := by
  set w := exp (θ * I)
  have hθ' := abs_lt.mp hθ
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hw0 : w ≠ 0 := exp_ne_zero _
  have hnw : ‖w‖ = 1 := by simp [w, norm_exp]
  have harg : arg w = θ := by
    rw [arg_exp_mul_I, toIocMod_eq_self]; constructor <;> linarith [Real.pi_pos]
  have hrew : w.re = Real.cos θ := by simp [w, exp_re]
  set f : ℂ → ℝ → ℝ := fun a s => ‖(Gamma a)⁻¹‖ * Real.exp (-(θ * a.im)) *
    (s ^ (a.re - 1) * Real.exp (-(Real.cos θ * s)))
  have hf : ∀ a : ℂ, 0 < a.re → IntegrableOn (f a) (Ioi 0) := fun a ha => by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a.re - 1) (b := Real.cos θ)
      (by linarith) one_pos hcos
    exact IntegrableOn.congr_fun
        (Integrable.const_mul this (‖(Gamma a)⁻¹‖ * Real.exp (-(θ * a.im))))
      (fun s _ => by simp only [f, Real.rpow_one, neg_mul]) measurableSet_Ioi
  have hfint : ∀ a : ℂ, 0 < a.re → ∫ s in Ioi (0 : ℝ), f a s = rotEulerVariation a θ := by
    intro a ha
    simp only [f]
    rw [MeasureTheory.integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ha hcos,
      rotEulerVariation, norm_inv, one_div, Real.inv_rpow hcos.le]
    field_simp
  have hdom : ∀ᵐ a ∂quadrantMeasure, ‖twoF0RotIntegrand n (((α, β, x), w), ((a.1 : ℂ), (a.2 : ℂ)))‖
      ≤ f (α + n) a.1 * f (β + n) a.2 := by
    filter_upwards [ae_quadrantMeasure] with a ha
    have hE : ‖expRemainder n ((a.1 : ℂ) * w * ((a.2 : ℂ) * w) * x)‖ ≤ 1 := by
      refine norm_expRemainder_le n ?_
      rw [show (a.1 : ℂ) * w * ((a.2 : ℂ) * w) * x = ((a.1 * a.2 : ℝ) : ℂ) * (w ^ 2 * x) by
        push_cast; ring, re_ofReal_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_pos ha.1 ha.2).le hx
    have hexp : ∀ {s : ℝ}, ‖exp (-((s : ℂ) * w))‖ = Real.exp (-(Real.cos θ * s)) := by
      intro s; rw [norm_exp, neg_re, re_ofReal_mul, hrew]; ring_nf
    simp only [twoF0RotIntegrand, twoF0Integrand, norm_mul]
    rw [norm_ofReal_mul_cpow ha.1 hw0, norm_ofReal_mul_cpow ha.2 hw0, hexp, hexp, norm_pow, hnw,
      harg]
    simp only [Real.one_rpow, one_pow, sub_im, one_im, sub_zero, f]
    have hE0 := norm_nonneg (expRemainder n ((a.1 : ℂ) * w * ((a.2 : ℂ) * w) * x))
    have key : ∀ (g : ℝ) (A : ℂ) (s : ℝ),
        ‖(Gamma A)⁻¹‖ * (s ^ (A - 1).re * (1 / Real.exp (θ * A.im)) *
        Real.exp (-(Real.cos θ * s))) = ‖(Gamma A)⁻¹‖ * Real.exp (-(θ * A.im)) *
          (s ^ (A.re - 1) * Real.exp (-(Real.cos θ * s))) := by
      intro _ A s; simp only [Real.exp_neg, sub_re, one_re]; ring
    rw [key 0 (α + n) a.1, key 0 (β + n) a.2]
    have hF := mul_nonneg (show 0 ≤ ‖(Gamma (α + n))⁻¹‖ * Real.exp (-(θ * (α + n).im)) *
      (a.1 ^ ((α + n).re - 1) * Real.exp (-(Real.cos θ * a.1))) from
        mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
          (mul_nonneg (Real.rpow_nonneg ha.1.le _) (Real.exp_pos _).le))
      (show 0 ≤ ‖(Gamma (β + n))⁻¹‖ * Real.exp (-(θ * (β + n).im)) *
      (a.2 ^ ((β + n).re - 1) * Real.exp (-(Real.cos θ * a.2))) from
        mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
          (mul_nonneg (Real.rpow_nonneg ha.2.le _) (Real.exp_pos _).le))
    nlinarith
  have hint : Integrable (fun a : ℝ × ℝ => f (α + n) a.1 * f (β + n) a.2) quadrantMeasure :=
    (hf _ hα).mul_prod (hf _ hβ)
  rw [twoF0DoubleRot]
  refine (norm_integral_le_of_norm_le hint hdom).trans (le_of_eq ?_)
  rw [quadrantMeasure, integral_prod_mul, hfint _ hα, hfint _ hβ]

/-- **Theorem 5.12-7, error bound (5.12-15)** on the whole sector `|ph(-x)| < 3π/2`: with
`φ = -(1/3) ph(-x)` and `re (α + n), re (β + n) > 0`, the error of the `n`-th partial sum of the
`₂F₀` series is at most the first omitted term times
`Γ(re(α+n)) Γ(re(β+n)) e^{-φ im(α+β)} / (|Γ(α+n) Γ(β+n)| (cos φ)^{re(α+β)+2n})`. -/
theorem norm_carlson2F0Sector_sub_sum_le (n : ℕ) {α β ζ : ℂ} (hα : 0 < (α + n).re)
    (hβ : 0 < (β + n).re) (hζ : |ζ.im| < 3 * π / 2) :
    ‖carlson2F0Sector α β ζ - ∑ m ∈ Finset.range n, twoF0Term m α β (-exp ζ)‖ ≤
      ‖twoF0Term n α β (-exp ζ)‖ *
        (rotEulerVariation (α + n) (twoF0Angle ζ) * rotEulerVariation (β + n) (twoF0Angle ζ)) := by
  have hθ := twoF0Angle_mem hζ
  rw [carlson2F0Sector_eq_twoF0RepRot hα hβ hζ hθ, twoF0RepRot, add_sub_cancel_left, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_twoF0DoubleRot_le n hα hβ hθ.1
    (mem_twoF0RotDomain_of_mem_twoF0Angles n hα hβ hθ).2.2.2.le) (norm_nonneg _)

/-- A uniform bound for the rotated total variation on a closed subsector. -/
theorem rotEulerVariation_le {a : ℂ} (ha : 0 < a.re) {c θ : ℝ} (hc : 0 < c)
    (hcθ : c ≤ Real.cos θ) (hθ : |θ| ≤ π / 2) :
    rotEulerVariation a θ ≤ Real.Gamma a.re / ‖Gamma a‖ *
        (Real.exp (π / 2 * |a.im|) / c ^ a.re) := by
  unfold rotEulerVariation
  have hG : 0 ≤ Real.Gamma a.re / ‖Gamma a‖ :=
      div_nonneg (Real.Gamma_pos_of_pos ha).le (norm_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ hG
  have h1 : Real.exp (-(θ * a.im)) ≤ Real.exp (π / 2 * |a.im|) := by
    apply Real.exp_le_exp.mpr
    calc -(θ * a.im) ≤ |θ * a.im| := neg_le_abs _
      _ = |θ| * |a.im| := abs_mul _ _
      _ ≤ π / 2 * |a.im| := mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
  have h2 : c ^ a.re ≤ Real.cos θ ^ a.re := Real.rpow_le_rpow hc.le hcθ ha.le
  have h3 : 0 < c ^ a.re := Real.rpow_pos_of_pos hc _
  exact div_le_div₀ (Real.exp_pos _).le h1 h3 h2

/-- **The asymptotic expansion (5.12-17) on the sector**: for every `δ > 0` and every `n`, the
error of the `n`-th partial sum of the `₂F₀` series is `O(|x|ⁿ)` as `x → 0`, uniformly in
`|ph(-x)| ≤ 3π/2 - δ`. -/
theorem exists_norm_carlson2F0Sector_sub_sum_le (α β : ℂ) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ ζ : ℂ, |ζ.im| ≤ 3 * π / 2 - δ → ‖exp ζ‖ ≤ 1 →
      ‖carlson2F0Sector α β ζ - ∑ m ∈ Finset.range n, twoF0Term m α β (-exp ζ)‖ ≤
        C * ‖exp ζ‖ ^ n := by
  set N := n + twoF0Depth α β
  obtain ⟨hα0, hβ0⟩ := re_add_twoF0Depth_pos α β
  have hαN : 0 < (α + N).re := by
    simp only [N, add_re, natCast_re, Nat.cast_add] at hα0 ⊢
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hβN : 0 < (β + N).re := by
    simp only [N, add_re, natCast_re, Nat.cast_add] at hβ0 ⊢
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set c₀ := Real.cos (π / 2 - δ / 3)
  set c : ℕ → ℝ := fun m => ‖(ascPochhammer ℂ m).eval α * (ascPochhammer ℂ m).eval β‖ / m.factorial
  set K := Real.Gamma (α + N).re / ‖Gamma (α + N)‖ *
      (Real.exp (π / 2 * |(α + N).im|) / c₀ ^ (α + N).re) *
    (Real.Gamma (β + N).re / ‖Gamma (β + N)‖ *
      (Real.exp (π / 2 * |(β + N).im|) / c₀ ^ (β + N).re))
  refine ⟨∑ m ∈ Finset.Ico n N, c m + c N * K, fun ζ hζ hx1 => ?_⟩
  set x := -exp ζ
  have hnx : ‖x‖ = ‖exp ζ‖ := norm_neg _
  have hζ' : |ζ.im| < 3 * π / 2 := by linarith
  have hφ : |twoF0Angle ζ| ≤ π / 2 - δ / 3 := by
    rw [twoF0Angle, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  have hc₀ : 0 < c₀ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg (twoF0Angle ζ), Real.pi_pos],
    by linarith⟩
  have hcφ : c₀ ≤ Real.cos (twoF0Angle ζ) := by
    rw [← Real.cos_abs (twoF0Angle ζ)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hφ
  have hφ' : |twoF0Angle ζ| ≤ π / 2 := by linarith
  have hterm : ∀ m, ‖twoF0Term m α β x‖ = c m * ‖x‖ ^ m := fun m => by
    simp only [twoF0Term, c, norm_div, norm_mul, norm_pow, Complex.norm_natCast]; ring
  have hx1' : ‖x‖ ≤ 1 := hnx ▸ hx1
  have hpow : ∀ m, n ≤ m → ‖x‖ ^ m ≤ ‖x‖ ^ n := fun m hm =>
    pow_le_pow_of_le_one (norm_nonneg _) hx1' hm
  have hc : ∀ m, 0 ≤ c m := fun m => by positivity
  have hK : 0 ≤ K := by
    have := Real.rpow_pos_of_pos hc₀ (α + N).re
    have := Real.rpow_pos_of_pos hc₀ (β + N).re
    have := (Real.Gamma_pos_of_pos hαN).le
    have := (Real.Gamma_pos_of_pos hβN).le
    positivity
  have hsplit : carlson2F0Sector α β ζ - ∑ m ∈ Finset.range n, twoF0Term m α β x =
      ∑ m ∈ Finset.Ico n N, twoF0Term m α β x +
        (carlson2F0Sector α β ζ - ∑ m ∈ Finset.range N, twoF0Term m α β x) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show n ≤ N by simp [N])]; ring
  rw [hsplit, ← hnx]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖∑ m ∈ Finset.Ico n N, twoF0Term m α β x‖ ≤ (∑ m ∈ Finset.Ico n N, c m) * ‖x‖ ^ n := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun m hm => ?_
    rw [hterm]
    exact mul_le_mul_of_nonneg_left (hpow m (Finset.mem_Ico.mp hm).1) (hc m)
  have h2 := norm_carlson2F0Sector_sub_sum_le N hαN hβN hζ'
  rw [hterm] at h2
  have hV : rotEulerVariation (α + N) (twoF0Angle ζ) * rotEulerVariation (β + N) (twoF0Angle ζ)
      ≤ K := by
    have v1 := rotEulerVariation_le hαN hc₀ hcφ hφ'
    have v2 := rotEulerVariation_le hβN hc₀ hcφ hφ'
    have v0 : 0 ≤ rotEulerVariation (β + N) (twoF0Angle ζ) := by
      unfold rotEulerVariation
      have := (Real.Gamma_pos_of_pos hβN).le
      have := Real.rpow_pos_of_pos (lt_of_lt_of_le hc₀ hcφ) (β + N).re
      positivity
    have v3 : 0 ≤ Real.Gamma (α + N).re / ‖Gamma (α + N)‖ *
        (Real.exp (π / 2 * |(α + N).im|) / c₀ ^ (α + N).re) := by
      have := (Real.Gamma_pos_of_pos hαN).le
      have := Real.rpow_pos_of_pos hc₀ (α + N).re
      positivity
    exact mul_le_mul v1 v2 v0 v3
  have h3 : c N * ‖x‖ ^ N * (rotEulerVariation (α + N) (twoF0Angle ζ) *
      rotEulerVariation (β + N) (twoF0Angle ζ)) ≤ c N * K * ‖x‖ ^ n := by
    have := mul_le_mul_of_nonneg_left (hpow N (by simp [N])) (mul_nonneg (hc N) hK)
    calc c N * ‖x‖ ^ N * (rotEulerVariation (α + N) (twoF0Angle ζ) *
          rotEulerVariation (β + N) (twoF0Angle ζ)) ≤ c N * ‖x‖ ^ N * K :=
          mul_le_mul_of_nonneg_left hV (mul_nonneg (hc N) (pow_nonneg (norm_nonneg _) _))
      _ = c N * K * ‖x‖ ^ N := by ring
      _ ≤ c N * K * ‖x‖ ^ n := this
  nlinarith

/-- The total variation of a rotated Euler measure is at most `2^{re a} e^{π |im a|}` when
`re a ≥ 1/2` and the angle is at most `π/3`. -/
theorem rotEulerVariation_le_two_rpow {a : ℂ} (ha : 1 / 2 ≤ a.re) {θ : ℝ} (hθ : |θ| ≤ π / 3) :
    rotEulerVariation a θ ≤ 2 ^ a.re * Real.exp (π * |a.im|) := by
  unfold rotEulerVariation
  have hG : Real.Gamma a.re / ‖Gamma a‖ ≤ Real.exp (π * |a.im| / 2) := by
    have := Complex.Gamma_div_norm_Gamma_le_exp ha a.im
    rwa [re_add_im] at this
  have hcos : 1 / 2 ≤ Real.cos θ := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hθ
  have hre : 0 < a.re := by linarith
  have hc : (1 / 2 : ℝ) ^ a.re ≤ Real.cos θ ^ a.re := Real.rpow_le_rpow (by norm_num) hcos hre.le
  have hc0 : 0 < (1 / 2 : ℝ) ^ a.re := Real.rpow_pos_of_pos (by norm_num) _
  have he : Real.exp (-(θ * a.im)) ≤ Real.exp (π * |a.im| / 3) := by
    apply Real.exp_le_exp.mpr
    calc -(θ * a.im) ≤ |θ| * |a.im| := by rw [← abs_mul]; exact neg_le_abs _
      _ ≤ π / 3 * |a.im| := mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
      _ = π * |a.im| / 3 := by ring
  have h2 : 1 / (1 / 2 : ℝ) ^ a.re = 2 ^ a.re := by
    rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, one_div_one_div]
  calc Real.Gamma a.re / ‖Gamma a‖ * (Real.exp (-(θ * a.im)) / Real.cos θ ^ a.re)
      ≤ Real.exp (π * |a.im| / 2) * (Real.exp (π * |a.im| / 3) / (1 / 2 : ℝ) ^ a.re) := by
        gcongr
    _ = 2 ^ a.re * Real.exp (π * |a.im| * (5 / 6)) := by
        rw [div_eq_mul_one_div (Real.exp _), h2, ← mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ 2 ^ a.re * Real.exp (π * |a.im|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        nlinarith [mul_nonneg Real.pi_pos.le (abs_nonneg a.im)]

/-- **Theorem 5.12-7, error bound (5.12-16)**: if `|ph(-x)| ≤ π` and
`re (α + n), re (β + n) > 1/2`, the error of the `n`-th partial sum of the `₂F₀` series is at most
the first omitted term times `2^{re(α+β)+2n} e^{π|im α| + π|im β|}`. -/
theorem norm_carlson2F0Sector_sub_sum_le_two_rpow (n : ℕ) {α β ζ : ℂ}
    (hα : 1 / 2 < (α + n).re) (hβ : 1 / 2 < (β + n).re) (hζ : |ζ.im| ≤ π) :
    ‖carlson2F0Sector α β ζ - ∑ m ∈ Finset.range n, twoF0Term m α β (-exp ζ)‖ ≤
      ‖twoF0Term n α β (-exp ζ)‖ *
        (2 ^ ((α + β).re + 2 * n) * Real.exp (π * |α.im| + π * |β.im|)) := by
  have hζ' : |ζ.im| < 3 * π / 2 := by linarith [Real.pi_pos]
  have hθ : |twoF0Angle ζ| ≤ π / 3 := by
    rw [twoF0Angle, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith
  refine (norm_carlson2F0Sector_sub_sum_le n (by linarith) (by linarith) hζ').trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (mul_le_mul (rotEulerVariation_le_two_rpow hα.le hθ)
    (rotEulerVariation_le_two_rpow hβ.le hθ) ?_ (by positivity)).trans (le_of_eq ?_)
  · unfold rotEulerVariation
    have := Real.Gamma_pos_of_pos (show 0 < (β + n).re by linarith)
    have hc : 0 < Real.cos (twoF0Angle ζ) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [abs_le.mp hθ, Real.pi_pos], by linarith [abs_le.mp hθ, Real.pi_pos]⟩
    have := Real.rpow_pos_of_pos hc (β + n).re
    positivity
  · simp only [add_re, natCast_re, add_im, natCast_im, add_zero]
    rw [show (2 : ℝ) ^ (α.re + β.re + 2 * (n : ℝ)) = 2 ^ (α.re + n) * 2 ^ (β.re + n) by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; ring_nf, Real.exp_add]
    ring

end Carlson
