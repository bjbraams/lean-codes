/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SaddleUniform
public import Carlson.Jacobi.ChebyshevSecondKind

/-!
# Joint second-kind saddle asymptotics

The centered saddle amplitude is jointly analytic in both endpoints and the
interior contour parameter. This supplies common derivative bounds on compact
families of segments avoiding the origin, including coincident endpoints.
The resulting uniform Laplace limit applies to Carlson's two-argument domain
`W` in Theorem 7.4-3. For arbitrary complex Jacobi parameters there is one
nonzero coefficient function such that the ratio to `C(x,y)((x+y)/2)^(-2n)`
tends to one uniformly on every compact subset of `W`. The degree shift is
removed, and comparison with the native average gives Carlson's R notation.

## Main results

* `exists_tendstoUniformlyOn_jacobiSecondKind_div_geometric_endpoints`: joint endpoint limit.
* `jacobiSaddleRatio_neg_sq` and `jacobiSaddleScale_neg_sq`: compatible square-root coordinates.
* `exists_tendstoUniformlyOn_carlsonR_secondKind_div`: Theorem 7.4-3 on all of `W`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Theorem 7.4-3, pp. 199–200.
-/

@[expose] public noncomputable section
namespace Carlson.TwoVariable
open Complex Set Filter MeasureTheory
open scoped Topology ComplexConjugate

/-- Joint analytic dependence of the saddle ratio on both endpoints at the origin. -/
theorem analyticAt_jacobiSaddleRatio_endpoints {r s : ℂ} (hz : (0 : ℂ) ∉ segment ℝ r s) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => jacobiSaddleRatio p.1 p.2 0) (r, s) := by
  have hr : 0 - r ≠ 0 := sub_ne_zero.mpr (fun h => hz (h ▸ left_mem_segment ℝ r s))
  exact ((analyticAt_const.sub analyticAt_snd).div (analyticAt_const.sub analyticAt_fst) hr).cpow
    analyticAt_const (div_mem_slitPlane_of_not_mem_segment hz)

/-- Complex contour extension of the amplitude with both endpoints varying. -/
def jacobiSaddleAmplitudeJointComplex (a b : ℂ) (m : ℕ) (p : (ℂ × ℂ) × ℂ) : ℂ :=
  let c := jacobiSaddleRatio p.1.1 p.1.2 0
  let t := (p.2 + 1) / 2
  c ^ (a + 1) * (t ^ a * (1 - t) ^ b) *
    (1 - t + c * t) ^ ((m : ℂ) - a - b - 2) *
      (c * t * (0 - p.1.1) + (1 - t) * (0 - p.1.2)) ^ (-(m : ℤ))

/-- Restricting the joint complex amplitude recovers the centered real contour. -/
theorem jacobiSaddleAmplitudeJointComplex_ofReal (a b : ℂ) (m : ℕ) (r s : ℂ) (u : ℝ) :
    jacobiSaddleAmplitudeJointComplex a b m ((r, s), u) =
      jacobiSaddleAmplitude a b m r s 0 u := by
  simp [jacobiSaddleAmplitudeJointComplex, jacobiSaddleAmplitude, jacobiMobiusIntegrand,
    Polynomial.complexJacobiWeight, ofReal_div, ofReal_add]

/-- The amplitude is analytic in both endpoints and the interior contour variable. -/
theorem analyticAt_jacobiSaddleAmplitudeJointComplex (a b : ℂ) (m : ℕ) {r s : ℂ}
    (hz : (0 : ℂ) ∉ segment ℝ r s) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    AnalyticAt ℂ (jacobiSaddleAmplitudeJointComplex a b m) ((r, s), u) := by
  let c := jacobiSaddleRatio r s 0
  let t : ℝ := (u + 1) / 2
  have ht : t ∈ Ioo (0 : ℝ) 1 := by constructor <;> dsimp [t] <;> linarith [hu.1, hu.2]
  have hc : 0 < c.re := re_jacobiSaddleRatio_pos hz
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have hzr : (0 : ℂ) ≠ r := fun h => hz (h ▸ left_mem_segment ℝ r s)
  have hcz : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ => jacobiSaddleRatio p.1.1 p.1.2 0) ((r, s), u) :=
    (analyticAt_jacobiSaddleRatio_endpoints hz).comp_of_eq analyticAt_fst rfl
  have hr : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ => p.1.1) ((r, s), u) :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ)).analyticAt _
  have hs : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ => p.1.2) ((r, s), u) :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ)).analyticAt _
  have htz : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ => (p.2 + 1) / 2) ((r, s), u) :=
    (analyticAt_snd.add analyticAt_const).div analyticAt_const (by norm_num)
  have ht0 : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht.1
  have ht1 : 1 - (t : ℂ) ∈ slitPlane := by
    left; simp only [sub_re, one_re, ofReal_re]; linarith [ht.2]
  have hD : 1 - (t : ℂ) + c * t ∈ slitPlane := by
    left
    simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero]
    nlinarith [ht.1, ht.2]
  have hR := mobius_resolvent_ne_zero (sub_ne_zero.mpr hzr) hc
    (jacobiSaddleRatio_sq_mul hzr) (by rw [div_self hc0]; simp) (Ioo_subset_Icc_self ht)
  have htcast : (t : ℂ) = ((u : ℂ) + 1) / 2 := by simp [t]
  rw [htcast] at ht0 ht1 hD hR
  exact ((hcz.cpow analyticAt_const (Or.inl hc)).mul
    ((htz.cpow analyticAt_const ht0).mul
      ((analyticAt_const.sub htz).cpow analyticAt_const ht1)) |>.mul
        (((analyticAt_const.sub htz).add (hcz.mul htz)).cpow analyticAt_const hD)).mul
    ((((hcz.mul htz).mul (analyticAt_const.sub hr)).add
      ((analyticAt_const.sub htz).mul (analyticAt_const.sub hs))).zpow hR)

/-- The joint extension gives the contour derivative at every interior point. -/
theorem hasDerivAt_jacobiSaddleAmplitude_joint (a b : ℂ) (m : ℕ) {r s : ℂ}
    (hz : (0 : ℂ) ∉ segment ℝ r s) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (jacobiSaddleAmplitude a b m r s 0)
      (fderiv ℂ (jacobiSaddleAmplitudeJointComplex a b m) ((r, s), u) (0, 1)) u := by
  have h := (analyticAt_jacobiSaddleAmplitudeJointComplex a b m hz hu).differentiableAt
    |>.hasFDerivAt.comp_hasDerivAt (u : ℂ)
      ((hasDerivAt_const (u : ℂ) (r, s)).prodMk (hasDerivAt_id (u : ℂ))) |>.comp_ofReal
  simpa only [Function.comp_apply, jacobiSaddleAmplitudeJointComplex_ofReal] using h

/-- Compact families of endpoint pairs have a common central amplitude Lipschitz bound. -/
theorem exists_uniform_jacobiSaddleAmplitude_lipschitz_endpoints (a b : ℂ) (m : ℕ)
    {K : Set (ℂ × ℂ)} (hK : IsCompact K) (hKs : ∀ p ∈ K, (0 : ℂ) ∉ segment ℝ p.1 p.2) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ K, ∀ u ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      ‖jacobiSaddleAmplitude a b m p.1 p.2 0 u - jacobiSaddleAmplitude a b m p.1 p.2 0 0‖ ≤
          L * |u| := by
  let D : (ℂ × ℂ) × ℝ → ℂ := fun p =>
    fderiv ℂ (jacobiSaddleAmplitudeJointComplex a b m) (p.1, p.2) (0, 1)
  have hD : ContinuousOn D (K ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) := by
    intro p hp
    have hu : p.2 ∈ Ioo (-1 : ℝ) 1 := by constructor <;> linarith [hp.2.1, hp.2.2]
    have h :=
      (analyticAt_jacobiSaddleAmplitudeJointComplex a b m (hKs p.1 hp.1) hu).contDiffAt (n := 1)
    exact ((h.continuousAt_fderiv (by decide : (1 : WithTop ℕ∞) ≠ 0)).clm_apply continuousAt_const
      |>.comp (f := fun q : (ℂ × ℂ) × ℝ => (q.1, (q.2 : ℂ))) (by fun_prop)).continuousWithinAt
  obtain ⟨L, hL⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hD
  refine ⟨|L|, abs_nonneg _, fun p hp u hu => ?_⟩
  have hd (v : ℝ) (hv : v ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
      HasDerivWithinAt (jacobiSaddleAmplitude a b m p.1 p.2 0) (D (p, v))
        (Icc (-1 / 2 : ℝ) (1 / 2)) v :=
    (hasDerivAt_jacobiSaddleAmplitude_joint a b m (hKs p hp)
      (by constructor <;> linarith [hv.1, hv.2])).hasDerivWithinAt
  simpa only [sub_zero, Real.norm_eq_abs] using
    (convex_Icc (-1 / 2 : ℝ) (1 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (fun v hv => (hL (p, v) ⟨hp, hv⟩).trans (le_abs_self L))
      (by constructor <;> norm_num : (0 : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2)) hu

/-- Endpoint-contour joint continuity includes both ends of the contour when the
base exponents have positive real parts. -/
theorem continuousAt_jacobiMobiusIntegrand_endpoints {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (m : ℕ) {r s : ℂ} (hz : (0 : ℂ) ∉ segment ℝ r s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun p : (ℂ × ℂ) × ℝ => jacobiMobiusIntegrand a b m (0 - p.1.1) (0 - p.1.2)
      (jacobiSaddleRatio p.1.1 p.1.2 0) p.2) ((r, s), t) := by
  have hzr : (0 : ℂ) ≠ r := fun h => hz (h ▸ left_mem_segment ℝ r s)
  have hc := re_jacobiSaddleRatio_pos hz
  have hcz : ContinuousAt (fun p : (ℂ × ℂ) × ℝ => jacobiSaddleRatio p.1.1 p.1.2 0) ((r, s), t) :=
    ContinuousAt.comp' (g := fun p : ℂ × ℂ => jacobiSaddleRatio p.1 p.2 0)
      (analyticAt_jacobiSaddleRatio_endpoints hz).continuousAt continuousAt_fst
  have ht' : ContinuousAt (fun p : (ℂ × ℂ) × ℝ => (p.2 : ℂ)) ((r, s), t) :=
    continuous_ofReal.continuousAt.comp continuousAt_snd
  have hr : ContinuousAt (fun p : (ℂ × ℂ) × ℝ => p.1.1) ((r, s), t) := by fun_prop
  have hs : ContinuousAt (fun p : (ℂ × ℂ) × ℝ => p.1.2) ((r, s), t) := by fun_prop
  have hw : Continuous (fun t : ℝ => Polynomial.complexJacobiWeight a b t) := by
    simpa only [sub_add_cancel] using
      (Polynomial.continuous_complexJacobiWeight_succ (α := a - 1) (β := b - 1)
        (by simp only [sub_re, one_re]; linarith) (by simp only [sub_re, one_re]; linarith))
  have hD : (1 - (t : ℂ)) + jacobiSaddleRatio r s 0 * t ∈ slitPlane := by
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
  · exact ContinuousAt.zpow₀ (((hcz.mul ht').mul (continuousAt_const.sub hr)).add
      ((continuousAt_const.sub ht').mul (continuousAt_const.sub hs))) _ (Or.inl hL)

/-- The centered shape is continuous in both endpoints when their segment avoids zero. -/
theorem continuousAt_jacobiSaddleShape_endpoints {r s : ℂ} (hz : (0 : ℂ) ∉ segment ℝ r s) :
    ContinuousAt (fun z => jacobiSaddleShape (jacobiSaddleRatio z.1 z.2 0)) (r, s) := by
  have hc := (analyticAt_jacobiSaddleRatio_endpoints hz).continuousAt
  have hne : jacobiSaddleRatio r s 0 + 1 ≠ 0 := by
    intro h
    have h' := congrArg re h
    simp only [add_re, one_re, zero_re] at h'
    linarith [re_jacobiSaddleRatio_pos hz]
  exact ((hc.sub continuousAt_const).div (hc.add continuousAt_const) hne).pow 2

/-- The full Gaussian limit is joint-uniform on compact families of endpoint
pairs whose segments avoid zero. All amplitude bounds are derived here. -/
theorem tendstoUniformlyOn_sqrt_mul_integral_jacobiSaddleAmplitude_endpoints {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (m : ℕ) {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) (hKs : ∀ z ∈ K, (0 : ℂ) ∉ segment ℝ z.1 z.2) :
    TendstoUniformlyOn (fun n : ℕ => fun z => (Real.sqrt n : ℂ) *
      ∫ u in Icc (-1 : ℝ) 1, jacobiSaddleAmplitude a b m z.1 z.2 0 u *
        jacobiSaddleKernel (jacobiSaddleShape (jacobiSaddleRatio z.1 z.2 0)) u ^ n)
      (fun z => jacobiSaddleAmplitude a b m z.1 z.2 0 0 *
        (Real.pi / (1 - jacobiSaddleShape (jacobiSaddleRatio z.1 z.2 0))) ^ (1 / 2 : ℂ))
      atTop K := by
  let w := fun z : ℂ × ℂ => jacobiSaddleShape (jacobiSaddleRatio z.1 z.2 0)
  have hwc : ContinuousOn (fun z => 1 - ‖w z‖) K :=
    continuousOn_const.sub
        (fun z hz => (continuousAt_jacobiSaddleShape_endpoints (hKs z hz)).norm.continuousWithinAt)
  obtain ⟨η, hη, hηw⟩ := hK.exists_forall_le' hwc
    (fun z hz => sub_pos.mpr (norm_jacobiSaddleShape_lt_one (re_jacobiSaddleRatio_pos (hKs z hz))))
  let ρ := max 0 (1 - η)
  have hρ0 : 0 ≤ ρ := le_max_left _ _
  have hρ : ρ < 1 := max_lt (by norm_num) (by linarith)
  have hw (z : ℂ × ℂ) (hz : z ∈ K) : ‖w z‖ ≤ ρ :=
    (by linarith [hηw z hz] : ‖w z‖ ≤ 1 - η).trans (le_max_right _ _)
  let δ := min (1 / 2) (Real.sqrt (1 - ρ) / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hsmall : 4 * δ ^ 2 ≤ 1 - ρ := by
    have := min_le_right (1 / 2 : ℝ) (Real.sqrt (1 - ρ) / 2)
    have := Real.sq_sqrt (sub_nonneg.mpr hρ.le)
    have := Real.sqrt_nonneg (1 - ρ)
    dsimp only [δ] at hδ
    nlinarith
  let A := fun z : ℂ × ℂ => jacobiSaddleAmplitude a b m z.1 z.2 0
  have hAc : ContinuousOn (fun p : (ℂ × ℂ) × ℝ => A p.1 p.2) (K ×ˢ Icc (-1 : ℝ) 1) := by
    intro p hp
    have ht : (p.2 + 1) / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hp.2.1, hp.2.2]
    exact ((continuousAt_jacobiMobiusIntegrand_endpoints ha hb m (hKs p.1 hp.1) ht).comp
      (f := fun q : (ℂ × ℂ) × ℝ => (q.1, (q.2 + 1) / 2)) (by fun_prop)).continuousWithinAt
  obtain ⟨M, hM⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hAc
  obtain ⟨L, hL, hAL⟩ := exists_uniform_jacobiSaddleAmplitude_lipschitz_endpoints a b m hK hKs
  apply tendstoUniformlyOn_sqrt_mul_integral_jacobiSaddleKernel hρ0 hρ hδ hδhalf hsmall hL
    (abs_nonneg M) (by positivity : 0 ≤ 2 * |M|) hw
    (fun z _ => measurable_jacobiSaddleAmplitude a b m z.1 z.2 0)
    (fun z hz => (continuousOn_jacobiSaddleAmplitude ha hb m (hKs z hz)).integrableOn_Icc)
  · intro z hz
    exact (hM (z, 0) ⟨hz, by constructor <;> norm_num⟩).trans (le_abs_self M)
  · intro z hz u hu
    exact hAL z hz u ⟨by linarith [hu.1], hu.2.trans hδhalf⟩
  · intro z hz
    calc
      _ ≤ ∫ _ in Icc (-1 : ℝ) 1, |M| := by
        apply setIntegral_mono_on
          (continuousOn_jacobiSaddleAmplitude ha hb m (hKs z hz) |>.norm.integrableOn_Icc)
          (integrableOn_const (by simp : volume (Icc (-1 : ℝ) 1) ≠ ⊤)) measurableSet_Icc
        intro u hu
        exact (hM (z, u) ⟨hz, hu⟩).trans (le_abs_self M)
      _ = 2 * |M| := by norm_num [integral_const, smul_eq_mul]

/-- The Gaussian leading constant is continuous in both endpoints whenever
their segment avoids zero, independently of endpoint integrability. -/
theorem continuousAt_jacobiSaddleLeading_endpoints (a b : ℂ) (m : ℕ) {r s : ℂ}
    (hz : (0 : ℂ) ∉ segment ℝ r s) :
        ContinuousAt (fun z => jacobiSaddleLeading a b m z.1 z.2 0) (r, s) := by
  have hA : ContinuousAt (fun z => jacobiSaddleAmplitude a b m z.1 z.2 0 0) (r, s) := by
    have h := (analyticAt_jacobiSaddleAmplitudeJointComplex a b m hz
      (by constructor <;> norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1)).continuousAt.comp
        (f := fun z : ℂ × ℂ => (z, (0 : ℂ))) (by fun_prop)
    convert h using 1
    funext p
    exact (jacobiSaddleAmplitudeJointComplex_ofReal a b m p.1 p.2 0).symm
  have hq := Complex.re_one_sub_pos (norm_jacobiSaddleShape_lt_one (re_jacobiSaddleRatio_pos hz))
  have hqne : 1 - jacobiSaddleShape (jacobiSaddleRatio r s 0) ≠ 0 := by
    intro h; simp [h] at hq
  have hslit : (Real.pi : ℂ) / (1 - jacobiSaddleShape (jacobiSaddleRatio r s 0)) ∈ slitPlane := by
    left
    rw [div_re]
    simp only [ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos Real.pi_pos hq) (normSq_pos.mpr hqne)
  exact (hA.mul ((continuousAt_const.div
    (continuousAt_const.sub (continuousAt_jacobiSaddleShape_endpoints hz)) hqne).cpow
      continuousAt_const hslit)).div_const 2

/-- Compact-uniform Gaussian asymptotics for the shifted Möbius Euler integral. -/
theorem tendstoUniformlyOn_sqrt_mul_pow_mul_integral_jacobiMobius_endpoints {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (m : ℕ) {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) (hKs : ∀ z ∈ K, (0 : ℂ) ∉ segment ℝ z.1 z.2) :
    TendstoUniformlyOn (fun k : ℕ => fun z => (Real.sqrt k : ℂ) * jacobiSaddleScale z.1 z.2 0 ^ k *
      ∫ t in (0 : ℝ)..1, jacobiMobiusIntegrand (a + k) (b + k) (m + k)
        (0 - z.1) (0 - z.2) (jacobiSaddleRatio z.1 z.2 0) t)
      (fun z => jacobiSaddleLeading a b m z.1 z.2 0) atTop K := by
  have h := (uniformContinuous_div_const' (2 : ℂ)).comp_tendstoUniformlyOn
    (tendstoUniformlyOn_sqrt_mul_integral_jacobiSaddleAmplitude_endpoints ha hb m hK hKs)
  apply h.congr (Eventually.of_forall (fun k z hz => ?_))
  dsimp only [Function.comp_apply]
  rw [integral_jacobiSaddleAmplitude_mul_kernel_pow a b m k (hKs z hz)]
  ring

/-- The normalized second-kind functions converge jointly in the endpoint pair
to their nonzero saddle coefficient, after a fixed degree shift. -/
theorem tendstoUniformlyOn_jacobiSecondKind_saddle_shift_endpoints (α β : ℂ) (N : ℕ)
    (hα : 0 < (α + N).re) (hβ : 0 < (β + N).re) {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) (hKs : ∀ z ∈ K, (0 : ℂ) ∉ segment ℝ z.1 z.2) :
    TendstoUniformlyOn (fun k : ℕ => fun z => jacobiSecondKind α β z.1 z.2 (N + k) 0 *
      (jacobiSaddleScale z.1 z.2 0 / 4) ^ k)
      (fun z => jacobiSecondKindSaddleCoefficient α β N z.1 z.2 0) atTop K := by
  have hnum :=
    tendstoUniformlyOn_sqrt_mul_pow_mul_integral_jacobiMobius_endpoints hα hβ (N + 1) hK hKs
      |>.tendstoLocallyUniformlyOn
  have href := (tendsto_sqrt_mul_pow_mul_integral_jacobiMobius hα hβ (N + 1)
    (r := 0) (s := 0) (z := 1) (by simp)).tendstoUniformlyOn_const K |>.tendstoLocallyUniformlyOn
  have hdiv := hnum.div₀ href
    (fun z hz => (continuousAt_jacobiSaddleLeading_endpoints _ _ _ (hKs z hz)).continuousWithinAt)
    continuousOn_const (fun _ _ => jacobiSaddleLeading_ne_zero _ _ _ (by simp))
  have h := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp hdiv
  apply h.congr
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  intro z hz
  have hs : (Real.sqrt k : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)).ne'
  dsimp only [Pi.div_apply]
  rw [jacobiSecondKind_eq_saddle_integral_div_reference α β z.1 z.2 N k hα hβ (hKs z hz)]
  simp only [jacobiSaddleScale_reference, div_pow]
  field_simp

/-- The relative second-kind asymptotic is uniform on compact families of endpoint
pairs whose segments avoid zero; the explicitly defined coefficient is nonzero. -/
theorem tendstoUniformlyOn_jacobiSecondKind_div_saddle_shift_endpoints (α β : ℂ) (N : ℕ)
    (hα : 0 < (α + N).re) (hβ : 0 < (β + N).re) {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) (hKs : ∀ z ∈ K, (0 : ℂ) ∉ segment ℝ z.1 z.2) :
    TendstoUniformlyOn (fun k : ℕ => fun z => jacobiSecondKind α β z.1 z.2 (N + k) 0 /
      (jacobiSecondKindSaddleCoefficient α β N z.1 z.2 0 * (4 / jacobiSaddleScale z.1 z.2 0) ^ k))
      (fun _ => 1) atTop K := by
  have hc : ContinuousOn (fun z => jacobiSecondKindSaddleCoefficient α β N z.1 z.2 0) K := by
    intro z hz
    exact (continuousAt_jacobiSaddleLeading_endpoints _ _ _ (hKs z hz)).continuousWithinAt
      |>.div_const _
  have h := tendstoUniformlyOn_jacobiSecondKind_saddle_shift_endpoints α β N hα hβ hK hKs
    |>.tendstoLocallyUniformlyOn
  have hconst : TendstoLocallyUniformlyOn
      (fun _ : ℕ => fun z => jacobiSecondKindSaddleCoefficient α β N z.1 z.2 0)
      (fun z => jacobiSecondKindSaddleCoefficient α β N z.1 z.2 0) atTop K :=
    (Metric.tendstoUniformlyOn_iff.mpr (fun ε hε =>
      Eventually.of_forall (fun n z hz => by simpa using hε))).tendstoLocallyUniformlyOn
  have hdiv := (h.div₀ hconst hc hc (fun z hz =>
    jacobiSecondKindSaddleCoefficient_ne_zero _ _ _ (hKs z hz))).congr_right
      (fun z hz => div_self (jacobiSecondKindSaddleCoefficient_ne_zero _ _ _ (hKs z hz)))
  have h := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp hdiv
  apply h.congr (Eventually.of_forall (fun k z hz => ?_))
  dsimp only [Pi.div_apply]
  rw [div_pow, div_pow]
  field_simp

/-- The compact-uniform relative second-kind asymptotic for arbitrary complex
Jacobi parameters, with the auxiliary degree shift removed. The same nonzero
coefficient works on every compact family of endpoint pairs whose segments avoid zero. -/
theorem exists_tendstoUniformlyOn_jacobiSecondKind_div_geometric_endpoints (α β : ℂ) :
    ∃ C : (ℂ × ℂ) → ℂ, (∀ z, (0 : ℂ) ∉ segment ℝ z.1 z.2 → C z ≠ 0) ∧
      ∀ K : Set (ℂ × ℂ), IsCompact K → (∀ z ∈ K, (0 : ℂ) ∉ segment ℝ z.1 z.2) →
        TendstoUniformlyOn (fun n : ℕ => fun z => jacobiSecondKind α β z.1 z.2 n 0 /
          (C z * (4 / jacobiSaddleScale z.1 z.2 0) ^ n)) (fun _ => 1) atTop K := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (-α.re) (-β.re))
  have hα : 0 < (α + N).re := by
    simp only [add_re, natCast_re]
    linarith [le_max_left (-α.re) (-β.re)]
  have hβ : 0 < (β + N).re := by
    simp only [add_re, natCast_re]
    linarith [le_max_right (-α.re) (-β.re)]
  let G := fun z : ℂ × ℂ => 4 / jacobiSaddleScale z.1 z.2 0
  have hG (z : ℂ × ℂ) (hz : (0 : ℂ) ∉ segment ℝ z.1 z.2) : G z ≠ 0 :=
    div_ne_zero (by norm_num) (jacobiSaddleScale_ne_zero hz)
  refine ⟨fun z => jacobiSecondKindSaddleCoefficient α β N z.1 z.2 0 / G z ^ N,
    fun z hz => div_ne_zero (jacobiSecondKindSaddleCoefficient_ne_zero _ _ _ hz)
      (pow_ne_zero _ (hG z hz)), fun K hK hKs => ?_⟩
  have h := tendstoUniformlyOn_jacobiSecondKind_div_saddle_shift_endpoints α β N hα hβ hK hKs
    |>.seq_tendstoUniformlyOn (fun n => n - N) (tendsto_sub_atTop_nat N)
  apply h.congr
  filter_upwards [eventually_ge_atTop N] with n hn
  intro z hz
  dsimp only
  rw [show N + (n - N) = n by omega]
  have hpow : G z ^ (n - N) * G z ^ N = G z ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  change _ / (_ * G z ^ (n - N)) = _ / ((_ / G z ^ N) * G z ^ n)
  rw [← hpow]
  field_simp [hG z (hKs z hz)]

/-- Carlson's domain `W` makes the segment between the negative square arguments
avoid the origin, including at coincident arguments. -/
theorem zero_not_mem_segment_neg_sq {x y : ℂ} (h : 0 < (x * conj y).re) :
    (0 : ℂ) ∉ segment ℝ (-(x ^ 2)) (-(y ^ 2)) := by
  rintro ⟨a, b, ha, hb, hab, he⟩
  apply sq_segment_ne_zero h (t := a) ⟨ha, by linarith⟩
  rw [show b = 1 - a by linarith] at he
  simp only [real_smul] at he
  push_cast at he
  linear_combination -he

/-- The compatible square-root ratio on `W` is the quotient of Carlson's square roots. -/
theorem jacobiSaddleRatio_neg_sq {x y : ℂ} (h : 0 < (x * conj y).re) :
    jacobiSaddleRatio (-(x ^ 2)) (-(y ^ 2)) 0 = y / x := by
  have hx : x ≠ 0 := by intro hx; simp [hx] at h
  have hdiv : 0 < (y / x).re := by
    have he : (y / x).re = (x * conj y).re / normSq x := by
      simp only [div_re, mul_re, conj_re, conj_im]
      ring
    rw [he]
    exact div_pos h (normSq_pos.mpr hx)
  have hz := zero_not_mem_segment_neg_sq h
  have hr := re_jacobiSaddleRatio_pos hz
  have hs := jacobiSaddleRatio_sq_mul (r := -(x ^ 2)) (s := -(y ^ 2)) (z := 0)
    (by simpa using hx)
  simp only [zero_sub, neg_neg] at hs
  have he : jacobiSaddleRatio (-(x ^ 2)) (-(y ^ 2)) 0 ^ 2 = (y / x) ^ 2 := by
    apply (mul_right_cancel₀ (pow_ne_zero 2 hx))
    rw [hs, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hx)]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · exact he
  · rw [he, neg_re] at hr
    linarith

/-- In square-root coordinates the complex saddle scale is `(x+y)²`. -/
theorem jacobiSaddleScale_neg_sq {x y : ℂ} (h : 0 < (x * conj y).re) :
    jacobiSaddleScale (-(x ^ 2)) (-(y ^ 2)) 0 = (x + y) ^ 2 := by
  have hx : x ≠ 0 := by intro hx; simp [hx] at h
  simp only [jacobiSaddleScale, zero_sub, neg_neg, jacobiSaddleRatio_neg_sq h]
  field_simp
  ring

/-- The saddle's geometric factor agrees with Carlson's integer negative power. -/
theorem jacobiSaddle_geometricFactor_neg_sq {x y : ℂ} (h : 0 < (x * conj y).re) (n : ℕ) :
    (4 / jacobiSaddleScale (-(x ^ 2)) (-(y ^ 2)) 0) ^ n =
      ((x + y) / 2) ^ (-(2 * (n : ℤ))) := by
  rw [jacobiSaddleScale_neg_sq h, zpow_neg, zpow_mul, zpow_natCast]
  norm_num [div_pow, inv_pow, inv_div]

/-- Theorem 7.4-3 in terms of the continued second-kind functions: joint relative
convergence on compact subsets of Carlson's `W`, with a nonzero coefficient. -/
theorem exists_tendstoUniformlyOn_jacobiSecondKind_sq_div (α β : ℂ) :
    ∃ C : (ℂ × ℂ) → ℂ, (∀ p ∈ chebyshevDomain, C p ≠ 0) ∧
      ∀ K : Set (ℂ × ℂ), IsCompact K → K ⊆ chebyshevDomain →
        TendstoUniformlyOn (fun n : ℕ => fun p =>
          jacobiSecondKind α β (-(p.1 ^ 2)) (-(p.2 ^ 2)) n 0 /
            (C p * ((p.1 + p.2) / 2) ^ (-(2 * (n : ℤ))))) (fun _ => 1) atTop K := by
  obtain ⟨C, hC, hlim⟩ := exists_tendstoUniformlyOn_jacobiSecondKind_div_geometric_endpoints α β
  let f : (ℂ × ℂ) → ℂ × ℂ := fun p => (-(p.1 ^ 2), -(p.2 ^ 2))
  have hf : Continuous f := by fun_prop
  refine ⟨C ∘ f, fun p hp => hC (f p) (zero_not_mem_segment_neg_sq hp), fun K hK hKW => ?_⟩
  have H := hlim (f '' K) (hK.image hf) (by
    rintro _ ⟨p, hp, rfl⟩
    exact zero_not_mem_segment_neg_sq (hKW hp))
  have H := (H.comp f).mono (show K ⊆ f ⁻¹' (f '' K) from fun p hp => mem_image_of_mem f hp)
  apply H.congr (Eventually.of_forall (fun n p hp => ?_))
  dsimp only [Function.comp_apply, f]
  rw [jacobiSaddle_geometricFactor_neg_sq (hKW hp)]

/-- On the native convergence region, the second-kind function at negative square
endpoints is Carlson's ordinary Dirichlet average at the positive square nodes. -/
theorem jacobiSecondKind_neg_sq_eq_average (α β : ℂ) (n : ℕ)
    (hα : 0 < (α + n + 1).re) (hβ : 0 < (β + n + 1).re) {x y : ℂ}
    (h : 0 < (x * conj y).re) :
    jacobiSecondKind α β (-(x ^ 2)) (-(y ^ 2)) n 0 =
      Gamma (α + n + 1 + (β + n + 1)) *
        Dirichlet.regCarlsonDirichletAverage (pair (α + n + 1) (β + n + 1))
          (pair (x ^ 2) (y ^ 2)) (fun w => w ^ (-(n + 1 : ℤ))) := by
  have hb : pair (α + n + 1) (β + n + 1) ∈ mvBetaConvergent := by
    intro i; fin_cases i
    · exact hα
    · exact hβ
  rw [jacobiSecondKind_eq_native _ _ _ _ _ n hb (zero_not_mem_segment_neg_sq h),
    Dirichlet.carlsonDirichletAverage, sum_pair]
  congr 1
  have haff := Dirichlet.regCarlsonDirichletAverage_comp_affine
    (pair (α + n + 1) (β + n + 1)) (pair (-(x ^ 2)) (-(y ^ 2)))
    (fun w => w ^ (-(n + 1 : ℤ))) (-1) 0
  have hnodes : (fun i => -pair (-(x ^ 2)) (-(y ^ 2)) i) = pair (x ^ 2) (y ^ 2) := by
    funext i; fin_cases i <;> simp
  simpa only [neg_one_mul, add_zero, zero_sub, hnodes] using haff

/-- **Carlson's Theorem 7.4-3**: for arbitrary complex parameters, the ordinary
second-kind R average divided by `C(x,y)((x+y)/2)^(-2n)` tends to one jointly
uniformly on compact subsets of `W`. The coefficient is nonzero throughout `W`;
no exclusion of the diagonal `x=y` is needed. -/
theorem exists_tendstoUniformlyOn_carlsonR_secondKind_div (α β : ℂ) :
    ∃ C : (ℂ × ℂ) → ℂ, (∀ p ∈ chebyshevDomain, C p ≠ 0) ∧
      ∀ K : Set (ℂ × ℂ), IsCompact K → K ⊆ chebyshevDomain →
        TendstoUniformlyOn (fun n : ℕ => fun p =>
          (Gamma (α + n + 1 + (β + n + 1)) *
            Dirichlet.regCarlsonDirichletAverage (pair (α + n + 1) (β + n + 1))
              (pair (p.1 ^ 2) (p.2 ^ 2)) (fun w => w ^ (-(n + 1 : ℤ)))) /
            (C p * ((p.1 + p.2) / 2) ^ (-(2 * (n : ℤ))))) (fun _ => 1) atTop K := by
  obtain ⟨C, hC, hlim⟩ := exists_tendstoUniformlyOn_jacobiSecondKind_sq_div α β
  refine ⟨C, hC, fun K hK hKW => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max (-α.re) (-β.re))
  apply (hlim K hK hKW).congr
  filter_upwards [eventually_ge_atTop N] with n hn
  intro p hp
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < (α + n + 1).re := by
    simp only [add_re, natCast_re, one_re]
    linarith [le_max_left (-α.re) (-β.re)]
  have hb : 0 < (β + n + 1).re := by
    simp only [add_re, natCast_re, one_re]
    linarith [le_max_right (-α.re) (-β.re)]
  dsimp only
  rw [jacobiSecondKind_neg_sq_eq_average α β n ha hb (hKW hp)]

end Carlson.TwoVariable
