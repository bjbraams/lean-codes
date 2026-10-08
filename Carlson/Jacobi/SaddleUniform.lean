/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SaddleLaplace
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Uniform Jacobi saddle asymptotics

Common bounds on compact sets upgrade the Gaussian saddle estimates to uniform
asymptotics. The complex extension of the centered amplitude supplies a common
bound on its derivative near the saddle. Comparison with the reference beta
integral gives the relative second-kind asymptotic for fixed complex endpoints,
uniform on compact subsets of their segment complement. The Jacobi parameters
are arbitrary complex numbers, and coincident endpoints are included.

## Main results

* `exists_uniform_jacobiSaddleAmplitude_lipschitz`: derived amplitude bounds.
* `tendstoUniformlyOn_sqrt_mul_integral_jacobiSaddleKernel`: the uniform kernel limit.
* `tendstoUniformlyOn_sqrt_mul_pow_mul_integral_jacobiMobius`: the actual Euler limit.
* `tendstoUniformlyOn_jacobiSecondKind_div_saddle_shift`: a specified leading coefficient.
* `exists_tendstoUniformlyOn_jacobiSecondKind_div_geometric`: the full degree sequence,
  with one nonzero coefficient function working on every compact exterior set.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  §7.4, Theorem 7.4-3 and the second-kind part of Corollary 7.4-4.
-/

@[expose] public noncomputable section
namespace Carlson.TwoVariable
open Complex Set Filter MeasureTheory
open scoped Topology

/-- Complex extension of the centered saddle amplitude, used near its saddle. -/
def jacobiSaddleAmplitudeComplex (a b : ℂ) (m : ℕ) (r s : ℂ) (p : ℂ × ℂ) : ℂ :=
  let c := jacobiSaddleRatio r s p.1
  let t := (p.2 + 1) / 2
  c ^ (a + 1) * (t ^ a * (1 - t) ^ b) *
    (1 - t + c * t) ^ ((m : ℂ) - a - b - 2) *
      (c * t * (p.1 - r) + (1 - t) * (p.1 - s)) ^ (-(m : ℤ))

/-- The complex extension agrees with the real centered amplitude. -/
theorem jacobiSaddleAmplitudeComplex_ofReal (a b : ℂ) (m : ℕ) (r s z : ℂ) (u : ℝ) :
    jacobiSaddleAmplitudeComplex a b m r s (z, u) = jacobiSaddleAmplitude a b m r s z u := by
  simp [jacobiSaddleAmplitudeComplex, jacobiSaddleAmplitude, jacobiMobiusIntegrand,
    Polynomial.complexJacobiWeight, ofReal_div, ofReal_add]

/-- The centered amplitude is jointly analytic near every interior contour point. -/
theorem analyticAt_jacobiSaddleAmplitudeComplex (a b : ℂ) (m : ℕ) {r s z : ℂ}
    (hz : z ∉ segment ℝ r s) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    AnalyticAt ℂ (jacobiSaddleAmplitudeComplex a b m r s) (z, u) := by
  let c := jacobiSaddleRatio r s z
  let t : ℝ := (u + 1) / 2
  have ht : t ∈ Ioo (0 : ℝ) 1 := by constructor <;> dsimp [t] <;> linarith [hu.1, hu.2]
  have hc : 0 < c.re := re_jacobiSaddleRatio_pos hz
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have hzr : z ≠ r := fun h => hz (h ▸ left_mem_segment ℝ r s)
  have hcz : AnalyticAt ℂ (fun p : ℂ × ℂ => jacobiSaddleRatio r s p.1) (z, u) := by
    exact ((analyticAt_fst.sub analyticAt_const).div (analyticAt_fst.sub analyticAt_const)
      (sub_ne_zero.mpr hzr)).cpow analyticAt_const (div_mem_slitPlane_of_not_mem_segment hz)
  have htz : AnalyticAt ℂ (fun p : ℂ × ℂ => (p.2 + 1) / 2) (z, u) :=
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
    ((((hcz.mul htz).mul (analyticAt_fst.sub analyticAt_const)).add
      ((analyticAt_const.sub htz).mul (analyticAt_fst.sub analyticAt_const))).zpow hR)

/-- Differentiating the complex extension in the contour direction differentiates
its restriction to the real centered contour. -/
theorem hasDerivAt_jacobiSaddleAmplitude (a b : ℂ) (m : ℕ) {r s z : ℂ}
    (hz : z ∉ segment ℝ r s) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (jacobiSaddleAmplitude a b m r s z)
      (fderiv ℂ (jacobiSaddleAmplitudeComplex a b m r s) (z, u) (0, 1)) u := by
  have h := (analyticAt_jacobiSaddleAmplitudeComplex a b m hz hu).differentiableAt
    |>.hasFDerivAt.comp_hasDerivAt (u : ℂ)
      ((hasDerivAt_const (u : ℂ) z).prodMk (hasDerivAt_id (u : ℂ))) |>.comp_ofReal
  simpa only [Function.comp_apply, jacobiSaddleAmplitudeComplex_ofReal] using h

/-- On a compact set off the focal segment, the amplitudes share a Lipschitz
bound on the fixed central interval `[-1/2, 1/2]`. -/
theorem exists_uniform_jacobiSaddleAmplitude_lipschitz (a b : ℂ) (m : ℕ) {r s : ℂ}
    {K : Set ℂ} (hK : IsCompact K) (hKs : ∀ z ∈ K, z ∉ segment ℝ r s) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z ∈ K, ∀ u ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      ‖jacobiSaddleAmplitude a b m r s z u - jacobiSaddleAmplitude a b m r s z 0‖ ≤ L * |u| := by
  let D : ℂ × ℝ → ℂ := fun p =>
    fderiv ℂ (jacobiSaddleAmplitudeComplex a b m r s) (p.1, p.2) (0, 1)
  have hD : ContinuousOn D (K ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) := by
    intro p hp
    have hu : p.2 ∈ Ioo (-1 : ℝ) 1 := by constructor <;> linarith [hp.2.1, hp.2.2]
    have h := (analyticAt_jacobiSaddleAmplitudeComplex a b m (hKs p.1 hp.1) hu).contDiffAt (n := 1)
    exact ((h.continuousAt_fderiv (by decide : (1 : WithTop ℕ∞) ≠ 0)).clm_apply continuousAt_const
      |>.comp (f := fun q : ℂ × ℝ => (q.1, (q.2 : ℂ))) (by fun_prop)).continuousWithinAt
  obtain ⟨L, hL⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hD
  refine ⟨|L|, abs_nonneg _, fun z hz u hu => ?_⟩
  have hd (v : ℝ) (hv : v ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
      HasDerivWithinAt (jacobiSaddleAmplitude a b m r s z) (D (z, v))
        (Icc (-1 / 2 : ℝ) (1 / 2)) v :=
    (hasDerivAt_jacobiSaddleAmplitude a b m (hKs z hz)
      (by constructor <;> linarith [hv.1, hv.2])).hasDerivWithinAt
  simpa only [sub_zero, Real.norm_eq_abs] using
    (convex_Icc (-1 / 2 : ℝ) (1 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (fun v hv => (hL (z, v) ⟨hz, hv⟩).trans (le_abs_self L))
      (by constructor <;> norm_num : (0 : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2)) hu

/-- A family of centered Jacobi integrals converges uniformly when its shape stays
in a smaller disk and its amplitudes have common local and integral bounds. -/
theorem tendstoUniformlyOn_sqrt_mul_integral_jacobiSaddleKernel {P : Type*} {S : Set P}
    {A : P → ℝ → ℂ} {w : P → ℂ} {ρ δ L M T : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hsmall : 4 * δ ^ 2 ≤ 1 - ρ) (hL : 0 ≤ L) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hw : ∀ p ∈ S, ‖w p‖ ≤ ρ) (hAc : ∀ p ∈ S, Measurable (A p))
    (hAi : ∀ p ∈ S, IntegrableOn (A p) (Icc (-1 : ℝ) 1))
    (hA0 : ∀ p ∈ S, ‖A p 0‖ ≤ M)
    (hA : ∀ p ∈ S, ∀ u ∈ Icc (-δ) δ, ‖A p u - A p 0‖ ≤ L * |u|)
    (hAT : ∀ p ∈ S, (∫ u in Icc (-1 : ℝ) 1, ‖A p u‖) ≤ T) :
    TendstoUniformlyOn (fun n : ℕ => fun p => (Real.sqrt n : ℂ) *
      ∫ u in Icc (-1 : ℝ) 1, A p u * jacobiSaddleKernel (w p) u ^ n)
      (fun p => A p 0 * (Real.pi / (1 - w p)) ^ (1 / 2 : ℂ)) atTop S := by
  let c := (1 - ρ) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hq0 (p : P) (hp : p ∈ S) : 1 - ρ ≤ (1 - w p).re := by
    have := (re_le_norm (w p)).trans (hw p hp)
    simp only [sub_re, one_re]; linarith
  have hcentral : TendstoUniformlyOn (fun n : ℕ => fun p => (Real.sqrt n : ℂ) *
      ∫ u in Icc (-δ) δ, A p u * jacobiSaddleKernel (w p) u ^ n)
      (fun p => A p 0 * (Real.pi / (1 - w p)) ^ (1 / 2 : ℂ)) atTop S := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => ((L + M / δ) / c + M / c ^ 2) / Real.sqrt n)
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_gt_atTop (0 : ℕ), hlim.eventually (gt_mem_nhds hε)] with n hn hεn
    intro p hp
    rw [dist_comm, dist_eq_norm]
    apply (norm_sqrt_mul_integral_jacobiSaddleKernel_sub_le ((hw p hp).trans_lt hρ)
      hδ hδhalf (hsmall.trans (hq0 p hp)) (hAc p hp) (hA0 p hp) (hA p hp) hn).trans_lt
    apply lt_of_le_of_lt _ hεn
    have hcle : c ≤ (1 - w p).re / 2 := div_le_div_of_nonneg_right (hq0 p hp) (by norm_num)
    gcongr
  let R := 1 - (1 - ρ) * δ ^ 2
  have hR0 : 0 ≤ R := by dsimp [R]; nlinarith [sq_nonneg δ, mul_nonneg hρ0 (sq_nonneg δ)]
  have hR1 : R < 1 := by dsimp [R]; nlinarith [sq_pos_of_pos hδ]
  have htail : TendstoUniformlyOn (fun n : ℕ => fun p => (Real.sqrt n : ℂ) *
      ((∫ u in Icc (-1 : ℝ) 1, A p u * jacobiSaddleKernel (w p) u ^ n) -
       (∫ u in Icc (-δ) δ, A p u * jacobiSaddleKernel (w p) u ^ n)))
      (fun _ => 0) atTop S := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => ((n : ℝ) * R ^ n) * T) atTop (𝓝 0) := by
      simpa using (tendsto_self_mul_const_pow_of_lt_one hR0 hR1).mul_const T
    filter_upwards [eventually_ge_atTop (1 : ℕ), hlim.eventually (gt_mem_nhds hε)] with n hn hεn
    intro p hp
    rw [dist_comm, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hb := norm_integral_jacobiSaddleKernel_tail_le ((hw p hp).trans_lt hρ) (hAi p hp)
      hδ.le (by linarith) n
    have hs : Real.sqrt n ≤ (n : ℝ) := Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hn))
    have hrp : 0 ≤ 1 - (1 - ‖w p‖) * δ ^ 2 := by
      nlinarith [norm_nonneg (w p), mul_nonneg (norm_nonneg (w p)) (sq_nonneg δ)]
    calc
      _ ≤ Real.sqrt n * ((∫ u in Icc (-1 : ℝ) 1, ‖A p u‖) *
          (1 - (1 - ‖w p‖) * δ ^ 2) ^ n) := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
      _ ≤ (n : ℝ) * (T * R ^ n) := by
        apply mul_le_mul hs _ (mul_nonneg (integral_nonneg (fun _ => norm_nonneg _))
          (pow_nonneg hrp n)) (Nat.cast_nonneg n)
        apply mul_le_mul (hAT p hp) _ (pow_nonneg hrp n) hT
        apply pow_le_pow_left₀ hrp
        dsimp [R]; nlinarith [hw p hp]
      _ = ((n : ℝ) * R ^ n) * T := by ring
      _ < ε := hεn
  convert htail.add hcentral using 1
  · funext n p
    simp only [Pi.add_apply]
    ring
  · funext p
    exact (zero_add _).symm

/-- The centered shape depends continuously on the evaluation point off the segment. -/
theorem continuousAt_jacobiSaddleShape_ratio {r s z : ℂ} (hz : z ∉ segment ℝ r s) :
    ContinuousAt (fun z => jacobiSaddleShape (jacobiSaddleRatio r s z)) z := by
  have hc := continuousAt_jacobiSaddleRatio hz
  have hne : jacobiSaddleRatio r s z + 1 ≠ 0 := by
    intro h
    have h' := congrArg re h
    simp only [add_re, one_re, zero_re] at h'
    linarith [re_jacobiSaddleRatio_pos hz]
  exact ((hc.sub continuousAt_const).div (hc.add continuousAt_const) hne).pow 2

/-- The full centered Gaussian limit is uniform on every compact set off the
focal segment. All bounds on the actual Jacobi amplitude are derived here. -/
theorem tendstoUniformlyOn_sqrt_mul_integral_jacobiSaddleAmplitude {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (m : ℕ) {r s : ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hKs : ∀ z ∈ K, z ∉ segment ℝ r s) :
    TendstoUniformlyOn (fun n : ℕ => fun z => (Real.sqrt n : ℂ) *
      ∫ u in Icc (-1 : ℝ) 1, jacobiSaddleAmplitude a b m r s z u *
        jacobiSaddleKernel (jacobiSaddleShape (jacobiSaddleRatio r s z)) u ^ n)
      (fun z => jacobiSaddleAmplitude a b m r s z 0 *
        (Real.pi / (1 - jacobiSaddleShape (jacobiSaddleRatio r s z))) ^ (1 / 2 : ℂ)) atTop K := by
  let w := fun z => jacobiSaddleShape (jacobiSaddleRatio r s z)
  have hwc : ContinuousOn (fun z => 1 - ‖w z‖) K :=
    continuousOn_const.sub
        (fun z hz => (continuousAt_jacobiSaddleShape_ratio (hKs z hz)).norm.continuousWithinAt)
  obtain ⟨η, hη, hηw⟩ := hK.exists_forall_le' hwc
    (fun z hz => sub_pos.mpr (norm_jacobiSaddleShape_lt_one (re_jacobiSaddleRatio_pos (hKs z hz))))
  let ρ := max 0 (1 - η)
  have hρ0 : 0 ≤ ρ := le_max_left _ _
  have hρ : ρ < 1 := max_lt (by norm_num) (by linarith)
  have hw (z : ℂ) (hz : z ∈ K) : ‖w z‖ ≤ ρ :=
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
  let A := jacobiSaddleAmplitude a b m r s
  have hAc : ContinuousOn (fun p : ℂ × ℝ => A p.1 p.2) (K ×ˢ Icc (-1 : ℝ) 1) := by
    intro p hp
    have ht : (p.2 + 1) / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hp.2.1, hp.2.2]
    exact ((continuousAt_jacobiMobiusIntegrand_saddle ha hb m (hKs p.1 hp.1) ht).comp
      (f := fun q : ℂ × ℝ => (q.1, (q.2 + 1) / 2)) (by fun_prop)).continuousWithinAt
  obtain ⟨M, hM⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hAc
  obtain ⟨L, hL, hAL⟩ := exists_uniform_jacobiSaddleAmplitude_lipschitz a b m hK hKs
  apply tendstoUniformlyOn_sqrt_mul_integral_jacobiSaddleKernel hρ0 hρ hδ hδhalf hsmall hL
    (abs_nonneg M) (by positivity : 0 ≤ 2 * |M|) hw
    (fun z _ => measurable_jacobiSaddleAmplitude a b m r s z)
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

/-- The Gaussian leading constant is continuous off the focal segment for all
complex exponents, independently of endpoint integrability. -/
theorem continuousAt_jacobiSaddleLeading (a b : ℂ) (m : ℕ) {r s z : ℂ}
    (hz : z ∉ segment ℝ r s) : ContinuousAt (jacobiSaddleLeading a b m r s) z := by
  have hA : ContinuousAt (fun z => jacobiSaddleAmplitude a b m r s z 0) z := by
    have h := (analyticAt_jacobiSaddleAmplitudeComplex a b m hz
      (by constructor <;> norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1)).continuousAt.comp
        (f := fun z : ℂ => (z, (0 : ℂ))) (by fun_prop)
    simpa only [Function.comp_def, ← ofReal_zero, jacobiSaddleAmplitudeComplex_ofReal] using h
  have hq := Complex.re_one_sub_pos (norm_jacobiSaddleShape_lt_one (re_jacobiSaddleRatio_pos hz))
  have hqne : 1 - jacobiSaddleShape (jacobiSaddleRatio r s z) ≠ 0 := by
    intro h; simp [h] at hq
  have hslit : (Real.pi : ℂ) / (1 - jacobiSaddleShape (jacobiSaddleRatio r s z)) ∈ slitPlane := by
    left
    rw [div_re]
    simp only [ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos Real.pi_pos hq) (normSq_pos.mpr hqne)
  exact (hA.mul ((continuousAt_const.div
    (continuousAt_const.sub (continuousAt_jacobiSaddleShape_ratio hz)) hqne).cpow
      continuousAt_const hslit)).div_const 2

/-- Compact-uniform Gaussian asymptotics for the shifted Möbius Euler integral. -/
theorem tendstoUniformlyOn_sqrt_mul_pow_mul_integral_jacobiMobius {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (m : ℕ) {r s : ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hKs : ∀ z ∈ K, z ∉ segment ℝ r s) :
    TendstoUniformlyOn (fun k : ℕ => fun z => (Real.sqrt k : ℂ) * jacobiSaddleScale r s z ^ k *
      ∫ t in (0 : ℝ)..1, jacobiMobiusIntegrand (a + k) (b + k) (m + k)
        (z - r) (z - s) (jacobiSaddleRatio r s z) t)
      (jacobiSaddleLeading a b m r s) atTop K := by
  have h := (uniformContinuous_div_const' (2 : ℂ)).comp_tendstoUniformlyOn
    (tendstoUniformlyOn_sqrt_mul_integral_jacobiSaddleAmplitude ha hb m hK hKs)
  apply h.congr (Eventually.of_forall (fun k z hz => ?_))
  dsimp only [Function.comp_apply]
  rw [integral_jacobiSaddleAmplitude_mul_kernel_pow a b m k (hKs z hz)]
  ring

/-- The normalized second-kind functions converge uniformly on compact sets off
the segment to their nonzero saddle coefficient, after a fixed degree shift. -/
theorem tendstoUniformlyOn_jacobiSecondKind_saddle_shift (α β r s : ℂ) (N : ℕ)
    (hα : 0 < (α + N).re) (hβ : 0 < (β + N).re) {K : Set ℂ}
    (hK : IsCompact K) (hKs : ∀ z ∈ K, z ∉ segment ℝ r s) :
    TendstoUniformlyOn (fun k : ℕ => fun z => jacobiSecondKind α β r s (N + k) z *
      (jacobiSaddleScale r s z / 4) ^ k)
      (jacobiSecondKindSaddleCoefficient α β N r s) atTop K := by
  have hnum := tendstoUniformlyOn_sqrt_mul_pow_mul_integral_jacobiMobius hα hβ (N + 1) hK hKs
    |>.tendstoLocallyUniformlyOn
  have href := (tendsto_sqrt_mul_pow_mul_integral_jacobiMobius hα hβ (N + 1)
    (r := 0) (s := 0) (z := 1) (by simp)).tendstoUniformlyOn_const K |>.tendstoLocallyUniformlyOn
  have hdiv := hnum.div₀ href
    (fun z hz => (continuousAt_jacobiSaddleLeading _ _ _ (hKs z hz)).continuousWithinAt)
    continuousOn_const (fun _ _ => jacobiSaddleLeading_ne_zero _ _ _ (by simp))
  have h := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp hdiv
  apply h.congr
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  intro z hz
  have hs : (Real.sqrt k : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)).ne'
  dsimp only [Pi.div_apply]
  rw [jacobiSecondKind_eq_saddle_integral_div_reference α β r s N k hα hβ (hKs z hz)]
  simp only [jacobiSaddleScale_reference, div_pow]
  field_simp

/-- Carlson's relative second-kind asymptotic is uniform on compact sets off the
focal segment. The explicitly defined leading coefficient never vanishes there. -/
theorem tendstoUniformlyOn_jacobiSecondKind_div_saddle_shift (α β r s : ℂ) (N : ℕ)
    (hα : 0 < (α + N).re) (hβ : 0 < (β + N).re) {K : Set ℂ}
    (hK : IsCompact K) (hKs : ∀ z ∈ K, z ∉ segment ℝ r s) :
    TendstoUniformlyOn (fun k : ℕ => fun z => jacobiSecondKind α β r s (N + k) z /
      (jacobiSecondKindSaddleCoefficient α β N r s z * (4 / jacobiSaddleScale r s z) ^ k))
      (fun _ => 1) atTop K := by
  have hc : ContinuousOn (jacobiSecondKindSaddleCoefficient α β N r s) K := by
    intro z hz
    exact (continuousAt_jacobiSaddleLeading _ _ _ (hKs z hz)).continuousWithinAt.div_const _
  have h := tendstoUniformlyOn_jacobiSecondKind_saddle_shift α β r s N hα hβ hK hKs
    |>.tendstoLocallyUniformlyOn
  have hconst : TendstoLocallyUniformlyOn
      (fun _ : ℕ => jacobiSecondKindSaddleCoefficient α β N r s)
      (jacobiSecondKindSaddleCoefficient α β N r s) atTop K :=
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
coefficient function works on every compact set off the focal segment. -/
theorem exists_tendstoUniformlyOn_jacobiSecondKind_div_geometric (α β r s : ℂ) :
    ∃ C : ℂ → ℂ, (∀ z ∉ segment ℝ r s, C z ≠ 0) ∧
      ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, z ∉ segment ℝ r s) →
        TendstoUniformlyOn (fun n : ℕ => fun z => jacobiSecondKind α β r s n z /
          (C z * (4 / jacobiSaddleScale r s z) ^ n)) (fun _ => 1) atTop K := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (-α.re) (-β.re))
  have hα : 0 < (α + N).re := by
    simp only [add_re, natCast_re]
    linarith [le_max_left (-α.re) (-β.re)]
  have hβ : 0 < (β + N).re := by
    simp only [add_re, natCast_re]
    linarith [le_max_right (-α.re) (-β.re)]
  let G := fun z => 4 / jacobiSaddleScale r s z
  have hG (z : ℂ) (hz : z ∉ segment ℝ r s) : G z ≠ 0 :=
    div_ne_zero (by norm_num) (jacobiSaddleScale_ne_zero hz)
  refine ⟨fun z => jacobiSecondKindSaddleCoefficient α β N r s z / G z ^ N,
    fun z hz => div_ne_zero (jacobiSecondKindSaddleCoefficient_ne_zero _ _ _ hz)
      (pow_ne_zero _ (hG z hz)), fun K hK hKs => ?_⟩
  have h := tendstoUniformlyOn_jacobiSecondKind_div_saddle_shift α β r s N hα hβ hK hKs
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

end Carlson.TwoVariable
