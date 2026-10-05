/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.KernelSeries
public import Carlson.Jacobi.SeriesCoefficients
public import Mathlib.Analysis.Normed.Group.Tannery
public import ToMathlib.Analysis.Holomorphic.PolynomialApproximation

/-!
# Jacobi expansions from polynomial approximation

On a sufficiently distant cycle, the second-kind estimates give summable bounds
for contour coefficients multiplied by the monic Jacobi polynomials. These bounds
allow passage from finite polynomial expansions to limits of polynomials. This
proves expansion existence for holomorphic functions on disks under a sufficient
separation condition. For entire functions, moving the contour to a large circle
removes that condition: the Jacobi series converges absolutely at every point and
uniformly on every compact set to the function. Its coefficients may be computed
on any fixed index-one `C¹` cycle avoiding the endpoint segment.

Parameters and endpoints are complex, and coincident endpoints are included.
Identification with the function requires the existing basis admissibility
condition: `α+β+2` is not a nonpositive integer. Sharp convergence on confocal
ellipses remains further work. The initial-region Cauchy-kernel identity is proved
separately in `Carlson.Jacobi.CauchyKernel`.

## Main results

* `exists_summable_norm_jacobiContourCoefficient_mul`: summable bounds for the
  expansion terms, uniform over functions bounded on the cycle.
* `hasSum_jacobiContourCoefficient_of_polynomial_approximation`: passage from
  polynomial approximation to a Jacobi expansion.
* `hasSum_jacobiContourCoefficient_on_ball`: existence for holomorphic functions
  under disk and contour-separation hypotheses.
* `hasSum_jacobiContourCoefficient_of_entire`: expansion of every entire function.
* `tendstoLocallyUniformlyOn_sum_jacobiContourCoefficient_of_entire`: local uniform
  convergence throughout the plane.
* `summable_norm_jacobiContourCoefficient_mul_of_entire`: absolute convergence.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §§7.2 and 7.5.
-/

public noncomputable section
namespace Carlson.TwoVariable
open Complex Polynomial Set Filter ContinuousLinearMap
open scoped Topology NNReal

/-- Multiplication of the argument by a constant multiplies its contour
coefficient by the same constant, including for totalized integrals. -/
theorem jacobiContourCoefficient_const_mul (α β r s : ℂ) (n : ℕ)
    (Γ : Cycle) (c : ℂ) (f : ℂ → ℂ) :
    jacobiContourCoefficient α β r s n Γ (fun z => c * f z) =
      c * jacobiContourCoefficient α β r s n Γ f := by
  have he : (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * (c * f z))) =
      c • (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * f z)) := by
    ext z
    simp [mul_comm, mul_left_comm, mul_assoc]
  unfold jacobiContourCoefficient
  rw [he, Γ.integral_smul]
  simp only [smul_eq_mul]
  ring

/-- On a cycle sufficiently far from the segment, expansion terms admit a
summable majorant proportional to any uniform bound for the expanded function. -/
theorem exists_summable_norm_jacobiContourCoefficient_mul (α β r s : ℂ)
    {K : Set ℂ} {C R d : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hd : 0 < d) (hRd : R < d)
    (hp : ∀ n x, x ∈ K → ‖(jacobiOn α β r s n).eval x‖ ≤ C * R ^ n)
    (Γ : Cycle) (hΓ : Γ.IsC1)
    (hdist : ∀ z ∈ Γ.range, ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ (f : ℂ → ℂ) (F : ℝ), 0 ≤ F →
      (∀ z ∈ Γ.range, ‖f z‖ ≤ F) → ∀ n x, x ∈ K →
      ‖jacobiContourCoefficient α β r s n Γ f * (jacobiOn α β r s n).eval x‖ ≤
        M n * F := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_norm_jacobiOn_mul_jacobiSecondKind
    α β r s hC hR hd hRd hp Γ.isCompact_range hdist
  obtain ⟨L, hL, hΓbound⟩ := Γ.exists_norm_integral_le (F := ℂ) hΓ
  let A := ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * L
  refine ⟨fun n => A * M n, hM.mul_left A, ?_⟩
  intro f F hF hf n x hx
  rw [mul_comm, ← jacobiContourCoefficient_const_mul]
  unfold jacobiContourCoefficient
  rw [norm_mul]
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (L * (M n * F)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply hΓbound
      intro z hz
      rw [show jacobiSecondKind α β r s n z * ((jacobiOn α β r s n).eval x * f z) =
        ((jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n z) * f z by ring,
        norm_mul]
      exact (mul_le_mul_of_nonneg_left (hf z hz) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hbound n x hx z hz) hF)
    _ = _ := by ring

/-- The finite polynomial expansion can be written as an infinite sum because
all coefficients above the polynomial degree vanish. -/
theorem tsum_carlsonJacobiCoefficient_eval (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) (p : ℂ[X]) (x : ℂ) :
    ∑' n, carlsonJacobiCoefficient α β r s n p * (jacobiOn α β r s n).eval x =
      p.eval x := by
  rw [tsum_eq_sum (s := Finset.range (p.natDegree + 1)) (fun n hn => ?_)]
  · simpa only [eval_finsetSum, eval_smul, smul_eq_mul] using
      congrArg (Polynomial.eval x) (sum_carlsonJacobiCoefficient α β r s hc p)
  · have hn' : p.natDegree < n := by simp only [Finset.mem_range] at hn; omega
    rw [carlsonJacobiCoefficient_apply, iterate_derivative_eq_zero hn', map_zero,
      zero_div, zero_mul]

/-- Uniform polynomial approximation on a sufficiently distant index-one cycle,
together with convergence at the evaluation point, yields its Jacobi expansion.
The separation condition is sufficient and is not the sharp ellipse condition. -/
theorem hasSum_jacobiContourCoefficient_of_polynomial_approximation (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {x : ℂ} {C R d : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 < d) (hRd : R < d)
    (hp : ∀ n, ‖(jacobiOn α β r s n).eval x‖ ≤ C * R ^ n)
    (Γ : Cycle) (hΓ : Γ.IsC1) (hind : Γ.index r = 1)
    (hdist : ∀ z ∈ Γ.range, ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖)
    {p : ℕ → ℂ[X]} {f : ℂ → ℂ}
    (hlim : TendstoUniformlyOn (fun N z => (p N).eval z) f atTop Γ.range)
    (hx : Tendsto (fun N => (p N).eval x) atTop (𝓝 (f x))) :
    HasSum (fun n => jacobiContourCoefficient α β r s n Γ f *
      (jacobiOn α β r s n).eval x) (f x) := by
  have havoid : Γ.range ⊆ (segment ℝ r s)ᶜ := by
    intro z hz hzs
    have := hdist z hz z hzs
    simp only [sub_self, norm_zero] at this
    linarith
  have hpcont (N : ℕ) : ContinuousOn (fun z => (p N).eval z) Γ.range :=
    (p N).continuous.continuousOn
  obtain ⟨B, hB⟩ := Γ.isCompact_range.exists_bound_of_continuousOn
    (hlim.continuousOn (Frequently.of_forall hpcont))
  let F := max B 0 + 1
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hf : ∀ z ∈ Γ.range, ‖f z‖ ≤ F := by
    intro z hz
    exact (hB z hz).trans (by dsimp [F]; linarith [le_max_left B 0])
  have hpb : ∀ᶠ N in atTop, ∀ z ∈ Γ.range, ‖(p N).eval z‖ ≤ F := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) 1 zero_lt_one] with N hN
    intro z hz
    have hdiff : ‖(p N).eval z - f z‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hN z hz
    have hnorm := norm_le_norm_sub_add ((p N).eval z) (f z)
    have hb := hB z hz
    dsimp [F]
    linarith [le_max_left B 0]
  obtain ⟨M, hM, hbound⟩ := exists_summable_norm_jacobiContourCoefficient_mul α β r s
    (K := {x}) hC hR hd hRd (by intro n y hy; simpa only [mem_singleton_iff.mp hy] using hp n)
    Γ hΓ hdist
  have hsum : Summable (fun n => jacobiContourCoefficient α β r s n Γ f *
      (jacobiOn α β r s n).eval x) :=
    (hM.mul_right F).of_norm_bounded (fun n => hbound f F hF hf n x (mem_singleton x))
  have ht := tendsto_tsum_of_dominated_convergence (hM.mul_right F)
    (fun n => (tendsto_jacobiContourCoefficient α β r s n Γ hΓ havoid hpcont hlim).mul_const
      ((jacobiOn α β r s n).eval x))
    (hpb.mono fun N hN n => hbound (fun z => (p N).eval z) F hF hN n x (mem_singleton x))
  have he (N : ℕ) : (∑' n, jacobiContourCoefficient α β r s n Γ
      (fun z => (p N).eval z) * (jacobiOn α β r s n).eval x) = (p N).eval x := by
    simp_rw [jacobiContourCoefficient_polynomial α β r s _ _ Γ hΓ havoid, hind, one_mul]
    exact tsum_carlsonJacobiCoefficient_eval α β r s hc (p N) x
  simp only [he] at ht
  exact (tendsto_nhds_unique ht hx) ▸ hsum.hasSum

/-- An entire function has a Jacobi expansion with contour coefficients on any
index-one cycle satisfying the sufficient distance separation condition. -/
theorem hasSum_jacobiContourCoefficient_of_entire_of_separated (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {x : ℂ} {C R d : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 < d) (hRd : R < d)
    (hp : ∀ n, ‖(jacobiOn α β r s n).eval x‖ ≤ C * R ^ n)
    (Γ : Cycle) (hΓ : Γ.IsC1) (hind : Γ.index r = 1)
    (hdist : ∀ z ∈ Γ.range, ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    HasSum (fun n => jacobiContourCoefficient α β r s n Γ f *
      (jacobiOn α β r s n).eval x) (f x) := by
  obtain ⟨p, hlim⟩ := exists_polynomial_tendstoLocallyUniformlyOn hf
  exact hasSum_jacobiContourCoefficient_of_polynomial_approximation α β r s hc
    hC hR hd hRd hp Γ hΓ hind hdist
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hlim
      Γ.range (subset_univ _) Γ.isCompact_range)
    (hlim.tendsto_at (mem_univ x))

/-- A function holomorphic on a disk has its Jacobi expansion at points inside
that disk when an index-one cycle in the disk satisfies the sufficient separation
condition. This proves existence without assuming convergence of the Jacobi series. -/
theorem hasSum_jacobiContourCoefficient_on_ball (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {x c : ℂ} {ρ : ℝ≥0}
    (hρ : 0 < ρ) (hx : x ∈ Metric.ball c ρ) {C R d : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 < d) (hRd : R < d)
    (hp : ∀ n, ‖(jacobiOn α β r s n).eval x‖ ≤ C * R ^ n)
    (Γ : Cycle) (hΓ : Γ.IsC1) (hind : Γ.index r = 1)
    (hΓball : Γ.range ⊆ Metric.ball c ρ)
    (hdist : ∀ z ∈ Γ.range, ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.closedBall c ρ)) :
    HasSum (fun n => jacobiContourCoefficient α β r s n Γ f *
      (jacobiOn α β r s n).eval x) (f x) := by
  obtain ⟨p, hlim⟩ := exists_polynomial_tendstoLocallyUniformlyOn_on_ball hρ (hf.mono Metric.ball_subset_closedBall)
  exact hasSum_jacobiContourCoefficient_of_polynomial_approximation α β r s hc
    hC hR hd hRd hp Γ hΓ hind hdist
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).mp hlim
      Γ.range hΓball Γ.isCompact_range)
    (hlim.tendsto_at hx)

/-- A large positively oriented circle gives an index-one cycle with any
prescribed positive distance from the endpoint segment. -/
private theorem exists_separated_jacobiCycle (r s : ℂ) {d : ℝ} (hd : 0 < d) :
    ∃ Γ : Cycle, Γ.IsC1 ∧ Γ.index r = 1 ∧
      ∀ z ∈ Γ.range, ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖ := by
  have hcompact : IsCompact (segment ℝ r s) := by
    rw [← convexHull_range_pair]
    exact (finite_range (pair r s)).isCompact_convexHull ℝ
  obtain ⟨B, hB, hseg⟩ := hcompact.isBounded.subset_ball_lt 0 (0 : ℂ)
  let ρ := B + d
  have hρ : 0 < ρ := add_pos hB hd
  let γ : Loop := Loop.ofPath (Path.circle 0 ρ)
  let Γ := Cycle.zsmulLoop 1 γ
  have hΓ : Γ.IsC1 := Cycle.zsmulLoop_isC1 _ (Path.contDiffOn_circle 0 ρ)
  have hrange : Γ.range ⊆ Metric.sphere 0 ρ := by
    apply (Cycle.zsmulLoop_range_subset _ γ).trans
    change range (Path.circle 0 ρ) ⊆ Metric.sphere 0 ρ
    rw [Path.range_circle, abs_of_pos hρ]
  have hrball : r ∈ Metric.ball 0 ρ :=
    (Metric.ball_subset_ball (by dsimp [ρ]; linarith)) (hseg (left_mem_segment ℝ r s))
  have hind : Γ.index r = 1 := by
    rw [Cycle.index_zsmulLoop]
    change (1 : ℤ) * curveIndex (Path.circle 0 ρ) r = 1
    rw [curveIndex_circle_of_mem_ball hrball]
    norm_num
  refine ⟨Γ, hΓ, hind, ?_⟩
  intro z hz w hw
  have hzρ : ‖z‖ = ρ := by simpa only [Metric.mem_sphere, dist_zero_right] using hrange hz
  have hwB : ‖w‖ < B := by simpa only [Metric.mem_ball, dist_zero_right] using hseg hw
  have ht := norm_le_norm_sub_add z w
  dsimp [ρ] at hzρ
  linarith

/-- Every entire function has its Jacobi expansion at every complex point.
Coefficients may be computed on any index-one `C¹` cycle avoiding the endpoint
segment; no separation condition or restriction on the individual parameters is
needed. The total parameter must be admissible for the monic Jacobi basis. -/
theorem hasSum_jacobiContourCoefficient_of_entire (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2))
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ)
    (hind : Γ.index r = 1) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (x : ℂ) :
    HasSum (fun n => jacobiContourCoefficient α β r s n Γ f *
      (jacobiOn α β r s n).eval x) (f x) := by
  obtain ⟨C, R, hC, hR, hp⟩ := exists_geometric_bound_jacobiOn α β r s
    (isCompact_singleton (x := x))
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  obtain ⟨Δ, hΔ, hΔindex, hdist⟩ := exists_separated_jacobiCycle r s
    (d := R + 1) (by linarith)
  have hΔavoid : Δ.range ⊆ (segment ℝ r s)ᶜ := by
    intro z hz hzs
    have := hdist z hz z hzs
    simp only [sub_self, norm_zero] at this
    linarith
  have he (n : ℕ) : jacobiContourCoefficient α β r s n Γ f =
      jacobiContourCoefficient α β r s n Δ f := by
    unfold jacobiContourCoefficient
    rw [cycleIntegral_jacobiSecondKind_mul_eq_of_index_eq α β r s n
      isOpen_univ hf.differentiableOn Γ Δ hΓ hΔ (subset_univ _) (subset_univ _)
      havoid hΔavoid (by simp) (hind.trans hΔindex.symm)]
  simp_rw [he]
  exact hasSum_jacobiContourCoefficient_of_entire_of_separated α β r s hc hC hR0
    (by linarith) (by linarith) (fun n => hp n x (mem_singleton x))
    Δ hΔ hΔindex hdist hf

/-- The Jacobi expansion terms of an entire function have a common summable
majorant on each compact set. -/
theorem exists_summable_norm_jacobiExpansion_of_entire (α β r s : ℂ)
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ)
    (hind : Γ.index r = 1) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ n x, x ∈ K →
      ‖jacobiContourCoefficient α β r s n Γ f * (jacobiOn α β r s n).eval x‖ ≤ M n := by
  obtain ⟨C, R, hC, hR, hp⟩ := exists_geometric_bound_jacobiOn α β r s hK
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  obtain ⟨Δ, hΔ, hΔindex, hdist⟩ := exists_separated_jacobiCycle r s
    (d := R + 1) (by linarith)
  have hΔavoid : Δ.range ⊆ (segment ℝ r s)ᶜ := by
    intro z hz hzs
    have := hdist z hz z hzs
    simp only [sub_self, norm_zero] at this
    linarith
  have he (n : ℕ) : jacobiContourCoefficient α β r s n Γ f =
      jacobiContourCoefficient α β r s n Δ f := by
    unfold jacobiContourCoefficient
    rw [cycleIntegral_jacobiSecondKind_mul_eq_of_index_eq α β r s n
      isOpen_univ hf.differentiableOn Γ Δ hΓ hΔ (subset_univ _) (subset_univ _)
      havoid hΔavoid (by simp) (hind.trans hΔindex.symm)]
  obtain ⟨M, hM, hbound⟩ := exists_summable_norm_jacobiContourCoefficient_mul α β r s
    hC hR0 (by linarith) (by linarith) hp Δ hΔ hdist
  obtain ⟨B, hB⟩ := Δ.isCompact_range.exists_bound_of_continuousOn hf.continuous.continuousOn
  refine ⟨fun n => M n * max B 0, hM.mul_right (max B 0), ?_⟩
  intro n x hx
  rw [he]
  exact hbound f (max B 0) (le_max_right _ _)
    (fun z hz => (hB z hz).trans (le_max_left _ _)) n x hx

/-- Jacobi expansions of entire functions converge uniformly on every compact
set, with coefficients taken on any fixed index-one cycle off the segment. -/
theorem tendstoUniformlyOn_sum_jacobiContourCoefficient_of_entire (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2))
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ)
    (hind : Γ.index r = 1) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N x => ∑ n ∈ Finset.range N, jacobiContourCoefficient α β r s n Γ f *
        (jacobiOn α β r s n).eval x) f atTop K := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_norm_jacobiExpansion_of_entire
    α β r s Γ hΓ havoid hind hf hK
  have hs (x : ℂ) : (∑' n, jacobiContourCoefficient α β r s n Γ f *
      (jacobiOn α β r s n).eval x) = f x :=
    (hasSum_jacobiContourCoefficient_of_entire α β r s hc Γ hΓ havoid hind hf x).tsum_eq
  simpa only [hs] using tendstoUniformlyOn_tsum_nat hM hbound

/-- The Jacobi expansion of an entire function converges locally uniformly
throughout the complex plane. -/
theorem tendstoLocallyUniformlyOn_sum_jacobiContourCoefficient_of_entire (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2))
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ)
    (hind : Γ.index r = 1) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    TendstoLocallyUniformlyOn
      (fun N x => ∑ n ∈ Finset.range N, jacobiContourCoefficient α β r s n Γ f *
        (jacobiOn α β r s n).eval x) f atTop univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  exact fun K _ hK => tendstoUniformlyOn_sum_jacobiContourCoefficient_of_entire
    α β r s hc Γ hΓ havoid hind hf hK

/-- The Jacobi expansion of an entire function is absolutely convergent at
every complex point. -/
theorem summable_norm_jacobiContourCoefficient_mul_of_entire (α β r s : ℂ)
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ)
    (hind : Γ.index r = 1) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (x : ℂ) :
    Summable (fun n => ‖jacobiContourCoefficient α β r s n Γ f *
      (jacobiOn α β r s n).eval x‖) := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_norm_jacobiExpansion_of_entire
    α β r s Γ hΓ havoid hind hf (isCompact_singleton (x := x))
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => hbound n x (mem_singleton x)) hM

end Carlson.TwoVariable
