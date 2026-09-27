/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.AnalyticExpansion
public import Carlson.Jacobi.EllipseCoordinates
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The Cauchy-kernel identity on an initial region and its continuation

The contour coefficient of the scalar Cauchy kernel is the corresponding Jacobi
function of the second kind. This follows from the continued derivative-average
formula and applies at arbitrary complex parameters, without a native-integral
positivity hypothesis. Polynomial approximation then proves the kernel identity
for sufficiently distant poles, uniformly when the polynomial variable and pole
range over compact sets in the stated initial region. For coincident endpoints
the exact circular convergence domain is proved directly.

Connectedness of elliptic exteriors supplies the identity-principle step: local
uniform convergence on such an exterior would extend the initial identity to it.
That convergence remains an explicit hypothesis. The full domain of Lemma 7.6-1,
`μ(x) < μ(y)`, still requires the sharp large-degree estimates.

## Main results

* `circleIntegral_jacobiSecondKind_mul_cauchyKernel`: coefficient extraction for
  a pole outside an enclosing circle.
* `hasSum_jacobiOn_mul_jacobiSecondKind_of_circle`: the kernel identity under
  sufficient circle-separation hypotheses.
* `exists_radius_uniform_cauchyKernel`: an initial convergence region uniform
  over compact sets of polynomial evaluation points.
* `eqOn_cauchyKernel_of_tendstoLocallyUniformlyOn`: analytic continuation of the
  identity, conditional on local uniform convergence on the elliptic exterior.
* `hasSum_jacobiOn_mul_jacobiSecondKind_self`: the exact coincident-endpoint case.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Lemma 7.6-1 and its proof, equation (6).
-/

public noncomputable section
namespace Carlson.TwoVariable
open Complex Polynomial Set Filter Dirichlet Metric ContinuousLinearMap
open scoped Topology NNReal

/-- The derivatives of a Cauchy kernel have the positive factorial normalization
used in Carlson's derivative-average coefficients. -/
private theorem iteratedDeriv_cauchyKernel (n : ℕ) (y : ℂ) :
    iteratedDeriv n (fun w => (y - w)⁻¹) =
      fun w => (n.factorial : ℂ) * (y - w) ^ (-(n + 1 : ℤ)) := by
  rw [iteratedDeriv_eq_iterate]
  have h := iter_deriv_inv_linear n (-1 : ℂ) y
  simp only [neg_one_mul, neg_add_eq_sub] at h
  rw [h]
  funext w
  rw [show (-1 - (n : ℤ)) = -(n + 1) by ring]
  have he : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_pow]; simp
  linear_combination (n.factorial : ℂ) * (y - w) ^ (-(n + 1 : ℤ)) * he

/-- A Cauchy kernel is holomorphic on every closed disk avoiding its pole. -/
private theorem differentiableOn_cauchyKernel_closedBall {c y : ℂ} {ρ : ℝ}
    (hy : y ∉ closedBall c ρ) :
    DifferentiableOn ℂ (fun w => (y - w)⁻¹) (closedBall c ρ) := by
  intro w hw
  have hne : y - w ≠ 0 := sub_ne_zero.mpr (fun he => hy (he.symm ▸ hw))
  exact (((hasDerivAt_id w).const_sub y).inv hne).differentiableAt.differentiableWithinAt

/-- The contour coefficient of a Cauchy kernel equals the second-kind function
at its exterior pole. Parameters and endpoints may be arbitrary complex numbers. -/
theorem circleIntegral_jacobiSecondKind_mul_cauchyKernel (α β r s : ℂ) (n : ℕ)
    {c y : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hnodes : range (pair r s) ⊆ ball c ρ) (hy : y ∉ closedBall c ρ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∮ w in C(c, ρ), jacobiSecondKind α β r s n w * (y - w)⁻¹) =
        jacobiSecondKind α β r s n y := by
  have hseg : segment ℝ r s ⊆ ball c ρ := by
    rw [← convexHull_range_pair]
    exact convexHull_min hnodes (convex_ball c ρ)
  have hdom : (y, pair r s) ∈ carlsonResolventDomain :=
    mem_carlsonResolventDomain_of_not_mem_convexHull (by
      rw [convexHull_range_pair]
      exact fun h => hy (ball_subset_closedBall (hseg h)))
  have hG : IsRegCarlsonContinuation (iteratedDeriv n (fun w => (y - w)⁻¹))
      (pair r s) (fun b => (n.factorial : ℂ) * continuedRegCarlsonResolvent n b (pair r s) y) := by
    apply ((isRegCarlsonContinuation_continuedRegCarlsonResolvent n hdom).smul
      (n.factorial : ℂ)).congr
    intro u hu
    simp only [iteratedDeriv_cauchyKernel]
  have hf := differentiableOn_cauchyKernel_closedBall hy
  have h := circleIntegral_jacobiSecondKind_mul α β r s n hG hρ
    ⟨hf.mono ball_subset_closedBall, hf.continuousOn.mono closure_ball_subset_closedBall⟩ hnodes
  rw [h, jacobiSecondKind]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- The Jacobi kernel series sums to the Cauchy kernel under sufficient circle
separation conditions. This is the initial region for Carlson's Lemma 7.6-1;
its full confocal-ellipse domain requires the sharp degree estimates. -/
theorem hasSum_jacobiOn_mul_jacobiSecondKind_of_circle (α β r s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) {x y c : ℂ} {ρ : ℝ≥0} {σ : ℝ}
    (hσ : 0 < σ) (hσρ : σ < ρ) (hx : x ∈ ball c ρ)
    (hnodes : range (pair r s) ⊆ ball c σ) (hy : y ∉ closedBall c ρ)
    {C R d : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 < d) (hRd : R < d)
    (hp : ∀ n, ‖(jacobiOn α β r s n).eval x‖ ≤ C * R ^ n)
    (hdist : ∀ z ∈ sphere c σ, ∀ w ∈ segment ℝ r s, d ≤ ‖z - w‖) :
    HasSum (fun n => (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y)
      (y - x)⁻¹ := by
  let γ : Loop := Loop.ofPath (Path.circle c σ)
  let Γ := Cycle.zsmulLoop 1 γ
  have hΓ : Γ.IsC1 := Cycle.zsmulLoop_isC1 _ (Path.contDiffOn_circle c σ)
  have hrange : Γ.range ⊆ sphere c σ := by
    apply (Cycle.zsmulLoop_range_subset _ γ).trans
    change range (Path.circle c σ) ⊆ sphere c σ
    rw [Path.range_circle, abs_of_pos hσ]
  have hr : r ∈ ball c σ := hnodes ⟨0, pair_zero r s⟩
  have hind : Γ.index r = 1 := by
    rw [Cycle.zsmulLoop_index]
    change (1 : ℤ) * curveIndex (Path.circle c σ) r = 1
    rw [curveIndex_circle_of_mem_ball hr]
    norm_num
  have hΓball : Γ.range ⊆ ball c ρ := by
    intro z hz
    exact (mem_ball.mpr ((mem_sphere.mp (hrange hz)).trans_lt hσρ))
  have h := hasSum_jacobiContourCoefficient_on_ball α β r s hc
    (show 0 < ρ by exact_mod_cast hσ.trans hσρ) hx hC hR hd hRd hp Γ hΓ hind hΓball
    (fun z hz => hdist z (hrange hz)) (differentiableOn_cauchyKernel_closedBall hy)
  have he (n : ℕ) : jacobiContourCoefficient α β r s n Γ (fun w => (y - w)⁻¹) =
      jacobiSecondKind α β r s n y := by
    unfold jacobiContourCoefficient
    rw [Cycle.zsmulLoop_integral]
    change (2 * (Real.pi : ℂ) * I)⁻¹ *
      ((1 : ℤ) • curveIntegral (fun w => toSpanSingleton ℂ
        (jacobiSecondKind α β r s n w * (y - w)⁻¹)) (Path.circle c σ)) = _
    rw [one_smul, curveIntegral_circle]
    exact circleIntegral_jacobiSecondKind_mul_cauchyKernel α β r s n hσ hnodes
      (fun hyσ => hy (closedBall_subset_closedBall hσρ.le hyσ))
  simpa only [he, mul_comm] using h

/-- On every compact set of polynomial evaluation points, the kernel identity
holds for all sufficiently distant poles, uniformly on compact sets of such poles. -/
theorem exists_radius_uniform_cauchyKernel (α β r s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) {K : Set ℂ} (hK : IsCompact K) :
    ∃ T : ℝ, 0 < T ∧
      (∀ x ∈ K, ∀ y : ℂ, T < ‖y‖ →
        HasSum (fun n => (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y)
          (y - x)⁻¹) ∧
      ∀ L : Set ℂ, IsCompact L → (∀ y ∈ L, T < ‖y‖) →
        TendstoUniformlyOn
          (fun N (xy : ℂ × ℂ) => ∑ n ∈ Finset.range N,
            (jacobiOn α β r s n).eval xy.1 * jacobiSecondKind α β r s n xy.2)
          (fun xy => (xy.2 - xy.1)⁻¹) atTop (K ×ˢ L) := by
  obtain ⟨C, R, hC, hR, hp⟩ := exists_geometric_bound_jacobiOn α β r s hK
  have hsegcompact : IsCompact (segment ℝ r s) := by
    rw [← convexHull_range_pair]
    exact (finite_range (pair r s)).isCompact_convexHull ℝ
  obtain ⟨B, hB, hball⟩ := (hK.union hsegcompact).isBounded.subset_ball_lt 0 (0 : ℂ)
  have hseg : segment ℝ r s ⊆ ball 0 B := fun z hz => hball (Or.inr hz)
  let σ := B + R + 1
  let ρ : ℝ≥0 := ⟨σ + 1, by dsimp [σ]; linarith⟩
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσρ : σ < (ρ : ℝ) := by change σ < σ + 1; linarith
  have hnodes : range (pair r s) ⊆ ball 0 σ := by
    apply (subset_convexHull ℝ (range (pair r s))).trans
    rw [convexHull_range_pair]
    exact hseg.trans (ball_subset_ball (by dsimp [σ]; linarith))
  have hdist (z : ℂ) (hz : σ ≤ ‖z‖) (w : ℂ) (hw : w ∈ segment ℝ r s) :
      R + 1 ≤ ‖z - w‖ := by
    have hwB : ‖w‖ < B := by simpa only [mem_ball, dist_zero_right] using hseg hw
    have ht := norm_le_norm_sub_add z w
    dsimp [σ] at hz
    linarith
  have hsum (x : ℂ) (hx : x ∈ K) (y : ℂ) (hy : (ρ : ℝ) < ‖y‖) :
      HasSum (fun n => (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y)
        (y - x)⁻¹ := by
    have hxB : ‖x‖ < B := by simpa only [mem_ball, dist_zero_right] using hball (Or.inl hx)
    apply hasSum_jacobiOn_mul_jacobiSecondKind_of_circle α β r s hc hσ hσρ
      (by rw [mem_ball, dist_zero_right]; change ‖x‖ < B + R + 1 + 1; linarith)
      hnodes (by simpa only [mem_closedBall, dist_zero_right, not_le] using hy)
      hC (zero_le_one.trans hR) (d := R + 1) (by linarith) (by linarith) (fun n => hp n x hx)
    intro z hz
    exact hdist z (by simpa only [mem_sphere, dist_zero_right] using (mem_sphere.mp hz).ge)
  refine ⟨ρ, hσ.trans hσρ, hsum, ?_⟩
  intro L hL hLy
  have ht := tendstoUniformlyOn_sum_jacobiOn_mul_jacobiSecondKind α β r s hC
    (zero_le_one.trans hR) (d := R + 1) (by linarith) (by linarith) hp hL
    (fun z hz => hdist z (hσρ.trans (hLy z hz)).le)
  apply ht.congr_right
  intro xy hxy
  exact (hsum xy.1 hxy.1 xy.2 (hLy xy.2 hxy.2)).tsum_eq

/-- For every fixed polynomial evaluation point, the Jacobi kernel identity
holds at every sufficiently distant pole. The radius is uniform in that pole. -/
theorem exists_radius_hasSum_jacobiOn_mul_jacobiSecondKind (α β r s x : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) :
    ∃ T : ℝ, 0 < T ∧ ∀ y : ℂ, T < ‖y‖ →
      HasSum (fun n => (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y)
        (y - x)⁻¹ := by
  obtain ⟨T, hT, hsum, _⟩ := exists_radius_uniform_cauchyKernel α β r s hc
    (isCompact_singleton (x := x))
  exact ⟨T, hT, hsum x (mem_singleton x)⟩

/-- The identity principle extends the distant-pole kernel identity throughout
an elliptic exterior as soon as local uniform convergence there is established.
The convergence hypothesis is explicit; this theorem does not supply sharp bounds. -/
theorem eqOn_cauchyKernel_of_tendstoLocallyUniformlyOn (α β r s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) {x : ℂ} {ρ : ℝ}
    (hρ : ‖r - s‖ / 4 < ρ) (hx : jacobiEllipseRadius r s x ≤ ρ) {F : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn
      (fun N y => ∑ n ∈ Finset.range N,
        (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y)
      F atTop {y | ρ < jacobiEllipseRadius r s y}) :
    EqOn F (fun y => (y - x)⁻¹) {y | ρ < jacobiEllipseRadius r s y} := by
  let U := {y | ρ < jacobiEllipseRadius r s y}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_jacobiEllipseRadius r s)
  have havoid : U ⊆ (segment ℝ r s)ᶜ := by
    intro y hy hys
    have he := (jacobiEllipseRadius_eq_min_iff r s y).mpr hys
    change ρ < jacobiEllipseRadius r s y at hy
    linarith
  have hF : AnalyticOnNhd ℂ F U := by
    apply (hlim.differentiableOn (Eventually.of_forall fun N => ?_) hU).analyticOnNhd hU
    exact DifferentiableOn.fun_sum fun n _ =>
      (differentiableOn_const ((jacobiOn α β r s n).eval x)).fun_mul
        ((analyticOnNhd_jacobiSecondKind α β r s n).differentiableOn.mono havoid)
  have hg : AnalyticOnNhd ℂ (fun y => (y - x)⁻¹) U := by
    intro y hy
    have hyx : y ≠ x := by
      intro he
      subst y
      exact (not_lt_of_ge hx) hy
    exact (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hyx)
  obtain ⟨T, hT, hkernel⟩ := exists_radius_hasSum_jacobiOn_mul_jacobiSecondKind α β r s x hc
  obtain ⟨B, hB, hball⟩ := (isCompact_jacobiClosedEllipseDisk r s ρ).isBounded.subset_ball_lt T (0 : ℂ)
  have hB0 : 0 < B := hT.trans hB
  have hnormB : ‖(B : ℂ)‖ = B := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB0]
  have hBU : (B : ℂ) ∈ U := by
    change ρ < jacobiEllipseRadius r s (B : ℂ)
    by_contra hn
    have hm : (B : ℂ) ∈ jacobiClosedEllipseDisk r s ρ := le_of_not_gt hn
    have := hball hm
    simp only [mem_ball, dist_zero_right, hnormB, lt_self_iff_false] at this
  apply hF.eqOn_of_preconnected_of_eventuallyEq hg (isPreconnected_jacobiEllipse_exterior r s hρ) hBU
  filter_upwards [hU.mem_nhds hBU,
    (isOpen_lt continuous_const continuous_norm).mem_nhds
      (show T < ‖(B : ℂ)‖ by rwa [hnormB])] with y hy hTy
  exact tendsto_nhds_unique (hlim.tendsto_at hy) (hkernel y hTy).tendsto_sum_nat

/-- At coincident endpoints Carlson's kernel identity is the geometric-series
identity on its exact circular domain. -/
theorem hasSum_jacobiOn_mul_jacobiSecondKind_self (α β s x y : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) (hxy : ‖x - s‖ < ‖y - s‖) :
    HasSum (fun n => (jacobiOn α β s s n).eval x * jacobiSecondKind α β s s n y)
      (y - x)⁻¹ := by
  have hy : y ≠ s := sub_ne_zero.mp (norm_pos_iff.mp ((norm_nonneg _).trans_lt hxy))
  have hy0 : y - s ≠ 0 := sub_ne_zero.mpr hy
  have hquot : ‖(x - s) / (y - s)‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hy0)]
    exact hxy
  have hp (n : ℕ) : (ascPochhammer ℂ n).eval (α + β + n + 1) ≠ 0 :=
    jacobi_pochhammer_ne_zero_of_add_nat_ne_zero α β
      (fun k hk => hc k (by linear_combination hk)) n
  have h := (hasSum_geometric_of_norm_lt_one hquot).mul_right (y - s)⁻¹
  have he (n : ℕ) : (jacobiOn α β s s n).eval x * jacobiSecondKind α β s s n y =
      ((x - s) / (y - s)) ^ n * (y - s)⁻¹ := by
    rw [jacobiOn_self α β s n (hp n), eval_pow, eval_sub, eval_X, eval_C,
      jacobiSecondKind_self α β s y hc n hy]
    rw [zpow_neg, show (n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) by omega, zpow_natCast]
    simp only [div_eq_mul_inv, mul_pow, pow_succ, mul_inv_rev, inv_pow]
    ring
  have hval : (1 - (x - s) / (y - s))⁻¹ * (y - s)⁻¹ = (y - x)⁻¹ := by
    rw [← mul_inv_rev]
    congr 1
    field_simp
    ring
  simpa only [← he, hval] using h

end Carlson.TwoVariable
