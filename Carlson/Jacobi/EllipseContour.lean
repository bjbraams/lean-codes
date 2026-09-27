/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.EllipseCoordinates
public import ComplexAnalysis.Cycle
public import ComplexAnalysis.CurveIndex.Continuity
public import ComplexAnalysis.Integral.CirclePath
public import ToMathlib.Analysis.Integral.CurveIntegral.Map

/-!
# Confocal ellipses as integration contours

The confocal ellipse with foci `r, s` and mean radius `σ > ‖r - s‖/4` is the Joukowski image of
the circle of radius `σ`. As a closed `C¹` curve it lies on the level set `μ = σ` of Carlson's
mean radius. Pulling the Cauchy kernel back to the circle and splitting it into partial
fractions shows that it winds once around the midpoint of the foci; constancy of the index on
the convex elliptic disk and on the connected unbounded exterior gives index one inside and
zero outside.

## Main results

* `jacobiEllipsePath`, `jacobiEllipseCycle`: the ellipse as a path and as a cycle.
* `jacobiEllipseRadius_of_mem_range_jacobiEllipseCycle`: the cycle lies on `μ = σ`.
* `index_jacobiEllipseCycle_of_lt`, `index_jacobiEllipseCycle_of_gt`: index one inside and
  zero outside.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§7.5–7.6.
-/

@[expose] public noncomputable section
open Complex Set Metric Filter
open scoped Topology

namespace Carlson.TwoVariable

/-- The derivative of the Joukowski map with foci `r, s`. -/
theorem hasDerivAt_jacobiJoukowski (r s : ℂ) {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (jacobiJoukowski r s) (1 - (r - s) ^ 2 / (16 * w ^ 2)) w := by
  have h : HasDerivAt (fun v : ℂ => (r + s) / 2 + v + (r - s) ^ 2 / 16 * v⁻¹)
      (1 + (r - s) ^ 2 / 16 * -(w ^ 2)⁻¹) w :=
    ((hasDerivAt_id w).const_add ((r + s) / 2)).add
      ((hasDerivAt_inv hw).const_mul ((r - s) ^ 2 / 16))
  have he : jacobiJoukowski r s = fun v : ℂ => (r + s) / 2 + v + (r - s) ^ 2 / 16 * v⁻¹ := by
    funext v; simp only [jacobiJoukowski]; ring
  rw [he]
  convert h using 1
  field_simp
  ring

/-- Points of the circle path of positive radius are nonzero. -/
theorem ne_zero_of_mem_range_circle {σ : ℝ} (hσ : 0 < σ) {w : ℂ}
    (hw : w ∈ range (Path.circle 0 σ)) : w ≠ 0 := by
  rw [Path.range_circle, mem_sphere_zero_iff_norm, abs_of_pos hσ] at hw
  exact norm_pos_iff.mp (hw ▸ hσ)

/-- The confocal ellipse of mean radius `σ`, as the Joukowski image of the circle of radius `σ`. -/
def jacobiEllipsePath (r s : ℂ) {σ : ℝ} (hσ : 0 < σ) :=
  (Path.circle 0 σ).map' (fun _ hx =>
    ((hasDerivAt_jacobiJoukowski r s (ne_zero_of_mem_range_circle hσ hx)).hasFDerivAt
      ).continuousAt.continuousWithinAt)

/-- The confocal ellipse path is continuously differentiable. -/
theorem contDiffOn_jacobiEllipsePath (r s : ℂ) {σ : ℝ} (hσ : 0 < σ) :
    ContDiffOn ℝ 1 (jacobiEllipsePath r s hσ).extend unitInterval := by
  change ContDiffOn ℝ 1 (fun t => jacobiJoukowski r s ((Path.circle 0 σ).extend t)) unitInterval
  have hJ : ContDiffOn ℂ 1 (jacobiJoukowski r s) {w | w ≠ 0} := by
    intro w hw
    apply ContDiffAt.contDiffWithinAt
    show ContDiffAt ℂ 1 (fun w : ℂ => (r + s) / 2 + w + (r - s) ^ 2 / (16 * w)) w
    exact (contDiffAt_const.add contDiffAt_id).add
      (contDiffAt_const.div (contDiffAt_const.mul contDiffAt_id) (mul_ne_zero (by norm_num) hw))
  refine (hJ.restrict_scalars ℝ).comp (Path.contDiffOn_circle 0 σ) (fun t ht => ?_)
  exact ne_zero_of_mem_range_circle hσ ⟨⟨t, ht⟩, by rw [Path.extend_apply _ ht]⟩

/-- The confocal ellipse lies on the level set of the mean radius. -/
theorem jacobiEllipseRadius_of_mem_range_jacobiEllipsePath (r s : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hσr : ‖r - s‖ / 4 ≤ σ) {z : ℂ} (hz : z ∈ range (jacobiEllipsePath r s hσ)) :
    jacobiEllipseRadius r s z = σ := by
  obtain ⟨t, rfl⟩ := hz
  have hw := ne_zero_of_mem_range_circle hσ
    (show Path.circle 0 σ t ∈ range (Path.circle 0 σ) from ⟨t, rfl⟩)
  have hnorm : ‖Path.circle 0 σ t‖ = σ := by
    have h : Path.circle 0 σ t ∈ range (Path.circle 0 σ) := ⟨t, rfl⟩
    rw [Path.range_circle, mem_sphere_zero_iff_norm, abs_of_pos hσ] at h
    exact h
  change jacobiEllipseRadius r s (jacobiJoukowski r s (Path.circle 0 σ t)) = σ
  rw [jacobiEllipseRadius_jacobiJoukowski r s _ hw (by rw [hnorm]; exact hσr), hnorm]

/-- The confocal ellipse winds once around the midpoint of the foci. -/
theorem curveIndex_jacobiEllipsePath_midpoint (r s : ℂ) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ‖r - s‖ / 4 < σ) :
    curveIndex (jacobiEllipsePath r s hσ0) ((r + s) / 2) = 1 := by
  set J' : ℂ → ℂ := fun w => 1 - (r - s) ^ 2 / (16 * w ^ 2)
  set g' : ℂ → ℂ →L[ℂ] ℂ := fun w => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (J' w)
  have hg : ∀ w ∈ {w : ℂ | w ≠ 0}, HasFDerivAt (jacobiJoukowski r s) (g' w) w :=
    fun w hw => (hasDerivAt_jacobiJoukowski r s hw).hasFDerivAt
  have hγU : range (Path.circle 0 σ) ⊆ {w : ℂ | w ≠ 0} := fun w hw =>
    ne_zero_of_mem_range_circle hσ0 hw
  have hdiff : DifferentiableOn ℝ (Path.circle 0 σ).extend unitInterval :=
    (Path.contDiffOn_circle 0 σ (n := 1)).differentiableOn one_ne_zero
  have hmap := curveIntegral_map'_of_hasFDerivAt (𝕜 := ℂ) (Path.circle 0 σ) hg hγU hdiff
    (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - (r + s) / 2)⁻¹))
  unfold curveIndex
  rw [show jacobiEllipsePath r s hσ0 = (Path.circle 0 σ).map'
    (fun x hx => (hg x (hγU hx)).continuousAt.continuousWithinAt) from rfl, hmap]
  have hform : (fun x => (ContinuousLinearMap.toSpanSingleton ℂ
      ((jacobiJoukowski r s x - (r + s) / 2)⁻¹)).comp (g' x)) =
      fun x => ContinuousLinearMap.toSpanSingleton ℂ
        ((jacobiJoukowski r s x - (r + s) / 2)⁻¹ * J' x) := by
    funext x; ext; simp [g', mul_comm]
  rw [hform, curveIntegral_circle]
  set a : ℂ := I * (r - s) / 4
  have ha : ‖a‖ = ‖r - s‖ / 4 := by simp [a]
  have hk : (r - s) ^ 2 = -16 * a ^ 2 := by
    simp only [a]; ring_nf; rw [I_sq]; ring
  have hsph (w : ℂ) (hw : w ∈ sphere (0 : ℂ) σ) :
      (jacobiJoukowski r s w - (r + s) / 2)⁻¹ * J' w =
        (-1) * (w - 0)⁻¹ + (w - a)⁻¹ + (w - -a)⁻¹ := by
    have hwn : ‖w‖ = σ := by simpa using hw
    have hw0 : w ≠ 0 := norm_pos_iff.mp (hwn ▸ hσ0)
    have hwa : w - a ≠ 0 := fun h => by
      have : ‖w‖ = ‖a‖ := by rw [sub_eq_zero.mp h]
      linarith
    have hwa' : w - -a ≠ 0 := fun h => by
      have : ‖w‖ = ‖a‖ := by rw [sub_eq_zero.mp h, norm_neg]
      linarith
    have hJ : jacobiJoukowski r s w - (r + s) / 2 = (w - a) * (w - -a) / w := by
      simp only [jacobiJoukowski]
      rw [hk]
      field_simp
      ring
    rw [hJ]
    simp only [J']
    rw [hk]
    clear_value a
    field_simp
    ring
  have hσle : (0 : ℝ) ≤ σ := hσ0.le
  rw [circleIntegral.integral_congr hσle hsph]
  have ha_ball : a ∈ ball (0 : ℂ) σ := by rw [mem_ball_zero_iff, ha]; exact hσ
  have hna_ball : -a ∈ ball (0 : ℂ) σ := by rw [mem_ball_zero_iff, norm_neg, ha]; exact hσ
  have h0_ball : (0 : ℂ) ∈ ball (0 : ℂ) σ := mem_ball_self hσ0
  have hci (c : ℂ) (hc : c ∈ ball (0 : ℂ) σ) : CircleIntegrable (fun z => (z - c)⁻¹) 0 σ := by
    apply ContinuousOn.circleIntegrable hσle
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz h
    have h' : z = c := sub_eq_zero.mp h
    subst h'
    rw [mem_sphere_zero_iff_norm] at hz
    rw [mem_ball_zero_iff] at hc
    linarith
  have hA : CircleIntegrable (fun z : ℂ => (-1) * (z - 0)⁻¹) 0 σ :=
    (hci 0 h0_ball).const_mul (-1)
  have hB : CircleIntegrable (fun z : ℂ => (-1) * (z - 0)⁻¹ + (z - a)⁻¹) 0 σ :=
    hA.add (hci a ha_ball)
  rw [circleIntegral.integral_add (f := fun z : ℂ => (-1) * (z - 0)⁻¹ + (z - a)⁻¹)
      (g := fun z : ℂ => (z - -a)⁻¹) hB (hci (-a) hna_ball),
    circleIntegral.integral_add (f := fun z : ℂ => (-1) * (z - 0)⁻¹) (g := fun z : ℂ => (z - a)⁻¹)
      hA (hci a ha_ball),
    circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_inv_of_mem_ball h0_ball,
    circleIntegral.integral_sub_inv_of_mem_ball ha_ball,
    circleIntegral.integral_sub_inv_of_mem_ball hna_ball]
  have : (2 * (Real.pi : ℂ) * I) ≠ 0 := two_pi_I_ne_zero
  field_simp
  ring

/-- The mean radius is at least a quarter of the sum of the focal distances. -/
theorem quarter_le_jacobiEllipseRadius (r s z : ℂ) :
    (‖z - r‖ + ‖z - s‖) / 4 ≤ jacobiEllipseRadius r s z := by
  simp only [jacobiEllipseRadius]
  have := Real.sqrt_nonneg ((‖z - r‖ + ‖z - s‖) ^ 2 - ‖r - s‖ ^ 2)
  linarith

/-- The confocal ellipse winds once around every point of the open elliptic disk it bounds. -/
theorem curveIndex_jacobiEllipsePath_of_lt (r s : ℂ) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ‖r - s‖ / 4 < σ) {w : ℂ} (hw : jacobiEllipseRadius r s w < σ) :
    curveIndex (jacobiEllipsePath r s hσ0) w = 1 := by
  have hmid : (r + s) / 2 ∈ jacobiEllipseDisk r s σ := by
    change jacobiEllipseRadius r s ((r + s) / 2) < σ
    rw [(jacobiEllipseRadius_eq_min_iff r s _).mpr ⟨1 / 2, 1 / 2, by norm_num, by norm_num,
      by norm_num, by simp [real_smul]; ring⟩]
    exact hσ
  rw [← curveIndex_jacobiEllipsePath_midpoint r s hσ0 hσ]
  refine curveIndex_eq_of_isPreconnected _ (contDiffOn_jacobiEllipsePath r s hσ0)
    (convex_jacobiEllipseDisk r s hσ).isPreconnected ?_ hw hmid
  intro z hz hzr
  have := jacobiEllipseRadius_of_mem_range_jacobiEllipsePath r s hσ0 hσ.le hzr
  exact lt_irrefl σ (this ▸ hz)

/-- The confocal ellipse does not wind around points of the open elliptic exterior. -/
theorem curveIndex_jacobiEllipsePath_of_gt (r s : ℂ) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ‖r - s‖ / 4 < σ) {w : ℂ} (hw : σ < jacobiEllipseRadius r s w) :
    curveIndex (jacobiEllipsePath r s hσ0) w = 0 := by
  refine curveIndex_eq_zero_of_isPreconnected_of_not_isBounded _
    (contDiffOn_jacobiEllipsePath r s hσ0) (isPreconnected_jacobiEllipse_exterior r s hσ)
    ?_ ?_ hw
  · intro z hz hzr
    have := jacobiEllipseRadius_of_mem_range_jacobiEllipsePath r s hσ0 hσ.le hzr
    exact lt_irrefl σ (this ▸ hz)
  · intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    set z : ℂ := ((R + ‖r‖ + 4 * σ + 1 : ℝ) : ℂ)
    have hRnn : 0 ≤ R := by
      have h := hR (show jacobiJoukowski r s (σ + 1) ∈ _ from ?_)
      · exact le_trans dist_nonneg h
      · change σ < jacobiEllipseRadius r s _
        rw [jacobiEllipseRadius_jacobiJoukowski r s _ (by exact_mod_cast (by linarith : σ + 1 ≠ 0))]
        · rw [show ((σ : ℂ) + 1) = ((σ + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
            Real.norm_of_nonneg (by linarith)]; linarith
        · rw [show ((σ : ℂ) + 1) = ((σ + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
            Real.norm_of_nonneg (by linarith)]; linarith
    have hzn : ‖z‖ = R + ‖r‖ + 4 * σ + 1 := by
      simp only [z, norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (by positivity)
    have hzr : R + 4 * σ + 1 ≤ ‖z - r‖ := by
      have := norm_sub_norm_le z r
      linarith
    have hμ : σ < jacobiEllipseRadius r s z := by
      have := quarter_le_jacobiEllipseRadius r s z
      have := norm_nonneg (z - s)
      linarith
    have := hR hμ
    rw [mem_closedBall, dist_zero_right, hzn] at this
    have := norm_nonneg r
    linarith

/-- The confocal ellipse of mean radius `σ` as a cycle. -/
def jacobiEllipseCycle (r s : ℂ) {σ : ℝ} (hσ0 : 0 < σ) : Cycle :=
  Cycle.zsmulLoop 1 (Loop.ofPath (jacobiEllipsePath r s hσ0))

/-- The confocal ellipse cycle is continuously differentiable. -/
theorem jacobiEllipseCycle_isC1 (r s : ℂ) {σ : ℝ} (hσ0 : 0 < σ) :
    (jacobiEllipseCycle r s hσ0).IsC1 :=
  Cycle.zsmulLoop_isC1 _ (contDiffOn_jacobiEllipsePath r s hσ0)

/-- The confocal ellipse cycle lies on the level set of the mean radius. -/
theorem jacobiEllipseRadius_of_mem_range_jacobiEllipseCycle (r s : ℂ) {σ : ℝ} (hσ0 : 0 < σ)
    (hσr : ‖r - s‖ / 4 ≤ σ) {z : ℂ} (hz : z ∈ (jacobiEllipseCycle r s hσ0).range) :
    jacobiEllipseRadius r s z = σ :=
  jacobiEllipseRadius_of_mem_range_jacobiEllipsePath r s hσ0 hσr
    (Cycle.zsmulLoop_range_subset _ _ hz)

/-- The confocal ellipse cycle winds once around every point of the elliptic disk it bounds. -/
theorem index_jacobiEllipseCycle_of_lt (r s : ℂ) {σ : ℝ} (hσ0 : 0 < σ) (hσ : ‖r - s‖ / 4 < σ)
    {w : ℂ} (hw : jacobiEllipseRadius r s w < σ) : (jacobiEllipseCycle r s hσ0).index w = 1 := by
  rw [jacobiEllipseCycle, Cycle.zsmulLoop_index]
  change ((1 : ℤ) : ℂ) * curveIndex (jacobiEllipsePath r s hσ0) w = 1
  rw [curveIndex_jacobiEllipsePath_of_lt r s hσ0 hσ hw]; norm_num

/-- The confocal ellipse cycle has index zero at points of the elliptic exterior. -/
theorem index_jacobiEllipseCycle_of_gt (r s : ℂ) {σ : ℝ} (hσ0 : 0 < σ) (hσ : ‖r - s‖ / 4 < σ)
    {w : ℂ} (hw : σ < jacobiEllipseRadius r s w) : (jacobiEllipseCycle r s hσ0).index w = 0 := by
  rw [jacobiEllipseCycle, Cycle.zsmulLoop_index]
  change ((1 : ℤ) : ℂ) * curveIndex (jacobiEllipsePath r s hσ0) w = 0
  rw [curveIndex_jacobiEllipsePath_of_gt r s hσ0 hσ hw]; norm_num

end Carlson.TwoVariable
