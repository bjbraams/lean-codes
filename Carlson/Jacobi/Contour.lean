/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.SecondKind
public import ComplexAnalysis.Cycle.Cauchy

/-!
# Jacobi coefficient extraction on general cycles

Carlson's Jacobi polynomials and adjoint second-kind functions are biorthogonal
on every `C¹` cycle avoiding the endpoint segment, with the cycle's index as a
factor. Polynomial coefficient extraction is likewise independent of the contour
up to its winding number. No positivity assumption on the parameters or
distinctness assumption on the endpoints is needed.

The proof deforms the cycle to an enclosing circle by the homology form of
Cauchy's theorem. The second-kind function is the existing single-valued branch
off the segment. Contours crossing that segment and branches adapted to more
general nonconvex domains are not covered here.

## Main results

* `cycleIntegral_eq_index_mul_circleIntegral`: contour comparison for functions
  holomorphic off a segment.
* `cycleIntegral_jacobiSecondKind_mul_polynomial`: extraction of polynomial coefficients.
* `cycleIntegral_jacobiOn_mul_jacobiSecondKind`: biorthogonality weighted by the index.
* `curveIntegral_jacobiOn_mul_jacobiSecondKind`: the single closed-curve version.
* `cycleIntegral_jacobiSecondKind_mul_eq_of_index_eq`: contour independence for
  functions holomorphic on a common open domain, under the homology condition.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §7.2.
-/

public noncomputable section
namespace Carlson.TwoVariable
open Complex Polynomial Set Metric ContinuousLinearMap

/-- Cauchy's theorem compares two cycles whose indices agree outside the
holomorphy domain, by reversing the second cycle. -/
private theorem integral_eq_of_index_eq {U : Set ℂ} (hU : IsOpen U)
    (Γ₁ Γ₂ : Cycle) (h₁ : Γ₁.IsC1) (h₂ : Γ₂.IsC1)
    (h₁U : Γ₁.range ⊆ U) (h₂U : Γ₂.range ⊆ U)
    (hind : ∀ z, z ∉ U → Γ₁.index z = Γ₂.index z)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    Γ₁.integral (fun z => toSpanSingleton ℂ (f z)) =
      Γ₂.integral (fun z => toSpanSingleton ℂ (f z)) := by
  let Δ : Cycle := ⟨Γ₂.n, fun i => (Γ₂.loop i).symm⟩
  have hΔ : Δ.IsC1 := fun i => Loop.contDiffOn_symm (h₂ i)
  have hΔrange : Δ.range = Γ₂.range := by
    simp only [Cycle.range, Δ, Loop.range_symm]
  have hΔindex (z : ℂ) : Δ.index z = -Γ₂.index z := by
    change (∑ i, curveIndex (Γ₂.loop i).2.symm z) = -(∑ i, curveIndex (Γ₂.loop i).2 z)
    simp only [curveIndex_symm, Finset.sum_neg_distrib]
  have hΔintegral : Δ.integral (fun z => toSpanSingleton ℂ (f z)) =
      -Γ₂.integral (fun z => toSpanSingleton ℂ (f z)) := by
    change (∑ i, curveIntegral _ (Γ₂.loop i).2.symm) = -(∑ i, curveIntegral _ (Γ₂.loop i).2)
    simp only [curveIntegral_symm, Finset.sum_neg_distrib]
  have h := (Γ₁.append Δ).integral_eq_zero hU (Cycle.append_isC1 h₁ hΔ)
    (by rw [Cycle.append_range, hΔrange]; exact union_subset h₁U h₂U)
    (by intro z hz; rw [Cycle.append_index, hΔindex, hind z hz, add_neg_cancel]) hf
  rw [Cycle.append_integral, hΔintegral] at h
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)

/-- Integrating a holomorphic function against a Jacobi second-kind kernel is
unchanged between contours homologous in its domain minus the endpoint segment.
It suffices to compare indices outside the domain and at one endpoint. -/
theorem cycleIntegral_jacobiSecondKind_mul_eq_of_index_eq (α β r s : ℂ) (n : ℕ)
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (Γ₁ Γ₂ : Cycle) (h₁ : Γ₁.IsC1) (h₂ : Γ₂.IsC1)
    (h₁U : Γ₁.range ⊆ U) (h₂U : Γ₂.range ⊆ U)
    (h₁avoid : Γ₁.range ⊆ (segment ℝ r s)ᶜ)
    (h₂avoid : Γ₂.range ⊆ (segment ℝ r s)ᶜ)
    (hind : ∀ z, z ∉ U → Γ₁.index z = Γ₂.index z)
    (hr : Γ₁.index r = Γ₂.index r) :
    Γ₁.integral (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * f z)) =
      Γ₂.integral (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * f z)) := by
  have hcompact : IsCompact (segment ℝ r s) := by
    rw [← convexHull_range_pair]
    exact (finite_range (pair r s)).isCompact_convexHull ℝ
  apply integral_eq_of_index_eq (U := U ∩ (segment ℝ r s)ᶜ)
    (hU.inter hcompact.isClosed.isOpen_compl) Γ₁ Γ₂ h₁ h₂
    (subset_inter h₁U h₁avoid) (subset_inter h₂U h₂avoid)
  · intro z hz
    by_cases hzU : z ∈ U
    · have hzseg : z ∈ segment ℝ r s := by simpa [hzU] using hz
      rw [Γ₁.index_eq_of_isPreconnected h₁ (convex_segment r s).isPreconnected
        (fun w hw hwΓ => h₁avoid hwΓ hw) hzseg (left_mem_segment ℝ r s),
        Γ₂.index_eq_of_isPreconnected h₂ (convex_segment r s).isPreconnected
        (fun w hw hwΓ => h₂avoid hwΓ hw) hzseg (left_mem_segment ℝ r s)]
      exact hr
    · exact hind z hzU
  · exact ((analyticOnNhd_jacobiSecondKind α β r s n).differentiableOn.mono
      inter_subset_right).fun_mul (hf.mono inter_subset_left)

/-- A cycle avoiding a segment can be replaced by its index times an enclosing
circle when the integrand is holomorphic off that segment. -/
theorem cycleIntegral_eq_index_mul_circleIntegral (Γ : Cycle) (hΓ : Γ.IsC1)
    {r s : ℂ} (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (segment ℝ r s)ᶜ)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hseg : segment ℝ r s ⊆ ball c R) :
    Γ.integral (fun z => toSpanSingleton ℂ (f z)) =
      Γ.index r * (∮ z in C(c, R), f z) := by
  have hdisj : segment ℝ r s ⊆ Γ.rangeᶜ := fun z hz hzΓ => havoid hzΓ hz
  obtain ⟨k, hk⟩ := Γ.exists_int_index hΓ (hdisj (left_mem_segment ℝ r s))
  let γ : Loop := Loop.ofPath (Path.circle c R)
  let Δ := Cycle.zsmulLoop (-k) γ
  have hΔ : Δ.IsC1 := Cycle.zsmulLoop_isC1 _ (Path.contDiffOn_circle c R)
  have hΔrange : Δ.range ⊆ sphere c R := by
    apply (Cycle.zsmulLoop_range_subset _ γ).trans
    change range (Path.circle c R) ⊆ sphere c R
    rw [Path.range_circle, abs_of_pos hR]
  have hΔavoid : Δ.range ⊆ (segment ℝ r s)ᶜ := by
    intro z hz hzseg
    have h1 := mem_sphere.mp (hΔrange hz)
    have h2 := mem_ball.mp (hseg hzseg)
    linarith
  have hindex (z : ℂ) (hz : z ∈ segment ℝ r s) : Γ.index z = k := by
    rw [Γ.index_eq_of_isPreconnected hΓ (convex_segment r s).isPreconnected hdisj
      hz (left_mem_segment ℝ r s)]
    exact hk
  have hcompact : IsCompact (segment ℝ r s) := by
    rw [← convexHull_range_pair]
    exact (finite_range (pair r s)).isCompact_convexHull ℝ
  have hzero := (Γ.append Δ).integral_eq_zero
    hcompact.isClosed.isOpen_compl (Cycle.append_isC1 hΓ hΔ)
    (by rw [Cycle.append_range]; exact union_subset havoid hΔavoid)
    (by
      intro z hz
      have hzseg : z ∈ segment ℝ r s := by simpa using hz
      rw [Cycle.append_index, hindex z hzseg, Cycle.zsmulLoop_index]
      change (k : ℂ) + (-k : ℤ) * curveIndex (Path.circle c R) z = 0
      rw [curveIndex_circle_of_mem_ball (hseg hzseg)]
      simp) hf
  rw [Cycle.append_integral, Cycle.zsmulLoop_integral] at hzero
  change Γ.integral (fun z => toSpanSingleton ℂ (f z)) +
    (-k) • curveIntegral (fun z => toSpanSingleton ℂ (f z)) (Path.circle c R) = 0 at hzero
  rw [curveIntegral_circle, zsmul_eq_mul, Int.cast_neg] at hzero
  rw [hk]
  linear_combination hzero

/-- Every cycle avoiding the endpoint segment extracts a polynomial's Jacobi
coefficient multiplied by the winding number about either endpoint. -/
theorem cycleIntegral_jacobiSecondKind_mul_polynomial (α β r s : ℂ) (n : ℕ) (p : ℂ[X])
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      Γ.integral (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * p.eval z)) =
        Γ.index r * carlsonJacobiCoefficient α β r s n p := by
  have hcompact : IsCompact (segment ℝ r s) := by
    rw [← convexHull_range_pair]
    exact (finite_range (pair r s)).isCompact_convexHull ℝ
  obtain ⟨R, hR, hseg⟩ := hcompact.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hnodes : range (pair r s) ⊆ ball 0 R := by
    rw [← convexHull_range_pair] at hseg
    exact (subset_convexHull ℝ _).trans hseg
  rw [cycleIntegral_eq_index_mul_circleIntegral Γ hΓ havoid
    ((analyticOnNhd_jacobiSecondKind α β r s n).differentiableOn.fun_mul p.differentiableOn)
    hR hseg, ← mul_assoc, mul_comm _ (Γ.index r), mul_assoc,
    circleIntegral_jacobiSecondKind_mul_polynomial α β r s n p hR hnodes]

/-- Jacobi polynomials and their adjoint second-kind functions are biorthogonal
on arbitrary `C¹` cycles off the endpoint segment, with the index as a factor. -/
theorem cycleIntegral_jacobiOn_mul_jacobiSecondKind (α β r s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) (m n : ℕ)
    (Γ : Cycle) (hΓ : Γ.IsC1) (havoid : Γ.range ⊆ (segment ℝ r s)ᶜ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      Γ.integral (fun z => toSpanSingleton ℂ
        ((jacobiOn α β r s m).eval z * jacobiSecondKind α β r s n z)) =
        Γ.index r * (if m = n then 1 else 0) := by
  simp_rw [mul_comm ((jacobiOn α β r s m).eval _)]
  rw [cycleIntegral_jacobiSecondKind_mul_polynomial α β r s n _ Γ hΓ havoid,
    carlsonJacobiCoefficient_apply_jacobiOn α β r s hc]

/-- The single-contour form of Jacobi biorthogonality. A positively oriented
contour of index one gives the usual Kronecker delta. -/
theorem curveIntegral_jacobiOn_mul_jacobiSecondKind (α β r s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) (m n : ℕ)
    {a : ℂ} (γ : Path a a) (hγ : ContDiffOn ℝ 1 γ.extend unitInterval)
    (havoid : ∀ t, γ t ∉ segment ℝ r s) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      curveIntegral (fun z => toSpanSingleton ℂ
        ((jacobiOn α β r s m).eval z * jacobiSecondKind α β r s n z)) γ =
        curveIndex γ r * (if m = n then 1 else 0) := by
  let Γ := Cycle.replicate 1 (Loop.ofPath γ)
  have hΓ : Γ.IsC1 := fun _ => hγ
  have hΓavoid : Γ.range ⊆ (segment ℝ r s)ᶜ :=
    Γ.range_subset_iff.mpr fun _ t => havoid t
  simpa only [Γ, Cycle.replicate_integral, Cycle.replicate_index, one_smul,
    Nat.cast_one, one_mul, Loop.ofPath] using
    cycleIntegral_jacobiOn_mul_jacobiSecondKind α β r s hc m n Γ hΓ hΓavoid

end Carlson.TwoVariable
