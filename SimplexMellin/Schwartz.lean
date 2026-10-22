/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.L2
public import ToMathlib.Analysis.SchwartzExpExp
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Inversion with the exponential profile for smooth boundary kernels

For a kernel smooth near the closed simplex, including kernels nonzero on its faces,
the function inverted by `Dirichlet.regDirichletIntegral_inversion` is Schwartz in
logarithmic coordinates. It is the product of the Schwartz weight
`A(y) = exp (∑ i, (c i * y i - exp (y i)))` and the angular factor
`G(y) = g(e^y / ∑ e^y)`, whose derivatives of every order are bounded.

The derivative of normalized exponential coordinates is polynomial in their values.
The chain rule therefore expresses each angular derivative as another smooth function
on the compact closed simplex. This gives uniform bounds without a boundary-vanishing
hypothesis, and works with the order-dependent neighborhoods in `SmoothNearStdSimplex`.

## Main results

* `exists_bound_iteratedFDeriv_simplexAngle`: finite-order uniform angular derivative bounds.
* `hasTemperateGrowth_simplexAngle_of_smoothNear`: temperate growth without boundary vanishing.
* `exists_schwartzMap_radialLog_exp`: the exponential-profile logarithmic kernel is Schwartz.
* `integrable_simplexMellin_of_smoothNear`: integrability on every positive vertical plane.
* `regDirichletIntegral_inversion_exp_of_smoothNear`: unconditional interior inversion.
* `integral_norm_sq_simplexMellin_of_smoothNear`: exponential-profile Plancherel.

The former face-supported interfaces are retained as specialization wrappers.
-/

open Complex MeasureTheory Set
open MvMellin
open scoped FourierTransform ContDiff

universe u v

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type u} [Fintype ι]

/-- Normalized exponential coordinates on the simplex. -/
def simplexSoftmax (y : EuclideanSpace ℝ ι) : ι → ℝ :=
  (∑ i, Real.exp (y i))⁻¹ • fun i => Real.exp (y i)

/-- Normalized exponential coordinates belong to the closed simplex. -/
theorem simplexSoftmax_mem [Nonempty ι] (y : EuclideanSpace ℝ ι) :
    simplexSoftmax y ∈ Convexity.StdSimplex.coordinateSet ℝ ι :=
  inv_sum_smul_mem_coordinateSet fun _ _ => Real.exp_pos _

open scoped Classical in
/-- The polynomial expression for the derivative of normalized exponential coordinates. -/
def simplexSoftmaxDeriv (u : ι → ℝ) : EuclideanSpace ℝ ι →L[ℝ] (ι → ℝ) :=
  (∑ i, (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).smulRight (Pi.single i (u i))) -
    (∑ i, u i • PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).smulRight u

/-- The derivative expression is smooth, including at boundary points. -/
theorem contDiff_simplexSoftmaxDeriv : ContDiff ℝ ∞ (simplexSoftmaxDeriv (ι := ι)) := by
  classical
  unfold simplexSoftmaxDeriv
  apply ContDiff.sub
  · apply ContDiff.sum
    intro i _
    apply ContDiff.smulRight contDiff_const
    exact contDiff_pi.mpr fun j => by
      by_cases h : j = i
      · subst j; simpa using (contDiff_apply ℝ (fun _ : ι => ℝ) i)
      · simp only [Pi.single_eq_of_ne h]; exact contDiff_const
  · apply ContDiff.smulRight
    · exact ContDiff.sum fun i _ => (contDiff_apply ℝ (fun _ : ι => ℝ) i).smul contDiff_const
    · exact contDiff_id

/-- Differentiating normalized exponential coordinates gives a polynomial in their values. -/
theorem hasFDerivAt_simplexSoftmax [Nonempty ι] (y : EuclideanSpace ℝ ι) :
    HasFDerivAt simplexSoftmax (simplexSoftmaxDeriv (simplexSoftmax y)) y := by
  classical
  let p : ι → EuclideanSpace ℝ ι →L[ℝ] ℝ := fun i =>
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i
  have hp (i : ι) : HasFDerivAt (fun y : EuclideanSpace ℝ ι => Real.exp (y i))
      (Real.exp (y i) • p i) y := by
    simpa [p, Function.comp_def] using
      (Real.hasDerivAt_exp (y i)).comp_hasFDerivAt y (p i).hasFDerivAt
  have hs : HasFDerivAt (fun y : EuclideanSpace ℝ ι => ∑ i, Real.exp (y i))
      (∑ i, Real.exp (y i) • p i) y := by
    simpa only [Finset.sum_fn] using HasFDerivAt.sum (u := Finset.univ) fun i _ => hp i
  have hpos : 0 < ∑ i, Real.exp (y i) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hinv := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt y hs
  apply hasFDerivAt_pi''
  intro i
  apply (hinv.mul (hp i)).congr_fderiv
  ext v
  simp [simplexSoftmaxDeriv, simplexSoftmax, p, Pi.single_apply, mul_ite,
    Finset.mul_sum, Finset.sum_mul]
  field_simp
  ring

/-- Normalized exponential coordinates are smooth. -/
theorem contDiff_simplexSoftmax [Nonempty ι] :
    ContDiff ℝ ∞ (simplexSoftmax (ι := ι)) := by
  have hp : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ ι => fun i => Real.exp (y i)) :=
    contDiff_pi.mpr fun i => Real.contDiff_exp.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).contDiff
  have hs : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ ι => ∑ i, Real.exp (y i)) :=
    ContDiff.sum fun i _ => contDiff_pi.mp hp i
  exact (hs.inv fun _ => (Finset.sum_pos (fun _ _ => Real.exp_pos _)
    Finset.univ_nonempty).ne').smul hp

/-- The angular factor in logarithmic coordinates: `y ↦ g(e^y / ∑ e^y)`. -/
def simplexAngle (g : (ι → ℝ) → ℂ) (y : EuclideanSpace ℝ ι) : ℂ :=
  g ((∑ i, piExp y.ofLp i)⁻¹ • piExp y.ofLp)

/-- The angular factor is smooth when the kernel is. -/
theorem contDiff_simplexAngle [Nonempty ι] {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (simplexAngle g) :=
  hg.comp contDiff_simplexSoftmax

/-- The angular factor is invariant under translation along the diagonal. -/
theorem simplexAngle_sub_smul_one (g : (ι → ℝ) → ℂ) (y : EuclideanSpace ℝ ι) (a : ℝ) :
    simplexAngle g (y - a • WithLp.toLp 2 (fun _ => (1 : ℝ))) = simplexAngle g y := by
  unfold simplexAngle
  have hpe : piExp (y - a • WithLp.toLp 2 (fun _ => (1 : ℝ))).ofLp =
      Real.exp (-a) • piExp y.ofLp := by
    funext i
    simp only [piExp, Pi.smul_apply, smul_eq_mul]
    rw [← Real.exp_add]
    congr 1
    simp
    ring
  rw [hpe]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, smul_smul]
  congr 1
  have := (Real.exp_pos (-a)).ne'
  field_simp

/-- Every derivative of a smooth kernel in normalized exponential coordinates is bounded. -/
private theorem exists_bound_iteratedFDeriv_simplexAngle_aux [Nonempty ι] (n : ℕ)
    {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hΔ : Convexity.StdSimplex.coordinateSet ℝ ι ⊆ U)
    {g : (ι → ℝ) → F} (hg : ContDiffOn ℝ n g U) :
    ∃ C, ∀ y : EuclideanSpace ℝ ι,
      ‖iteratedFDeriv ℝ n (g ∘ simplexSoftmax) y‖ ≤ C := by
  induction n generalizing F with
  | zero =>
    obtain ⟨C, hC⟩ := (Convexity.StdSimplex.isCompact_coordinateSet ℝ
      ι).exists_bound_of_continuousOn
      (hg.continuousOn.mono hΔ)
    refine ⟨C, fun y => ?_⟩
    simpa only [norm_iteratedFDeriv_zero, Function.comp_apply] using
      hC _ (simplexSoftmax_mem y)
  | succ n ih =>
    let G : (ι → ℝ) → (EuclideanSpace ℝ ι →L[ℝ] F) :=
      fun u => (fderiv ℝ g u).comp (simplexSoftmaxDeriv u)
    have hg' : ContDiffOn ℝ n (fderiv ℝ g) U := hg.fderiv_of_isOpen hU (by simp)
    have hA : ContDiff ℝ (n : ℕ∞ω) (simplexSoftmaxDeriv (ι := ι)) :=
      contDiff_simplexSoftmaxDeriv.of_le (by simp)
    have hG : ContDiffOn ℝ n G U := hg'.clm_comp hA.contDiffOn
    obtain ⟨C, hC⟩ := ih hG
    have hd : fderiv ℝ (g ∘ simplexSoftmax) = G ∘ simplexSoftmax := by
      funext y
      exact ((hg.contDiffAt (hU.mem_nhds (hΔ (simplexSoftmax_mem y)))).differentiableAt
        (by simp)).hasFDerivAt.comp y (hasFDerivAt_simplexSoftmax y) |>.fderiv
    refine ⟨C, fun y => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv, hd]
    exact hC y

/-- Boundary values do not obstruct bounded angular derivatives of a smooth simplex kernel. -/
theorem exists_bound_iteratedFDeriv_simplexAngle [Nonempty ι] (n : ℕ)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex n g) :
    ∃ C, ∀ y : EuclideanSpace ℝ ι, ‖iteratedFDeriv ℝ n (simplexAngle g) y‖ ≤ C := by
  obtain ⟨U, hU, hΔ, hg⟩ := hg
  let e : ULift.{u} ℂ ≃ₗᵢ[ℝ] ℂ := LinearIsometryEquiv.ulift ℝ ℂ
  obtain ⟨C, hC⟩ := exists_bound_iteratedFDeriv_simplexAngle_aux n hU hΔ
    (e.symm.contDiff.comp_contDiffOn hg)
  refine ⟨C, fun y => ?_⟩
  have hfun : (e.symm ∘ g) ∘ simplexSoftmax = e.symm ∘ simplexAngle g := rfl
  simpa only [hfun, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left] using hC y

/-- Angular kernels smooth near the closed simplex are smooth in logarithmic coordinates. -/
theorem contDiff_simplexAngle_of_smoothNear [Nonempty ι] {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) : ContDiff ℝ ∞ (simplexAngle g) := by
  rw [contDiff_infty]
  intro n
  obtain ⟨U, hU, hΔ, hgs⟩ := hg n
  exact hgs.comp_contDiff (contDiff_simplexSoftmax.of_le (by simp))
    fun y => hΔ (simplexSoftmax_mem y)

/-- No boundary vanishing is needed for temperate growth of a smooth angular kernel. -/
theorem hasTemperateGrowth_simplexAngle_of_smoothNear [Nonempty ι] {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) : (simplexAngle g).HasTemperateGrowth := by
  refine ⟨contDiff_simplexAngle_of_smoothNear hg, fun n => ?_⟩
  obtain ⟨C, hC⟩ := exists_bound_iteratedFDeriv_simplexAngle n (hg n)
  exact ⟨0, C, fun y => by simpa only [pow_zero, mul_one] using hC y⟩

/-- **Temperate growth of the angular factor.** The face-supported interface specializes the
boundary-kernel theorem; support away from the faces is no longer needed by the proof. -/
theorem hasTemperateGrowth_simplexAngle [Nonempty ι] {g : (ι → ℝ) → ℂ} (hgs : ContDiff ℝ ∞ g)
    {δ : ℝ} (_hδ : 0 < δ)
    (_hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) :
    (simplexAngle g).HasTemperateGrowth :=
  hasTemperateGrowth_simplexAngle_of_smoothNear fun n =>
    ⟨univ, isOpen_univ, subset_univ _, (hgs.of_le (by simp)).contDiffOn⟩

/-- The logarithmic kernel with exponential radial profile is Schwartz for every kernel
smooth near the closed simplex, with arbitrary values on the faces. -/
theorem exists_schwartzMap_radialLog_exp [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hgs : SmoothNearStdSimplex g) :
    ∃ S : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
      ⇑S = radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g := by
  have hG := hasTemperateGrowth_simplexAngle_of_smoothNear hgs
  refine ⟨SchwartzMap.smulLeftCLM ℂ (simplexAngle g) (expExpSchwartz c hc), ?_⟩
  funext y
  rw [SchwartzMap.smulLeftCLM_apply_apply hG, expExpSchwartz_apply]
  simp only [radialLog, simplexAngle, smul_eq_mul, piExp]
  rw [← Complex.coe_smul, smul_eq_mul, Finset.sum_sub_distrib, sub_eq_add_neg, Real.exp_add,
    ofReal_mul]
  ring

/-- The exponential-profile transform is integrable on every positive vertical plane for
kernels smooth near the closed simplex; no vanishing at the faces is required. -/
theorem integrable_simplexMellin_of_smoothNear [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hgs : SmoothNearStdSimplex g) :
    Integrable fun ξ : ι → ℝ => simplexMellin (mellinPlane c ξ) g := by
  set φ : ℝ → ℂ := fun t => ((Real.exp (-t) : ℝ) : ℂ)
  obtain ⟨S, hS⟩ := exists_schwartzMap_radialLog_exp hc hgs
  have hF : Integrable (𝓕 (radialLog c φ g)) := by
    rw [← hS, ← SchwartzMap.fourier_coe]
    exact (𝓕 S).integrable
  rw [show 𝓕 (radialLog c φ g) = fun ξ : EuclideanSpace ℝ ι =>
      simplexMellinRadial φ (mellinPlane c ξ) g from
    funext (fourier_radialLog hc hgs.continuousOn (by fun_prop)),
    ← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
      (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hF
  refine hF.congr (Filter.Eventually.of_forall fun ξ => ?_)
  refine simplexMellinRadial_exp_eq ?_ g
  rw [re_sum]
  exact Finset.sum_pos (fun i _ => by simpa [mellinPlane] using hc i) Finset.univ_nonempty

/-- **Integrability for the exponential profile.** The former face-supported interface is a
specialization of integrability for kernels smooth near the closed simplex. -/
theorem integrable_simplexMellin [Nonempty ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hgs : ContDiff ℝ ∞ g) {δ : ℝ} (_hδ : 0 < δ)
    (_hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) :
    Integrable fun ξ : ι → ℝ => simplexMellin (mellinPlane c ξ) g :=
  integrable_simplexMellin_of_smoothNear hc fun n =>
    ⟨univ, isOpen_univ, subset_univ _, (hgs.of_le (by simp)).contDiffOn⟩

/-- Exponential-profile inversion holds at every interior point for kernels smooth near the
closed simplex, including kernels nonzero on its faces. -/
theorem regDirichletIntegral_inversion_exp_of_smoothNear [Nonempty ι] {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ} (hgs : SmoothNearStdSimplex g)
    {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    g u = Real.exp 1 * ∫ ξ : ι → ℝ,
      (∏ i, (u i : ℂ) ^ (-mellinPlane c ξ i)) * simplexMellin (mellinPlane c ξ) g :=
  regDirichletIntegral_inversion hc hgs.continuousOn
    (integrable_simplexMellin_of_smoothNear hc hgs) hu

/-- **Unconditional inversion with the exponential profile.** For a smooth kernel `g` vanishing at
the points of the simplex with a coordinate below some `δ > 0`, every `c` with positive
coordinates and every interior point `u` of the simplex,
`g u = e ∫ (∏ i, u i ^ (-b i)) Γ(∑ b) ∏ Γ(b i) T_b[g] dξ`, `b = c - 2πiξ`. -/
theorem regDirichletIntegral_inversion_exp_of_contDiff [Nonempty ι] {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ} (hgs : ContDiff ℝ ∞ g) {δ : ℝ} (_hδ : 0 < δ)
    (_hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    g u = Real.exp 1 * ∫ ξ : ι → ℝ,
      (∏ i, (u i : ℂ) ^ (-mellinPlane c ξ i)) * simplexMellin (mellinPlane c ξ) g :=
  regDirichletIntegral_inversion hc hgs.continuous.continuousOn
    (integrable_simplexMellin hc hgs _hδ _hgsupp) hu

/-- Exponential-profile Plancherel for kernels smooth near the closed simplex, including
nonzero boundary values. The squared radial profile on the right is `exp (-2t)`. -/
theorem integral_norm_sq_simplexMellin_of_smoothNear [Nonempty ι] {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) {g : (ι → ℝ) → ℂ} (hgs : SmoothNearStdSimplex g) :
    ((∫ ξ : ι → ℝ, ‖simplexMellin (mellinPlane c ξ) g‖ ^ 2 : ℝ) : ℂ) =
      simplexMellinRadial (fun t => ((Real.exp (-t) ^ 2 : ℝ) : ℂ))
        (fun i => ((2 * c i : ℝ) : ℂ)) (fun u => ((‖g u‖ ^ 2 : ℝ) : ℂ)) :=
  integral_norm_sq_simplexMellin_of_continuous hc hgs.continuousOn

end Dirichlet

end
