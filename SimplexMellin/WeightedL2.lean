/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.L2
public import Dirichlet.Bridge
public import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The simplex Mellin transform on the complete weighted `L²` space

For positive abscissae `c`, the exponential radial profile gives the simplex measure
`(∏ Γ(2cᵢ) / 2^(2∑cᵢ)) • Dirichlet(2c)`. Its density is proportional to
`∏ uᵢ^(2cᵢ-1)`. The logarithmic kernel map on Schwartz kernels is an isometry for
this measure. Mathlib's density of Schwartz functions in `Lp` and its extension
of linear isometries extend the map to all weighted `L²` equivalence classes.
Fourier transformation then gives the full-plane simplex Mellin transform.

The construction uses Mathlib's completion APIs rather than assuming convergence
of the native Mellin integral for every measurable kernel. Tau Ceti's `Lp` norm
identity converts the established continuous-kernel Plancherel formula to an
equality of norms.
-/

open Complex MeasureTheory Set ProbabilityTheory
open scoped FourierTransform

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The squared norm of the exponential logarithmic radial weight, normalized against
the Dirichlet probability measure of shapes `2c`. -/
def simplexMellinL2Mass (c : ι → ℝ) : ℝ :=
  (∏ i, Real.Gamma (2 * c i)) / (2 : ℝ) ^ (∑ i, 2 * c i)

/-- The finite weighted simplex measure for which the exponential-profile transform
preserves the `L²` norm. Its density is proportional to `∏ uᵢ^(2cᵢ-1)`. -/
def simplexMellinMeasure (c : ι → ℝ) (_hc : ∀ i, 0 < c i) : Measure (ι → ℝ) :=
  ENNReal.ofReal (simplexMellinL2Mass c) • dirichletMeasure (fun i => 2 * c i)

omit [Nonempty ι] in
/-- The radial normalization is strictly positive for positive abscissae. -/
theorem simplexMellinL2Mass_pos {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    0 < simplexMellinL2Mass c :=
  div_pos (Finset.prod_pos fun i _ => Real.Gamma_pos_of_pos (mul_pos zero_lt_two (hc i)))
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- The weighted simplex measure is finite. -/
instance {c : ι → ℝ} (hc : ∀ i, 0 < c i) : IsFiniteMeasure (simplexMellinMeasure c hc) := by
  have := isProbabilityMeasure_dirichletMeasure (fun i => mul_pos zero_lt_two (hc i))
  exact (dirichletMeasure (fun i => 2 * c i)).smul_finite ENNReal.ofReal_ne_top

omit [Nonempty ι] in
/-- Squared-norm integration against the weighted simplex measure is a multiple of the
corresponding Dirichlet probability expectation. -/
theorem integral_norm_sq_simplexMellinMeasure {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (g : (ι → ℝ) → ℂ) :
    ∫ u, ‖g u‖ ^ 2 ∂simplexMellinMeasure c hc =
      simplexMellinL2Mass c * ∫ u, ‖g u‖ ^ 2 ∂dirichletMeasure (fun i => 2 * c i) := by
  rw [simplexMellinMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (simplexMellinL2Mass_pos hc).le, smul_eq_mul]

omit [Nonempty ι] in
/-- Explicit monomial density of the weighted simplex measure, with the radial
normalization `Γ(2∑c) / 2^(2∑c)` and zero density off the simplex interior. -/
theorem simplexMellinMeasure_eq_withDensity {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    simplexMellinMeasure c hc = Measure.stdSimplexMeasure.withDensity
      (fun u => ENNReal.ofReal ((Real.Gamma (∑ i, 2 * c i) / (2 : ℝ) ^ (∑ i, 2 * c i)) *
        stdSimplexInterior.indicator (fun u => ∏ i, u i ^ (2 * c i - 1)) u)) := by
  have hprod : (∏ i, Real.Gamma (2 * c i)) ≠ 0 :=
    (Finset.prod_pos fun i _ => Real.Gamma_pos_of_pos (mul_pos zero_lt_two (hc i))).ne'
  have hcoef : simplexMellinL2Mass c * (1 / mvRealBeta (fun i => 2 * c i)) =
      Real.Gamma (∑ i, 2 * c i) / (2 : ℝ) ^ (∑ i, 2 * c i) := by
    unfold simplexMellinL2Mass mvRealBeta
    field_simp
  rw [simplexMellinMeasure, dirichletMeasure,
    ← withDensity_smul _ (measurable_dirichletPdf _)]
  apply withDensity_congr_ae
  filter_upwards with u
  simp only [Pi.smul_apply, smul_eq_mul, dirichletPdf, dirichletPdfReal]
  rw [← ENNReal.ofReal_mul (simplexMellinL2Mass_pos hc).le, ← mul_assoc, hcoef]

/-- The Mellin transform of the squared exponential profile at a positive real exponent. -/
private theorem mellin_exp_sq_ofReal {B : ℝ} (hB : 0 < B) :
    mellin (fun t => ((Real.exp (-t) ^ 2 : ℝ) : ℂ)) (B : ℂ) =
      (((2 : ℝ) ^ (-B) * Real.Gamma B : ℝ) : ℂ) := by
  have hφ : (fun t => ((Real.exp (-t) ^ 2 : ℝ) : ℂ)) =
      (fun t => ((Real.exp (-(2 * t)) : ℝ) : ℂ)) := by
    funext t
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  rw [hφ, mellin_comp_mul_left (fun t => ((Real.exp (-t) : ℝ) : ℂ)) _ (by norm_num),
    ← GammaIntegral_eq_mellin, ← Gamma_eq_integral (by simpa using hB), Gamma_ofReal]
  rw [smul_eq_mul, ← ofReal_neg, ← ofReal_cpow (by norm_num)]
  push_cast
  rfl

/-- The logarithmic `L²` norm is exactly the weighted simplex norm, for continuous
kernels. This is the norm identity used to extend the transform by density. -/
theorem integral_norm_sq_radialLog_exp_eq_weighted {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    ∫ y : EuclideanSpace ℝ ι, ‖radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g y‖ ^ 2 =
      ∫ u, ‖g u‖ ^ 2 ∂simplexMellinMeasure c hc := by
  have h₂ (i : ι) : 0 < 2 * c i := mul_pos zero_lt_two (hc i)
  have hB : 0 < ∑ i, 2 * c i := Finset.sum_pos (fun i _ => h₂ i) Finset.univ_nonempty
  have hΓ : Real.Gamma (∑ i, 2 * c i) ≠ 0 := (Real.Gamma_pos_of_pos hB).ne'
  have h := ofReal_integral_norm_sq_radialLog hc hg
    (φ := fun t => ((Real.exp (-t) : ℝ) : ℂ)) (by fun_prop)
  simp only [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
  rw [simplexMellinRadial, regDirichletIntegral_ofReal h₂] at h
  have hsum : (∑ i, ((2 * c i : ℝ) : ℂ)) = ((∑ i, 2 * c i : ℝ) : ℂ) := by push_cast; rfl
  rw [hsum, mellin_exp_sq_ofReal hB, Gamma_ofReal] at h
  simp_rw [Gamma_ofReal] at h
  rw [← ofReal_prod, integral_complex_ofReal] at h
  norm_cast at h
  rw [integral_norm_sq_simplexMellinMeasure hc, h, simplexMellinL2Mass,
    Real.rpow_neg (by norm_num)]
  field_simp

omit [Nonempty ι] in
/-- The weighted measure is supported on the closed simplex. -/
theorem simplexMellinMeasure_restrict {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    (simplexMellinMeasure c hc).restrict (Convexity.StdSimplex.coordinateSet ℝ ι) =
      simplexMellinMeasure c hc := by
  rw [simplexMellinMeasure, Measure.restrict_smul, dirichletMeasure_restrict]

/-- Every kernel continuous on the closed simplex belongs to its weighted `L²` space. -/
theorem memLp_simplexMellinMeasure {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    MemLp g 2 (simplexMellinMeasure c hc) := by
  have hm := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  have hgm := hg.aestronglyMeasurable (μ := simplexMellinMeasure c hc) hm
  rw [simplexMellinMeasure_restrict] at hgm
  obtain ⟨C, hC⟩ := (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι).exists_bound_of_continuousOn hg
  apply MemLp.of_bound hgm C
  have hmem : ∀ᵐ u ∂simplexMellinMeasure c hc,
      u ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
    rw [← simplexMellinMeasure_restrict hc]
    exact ae_restrict_mem hm
  exact hmem.mono fun u hu => hC u hu

/-- The unbundled logarithmic kernel has the weighted simplex norm for every continuous
kernel. The membership proofs only choose representatives of the same `L²` classes. -/
theorem norm_toLp_radialLog_exp_eq {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    (h₂g : MemLp g 2 (simplexMellinMeasure c hc))
    (h₂log : MemLp (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g) 2) :
    ‖h₂log.toLp (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g)‖ = ‖h₂g.toLp g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Lp.integral_norm_sq_eq_norm_sq, ← Lp.integral_norm_sq_eq_norm_sq]
  calc
    _ = ∫ y : EuclideanSpace ℝ ι,
        ‖radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g y‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [h₂log.coeFn_toLp] with y hy
      rw [hy]
    _ = ∫ u, ‖g u‖ ^ 2 ∂simplexMellinMeasure c hc :=
      integral_norm_sq_radialLog_exp_eq_weighted hc hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [h₂g.coeFn_toLp] with u hu
      rw [hu]

/-- A Schwartz angular kernel gives a square-integrable exponential logarithmic kernel. -/
theorem memLp_radialLog_exp_schwartz {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (g : SchwartzMap (ι → ℝ) ℂ) :
    MemLp (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g) 2 := by
  exact memLp_radialLog_exp hc g.continuous.continuousOn

/-- The logarithmic kernel map on the dense Schwartz core. -/
def simplexLogL2Core {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    SchwartzMap (ι → ℝ) ℂ →ₗ[ℂ] Lp (α := EuclideanSpace ℝ ι) ℂ 2 where
  toFun g := (memLp_radialLog_exp_schwartz hc g).toLp
    (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g)
  map_add' g h := by
    rw [← MemLp.toLp_add]
    congr 1
    funext y
    simp [radialLog, mul_add, smul_add]
  map_smul' a g := by
    rw [← MemLp.toLp_const_smul]
    congr 1
    funext y
    simp only [Pi.smul_apply, RingHom.id_apply, radialLog, smul_apply, smul_eq_mul, real_smul]
    ring

/-- The dense logarithmic kernel map preserves the weighted simplex `L²` norm. -/
theorem norm_simplexLogL2Core {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (g : SchwartzMap (ι → ℝ) ℂ) :
    ‖simplexLogL2Core hc g‖ = ‖g.toLp 2 (simplexMellinMeasure c hc)‖ :=
  norm_toLp_radialLog_exp_eq hc g.continuous.continuousOn (g.memLp 2 _)
    (memLp_radialLog_exp_schwartz hc g)

/-- The logarithmic kernel map on the entire weighted simplex `L²` space, obtained by
Mathlib's isometric extension from the dense Schwartz core. -/
def simplexLogL2Isometry {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    Lp ℂ 2 (simplexMellinMeasure c hc) →ₗᵢ[ℂ] Lp (α := EuclideanSpace ℝ ι) ℂ 2 :=
  (simplexLogL2Core hc).extendOfIsometry
    (e := (SchwartzMap.toLpCLM ℂ ℂ 2 (simplexMellinMeasure c hc)).toLinearMap)
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top) (norm_simplexLogL2Core hc)

/-- The completed logarithmic map agrees with the logarithmic kernel on Schwartz functions. -/
theorem simplexLogL2Isometry_toLp {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (g : SchwartzMap (ι → ℝ) ℂ) :
    simplexLogL2Isometry hc (g.toLp 2 (simplexMellinMeasure c hc)) =
      (memLp_radialLog_exp_schwartz hc g).toLp
        (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g) :=
  LinearMap.extendOfIsometry_eq _ _ _ g

/-- The completed logarithmic map agrees with the actual logarithmic kernel for every
continuous boundary kernel, not only for the dense Schwartz core. -/
theorem simplexLogL2Isometry_of_continuous {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    simplexLogL2Isometry hc ((memLp_simplexMellinMeasure hc hg).toLp g) =
      (memLp_radialLog_exp hc hg).toLp (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g) := by
  let x := (memLp_simplexMellinMeasure hc hg).toLp g
  let y := (memLp_radialLog_exp hc hg).toLp
    (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g)
  have hd (S : SchwartzMap (ι → ℝ) ℂ) :
      dist (simplexLogL2Core hc S) y = dist (S.toLp 2 (simplexMellinMeasure c hc)) x := by
    change dist ((memLp_radialLog_exp_schwartz hc S).toLp _) y =
      dist ((S.memLp 2 (simplexMellinMeasure c hc)).toLp S) x
    dsimp only [x, y]
    rw [dist_eq_norm, dist_eq_norm, ← MemLp.toLp_sub, ← MemLp.toLp_sub]
    have heq : (radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) S -
        radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) g) =
        radialLog c (fun t => ((Real.exp (-t) : ℝ) : ℂ)) ((S : (ι → ℝ) → ℂ) - g) := by
      funext z
      simp [radialLog, mul_sub, smul_sub]
    simpa only [heq] using norm_toLp_radialLog_exp_eq hc (S.continuous.continuousOn.sub hg)
      ((S.memLp 2 _).sub (memLp_simplexMellinMeasure hc hg))
      (memLp_radialLog_exp hc (S.continuous.continuousOn.sub hg))
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨S, hS⟩ := (SchwartzMap.denseRange_toLpCLM (E := ι → ℝ) (F := ℂ)
    (p := 2) (μ := simplexMellinMeasure c hc) ENNReal.ofNat_ne_top).exists_dist_lt x (half_pos hε)
  change dist x (S.toLp 2 (simplexMellinMeasure c hc)) < ε / 2 at hS
  have htri := dist_triangle (simplexLogL2Isometry hc x)
    (simplexLogL2Isometry hc (S.toLp 2 (simplexMellinMeasure c hc))) y
  rw [(simplexLogL2Isometry hc).isometry.dist_eq, simplexLogL2Isometry_toLp] at htri
  change dist (simplexLogL2Isometry hc x) y ≤
    dist x (S.toLp 2 (simplexMellinMeasure c hc)) + dist (simplexLogL2Core hc S) y at htri
  rw [hd, dist_comm (S.toLp 2 (simplexMellinMeasure c hc)) x] at htri
  exact htri.trans (by linarith)

/-- The full-plane simplex Mellin transform on weighted simplex `L²` equivalence classes.
It is the Fourier isometry composed with the completed logarithmic kernel map. -/
def simplexMellinL2Isometry {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    Lp ℂ 2 (simplexMellinMeasure c hc) →ₗᵢ[ℂ] Lp (α := EuclideanSpace ℝ ι) ℂ 2 :=
  (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ).toLinearIsometry.comp
    (simplexLogL2Isometry hc)

/-- Plancherel on the complete weighted simplex `L²` space. -/
theorem norm_simplexMellinL2Isometry {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (g : Lp ℂ 2 (simplexMellinMeasure c hc)) :
    ‖simplexMellinL2Isometry hc g‖ = ‖g‖ :=
  (simplexMellinL2Isometry hc).norm_map g

/-- Fourier inversion recovers the completed logarithmic kernel in `L²`. -/
theorem fourierInv_simplexMellinL2Isometry {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (g : Lp ℂ 2 (simplexMellinMeasure c hc)) :
    𝓕⁻ (simplexMellinL2Isometry hc g) = simplexLogL2Isometry hc g :=
  FourierTransform.fourierInv_fourier_eq _

/-- The completed weighted transform agrees almost everywhere with the native integral
for every continuous kernel, including kernels with nonzero face values. -/
theorem simplexMellinL2Isometry_of_continuous_ae_eq {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    simplexMellinL2Isometry hc ((memLp_simplexMellinMeasure hc hg).toLp g) =ᵐ[volume]
      (fun ξ : EuclideanSpace ℝ ι => simplexMellin (mellinPlane c ξ) g) := by
  change (𝓕 (simplexLogL2Isometry hc ((memLp_simplexMellinMeasure hc hg).toLp g)) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) =ᵐ[volume] _
  rw [simplexLogL2Isometry_of_continuous hc hg]
  filter_upwards [Real.fourier_toLp_ae_eq (integrable_radialLog_exp hc hg)
    (memLp_radialLog_exp hc hg)] with ξ hξ
  rw [hξ, fourier_radialLog hc hg (by fun_prop)]
  apply simplexMellinRadial_exp_eq
  rw [re_sum]
  exact Finset.sum_pos (fun i _ => by simpa [mellinPlane] using hc i) Finset.univ_nonempty

/-- On the dense Schwartz core, the completed transform agrees almost everywhere with
the native full-plane simplex Mellin integral. -/
theorem simplexMellinL2Isometry_toLp_ae_eq {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (g : SchwartzMap (ι → ℝ) ℂ) :
    simplexMellinL2Isometry hc (g.toLp 2 (simplexMellinMeasure c hc)) =ᵐ[volume]
      (fun ξ : EuclideanSpace ℝ ι => simplexMellin (mellinPlane c ξ) g) :=
  simplexMellinL2Isometry_of_continuous_ae_eq hc g.continuous.continuousOn

/-- The image of the weighted simplex transform is a closed subspace of frequency `L²`. -/
theorem isClosed_range_simplexMellinL2Isometry {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    IsClosed (Set.range (simplexMellinL2Isometry hc)) :=
  (simplexMellinL2Isometry hc).isometry.isUniformInducing.isComplete_range.isClosed

/-- The full weighted simplex transform is an isometric equivalence onto its closed image.
The inverse recovers the weighted simplex equivalence class, not just its logarithmic image. -/
def simplexMellinL2EquivRange {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    Lp ℂ 2 (simplexMellinMeasure c hc) ≃ₗᵢ[ℂ]
      LinearMap.range (simplexMellinL2Isometry hc).toLinearMap :=
  (simplexMellinL2Isometry hc).equivRange

/-- Inversion on the closed image of the weighted simplex transform. -/
theorem simplexMellinL2EquivRange_symm_apply {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (g : Lp ℂ 2 (simplexMellinMeasure c hc)) :
    (simplexMellinL2EquivRange hc).symm ((simplexMellinL2EquivRange hc) g) = g :=
  (simplexMellinL2EquivRange hc).symm_apply_apply g

/-- Every weighted simplex `L²` class is approximated by Schwartz kernels, and their
completed transforms converge in frequency `L²` to its transform. -/
theorem exists_schwartz_approximation_simplexMellinL2 {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (g : Lp ℂ 2 (simplexMellinMeasure c hc)) :
    ∃ S : ℕ → SchwartzMap (ι → ℝ) ℂ,
      Filter.Tendsto (fun n => (S n).toLp 2 (simplexMellinMeasure c hc))
        Filter.atTop (nhds g) ∧
      Filter.Tendsto (fun n => simplexMellinL2Isometry hc ((S n).toLp 2 (simplexMellinMeasure c hc)))
        Filter.atTop (nhds (simplexMellinL2Isometry hc g)) := by
  have hmem := (SchwartzMap.denseRange_toLpCLM (E := ι → ℝ) (F := ℂ)
    (p := 2) (μ := simplexMellinMeasure c hc) ENNReal.ofNat_ne_top).closure_range ▸ Set.mem_univ g
  obtain ⟨v, hv, hvg⟩ := mem_closure_iff_seq_limit.1 hmem
  choose S hS using hv
  have hlim : Filter.Tendsto (fun n => (S n).toLp 2 (simplexMellinMeasure c hc))
      Filter.atTop (nhds g) := by
    convert hvg using 2 with n
    exact hS n
  exact ⟨S, hlim, ((simplexMellinL2Isometry hc).continuous.tendsto g).comp hlim⟩

end Dirichlet
