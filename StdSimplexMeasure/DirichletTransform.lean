/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/

import StdSimplexMeasure.ComplexDirichlet
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The Dirichlet or Simplex Mellin transform

By the regularized Dirichlet transform we understand the transformation from a complex-valued
function $f$ on the standard simplex $E^{k-1}$ (embedded in $ℝ^k$) to an analytic function of
$b∈ℂ^k$ that is the analytic continuation of `regDirichletIntegral b f`.

Terminology here is provisional. We are using the name (regularized) Dirichlet transform
because it is the central transform in Carlson's theory of Dirichlet averages. However,
the name (regularized) simplex Mellin transform is also appropriate.

## Main definitions and results

* `regDirichletMonomialTransform`: the regularized Dirichlet transform of a monomial.
* `regDirichletMvPolynomialTransform`: the regularized Dirichlet transform of an
  `MvPolynomial`.
* `differentiable_regDirichletMonomialTransform`: the monomial transform is entire.
* `differentiable_regDirichletMvPolynomialTransform`: the polynomial transform is entire.
* `dirichletConvergenceRegion`: the parameter region `re (b i) > -N`.
* `ContDiffNearStdSimplex`: finite differentiability on a neighborhood of the closed simplex.
* `exists_regDirichletContinuation_of_contDiffNear`: finite differentiability gives analytic
  continuation to the corresponding convergence region.

## References
[Carl77] Carlson, Bille Chandler. "Special functions of applied mathematics." Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

public noncomputable section DirichletTransform

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- A file-local shorthand for the product of Pochhammer polynomials associated to a
multi-index. Since `ι` is finite, monomial multi-indices are represented by ordinary functions
`ι → ℕ`; the finitely supported indices used by `MvPolynomial` coerce to this type. -/
private def mvPochhammer (b : ι → ℂ) (m : ι → ℕ) : ℂ :=
    ∏ i, (ascPochhammer ℂ (m i)).eval (b i)

/-- The regularized Dirichlet transform of the monomial with multi-index `m`.
This is an entire function of `b`. -/
def regDirichletMonomialTransform (m : ι → ℕ) (b : ι → ℂ) : ℂ :=
  mvPochhammer b m * (Gamma (∑ i, (b i + m i : ℂ)))⁻¹

/-- On its domain of definition the `regDirichletIntegral` of a monomial equals the
`regDirichletMonomialTransform`. -/
theorem regDirichletIntegral_monomial
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (m : ι → ℕ) :
    regDirichletIntegral b (fun u : ι → ℝ ↦ ∏ i, (u i : ℂ) ^ (m i)) =
      regDirichletMonomialTransform m b := by
  classical
  by_cases hι : Nonempty ι
  swap
  · let _ : IsEmpty ι := not_nonempty_iff.mp hι
    simp [regDirichletIntegral, regDirichletMonomialTransform, mvPochhammer,
      regDirichletDensity, MeasureTheory.Measure.stdSimplexMeasure_empty]
  let _ := hι
  let b' : ι → ℂ := fun i ↦ b i + m i
  have hbpos (i : ι) : 0 < (b i).re := by
    simpa [mvBetaConvergent] using hb i
  have hb' : b' ∈ mvBetaConvergent := by
    intro i
    dsimp [b']
    simpa only [add_re, ofReal_natCast] using
      add_pos_of_pos_of_nonneg (hbpos i) (Nat.cast_nonneg (m i))
  have hgamma (i : ι) :
      Gamma (b' i) = (ascPochhammer ℂ (m i)).eval (b i) * Gamma (b i) := by
    dsimp [b']
    apply (div_eq_iff (Gamma_ne_zero_of_re_pos (hbpos i))).mp
    exact Gamma_add_nat_div_Gamma_eq (b i) (fun k h ↦ by
      have hi := hbpos i
      rw [h] at hi
      simp only [neg_re] at hi
      exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg k))) hi)
  have hpoch (i : ι) : (ascPochhammer ℂ (m i)).eval (b i) ≠ 0 := by
    intro hzero
    have hgzero : Gamma (b' i) = 0 := by rw [hgamma, hzero, zero_mul]
    exact (Gamma_ne_zero_of_re_pos (hb' i)) hgzero
  have hae := MeasureTheory.Measure.ae_zero_lt_of_mem_stdSimplex (ι := ι)
  have hfun :
      (fun u : ι → ℝ ↦ regDirichletDensity b u * ∏ i, (u i : ℂ) ^ m i)
        =ᵐ[(MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict (stdSimplex ℝ ι)]
      fun u ↦ mvPochhammer b m * regDirichletDensity b' u := by
    have hmem := self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure) (isClosed_stdSimplex ℝ ι).measurableSet
    filter_upwards [hmem, hae] with u hu hupos
    have hinter : u ∈ stdSimplexInterior := ⟨hu, hupos⟩
    rw [regDirichletDensity, regDirichletDensity,
      Set.indicator_of_mem hinter, Set.indicator_of_mem hinter]
    unfold mvPochhammer
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [hgamma]
    have hu0 : (u i : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hupos i).ne'
    rw [show b' i - 1 = (b i - 1) + m i by simp [b']; ring,
      cpow_add _ _ hu0]
    rw [cpow_natCast]
    field_simp [hpoch i]
  unfold regDirichletIntegral regDirichletMonomialTransform
  rw [integral_congr_ae hfun, integral_const_mul,
    regDirichletIntegral_normalization b' hb']
  congr 1
  simp [b']

/-- Evaluation of a multivariate polynomial as the sum of its monomial terms. -/
private lemma eval_MvPolynomial_eq_sum_monomials (p : MvPolynomial ι ℂ) (x : ι → ℂ) :
    p.eval x = ∑ m ∈ p.support, p.coeff m * ∏ i, x i ^ m i := by
  calc
    p.eval x = MvPolynomial.eval x
        (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m)) := by
          rw [← MvPolynomial.as_sum p]
    _ = ∑ m ∈ p.support, MvPolynomial.eval x
        (MvPolynomial.monomial m (p.coeff m)) := MvPolynomial.eval_sum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [MvPolynomial.eval_monomial, m.prod_fintype]
      simp

/-- The `regDirichletMonomialTransform` extended linearly to multivariate polynomials. The
finitely supported indices in `p.support` are coerced to ordinary functions `ι → ℕ`. -/
def regDirichletMvPolynomialTransform (p : MvPolynomial ι ℂ) (b : ι → ℂ) : ℂ :=
  ∑ m ∈ p.support, p.coeff m * regDirichletMonomialTransform m b

/-- On its domain of definition the `regDirichletIntegral` of a multivariate polynomial equals
its regularized Dirichlet polynomial transform. -/
theorem regDirichletIntegral_mvPolynomial (b : ι → ℂ) (hb : b ∈ mvBetaConvergent)
    (p : MvPolynomial ι ℂ) :
    regDirichletIntegral b (fun u : ι → ℝ ↦ p.eval fun i ↦ (u i : ℂ)) =
      regDirichletMvPolynomialTransform p b := by
  unfold regDirichletIntegral regDirichletMvPolynomialTransform
  simp_rw [eval_MvPolynomial_eq_sum_monomials p, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    have hfun : (fun u : ι → ℝ ↦ regDirichletDensity b u *
        (p.coeff m * ∏ i, (u i : ℂ) ^ m i)) =
        fun u ↦ p.coeff m * (regDirichletDensity b u * ∏ i, (u i : ℂ) ^ m i) := by
      funext u
      ring
    rw [hfun]
    rw [integral_const_mul]
    change p.coeff m * regDirichletIntegral b
      (fun u : ι → ℝ ↦ ∏ i, (u i : ℂ) ^ m i) = _
    rw [regDirichletIntegral_monomial hb (m : ι → ℕ)]
  · intro m hm
    exact integrableOn_regDirichletDensity_mul b hb
      (by fun_prop)

/-- The regularized Dirichlet monomial transform is entire in all Dirichlet parameters. -/
theorem differentiable_regDirichletMonomialTransform (m : ι → ℕ) :
    Differentiable ℂ (regDirichletMonomialTransform m) := by
  unfold regDirichletMonomialTransform mvPochhammer
  have hnumerator : Differentiable ℂ fun b : ι → ℂ ↦
      ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
    fun_prop
  have hsum : Differentiable ℂ fun b : ι → ℂ ↦ ∑ i, (b i + m i : ℂ) := by
    fun_prop
  exact hnumerator.mul (Complex.differentiable_one_div_Gamma.comp hsum)

set_option backward.isDefEq.respectTransparency false in
/-- The regularized Dirichlet polynomial transform is entire in all Dirichlet parameters. -/
theorem differentiable_regDirichletMvPolynomialTransform (p : MvPolynomial ι ℂ) :
    Differentiable ℂ (regDirichletMvPolynomialTransform p) := by
  classical
  have heq : regDirichletMvPolynomialTransform p =
      ∑ m ∈ p.support, fun b : ι → ℂ ↦ p.coeff m *
        regDirichletMonomialTransform m b := by
    funext b
    simp only [regDirichletMvPolynomialTransform, Finset.sum_apply]
  rw [heq]
  exact Differentiable.sum fun m _ ↦
    (differentiable_const _).mul
      (differentiable_regDirichletMonomialTransform (m : ι → ℕ))

/-! ## Finite-order analytic continuation -/

/-- The region of Dirichlet parameters satisfying `-N < re (b i)` in every coordinate. -/
def dirichletConvergenceRegion (N : ℕ) : Set (ι → ℂ) :=
  {b | ∀ i, -(N : ℝ) < (b i).re}

/-- Dirichlet convergence regions are open. -/
theorem isOpen_dirichletConvergenceRegion (N : ℕ) :
    IsOpen (dirichletConvergenceRegion (ι := ι) N) := by
  rw [show dirichletConvergenceRegion (ι := ι) N =
      ⋂ i, {b : ι → ℂ | -(N : ℝ) < (b i).re} by
    ext b
    simp [dirichletConvergenceRegion]]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_lt (continuous_const : Continuous fun _ : ι → ℂ ↦ -(N : ℝ))
      (Complex.continuous_re.comp (continuous_apply i : Continuous fun b : ι → ℂ ↦ b i))

omit [Fintype ι] in
/-- The order-zero convergence region is the ordinary domain of absolute convergence. -/
@[simp] theorem dirichletConvergenceRegion_zero :
    dirichletConvergenceRegion (ι := ι) 0 = mvBetaConvergent := by
  ext b
  simp [dirichletConvergenceRegion, mvBetaConvergent]

omit [Fintype ι] in
/-- Increasing the available regularity enlarges the corresponding convergence region. -/
theorem dirichletConvergenceRegion_mono {N M : ℕ} (hNM : N ≤ M) :
    dirichletConvergenceRegion (ι := ι) N ⊆ dirichletConvergenceRegion M := by
  intro b hb i
  exact (neg_le_neg (Nat.cast_le.mpr hNM)).trans_lt (hb i)

omit [Fintype ι] in
/-- The ordinary convergence region is contained in every finite-order continuation region. -/
theorem mvBetaConvergent_subset_dirichletConvergenceRegion (N : ℕ) :
    mvBetaConvergent ⊆ dirichletConvergenceRegion (ι := ι) N := by
  rw [← dirichletConvergenceRegion_zero (ι := ι)]
  exact dirichletConvergenceRegion_mono (Nat.zero_le N)

/-- A function has `N` continuous derivatives near the closed standard simplex if it has that
regularity on some open neighborhood of the simplex in the ambient coordinate space. -/
def ContDiffNearStdSimplex (N : ℕ) (f : (ι → ℝ) → ℂ) : Prop :=
  ∃ U : Set (ι → ℝ), IsOpen U ∧ stdSimplex ℝ ι ⊆ U ∧ ContDiffOn ℝ N f U

/-- Having more derivatives near the simplex implies having any smaller number of derivatives
there. -/
theorem ContDiffNearStdSimplex.of_le {N M : ℕ} (hNM : N ≤ M)
    {f : (ι → ℝ) → ℂ} (hf : ContDiffNearStdSimplex M f) :
    ContDiffNearStdSimplex N f := by
  obtain ⟨U, hU, hsub, hf⟩ := hf
  exact ⟨U, hU, hsub, hf.of_le (by exact_mod_cast hNM)⟩

/-- Finite differentiability on a neighborhood implies continuity on the closed simplex. -/
theorem ContDiffNearStdSimplex.continuousOn {N : ℕ} {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex N f) : ContinuousOn f (stdSimplex ℝ ι) := by
  obtain ⟨U, hU, hsub, hf⟩ := hf
  exact hf.continuousOn.mono hsub

/-! ### Tangential derivatives -/

/-- The tangent vector to the simplex that increases coordinate `j` and decreases coordinate
`k` at the same rate. -/
def stdSimplexTangentVector (j k : ι) : ι → ℝ :=
  Pi.single j 1 - Pi.single k 1

/-- A simplex tangent vector has coordinate sum zero. -/
@[simp] theorem sum_stdSimplexTangentVector (j k : ι) :
    ∑ i, stdSimplexTangentVector j k i = 0 := by
  simp [stdSimplexTangentVector, Finset.sum_sub_distrib]

omit [Fintype ι] in
/-- Reversing a simplex tangent direction negates it. -/
theorem stdSimplexTangentVector_comm (j k : ι) :
    stdSimplexTangentVector k j = -stdSimplexTangentVector j k := by
  simp [stdSimplexTangentVector, sub_eq_add_neg]

omit [Fintype ι] in
/-- Transferring mass from a coordinate to itself gives the zero tangent vector. -/
@[simp] theorem stdSimplexTangentVector_self (j : ι) :
    stdSimplexTangentVector j j = 0 := by
  simp [stdSimplexTangentVector]

/-- The ambient directional derivative in the tangent direction that transfers mass from
coordinate `k` to coordinate `j`. Unlike a single coordinate derivative, this derivative is
intrinsic to the affine hyperplane containing the simplex. -/
def stdSimplexTangentDeriv (j k : ι) (f : (ι → ℝ) → ℂ) (u : ι → ℝ) : ℂ :=
  fderiv ℝ f u (stdSimplexTangentVector j k)

/-- Taking one tangential derivative consumes one order of differentiability near the
simplex. This is the differential operator used in the boundary integration-by-parts
recursion. -/
theorem ContDiffNearStdSimplex.tangentDeriv {N : ℕ} {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex (N + 1) f) (j k : ι) :
    ContDiffNearStdSimplex N (stdSimplexTangentDeriv j k f) := by
  obtain ⟨U, hU, hsub, hf⟩ := hf
  refine ⟨U, hU, hsub, ?_⟩
  unfold stdSimplexTangentDeriv
  apply ContDiffOn.clm_apply (hf.fderiv_of_isOpen hU ?_) contDiffOn_const
  norm_num

/-! ### Boundary faces -/

/-- Restriction of a function to the face where coordinate `i` is zero. The remaining
coordinates are indexed by `{j // j ≠ i}` and already sum to one on their standard simplex. -/
def stdSimplexFaceRestriction (i : ι) (f : (ι → ℝ) → ℂ) :
    ({j : ι // j ≠ i} → ℝ) → ℂ :=
  f ∘ stdSimplexCoordMap i

/-- The coordinate map sends the smaller standard simplex onto the face where coordinate `i`
is zero. -/
theorem stdSimplexCoordMap_mem_face (i : ι)
    {v : {j : ι // j ≠ i} → ℝ} (hv : v ∈ stdSimplex ℝ {j : ι // j ≠ i}) :
    stdSimplexCoordMap i v ∈ stdSimplex ℝ ι := by
  rw [stdSimplexCoordMap_mem_stdSimplex_iff]
  exact ⟨hv.1, hv.2.le⟩

/-- On the smaller standard simplex, the inserted coordinate of the face map is zero. -/
@[simp] theorem stdSimplexCoordMap_face_apply_self (i : ι)
    {v : {j : ι // j ≠ i} → ℝ} (hv : v ∈ stdSimplex ℝ {j : ι // j ≠ i}) :
    stdSimplexCoordMap i v i = 0 := by
  rw [stdSimplexCoordMap_apply_self, hv.2]
  simp

/-- Restricting to a boundary face preserves finite differentiability near the corresponding
lower-dimensional standard simplex. -/
theorem ContDiffNearStdSimplex.faceRestriction {N : ℕ} {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex N f) (i : ι) :
    ContDiffNearStdSimplex N (stdSimplexFaceRestriction i f) := by
  obtain ⟨U, hU, hsub, hf⟩ := hf
  let V : Set ({j : ι // j ≠ i} → ℝ) := stdSimplexCoordMap i ⁻¹' U
  have hcoord : ContDiff ℝ N (stdSimplexCoordMap (R := ℝ) i) := by
    rw [contDiff_pi]
    intro j
    by_cases hji : j = i
    · subst j
      simp_rw [stdSimplexCoordMap_apply_self]
      fun_prop
    · simp_rw [stdSimplexCoordMap_apply_of_ne i j hji]
      fun_prop
  refine ⟨V, hU.preimage (continuous_stdSimplexCoordMap i), ?_, ?_⟩
  · intro v hv
    exact hsub (stdSimplexCoordMap_mem_face i hv)
  · exact hf.comp hcoord.contDiffOn fun _ hv ↦ hv

/-- At order zero, the native regularized Dirichlet integral itself supplies the analytic
function on the ordinary convergence region. -/
theorem exists_regDirichletContinuation_zero {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex 0 f) :
    ∃ F : (ι → ℂ) → ℂ,
      AnalyticOn ℂ F (dirichletConvergenceRegion 0) ∧
        Set.EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  refine ⟨fun b ↦ regDirichletIntegral b f, ?_, fun _ _ ↦ rfl⟩
  simpa using regDirichletIntegral_analyticOn hf.continuousOn

/-- If `f` has `N` continuous derivatives on a neighborhood of the closed standard simplex,
then its regularized Dirichlet integral has an analytic continuation to the region
`-N < re (b i)` for every coordinate `i`. -/
theorem exists_regDirichletContinuation_of_contDiffNear {N : ℕ}
    {f : (ι → ℝ) → ℂ} (hf : ContDiffNearStdSimplex N f) :
    ∃ F : (ι → ℂ) → ℂ,
      AnalyticOn ℂ F (dirichletConvergenceRegion N) ∧
        Set.EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  sorry

end DirichletTransform

end DirichletTransform
