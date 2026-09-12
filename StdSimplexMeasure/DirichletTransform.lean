/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import StdSimplexMeasure.ComplexDirichlet
public import StdSimplexMeasure.IncompleteMellin
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Analytic.Uniqueness


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

open Complex MeasureTheory ProbabilityTheory MeasureTheory.Measure Set
open scoped Classical Topology

@[expose] public noncomputable section DirichletTransform

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- A file-local shorthand for the product of Pochhammer polynomials associated to a
multi-index. Since `ι` is finite, monomial multi-indices are represented by ordinary functions
`ι → ℕ`; the finitely supported indices used by `MvPolynomial` coerce to this type. -/
def mvPochhammer (b : ι → ℂ) (m : ι → ℕ) : ℂ :=
    ∏ i, (ascPochhammer ℂ (m i)).eval (b i)

/-- The regularized Dirichlet transform of the monomial with multi-index `m`.
This is an entire function of `b`. -/
def regDirichletMonomialTransform (m : ι → ℕ) (b : ι → ℂ) : ℂ :=
  mvPochhammer b m * (Gamma (∑ i, (b i + m i : ℂ)))⁻¹

/-- The explicit Pochhammer--Gamma formula for the regularized transform of a monomial.
This theorem exposes the useful formula while keeping the shorthand `mvPochhammer` local to
this file. -/
theorem regDirichletMonomialTransform_eq (m : ι → ℕ) (b : ι → ℂ) :
    regDirichletMonomialTransform m b =
      (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) *
        (Gamma (∑ i, (b i + m i : ℂ)))⁻¹ := by
  rfl

/-- The regularized transform of the constant monomial is the reciprocal Gamma factor. -/
@[simp] theorem regDirichletMonomialTransform_zero (b : ι → ℂ) :
    regDirichletMonomialTransform (fun _ ↦ 0) b = (Gamma (∑ i, b i))⁻¹ := by
  rw [regDirichletMonomialTransform_eq]
  simp

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

/-- The regularized Dirichlet monomial transform is analytic in all Dirichlet parameters. -/
theorem analyticOnNhd_regDirichletMonomialTransform (m : ι → ℕ) :
    AnalyticOnNhd ℂ (regDirichletMonomialTransform m) Set.univ := by
  intro b _
  unfold regDirichletMonomialTransform mvPochhammer
  have hp : AnalyticAt ℂ (fun b : ι → ℂ ↦
      ∏ i, (ascPochhammer ℂ (m i)).eval (b i)) b := by
    apply Finset.analyticAt_fun_prod
    intro i _
    exact ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (ascPochhammer ℂ (m i)))
      (b i) (Set.mem_univ _)).comp_of_eq
        ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b) rfl
  have hs : AnalyticAt ℂ (fun b : ι → ℂ ↦ ∑ i, (b i + m i : ℂ)) b := by
    apply Finset.analyticAt_fun_sum
    intro i _
    exact ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b).add analyticAt_const
  have hGammaInv : AnalyticAt ℂ (fun z : ℂ ↦ (Gamma z)⁻¹)
      (∑ i, (b i + m i : ℂ)) :=
    (analyticOnNhd_univ_iff_differentiable.mpr
      Complex.differentiable_one_div_Gamma) _ (Set.mem_univ _)
  exact hp.mul (hGammaInv.comp_of_eq hs rfl)

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

set_option backward.isDefEq.respectTransparency false in
/-- The regularized Dirichlet transform of a multivariate polynomial is analytic in all
Dirichlet parameters. -/
theorem analyticOnNhd_regDirichletMvPolynomialTransform (p : MvPolynomial ι ℂ) :
    AnalyticOnNhd ℂ (regDirichletMvPolynomialTransform p) Set.univ := by
  intro b _
  unfold regDirichletMvPolynomialTransform
  apply Finset.analyticAt_fun_sum
  intro m _
  exact analyticAt_const.mul
    (analyticOnNhd_regDirichletMonomialTransform (m : ι → ℕ) b (Set.mem_univ b))

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

/-! ### Slice parametrization -/

/-- The affine line from the face `u i = 0` to the vertex `e i`, parametrized so that the
omitted coordinate equals `t`. -/
def stdSimplexSlice (i : ι) (t : ℝ) (f : (ι → ℝ) → ℂ) :
    ({j : ι // j ≠ i} → ℝ) → ℂ :=
  fun v => f (stdSimplexCoordMap i (fun j => (1 - t) * v j))

theorem stdSimplexSlice_zero (i : ι) (f : (ι → ℝ) → ℂ) :
    stdSimplexSlice i 0 f = stdSimplexFaceRestriction i f := by
  funext v
  simp [stdSimplexSlice, stdSimplexFaceRestriction]

/-- On the standard simplex of the complementary coordinates, the scaled chart is the line
from the face point to the vertex `Pi.single i 1`. -/
theorem stdSimplexCoordMap_scale_eq_line (i : ι) (t : ℝ)
    {v : {j : ι // j ≠ i} → ℝ} (hv : ∑ j, v j = 1) :
    stdSimplexCoordMap i (fun j => (1 - t) * v j) =
      (t : ℝ) • Pi.single i (1 : ℝ) + (1 - t) • stdSimplexCoordMap i v := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [stdSimplexCoordMap_apply_self, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      Pi.single_eq_same, stdSimplexCoordMap_apply_self]
    rw [← Finset.mul_sum, hv, mul_one]
    simp [hv]
  · rw [stdSimplexCoordMap_apply_of_ne i j hji, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      Pi.single_eq_of_ne hji, stdSimplexCoordMap_apply_of_ne i j hji]
    simp

theorem hasDerivAt_stdSimplexCoordMap_scale (i : ι) (t : ℝ)
    {v : {j : ι // j ≠ i} → ℝ} (hv : ∑ j, v j = 1) :
    HasDerivAt (fun s : ℝ => stdSimplexCoordMap i (fun j => (1 - s) * v j))
      (Pi.single i (1 : ℝ) - stdSimplexCoordMap i v) t := by
  have heq :
      (fun s : ℝ => stdSimplexCoordMap i (fun j => (1 - s) * v j)) =
        fun s => (s : ℝ) • Pi.single i (1 : ℝ) + (1 - s) • stdSimplexCoordMap i v :=
    funext fun s => stdSimplexCoordMap_scale_eq_line i s hv
  rw [heq]
  have hid : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
  have h1 : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1) t := by
    simpa using hid.const_sub (1 : ℝ)
  have hderiv :
      (1 : ℝ) • Pi.single i (1 : ℝ) + (-1 : ℝ) • stdSimplexCoordMap i v =
        Pi.single i (1 : ℝ) - stdSimplexCoordMap i v := by
    simp [one_smul, neg_one_smul, sub_eq_add_neg]
  rw [← hderiv]
  exact (hid.smul_const _).add (h1.smul_const _)

/-- Finite differentiability near the simplex is inherited by every slice. -/
theorem ContDiffNearStdSimplex.slice {N : ℕ} {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex N f) (i : ι)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffNearStdSimplex N (stdSimplexSlice i t f) := by
  obtain ⟨U, hU, hsub, hfU⟩ := hf
  let V : Set ({j : ι // j ≠ i} → ℝ) :=
    (fun v => stdSimplexCoordMap i (fun j => (1 - t) * v j)) ⁻¹' U
  have hmap : ContDiff ℝ N
      (fun v : {j : ι // j ≠ i} → ℝ =>
        stdSimplexCoordMap i (fun j => (1 - t) * v j)) := by
    rw [contDiff_pi]
    intro j
    by_cases hji : j = i
    · subst j
      simp_rw [stdSimplexCoordMap_apply_self]
      fun_prop
    · simp_rw [stdSimplexCoordMap_apply_of_ne i j hji]
      fun_prop
  refine ⟨V, hU.preimage (hmap.continuous), ?_, ?_⟩
  · intro v hv
    have : stdSimplexCoordMap i (fun j => (1 - t) * v j) ∈ stdSimplex ℝ ι := by
      rw [stdSimplexCoordMap_mem_stdSimplex_iff]
      refine ⟨fun j => mul_nonneg (sub_nonneg.mpr ht.2) (hv.1 j), ?_⟩
      rw [← Finset.mul_sum, hv.2, mul_one]
      exact sub_le_self _ ht.1
    exact hsub this
  · exact hfU.comp hmap.contDiffOn fun _ hv ↦ hv

/-- On a singleton index type the regularized Dirichlet integral is `f 1 / Gamma b`, hence
entire in the Dirichlet parameter. -/
theorem exists_regDirichletContinuation_of_unique [Unique ι]
    {f : (ι → ℝ) → ℂ} (_hf : ContinuousOn f (stdSimplex ℝ ι)) :
    ∃ F : (ι → ℂ) → ℂ,
      AnalyticOn ℂ F Set.univ ∧
        Set.EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  let ones : ι → ℝ := fun _ => 1
  refine ⟨fun b => f ones * (Gamma (b default))⁻¹, ?_, ?_⟩
  · intro b _
    have hproj : AnalyticAt ℂ (fun c : ι → ℂ => c default) b :=
      (ContinuousLinearMap.proj (default : ι) : (ι → ℂ) →L[ℂ] ℂ).analyticAt b
    have hG : AnalyticAt ℂ (fun z : ℂ => (Gamma z)⁻¹) (b default) :=
      differentiable_one_div_Gamma.analyticAt _
    exact (analyticAt_const.mul (hG.comp_of_eq hproj rfl)).analyticWithinAt
  · intro b hb
    have hdirac : Measure.stdSimplexMeasure (ι := ι) = Measure.dirac ones :=
      Measure.stdSimplexMeasure_unique
    have hones : ones ∈ stdSimplex ℝ ι := by
      simp [ones, stdSimplex]
    change f ones * (Gamma (b default))⁻¹ =
      ∫ u in stdSimplex ℝ ι, regDirichletDensity b u * f u ∂Measure.stdSimplexMeasure
    rw [hdirac]
    have hinter : ones ∈ stdSimplexInterior :=
      ⟨hones, fun _ => by simp [ones]⟩
    rw [MeasureTheory.setIntegral_dirac]
    simp [regDirichletDensity, hinter, ones, Unique.eq_default, mul_comm, hones]

/-- The empty-index integral is identically zero, hence entire. -/
theorem exists_regDirichletContinuation_of_isEmpty [IsEmpty ι]
    (f : (ι → ℝ) → ℂ) :
    ∃ F : (ι → ℂ) → ℂ,
      AnalyticOn ℂ F Set.univ ∧
        Set.EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  refine ⟨fun _ => 0, analyticOn_const, ?_⟩
  intro b _
  simp [regDirichletIntegral, MeasureTheory.Measure.stdSimplexMeasure_empty]

/-- At order zero, the native regularized Dirichlet integral itself supplies the analytic
function on the ordinary convergence region. -/
theorem exists_regDirichletContinuation_zero {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex 0 f) :
    ∃ F : (ι → ℂ) → ℂ,
      AnalyticOn ℂ F (dirichletConvergenceRegion 0) ∧
        Set.EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  refine ⟨fun b ↦ regDirichletIntegral b f, ?_, fun _ _ ↦ rfl⟩
  simpa using regDirichletIntegral_analyticOn hf.continuousOn

omit [Fintype ι] in
/-- Dirichlet continuation regions are convex, hence preconnected. -/
theorem isPreconnected_dirichletConvergenceRegion (N : ℕ) :
    IsPreconnected (dirichletConvergenceRegion (ι := ι) N) := by
  have hconv : Convex ℝ (dirichletConvergenceRegion (ι := ι) N) := by
    intro x hx y hy a b ha hb hab i
    have hx' := hx i
    have hy' := hy i
    have hre :
        ((a • x + b • y) i).re = a * (x i).re + b * (y i).re := by
      simp [Pi.add_apply, Pi.smul_apply, add_re, real_smul, mul_re, ofReal_re]
    rw [hre]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have : b = 1 := by linarith
      simpa [this]
    · have hsum : a * (-(N : ℝ)) + b * (-(N : ℝ)) = -(N : ℝ) := by
        rw [← add_mul, hab, one_mul]
      have hlt :
          a * (-(N : ℝ)) + b * (-(N : ℝ)) < a * (x i).re + b * (y i).re :=
        add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hx' ha')
          (mul_le_mul_of_nonneg_left (le_of_lt hy') hb)
      rw [hsum] at hlt
      exact hlt
  exact hconv.isPreconnected

/-- Two analytic continuations to a Dirichlet convergence region that agree on the ordinary
convergence region agree everywhere on the continuation region. -/
theorem eqOn_dirichletContinuation {N : ℕ} {F G : (ι → ℂ) → ℂ}
    (hF : AnalyticOn ℂ F (dirichletConvergenceRegion N))
    (hG : AnalyticOn ℂ G (dirichletConvergenceRegion N))
    (hEq : EqOn F G mvBetaConvergent) :
    EqOn F G (dirichletConvergenceRegion N) := by
  have hopen := isOpen_dirichletConvergenceRegion (ι := ι) N
  have hF' := (hopen.analyticOn_iff_analyticOnNhd).1 hF
  have hG' := (hopen.analyticOn_iff_analyticOnNhd).1 hG
  have hz0 : (fun _ : ι => (1 : ℂ)) ∈ dirichletConvergenceRegion (ι := ι) N := by
    intro i
    change -(N : ℝ) < (1 : ℂ).re
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    simp [one_re]
    linarith
  have hz0β : (fun _ : ι => (1 : ℂ)) ∈ mvBetaConvergent (ι := ι) := by
    intro _
    simp
  have hnhds : mvBetaConvergent (ι := ι) ∈ 𝓝 (fun _ : ι => (1 : ℂ)) :=
    isOpen_mvBetaConvergent.mem_nhds hz0β
  have hev : F =ᶠ[𝓝 (fun _ : ι => (1 : ℂ))] G :=
    (hEq.eventuallyEq_of_mem hnhds)
  exact hF'.eqOn_of_preconnected_of_eventuallyEq hG'
    (isPreconnected_dirichletConvergenceRegion N) hz0 hev

/-- Jacobian identity for the complementary-coordinate exponent in a simplex slice. -/
theorem slice_jacobian_exponent (i : ι) [Nontrivial ι] (b : ι → ℂ) :
    ((Fintype.card ι - 2 : ℕ) : ℂ) + ∑ q : {j : ι // j ≠ i}, (b q - 1) =
      ∑ q : {j : ι // j ≠ i}, b q - 1 := by
  have hcard_rest : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hcard_two : 2 ≤ Fintype.card ι := Fintype.one_lt_card
  have hcast_rest : (Fintype.card {j : ι // j ≠ i} : ℂ) = (Fintype.card ι : ℂ) - 1 := by
    rw [hcard_rest, Nat.cast_sub (by omega)]
    norm_num
  have hcast_two : ((Fintype.card ι - 2 : ℕ) : ℂ) = (Fintype.card ι : ℂ) - 2 := by
    rw [Nat.cast_sub hcard_two]
    norm_num
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hcast_rest, hcast_two]
  ring

/-- Affine slices of a continuous simplex function remain continuous on the opposite face. -/
theorem continuousOn_stdSimplexSlice (i : ι) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {f : (ι → ℝ) → ℂ} (hf : ContinuousOn f (stdSimplex ℝ ι)) :
    ContinuousOn (stdSimplexSlice i t f) (stdSimplex ℝ {j : ι // j ≠ i}) := by
  have hmap : Continuous
      (fun v : {j : ι // j ≠ i} → ℝ =>
        stdSimplexCoordMap i (fun q => (1 - t) * v q)) := by
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      simp_rw [stdSimplexCoordMap_apply_self]
      fun_prop
    · simp_rw [stdSimplexCoordMap_apply_of_ne i j hji]
      fun_prop
  refine hf.comp hmap.continuousOn fun v hv => ?_
  rw [stdSimplexCoordMap_mem_stdSimplex_iff]
  refine ⟨fun j => mul_nonneg (sub_nonneg.mpr ht.2) (hv.1 j), ?_⟩
  rw [← Finset.mul_sum, hv.2, mul_one]
  exact sub_le_self _ ht.1

/-- Native slice formula: a regularized Dirichlet integral is an incomplete Mellin transform
in one coordinate of a complementary regularized Dirichlet integral on the opposite face. -/
theorem regDirichletIntegral_split_at [Nontrivial ι] (i : ι)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {f : (ι → ℝ) → ℂ} (hf : ContinuousOn f (stdSimplex ℝ ι)) :
    regDirichletIntegral b f =
      regIncompleteMellin (b i) 1 (fun t =>
        (1 - (t : ℂ)) ^ (∑ q : {j : ι // j ≠ i}, b q - 1) *
          regDirichletIntegral (fun q : {j : ι // j ≠ i} => b q)
            (stdSimplexSlice i t f)) := by
  classical
  let b' : {j : ι // j ≠ i} → ℂ := fun q ↦ b q
  let c : ℂ := ∑ q : {j : ι // j ≠ i}, b q
  have hb' : b' ∈ mvBetaConvergent := fun q ↦ hb q
  have hint : IntegrableOn
      (fun u : ι → ℝ ↦ (∏ j, (u j : ℂ) ^ (b j - 1)) * f u)
      (stdSimplex ℝ ι) stdSimplexMeasure :=
    (Complex.integrableOn_mvBetaMonomial b hb).mul_continuousOn hf
      (isCompact_stdSimplex ℝ ι)
  rw [regDirichletIntegral_eq_prod_invGamma_mul,
    integral_stdSimplex_split_at i _ hint]
  have hinner : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      (∫ v in stdSimplex ℝ {j : ι // j ≠ i},
        ((∏ k, ((stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k : ℝ) : ℂ) ^
          (b k - 1)) * f (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q)))
          ∂stdSimplexMeasure) =
        ((t : ℂ) ^ (b i - 1) *
          (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
          ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
            (∏ q, (v q : ℂ) ^ (b q - 1)) * stdSimplexSlice i t f v
              ∂stdSimplexMeasure := by
    intro t ht
    calc
      _ = ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
          ((t : ℂ) ^ (b i - 1) *
            (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
              ((∏ q, (v q : ℂ) ^ (b q - 1)) * stdSimplexSlice i t f v)
            ∂stdSimplexMeasure := by
          apply setIntegral_congr_fun (isClosed_stdSimplex ℝ _).measurableSet
          intro v hv
          change
            (∏ k, ((stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k : ℝ) : ℂ) ^
                (b k - 1)) * f (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q)) = _
          rw [prod_cpow_stdSimplexCoordMap_scale i b ht hv]
          simp only [stdSimplexSlice]
          ring
      _ = _ := by rw [integral_const_mul]
  have houter : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      ((1 - t) ^ (Fintype.card ι - 2)) •
          (∫ v in stdSimplex ℝ {j : ι // j ≠ i},
            ((∏ k, ((stdSimplexCoordMap i
              (fun q ↦ (1 - t) * v q) k : ℝ) : ℂ) ^ (b k - 1)) *
                f (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q)))
              ∂stdSimplexMeasure) =
        (t : ℂ) ^ (b i - 1) * (1 - t : ℂ) ^ (c - 1) *
          ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
            (∏ q, (v q : ℂ) ^ (b q - 1)) * stdSimplexSlice i t f v
              ∂stdSimplexMeasure := by
    filter_upwards [ae_restrict_of_ae
        (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)),
      ae_restrict_mem (μ := volume) measurableSet_Icc] with t heq htIcc
    have ht : t ∈ Set.Ico (0 : ℝ) 1 := heq.mpr htIcc
    rw [hinner t ht]
    have hbase : (1 - (t : ℂ)) ≠ 0 := by
      intro hz
      apply ht.2.ne
      exact_mod_cast (sub_eq_zero.mp hz).symm
    rw [Complex.real_smul, Complex.ofReal_pow, ← Complex.cpow_natCast]
    push_cast
    calc
      (1 - t : ℂ) ^ ((Fintype.card ι - 2 : ℕ) : ℂ) *
          (((t : ℂ) ^ (b i - 1) *
            (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
              ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
                (∏ q, (v q : ℂ) ^ (b q - 1)) * stdSimplexSlice i t f v
                  ∂stdSimplexMeasure) =
          (t : ℂ) ^ (b i - 1) *
            ((1 - t : ℂ) ^ ((Fintype.card ι - 2 : ℕ) : ℂ) *
              (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                ∫ v in stdSimplex ℝ {j : ι // j ≠ i},
                  (∏ q, (v q : ℂ) ^ (b q - 1)) * stdSimplexSlice i t f v
                    ∂stdSimplexMeasure := by ring
      _ = _ := by
        rw [← Complex.cpow_add _ _ hbase, slice_jacobian_exponent i b]
  rw [integral_congr_ae houter]
  unfold regIncompleteMellin
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  rw [mul_assoc]
  apply congrArg ((Gamma (b i))⁻¹ * ·)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [regDirichletIntegral_eq_prod_invGamma_mul]
  dsimp only [c, b']
  ring

/-- If `f` has `N` continuous derivatives on a neighborhood of the closed standard simplex,
then its regularized Dirichlet integral has an analytic continuation to the region
`-N < re (b i)` for every coordinate `i`. -/
theorem exists_regDirichletContinuation_of_contDiffNear {N : ℕ}
    {f : (ι → ℝ) → ℂ} (hf : ContDiffNearStdSimplex N f) :
    ∃ F : (ι → ℂ) → ℂ,
      AnalyticOn ℂ F (dirichletConvergenceRegion N) ∧
        Set.EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
      obtain ⟨F, hF, hEq⟩ := exists_regDirichletContinuation_of_isEmpty f
      exact ⟨F, hF.mono fun _ _ => trivial, hEq⟩
  | inr hι =>
      cases subsingleton_or_nontrivial ι with
      | inl hsub =>
          let : Unique ι :=
            { default := Classical.choice hι
              uniq := fun _ => Subsingleton.elim _ _ }
          obtain ⟨F, hF, hEq⟩ :=
            exists_regDirichletContinuation_of_unique hf.continuousOn
          exact ⟨F, hF.mono fun _ _ => trivial, hEq⟩
      | inr _ =>
          induction N with
          | zero => exact exists_regDirichletContinuation_zero hf
          | succ N ih =>
              -- Nontrivial index type, `N + 1` derivatives: slice at a coordinate,
              -- apply the incomplete Mellin continuation in that coordinate, and
              -- invoke the inductive hypothesis on faces.  See the helper stack
              -- in `IncompleteMellin.lean` and the slice identities above.
              sorry

/-- If a simplex function has every finite order of differentiability on a neighborhood of
the simplex, its compatible finite-order regularized continuations glue to an entire function
of all Dirichlet parameters. -/
theorem exists_entire_regDirichletContinuation_of_contDiffNear
    {f : (ι → ℝ) → ℂ} (hf : ∀ N, ContDiffNearStdSimplex N f) :
    ∃ F : (ι → ℂ) → ℂ,
      AnalyticOnNhd ℂ F Set.univ ∧
        Set.EqOn F (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  choose Φ hΦ using fun N ↦ exists_regDirichletContinuation_of_contDiffNear (hf N)
  have hexists (b : ι → ℂ) : ∃ N, b ∈ dirichletConvergenceRegion N := by
    choose n hn using fun i ↦ exists_nat_gt (-(b i).re)
    refine ⟨∑ i, n i, fun i ↦ ?_⟩
    have hni : (n i : ℝ) ≤ (∑ j, n j : ℕ) := by
      exact_mod_cast Finset.single_le_sum (fun j _ ↦ Nat.zero_le (n j))
        (Finset.mem_univ i)
    have hlt : -(n i : ℝ) < (b i).re := by linarith [hn i]
    linarith
  let order : (ι → ℂ) → ℕ := fun b ↦ Nat.find (hexists b)
  have horder (b : ι → ℂ) : b ∈ dirichletConvergenceRegion (order b) :=
    Nat.find_spec (hexists b)
  let F : (ι → ℂ) → ℂ := fun b ↦ Φ (order b) b
  refine ⟨F, ?_, ?_⟩
  · intro b _
    let N := order b
    have hbN : b ∈ dirichletConvergenceRegion N := horder b
    have hΦN : AnalyticAt ℂ (Φ N) b :=
      ((isOpen_dirichletConvergenceRegion N).analyticOn_iff_analyticOnNhd.mp
        (hΦ N).1) b hbN
    apply hΦN.congr
    filter_upwards [(isOpen_dirichletConvergenceRegion N).eventually_mem hbN] with x hxN
    let m := min N (order x)
    have hxm : x ∈ dirichletConvergenceRegion m := by
      change x ∈ dirichletConvergenceRegion (min N (order x))
      by_cases hle : N ≤ order x
      · rw [Nat.min_eq_left hle]
        exact hxN
      · rw [Nat.min_eq_right (Nat.le_of_not_ge hle)]
        exact horder x
    have hΦN_m : AnalyticOn ℂ (Φ N) (dirichletConvergenceRegion m) :=
      (hΦ N).1.mono (dirichletConvergenceRegion_mono (Nat.min_le_left _ _))
    have hΦx_m : AnalyticOn ℂ (Φ (order x)) (dirichletConvergenceRegion m) :=
      (hΦ (order x)).1.mono
        (dirichletConvergenceRegion_mono (Nat.min_le_right _ _))
    have heq : Set.EqOn (Φ N) (Φ (order x))
        (dirichletConvergenceRegion m) := by
      apply eqOn_dirichletContinuation hΦN_m hΦx_m
      intro c hc
      exact (hΦ N).2 hc |>.trans ((hΦ (order x)).2 hc).symm
    exact heq hxm
  · intro b hb
    exact (hΦ (order b)).2 hb

end DirichletTransform

end DirichletTransform
