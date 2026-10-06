/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Associated
public import Dirichlet.Transform.Laws
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import ToMathlib.Analysis.Calculus.IteratedDerivOpen

/-!
# Carlson averages with real nodes and finitely differentiable functions

Case (i) of Carlson's Theorems 5.3-2 and 5.4-1: `Ω` is an open interval, `f : Ω → ℂ` is only
`n` times continuously differentiable, the nodes are real and the parameters lie in the native
region `re bᵢ > 0`. The regularized average `F(b, z)/Γ(∑ b)` is `regCarlsonRealAverage b z f`.
Differentiation under the integral sign uses Mathlib's dominated-derivative theorem with a
uniform bound obtained by compactness of the simplex.

## Main results

* `Dirichlet.hasFDerivAt_regCarlsonRealAverage`: the Fréchet derivative in the nodes;
  `Dᵢ F(b, z) = bᵢ F'(b + eᵢ, z)` (`realPartialDeriv_regCarlsonRealAverage`).
* `Dirichlet.contDiffOn_regCarlsonRealAverage`: **5.3-2**, `F` is `Cⁿ` on `Ωᵏ` if `f` is `Cⁿ`
  on `Ω`.
* `Dirichlet.realIteratedPartialDeriv_regCarlsonRealAverage`: **(5.3-2)**, iterated partial
  derivatives under the integral sign.
* `Dirichlet.realDiagDeriv_iterate_regCarlsonRealAverage`: **(5.3-3)**, `(∑ Dᵢ)ᵏ F = F⁽ᵏ⁾`.
* `Dirichlet.realCarlsonCapDelta_iterate_regCarlsonRealAverage`: **(5.3-4)**, `Δᵏ F` is the
  average of `δᵏ f`.
* `Dirichlet.regCarlsonRealAverage_tangent`: the tangential contiguous relation for `C¹` kernels.
* `Dirichlet.realEulerPoissonOperator_regCarlsonRealAverage`: **5.4-1, case (i)**, the
  Euler–Poisson system for `f ∈ C²(Ω)`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§5.3–5.4.
-/

open Complex MeasureTheory Set Filter
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]

/-- The real affine form `u · z = ∑ᵢ uᵢ zᵢ`. -/
def realAffineForm (z u : ι → ℝ) : ℝ := ∑ i, u i * z i

/-- Carlson's regularized average `F(b, z)/Γ(∑ b)` of a function `f : ℝ → ℂ` at real nodes. -/
def regCarlsonRealAverage (b : ι → ℂ) (z : ι → ℝ) (f : ℝ → ℂ) : ℂ :=
  regDirichletIntegral b (fun u => f (realAffineForm z u))

/-- The real node domain `Ωᵏ`. -/
def realNodeDomain (Ω : Set ℝ) : Set (ι → ℝ) := Set.univ.pi fun _ => Ω

/-- The coordinate projection `z ↦ zᵢ` as a real-linear map into `ℂ`. -/
def realProj (i : ι) : (ι → ℝ) →L[ℝ] ℂ := ofRealCLM.comp (ContinuousLinearMap.proj i)

omit [Fintype ι] in
/-- Evaluation of the coordinate projection. -/
@[simp] theorem realProj_apply (i : ι) (v : ι → ℝ) : realProj i v = (v i : ℂ) := rfl

omit [Fintype ι] in
/-- Membership in the real node domain. -/
theorem mem_realNodeDomain {Ω : Set ℝ} {z : ι → ℝ} : z ∈ realNodeDomain Ω ↔ ∀ i, z i ∈ Ω := by
  simp [realNodeDomain]

/-- The real node domain of an open set is open. -/
theorem isOpen_realNodeDomain {Ω : Set ℝ} (hΩ : IsOpen Ω) :
    IsOpen (realNodeDomain Ω : Set (ι → ℝ)) :=
  isOpen_set_pi Set.finite_univ fun _ _ => hΩ

/-- The real affine form is jointly continuous. -/
theorem continuous_realAffineForm :
    Continuous fun p : (ι → ℝ) × (ι → ℝ) => realAffineForm p.1 p.2 := by
  unfold realAffineForm; fun_prop

/-- Simplex averages of nodes in a convex set stay in that set. -/
theorem realAffineForm_mem {Ω : Set ℝ} (hΩ : Convex ℝ Ω) {z : ι → ℝ} (hz : z ∈ realNodeDomain Ω)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) : realAffineForm z u ∈ Ω :=
  hΩ.sum_mem (fun i _ => hu.1 i) hu.2 fun i _ => mem_realNodeDomain.mp hz i

/-- A continuous function is uniformly bounded on the simplex averages of all node vectors near a
point of the node domain. -/
theorem exists_bound_near {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) {g : ℝ → ℂ}
    (hg : ContinuousOn g Ω) {z : ι → ℝ} (hz : z ∈ realNodeDomain Ω) :
    ∃ ε > 0, ∃ C, Metric.ball z ε ⊆ realNodeDomain Ω ∧ ∀ x ∈ Metric.ball z ε,
      ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, ‖g (realAffineForm x u)‖ ≤ C := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp (isOpen_realNodeDomain hΩo) z hz
  have hcb : Metric.closedBall z (ε / 2) ⊆ realNodeDomain Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hsub
  have hK : IsCompact (Metric.closedBall z (ε / 2) ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι) :=
    (isCompact_closedBall z _).prod (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
  have hcont : ContinuousOn (fun p : (ι → ℝ) × (ι → ℝ) => g (realAffineForm p.1 p.2))
      (Metric.closedBall z (ε / 2) ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι) :=
    hg.comp continuous_realAffineForm.continuousOn fun p hp =>
      realAffineForm_mem hΩc (hcb hp.1) hp.2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  exact ⟨ε / 2, by linarith, C, Metric.ball_subset_closedBall.trans hcb,
    fun x hx u hu => hC (x, u) ⟨Metric.ball_subset_closedBall hx, hu⟩⟩

/-- The restricted simplex measure used by `regDirichletIntegral`. -/
abbrev simplexMeasure : Measure (ι → ℝ) :=
  Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)

/-- Integrability of a continuous kernel against the regularized Dirichlet density. -/
theorem integrable_regDirichletDensity_mul {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    Integrable (fun u => regDirichletDensity b u * g u) (simplexMeasure (ι := ι)) :=
  integrableOn_regDirichletDensity_mul b hb hg

/-- Continuity of `u ↦ g(u · z)` on the simplex for nodes in the domain. -/
theorem continuousOn_comp_realAffineForm {Ω : Set ℝ} (hΩc : Convex ℝ Ω) {g : ℝ → ℂ}
    (hg : ContinuousOn g Ω) {z : ι → ℝ} (hz : z ∈ realNodeDomain Ω) :
    ContinuousOn (fun u => g (realAffineForm z u)) (Convexity.StdSimplex.coordinateSet ℝ ι) :=
  hg.comp (continuous_realAffineForm.comp (Continuous.prodMk_right z)).continuousOn
    fun _ hu => realAffineForm_mem hΩc hz hu

/-- **Carlson 5.3-2 for `n = 0`.** The real-node average of a continuous function is continuous
in the nodes. -/
theorem continuousOn_regCarlsonRealAverage {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f : ℝ → ℂ} (hf : ContinuousOn f Ω) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    ContinuousOn (fun z => regCarlsonRealAverage b z f) (realNodeDomain Ω) := by
  intro z hz
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨ε, hε, C, hball, hC⟩ := exists_bound_near hΩo hΩc hf hz
  have hnhds : Metric.ball z ε ∈ 𝓝 z := Metric.ball_mem_nhds z hε
  have hsimp : ∀ᵐ u ∂(simplexMeasure (ι := ι)), u ∈ Convexity.StdSimplex.coordinateSet ℝ ι :=
    self_mem_ae_restrict (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  refine continuousAt_of_dominated (bound := fun u => ‖regDirichletDensity b u‖ * C) ?_ ?_ ?_ ?_
  · filter_upwards [hnhds] with x hx
    exact (integrable_regDirichletDensity_mul hb
      (continuousOn_comp_realAffineForm hΩc hf (hball hx))).1
  · filter_upwards [hnhds] with x hx
    filter_upwards [hsimp] with u hu
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC x hx u hu) (norm_nonneg _)
  · exact (integrableOn_regDirichletDensity b hb).norm.mul_const C
  · filter_upwards [hsimp] with u hu
    have hfu : ContinuousAt f (realAffineForm z u) :=
      hf.continuousAt (hΩo.mem_nhds (realAffineForm_mem hΩc hz hu))
    have hl : Continuous fun x : ι → ℝ => realAffineForm x u := by
      unfold realAffineForm; fun_prop
    exact continuousAt_const.mul (hfu.comp (f := fun x => realAffineForm x u) hl.continuousAt)

/-- The real-linear map `x ↦ u · x`. -/
def realAffineCLM (u : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ := ∑ i, u i • ContinuousLinearMap.proj i

/-- Evaluation of `realAffineCLM`. -/
theorem realAffineCLM_apply (u x : ι → ℝ) : realAffineCLM u x = realAffineForm x u := by
  simp [realAffineCLM, realAffineForm]

/-- The node derivative `v ↦ ∑ᵢ uᵢ vᵢ` of the kernel `x ↦ f(u · x)`, without the factor `f'`. -/
def realKernelDeriv (u : ι → ℝ) : (ι → ℝ) →L[ℝ] ℂ := ∑ i, (u i : ℂ) • realProj i

/-- Evaluation of `realKernelDeriv`. -/
theorem realKernelDeriv_apply (u v : ι → ℝ) :
    realKernelDeriv u v = ∑ i, (u i : ℂ) * (v i : ℂ) := by
  simp [realKernelDeriv]

/-- `realKernelDeriv` is continuous in the simplex variable. -/
theorem continuous_realKernelDeriv : Continuous (realKernelDeriv (ι := ι)) := by
  unfold realKernelDeriv
  exact continuous_finsetSum _ fun i _ =>
    (continuous_ofReal.comp (continuous_apply i)).smul continuous_const

/-- On the simplex the kernel derivative is uniformly bounded. -/
theorem norm_realKernelDeriv_le {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    ‖realKernelDeriv u‖ ≤ ∑ i, ‖realProj (ι := ι) i‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul]
  have h : ‖(u i : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
    exact (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hu i).2
  exact mul_le_of_le_one_left (norm_nonneg _) h

/-- The derivative of the kernel `x ↦ f(u · x)` in the nodes. -/
theorem hasFDerivAt_comp_realAffineForm {f f' : ℝ → ℂ} {u x : ι → ℝ}
    (hf : HasDerivAt f (f' (realAffineForm x u)) (realAffineForm x u)) :
    HasFDerivAt (fun x => f (realAffineForm x u)) (f' (realAffineForm x u) • realKernelDeriv u)
      x := by
  have hL : HasFDerivAt (fun x => realAffineForm x u) (realAffineCLM u) x := by
    have h : (fun x => realAffineForm x u) = realAffineCLM u :=
      funext fun x => (realAffineCLM_apply u x).symm
    rw [h]; exact (realAffineCLM u).hasFDerivAt
  have h := hf.hasFDerivAt.comp x hL
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    realAffineCLM_apply, smul_apply, realKernelDeriv_apply, smul_eq_mul,
    Complex.real_smul, realAffineForm]
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Carlson 5.3-2, first order, real nodes.** If `f` has a continuous derivative `f'` on an
open interval `Ω`, the real-node average is Fréchet differentiable in the nodes, and
`∂ᵢ F(b, z) = bᵢ F'(b + eᵢ, z)` in the regularized normalization. -/
theorem hasFDerivAt_regCarlsonRealAverage {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f f' : ℝ → ℂ} (hf : ∀ x ∈ Ω, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' Ω)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) {z : ι → ℝ} (hz : z ∈ realNodeDomain Ω) :
    HasFDerivAt (fun x => regCarlsonRealAverage b x f)
      (∑ i, (b i * regCarlsonRealAverage (addDirichletUnit b i) z f') • realProj i) z := by
  obtain ⟨ε, hε, C, hball, hC⟩ := exists_bound_near hΩo hΩc hf' hz
  have hnhds : Metric.ball z ε ∈ 𝓝 z := Metric.ball_mem_nhds z hε
  have hsimp : ∀ᵐ u ∂(simplexMeasure (ι := ι)), u ∈ Convexity.StdSimplex.coordinateSet ℝ ι :=
    self_mem_ae_restrict (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  have hfc : ContinuousOn f Ω := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  set M : ℝ := ∑ i, ‖realProj (ι := ι) i‖
  set F' : (ι → ℝ) → (ι → ℝ) → (ι → ℝ) →L[ℝ] ℂ := fun x u =>
    (regDirichletDensity b u * f' (realAffineForm x u)) • realKernelDeriv u
  have hF'meas : AEStronglyMeasurable (F' z) (simplexMeasure (ι := ι)) :=
    (integrable_regDirichletDensity_mul hb (continuousOn_comp_realAffineForm hΩc hf' hz)).1.smul
      continuous_realKernelDeriv.aestronglyMeasurable
  have hbound : ∀ᵐ u ∂(simplexMeasure (ι := ι)), ∀ x ∈ Metric.ball z ε,
      ‖F' x u‖ ≤ ‖regDirichletDensity b u‖ * (C * M) := by
    filter_upwards [hsimp] with u hu x hx
    simp only [F', norm_smul, norm_mul]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hC x hx u hu) (norm_realKernelDeriv_le hu)
      (norm_nonneg _) ((norm_nonneg _).trans (hC x hx u hu))) (norm_nonneg _)
  have hbint : Integrable (fun u => ‖regDirichletDensity b u‖ * (C * M))
      (simplexMeasure (ι := ι)) :=
    (integrableOn_regDirichletDensity b hb).norm.mul_const _
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := simplexMeasure (ι := ι))
    (F := fun x u => regDirichletDensity b u * f (realAffineForm x u)) (F' := F') hnhds
    (by filter_upwards [hnhds] with x hx
        exact (integrable_regDirichletDensity_mul hb
          (continuousOn_comp_realAffineForm hΩc hfc (hball hx))).1)
    (integrable_regDirichletDensity_mul hb (continuousOn_comp_realAffineForm hΩc hfc hz))
    hF'meas hbound hbint
    (by filter_upwards [hsimp] with u hu x hx
        have hk := hasFDerivAt_comp_realAffineForm (u := u) (x := x)
          (hf _ (realAffineForm_mem hΩc (hball hx) hu))
        have := hk.const_mul (regDirichletDensity b u)
        simpa only [F', smul_smul] using this)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  have hint : Integrable (F' z) (simplexMeasure (ι := ι)) :=
    hbint.mono' hF'meas (by filter_upwards [hbound] with u hu using hu z (Metric.mem_ball_self hε))
  rw [ContinuousLinearMap.integral_apply hint]
  simp only [F', smul_apply, realKernelDeriv_apply, smul_eq_mul,
    FunLike.coe_sum, Finset.sum_apply, realProj_apply, regCarlsonRealAverage]
  have hi : ∀ i, Integrable (fun u => (v i : ℂ) * (regDirichletDensity b u *
      ((u i : ℂ) * f' (realAffineForm z u)))) (simplexMeasure (ι := ι)) := fun i =>
    (integrable_regDirichletDensity_mul hb (((continuous_ofReal.comp
      (continuous_apply i)).continuousOn).mul
        (continuousOn_comp_realAffineForm hΩc hf' hz))).const_mul _
  calc ∫ u, regDirichletDensity b u * f' (realAffineForm z u) * ∑ i, (u i : ℂ) * (v i : ℂ)
        ∂simplexMeasure
      = ∫ u, ∑ i, (v i : ℂ) * (regDirichletDensity b u * ((u i : ℂ) * f' (realAffineForm z u)))
        ∂simplexMeasure := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, (v i : ℂ) * regDirichletIntegral b (fun u => (u i : ℂ) * f' (realAffineForm z u)) := by
        rw [integral_finsetSum _ fun i _ => hi i]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← mul_regDirichletIntegral_addDirichletUnit hb i]
        ring

/-- The derivative of the real-node average, in the regularized normalization. -/
def realAverageDeriv (b : ι → ℂ) (f' : ℝ → ℂ) (z : ι → ℝ) : (ι → ℝ) →L[ℝ] ℂ :=
  ∑ i, (b i * regCarlsonRealAverage (addDirichletUnit b i) z f') • realProj i

/-- **Carlson 5.3-2, smoothness, real nodes.** If `f` is `n` times continuously differentiable on
an open interval `Ω`, the regularized average `F(b, z)/Γ(∑ b)` is `n` times continuously
differentiable on `Ωᵏ`. -/
theorem contDiffOn_regCarlsonRealAverage {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {n : ℕ} {f : ℝ → ℂ} (hf : ContDiffOn ℝ n f Ω) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    ContDiffOn ℝ n (fun z => regCarlsonRealAverage b z f) (realNodeDomain Ω) := by
  induction n generalizing f b with
  | zero =>
    exact contDiffOn_zero.mpr (continuousOn_regCarlsonRealAverage hΩo hΩc hf.continuousOn hb)
  | succ n ih =>
    have hd : ∀ x ∈ Ω, HasDerivAt f (deriv f x) x := fun x hx => by
      simpa using hf.hasDerivAt_iteratedDeriv_of_isOpen hΩo (k := 0) (by omega) hx
    have hf' : ContDiffOn ℝ n (deriv f) Ω := by
      simpa using hf.contDiffOn_iteratedDeriv_of_isOpen hΩo (k := 1) (by omega)
    have hF : ∀ z ∈ realNodeDomain Ω, HasFDerivAt (fun x => regCarlsonRealAverage b x f)
        (realAverageDeriv b (deriv f) z) z := fun z hz =>
      hasFDerivAt_regCarlsonRealAverage hΩo hΩc hd hf'.continuousOn hb hz
    have hD : ContDiffOn ℝ n (realAverageDeriv b (deriv f)) (realNodeDomain Ω) := by
      unfold realAverageDeriv
      exact ContDiffOn.sum fun i _ => (contDiffOn_const.mul
        (ih hf' (addDirichletUnit_mem_mvBetaConvergent hb i))).smul contDiffOn_const
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_realNodeDomain hΩo)]
    refine ⟨fun z hz => (hF z hz).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact hD.congr fun z hz => (hF z hz).fderiv

open scoped Classical in
/-- Carlson's partial derivative `Dᵢ` for functions of real nodes. -/
def realPartialDeriv (i : ι) (G : (ι → ℝ) → ℂ) (z : ι → ℝ) : ℂ :=
  deriv (fun w => G (Function.update z i w)) (z i)

/-- Iterated real partial derivatives, innermost index last. -/
def realIteratedPartialDeriv : List ι → ((ι → ℝ) → ℂ) → (ι → ℝ) → ℂ
  | [], G, z => G z
  | i :: is, G, z => realPartialDeriv i (fun w => realIteratedPartialDeriv is G w) z

open scoped Classical in
/-- A Fréchet derivative gives the partial derivatives. -/
theorem realPartialDeriv_eq_of_hasFDerivAt {G : (ι → ℝ) → ℂ} {D : (ι → ℝ) →L[ℝ] ℂ}
    {z : ι → ℝ} (hG : HasFDerivAt G D z) (i : ι) :
    realPartialDeriv i G z = D (Pi.single i 1) := by
  have hu := hasDerivAt_update z i (z i)
  have hG' : HasFDerivAt G D (Function.update z i (z i)) := by rwa [Function.update_eq_self]
  exact (hG'.comp_hasDerivAt (z i) hu).deriv

open scoped Classical in
/-- **Carlson 5.3-2, first order, real nodes**: `Dᵢ F(b, z) = bᵢ F'(b + eᵢ, z)`. -/
theorem realPartialDeriv_regCarlsonRealAverage {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f f' : ℝ → ℂ} (hf : ∀ x ∈ Ω, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' Ω)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) {z : ι → ℝ} (hz : z ∈ realNodeDomain Ω) (i : ι) :
    realPartialDeriv i (fun x => regCarlsonRealAverage b x f) z =
      b i * regCarlsonRealAverage (addDirichletUnit b i) z f' := by
  classical
  rw [realPartialDeriv_eq_of_hasFDerivAt (hasFDerivAt_regCarlsonRealAverage hΩo hΩc hf hf' hb hz)]
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, realProj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

open scoped Classical in
/-- Iterated partial derivatives as averages with shifted parameters. -/
theorem realIteratedPartialDeriv_eq_iteratedShift {Ω : Set ℝ} (hΩo : IsOpen Ω)
    (hΩc : Convex ℝ Ω) {n : ℕ} {f : ℝ → ℂ} (hf : ContDiffOn ℝ n f Ω) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (is : List ι) (his : is.length ≤ n) {z : ι → ℝ}
    (hz : z ∈ realNodeDomain Ω) :
    realIteratedPartialDeriv is (fun x => regCarlsonRealAverage b x f) z =
      iteratedDirichletShiftCoeff is b *
        regCarlsonRealAverage (iteratedAddDirichletUnit is b) z (iteratedDeriv is.length f) := by
  classical
  induction is generalizing z with
  | nil => simp [realIteratedPartialDeriv, iteratedDirichletShiftCoeff, iteratedAddDirichletUnit]
  | cons i is ih =>
    simp only [List.length_cons] at his
    rw [realIteratedPartialDeriv]
    have hev : (fun w => realIteratedPartialDeriv is (fun x => regCarlsonRealAverage b x f) w)
        =ᶠ[𝓝 z] fun w => iteratedDirichletShiftCoeff is b * regCarlsonRealAverage
          (iteratedAddDirichletUnit is b) w (iteratedDeriv is.length f) := by
      filter_upwards [(isOpen_realNodeDomain hΩo).mem_nhds hz] with w hw
      exact ih (by omega) hw
    have hk : is.length < n := by omega
    have hF := (hasFDerivAt_regCarlsonRealAverage hΩo hΩc
      (fun x hx => hf.hasDerivAt_iteratedDeriv_of_isOpen hΩo hk hx)
      (hf.contDiffOn_iteratedDeriv_of_isOpen hΩo (k := is.length + 1) (by omega)).continuousOn
      (iteratedAddDirichletUnit_mem hb is) hz).const_mul (iteratedDirichletShiftCoeff is b)
    rw [realPartialDeriv_eq_of_hasFDerivAt (hF.congr_of_eventuallyEq hev)]
    simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, realProj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp only [Pi.single_eq_same, ofReal_one, mul_one, iteratedDirichletShiftCoeff,
      iteratedAddDirichletUnit, List.length_cons]
    ring

/-- **Carlson 5.3-2, real nodes.** For `f ∈ Cⁿ(Ω)` and indices `i₁, …, i_m` with `m ≤ n`,
`D_{i₁} ⋯ D_{i_m} F(b, z) = ∫ u_{i₁} ⋯ u_{i_m} f⁽ᵐ⁾(u · z) dμ_b(u)`, in the regularized
normalization. -/
theorem realIteratedPartialDeriv_regCarlsonRealAverage {Ω : Set ℝ} (hΩo : IsOpen Ω)
    (hΩc : Convex ℝ Ω) {n : ℕ} {f : ℝ → ℂ} (hf : ContDiffOn ℝ n f Ω) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (is : List ι) (his : is.length ≤ n) {z : ι → ℝ}
    (hz : z ∈ realNodeDomain Ω) :
    realIteratedPartialDeriv is (fun x => regCarlsonRealAverage b x f) z =
      regDirichletIntegral b (fun u => (is.map fun i => (u i : ℂ)).prod *
        iteratedDeriv is.length f (realAffineForm z u)) := by
  rw [realIteratedPartialDeriv_eq_iteratedShift hΩo hΩc hf hb is his hz]
  exact iteratedDirichletShiftCoeff_mul_regDirichletIntegral is hb _

/-- Continuity of `u ↦ g(u · z)` combined with a continuous weight. -/
theorem continuousOn_coord_mul_comp {Ω : Set ℝ} (hΩc : Convex ℝ Ω) {g : ℝ → ℂ}
    (hg : ContinuousOn g Ω) {z : ι → ℝ} (hz : z ∈ realNodeDomain Ω) (i : ι) :
    ContinuousOn (fun u : ι → ℝ => (u i : ℂ) * g (realAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
  (continuous_ofReal.comp (continuous_apply i)).continuousOn.mul
    (continuousOn_comp_realAffineForm hΩc hg hz)

/-- Finite sums pass through the regularized Dirichlet integral of continuous kernels. -/
theorem regDirichletIntegral_sum {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) {α : Type*}
    {s : Finset α} {F : α → (ι → ℝ) → ℂ}
    (hF : ∀ a ∈ s, ContinuousOn (F a) (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regDirichletIntegral b (fun u => ∑ a ∈ s, F a u) = ∑ a ∈ s, regDirichletIntegral b (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [regDirichletIntegral]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [regDirichletIntegral_add b (hF a (Finset.mem_insert_self a s))
      (continuousOn_finsetSum _ fun c hc => hF c (Finset.mem_insert_of_mem hc)) hb,
      ih fun c hc => hF c (Finset.mem_insert_of_mem hc)]

/-- `u ↦ u · z` is continuous. -/
theorem continuous_realAffineForm_right {z : ι → ℝ} : Continuous fun u => realAffineForm z u :=
  continuous_realAffineForm.comp (Continuous.prodMk_right z)

/-- The diagonal derivative `D = ∑ᵢ Dᵢ` of a function of real nodes. -/
def realDiagDeriv (G : (ι → ℝ) → ℂ) (z : ι → ℝ) : ℂ := fderiv ℝ G z fun _ => 1

/-- **(5.3-3), first order, real nodes**: `∑ᵢ Dᵢ F(b, z) = F'(b, z)`. -/
theorem realDiagDeriv_regCarlsonRealAverage {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f f' : ℝ → ℂ} (hf : ∀ x ∈ Ω, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' Ω)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) {z : ι → ℝ} (hz : z ∈ realNodeDomain Ω) :
    realDiagDeriv (fun x => regCarlsonRealAverage b x f) z = regCarlsonRealAverage b z f' := by
  rw [realDiagDeriv, (hasFDerivAt_regCarlsonRealAverage hΩo hΩc hf hf' hb hz).fderiv,
    regCarlsonRealAverage, regDirichletIntegral_eq_sum_addDirichletUnit hb _
      (continuousOn_comp_realAffineForm hΩc hf' hz)]
  simp [regCarlsonRealAverage]

/-- **(5.3-3), real nodes**: `(∑ᵢ Dᵢ)ᵏ F(b, z) = F⁽ᵏ⁾(b, z)` for `f ∈ Cⁿ(Ω)` and `k ≤ n`. -/
theorem realDiagDeriv_iterate_regCarlsonRealAverage {Ω : Set ℝ} (hΩo : IsOpen Ω)
    (hΩc : Convex ℝ Ω) {n : ℕ} {f : ℝ → ℂ} (hf : ContDiffOn ℝ n f Ω) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) {k : ℕ} (hk : k ≤ n) {z : ι → ℝ} (hz : z ∈ realNodeDomain Ω) :
    realDiagDeriv^[k] (fun x => regCarlsonRealAverage b x f) z =
      regCarlsonRealAverage b z (iteratedDeriv k f) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', realDiagDeriv]
    have hev : realDiagDeriv^[k] (fun x => regCarlsonRealAverage b x f) =ᶠ[𝓝 z]
        fun x => regCarlsonRealAverage b x (iteratedDeriv k f) := by
      filter_upwards [(isOpen_realNodeDomain hΩo).mem_nhds hz] with w hw
      exact ih (by omega) hw
    rw [hev.fderiv_eq, ← realDiagDeriv]
    exact realDiagDeriv_regCarlsonRealAverage hΩo hΩc
      (fun x hx => hf.hasDerivAt_iteratedDeriv_of_isOpen hΩo (by omega) hx)
      (hf.contDiffOn_iteratedDeriv_of_isOpen hΩo (k := k + 1) hk).continuousOn hb hz

omit [Fintype ι] in
open scoped Classical in
/-- Real partial derivatives depend only on the germ of the function. -/
theorem realPartialDeriv_congr {G H : (ι → ℝ) → ℂ} {z : ι → ℝ} (h : G =ᶠ[𝓝 z] H) (i : ι) :
    realPartialDeriv i G z = realPartialDeriv i H z := by
  have hc : Tendsto (fun w => Function.update z i w) (𝓝 (z i)) (𝓝 z) := by
    have := ((continuous_const (y := z)).update i continuous_id).tendsto (z i)
    simpa using this
  exact Filter.EventuallyEq.deriv_eq (show (fun w => G (Function.update z i w)) =ᶠ[𝓝 (z i)]
    fun w => H (Function.update z i w) from hc.eventually h)

/-- Carlson's operator `δ = α + β d/dx + γ x d/dx` of (5.3-4) on functions of a real variable. -/
def realCarlsonDelta (α β γ : ℂ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => α * g x + (β + γ * x) * deriv g x

/-- Carlson's operator `Δ = α + β ∑ Dᵢ + γ ∑ zᵢ Dᵢ` of (5.3-4) on functions of real nodes. -/
def realCarlsonCapDelta (α β γ : ℂ) (G : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun z => α * G z + ∑ i, (β + γ * z i) * realPartialDeriv i G z

/-- The operator `δ` lowers smoothness by one. -/
theorem contDiffOn_realCarlsonDelta {Ω : Set ℝ} (hΩo : IsOpen Ω) {m : ℕ} {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ (m + 1 : ℕ) g Ω) (α β γ : ℂ) :
    ContDiffOn ℝ m (realCarlsonDelta α β γ g) Ω := by
  have hg' : ContDiffOn ℝ m (deriv g) Ω := by
    simpa using hg.contDiffOn_iteratedDeriv_of_isOpen hΩo (k := 1) (by omega)
  unfold realCarlsonDelta
  exact (contDiffOn_const.mul (hg.of_le (by push_cast; exact le_self_add))).add
    ((contDiffOn_const.add (contDiffOn_const.mul (ofRealCLM.contDiff.contDiffOn))).mul hg')

/-- **(5.3-4), first order, real nodes**: `Δ F(b, z)` is the average of `δ g`. -/
theorem realCarlsonCapDelta_regCarlsonRealAverage {Ω : Set ℝ} (hΩo : IsOpen Ω)
    (hΩc : Convex ℝ Ω) {g : ℝ → ℂ} (hg : ContDiffOn ℝ 1 g Ω) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (α β γ : ℂ) {z : ι → ℝ} (hz : z ∈ realNodeDomain Ω) :
    realCarlsonCapDelta α β γ (fun x => regCarlsonRealAverage b x g) z =
      regCarlsonRealAverage b z (realCarlsonDelta α β γ g) := by
  have hd : ∀ x ∈ Ω, HasDerivAt g (deriv g x) x := fun x hx => by
    simpa using ContDiffOn.hasDerivAt_iteratedDeriv_of_isOpen (hs := hΩo) (n := 1)
      (by simpa using hg)
      (k := 0) (by omega) hx
  have hg' : ContinuousOn (deriv g) Ω := by
    simpa using (ContDiffOn.contDiffOn_iteratedDeriv_of_isOpen (hs := hΩo) (n := 1)
      (by simpa using hg)
      (k := 1) le_rfl).continuousOn
  have hgc := continuousOn_comp_realAffineForm hΩc hg.continuousOn hz
  have hdc := continuousOn_comp_realAffineForm hΩc hg' hz
  simp only [realCarlsonCapDelta, realPartialDeriv_regCarlsonRealAverage hΩo hΩc hd hg' hb hz]
  have hsum : ∑ i, (β + γ * z i) * (b i * regCarlsonRealAverage (addDirichletUnit b i) z (deriv g))
      = regDirichletIntegral b (fun u => (β + γ * realAffineForm z u) *
          deriv g (realAffineForm z u)) := by
    simp only [regCarlsonRealAverage, mul_regDirichletIntegral_addDirichletUnit hb,
      ← regDirichletIntegral_smul]
    rw [← regDirichletIntegral_sum (F := fun i u => (β + γ * z i) *
      ((u i : ℂ) * deriv g (realAffineForm z u))) hb fun i _ =>
      continuousOn_const.mul (continuousOn_coord_mul_comp hΩc hg' hz i)]
    refine regDirichletIntegral_congr b fun u hu => ?_
    simp only [realAffineForm]
    have h1 : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
    calc ∑ i, (β + γ * (z i : ℂ)) * ((u i : ℂ) * deriv g (∑ i, u i * z i))
        = (β * ∑ i, (u i : ℂ) + γ * ∑ i, (u i : ℂ) * z i) * deriv g (∑ i, u i * z i) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by push_cast; rw [h1]; ring
  rw [hsum, regCarlsonRealAverage, ← regDirichletIntegral_smul,
    ← regDirichletIntegral_add (f := fun u => α * g (realAffineForm z u))
      (g := fun u => (β + γ * realAffineForm z u) * deriv g (realAffineForm z u)) b
      (continuousOn_const.mul hgc) (by
      exact (continuousOn_const.add (continuousOn_const.mul
        (continuous_ofReal.comp continuous_realAffineForm_right).continuousOn)).mul hdc) hb]
  rfl

/-- `δᵏ f` is `C^(n-k)` when `f` is `Cⁿ`. -/
theorem contDiffOn_realCarlsonDelta_iterate {Ω : Set ℝ} (hΩo : IsOpen Ω) {n : ℕ} {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ n f Ω) (α β γ : ℂ) {k : ℕ} (hk : k ≤ n) :
    ContDiffOn ℝ (n - k : ℕ) ((realCarlsonDelta α β γ)^[k] f) Ω := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact contDiffOn_realCarlsonDelta hΩo (by
      rw [show n - k = n - (k + 1) + 1 by omega] at ih; exact ih (by omega)) α β γ

/-- **(5.3-4), real nodes**: for `f ∈ Cⁿ(Ω)` and `k ≤ n`, `Δᵏ F(b, z)` is the average of `δᵏ f`
(Carlson's Theorem 5.3-2, case (i)). -/
theorem realCarlsonCapDelta_iterate_regCarlsonRealAverage {Ω : Set ℝ} (hΩo : IsOpen Ω)
    (hΩc : Convex ℝ Ω) {n : ℕ} {f : ℝ → ℂ} (hf : ContDiffOn ℝ n f Ω) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (α β γ : ℂ) {k : ℕ} (hk : k ≤ n) {z : ι → ℝ}
    (hz : z ∈ realNodeDomain Ω) :
    (realCarlsonCapDelta α β γ)^[k] (fun x => regCarlsonRealAverage b x f) z =
      regCarlsonRealAverage b z ((realCarlsonDelta α β γ)^[k] f) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hev : (realCarlsonCapDelta α β γ)^[k] (fun x => regCarlsonRealAverage b x f) =ᶠ[𝓝 z]
        fun x => regCarlsonRealAverage b x ((realCarlsonDelta α β γ)^[k] f) := by
      filter_upwards [(isOpen_realNodeDomain hΩo).mem_nhds hz] with w hw
      exact ih (by omega) hw
    have hcongr : realCarlsonCapDelta α β γ
        ((realCarlsonCapDelta α β γ)^[k] (fun x => regCarlsonRealAverage b x f)) z =
        realCarlsonCapDelta α β γ
          (fun x => regCarlsonRealAverage b x ((realCarlsonDelta α β γ)^[k] f)) z := by
      simp only [realCarlsonCapDelta, hev.eq_of_nhds, realPartialDeriv_congr hev]
    rw [hcongr]
    have hg := contDiffOn_realCarlsonDelta_iterate hΩo hf α β γ (k := k) (by omega)
    exact realCarlsonCapDelta_regCarlsonRealAverage hΩo hΩc
      (hg.of_le (by norm_cast; omega)) hb α β γ hz

/-- The real-linear map `u ↦ u · z`. -/
def realNodeCLM (z : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ := ∑ i, z i • ContinuousLinearMap.proj i

/-- Evaluation of `realNodeCLM`. -/
theorem realNodeCLM_apply (z u : ι → ℝ) : realNodeCLM z u = realAffineForm z u := by
  simp [realNodeCLM, realAffineForm, mul_comm]

open scoped Classical in
omit [Fintype ι] in
/-- Raising a Dirichlet parameter by one adds the coordinate unit vector. -/
private lemma addDirichletUnit_eq_add_single' (b : ι → ℂ) (i : ι) :
    addDirichletUnit b i = b + Pi.single i 1 := by
  ext k
  by_cases h : k = i <;> simp [addDirichletUnit, h]

open scoped Classical in
/-- **The tangential contiguous relation for real nodes** (Carlson 5.6-2, used in 5.4-1):
`(zᵢ - zⱼ) F'(b + eᵢ + eⱼ, z) = F(b + eᵢ, z) - F(b + eⱼ, z)` for `g ∈ C¹(Ω)`. -/
theorem regCarlsonRealAverage_tangent {Ω : Set ℝ} (hΩc : Convex ℝ Ω)
    {g g' : ℝ → ℂ} (hg : ∀ x ∈ Ω, HasDerivAt g (g' x) x) (hg' : ContinuousOn g' Ω)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) {z : ι → ℝ} (hz : z ∈ realNodeDomain Ω) (i j : ι) :
    ((z i : ℂ) - z j) * regCarlsonRealAverage (addDirichletUnit (addDirichletUnit b j) i) z g' =
      regCarlsonRealAverage (addDirichletUnit b i) z g -
        regCarlsonRealAverage (addDirichletUnit b j) z g := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  have hgc : ContinuousOn g Ω := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hc := continuousOn_comp_realAffineForm hΩc hgc hz
  have hdc := continuousOn_comp_realAffineForm hΩc hg' hz
  have ha (φ : (ι → ℝ) → ℂ) (hφ : ContinuousOn φ (Convexity.StdSimplex.coordinateSet ℝ ι)) :
      AnalyticOnNhd ℂ (fun b => regDirichletIntegral b φ) mvBetaConvergent :=
    isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp (regDirichletIntegral_analyticOn hφ)
  have hs (k : ι) (c : ι → ℂ) : AnalyticAt ℂ (fun b => addDirichletUnit b k) c := by
    simp_rw [addDirichletUnit_eq_add_single']
    exact analyticAt_id.add analyticAt_const
  have hleft : AnalyticOnNhd ℂ (fun b => ((z i : ℂ) - z j) *
      regCarlsonRealAverage (addDirichletUnit (addDirichletUnit b j) i) z g') mvBetaConvergent := by
    intro b hb
    exact analyticAt_const.mul (((ha _ hdc) _
      (addDirichletUnit_mem_mvBetaConvergent (addDirichletUnit_mem_mvBetaConvergent hb j)
          i)).comp_of_eq ((hs i _).comp_of_eq (hs j b) rfl) rfl)
  have hright : AnalyticOnNhd ℂ (fun b => regCarlsonRealAverage (addDirichletUnit b i) z g -
      regCarlsonRealAverage (addDirichletUnit b j) z g) mvBetaConvergent := by
    intro b hb
    exact (((ha _ hc) _ (addDirichletUnit_mem_mvBetaConvergent hb i)).comp_of_eq (hs i b) rfl).sub
      (((ha _ hc) _ (addDirichletUnit_mem_mvBetaConvergent hb j)).comp_of_eq (hs j b) rfl)
  apply hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (by simpa using isPreconnected_dirichletConvergenceRegion (ι := ι) 0)
    (z₀ := fun _ => 3) (by intro k; norm_num) _ hb
  have hev : ∀ᶠ b : ι → ℂ in 𝓝 (fun _ => 3), ∀ k, 2 < (b k).re := by
    apply Filter.eventually_all.mpr
    intro k
    exact (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply
        k))).eventually_mem (by norm_num)
  filter_upwards [hev] with b hb
  let q := addDirichletUnit (addDirichletUnit b j) i
  have hraise (c : ι → ℂ) (k : ι) (hc : ∀ l, 2 < (c l).re) :
      ∀ l, 2 < (addDirichletUnit c k l).re := by
    intro l
    by_cases hl : l = k
    · subst l
      simp only [addDirichletUnit, Function.update_self, add_re, one_re]
      linarith [hc k]
    · simpa [addDirichletUnit, hl] using hc l
  have hq : ∀ k, 2 < (q k).re := hraise _ i (hraise _ j hb)
  set φ : (ι → ℝ) → ℂ := fun u => g (realAffineForm z u)
  have hφd : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      HasFDerivAt φ ((ContinuousLinearMap.toSpanSingleton ℝ (g' (realAffineForm z u))).comp
        (realNodeCLM z)) u := by
    intro u hu
    have hL : HasFDerivAt (fun u => realAffineForm z u) (realNodeCLM z) u := by
      have h : (fun u => realAffineForm z u) = realNodeCLM z :=
        funext fun u => (realNodeCLM_apply z u).symm
      rw [h]; exact (realNodeCLM z).hasFDerivAt
    exact (hg _ (realAffineForm_mem hΩc hz hu)).hasFDerivAt.comp u hL
  have heq {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
      fderiv ℝ φ u (Pi.single i 1 - Pi.single j 1) =
        ((z i : ℂ) - z j) * g' (realAffineForm z u) := by
    rw [(hφd u hu).fderiv]
    simp only [ContinuousLinearMap.comp_apply, realNodeCLM_apply,
      ContinuousLinearMap.toSpanSingleton_apply, Complex.real_smul, realAffineForm]
    simp [Pi.single_apply, sub_mul, Finset.sum_sub_distrib]
  have hdiff : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, DifferentiableAt ℝ φ u :=
    fun u hu => (hφd u hu).differentiableAt
  have hdf : ContinuousOn (fun u => fderiv ℝ φ u (Pi.single i 1 - Pi.single j 1))
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    (continuousOn_const.mul hdc).congr fun u hu => heq hu
  have H := regDirichletIntegral_tangent_ibp j ⟨i, hij⟩ q hq hdiff hdf
  have hqi : q - Pi.single i 1 = addDirichletUnit b j := by
    simp [q, addDirichletUnit_eq_add_single']
  have hqj : q - Pi.single j 1 = addDirichletUnit b i := by
    simp [q, addDirichletUnit_eq_add_single']; abel
  rw [hqi, hqj] at H
  rw [show regDirichletIntegral q (fun u => fderiv ℝ φ u (Pi.single i 1 - Pi.single j 1)) =
      ((z i : ℂ) - z j) * regCarlsonRealAverage q z g' from by
    rw [regCarlsonRealAverage, ← regDirichletIntegral_smul]
    exact regDirichletIntegral_congr q fun u hu => heq hu] at H
  exact H

/-- Carlson's Euler–Poisson operator `(zᵢ - zⱼ) DᵢDⱼ + bᵢ Dⱼ - bⱼ Dᵢ` for real nodes. -/
def realEulerPoissonOperator (i j : ι) (b : ι → ℂ) (z : ι → ℝ) (G : (ι → ℝ) → ℂ) : ℂ :=
  ((z i : ℂ) - z j) * realPartialDeriv i (realPartialDeriv j G) z +
    b i * realPartialDeriv j G z - b j * realPartialDeriv i G z

/-- **Carlson 5.4-1, case (i).** If `f` is twice continuously differentiable on an open interval
`Ω`, the regularized average satisfies the Euler–Poisson system on `Ωᵏ`. -/
theorem realEulerPoissonOperator_regCarlsonRealAverage {Ω : Set ℝ} (hΩo : IsOpen Ω)
    (hΩc : Convex ℝ Ω) {f : ℝ → ℂ} (hf : ContDiffOn ℝ 2 f Ω) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) {z : ι → ℝ} (hz : z ∈ realNodeDomain Ω) (i j : ι) :
    realEulerPoissonOperator i j b z (fun x => regCarlsonRealAverage b x f) = 0 := by
  have hf2 : ContDiffOn ℝ (2 : ℕ) f Ω := by simpa using hf
  have hd0 : ∀ x ∈ Ω, HasDerivAt f (iteratedDeriv 1 f x) x := fun x hx => by
    simpa using hf2.hasDerivAt_iteratedDeriv_of_isOpen hΩo (k := 0) (by omega) hx
  have hd1 : ∀ x ∈ Ω, HasDerivAt (iteratedDeriv 1 f) (iteratedDeriv 2 f x) x := fun x hx =>
    hf2.hasDerivAt_iteratedDeriv_of_isOpen hΩo (k := 1) (by omega) hx
  have hc1 := hf2.continuousOn_iteratedDeriv_of_isOpen hΩo (k := 1) (by omega)
  have hc2 := hf2.continuousOn_iteratedDeriv_of_isOpen hΩo (k := 2) le_rfl
  have hD (k : ι) : realPartialDeriv k (fun x => regCarlsonRealAverage b x f) =ᶠ[𝓝 z]
      fun x => b k * regCarlsonRealAverage (addDirichletUnit b k) x (iteratedDeriv 1 f) := by
    filter_upwards [(isOpen_realNodeDomain hΩo).mem_nhds hz] with w hw
    exact realPartialDeriv_regCarlsonRealAverage hΩo hΩc hd0 hc1 hb hw k
  have hDD : realPartialDeriv i (realPartialDeriv j fun x => regCarlsonRealAverage b x f) z =
      b j * (addDirichletUnit b j i * regCarlsonRealAverage
        (addDirichletUnit (addDirichletUnit b j) i) z (iteratedDeriv 2 f)) := by
    rw [realPartialDeriv_congr (hD j)]
    have h := (hasFDerivAt_regCarlsonRealAverage hΩo hΩc hd1 hc2
      (addDirichletUnit_mem_mvBetaConvergent hb j) hz).const_mul (b j)
    rw [realPartialDeriv_eq_of_hasFDerivAt h]
    classical
    simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, realProj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i (fun l _ hl => by simp [hl]) (by simp)]
    simp
  have ht := regCarlsonRealAverage_tangent hΩc hd1 hc2 hb hz i j
  rw [realEulerPoissonOperator, hDD, (hD i).eq_of_nhds, (hD j).eq_of_nhds]
  rcases eq_or_ne i j with rfl | hij
  · ring
  have hbi : addDirichletUnit b j i = b i := by simp [addDirichletUnit, hij]
  rw [hbi]
  linear_combination b i * b j * ht

end Dirichlet
