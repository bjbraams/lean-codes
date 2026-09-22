/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform
public import SeveralComplexVariables.RealUniqueness

/-!
# The entire regularized Dirichlet transform

A general continuation specification and the unique transform of a smooth simplex kernel.
The interface distinguishes analytic continuation from the totalized native integral.
Linearity and independence of extensions are proved by uniqueness.
-/

open Complex MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]

/-- An entire regularized Dirichlet continuation agrees with the native integral on
its domain of absolute convergence. The integrand is an arbitrary simplex function. -/
def IsRegDirichletContinuation (g : (ι → ℝ) → ℂ) (F : (ι → ℂ) → ℂ) : Prop :=
  AnalyticOnNhd ℂ F univ ∧ EqOn F (fun b => regDirichletIntegral b g) mvBetaConvergent

/-- An admissible kernel has every finite order of differentiability near the closed simplex.
The neighborhood may depend on the order; values away from the simplex are immaterial. -/
def SmoothNearStdSimplex (g : (ι → ℝ) → ℂ) : Prop :=
  ∀ N, ContDiffNearStdSimplex N g

/-- A smooth simplex kernel is continuous on the closed simplex. -/
theorem SmoothNearStdSimplex.continuousOn {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι) :=
  (hg 0).continuousOn

/-- Two entire functions of the Dirichlet parameters that agree throughout the ordinary
convergence region agree everywhere.  This is the common continuation step for the identities
proved from Carlson's native integral. -/
theorem analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    {G H : (ι → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ)
    (hH : AnalyticOnNhd ℂ H Set.univ) (hEq : Set.EqOn G H mvBetaConvergent) :
    G = H := by
  let b₀ : ι → ℂ := fun _ ↦ 1
  have hb₀ : b₀ ∈ mvBetaConvergent := by
    intro i
    simp [b₀]
  apply hG.eq_of_eventuallyEq hH (z₀ := b₀)
  filter_upwards [isOpen_mvBetaConvergent.eventually_mem hb₀] with b hb
  exact hEq hb

/-- Two entire candidates which agree for every strictly positive real Dirichlet parameter
agree globally.  This is the uniqueness principle used to lift probability identities without
first proving them on the full complex convergence region. -/
theorem analyticOnNhd_eq_of_eqOn_realDirichletDomain
    {G H : (ι → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ)
    (hH : AnalyticOnNhd ℂ H Set.univ)
    (hEq : ∀ b : ι → ℝ, b ∈ mvRealBetaDomain →
      G (fun i ↦ (b i : ℂ)) = H (fun i ↦ (b i : ℂ))) : G = H := by
  apply hG.eq_of_eqOn_posReal_pi hH
  intro b hb
  exact hEq b hb

/-- An entire regularized Dirichlet continuation is analytic everywhere. -/
theorem IsRegDirichletContinuation.analyticOnNhd {g : (ι → ℝ) → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) : AnalyticOnNhd ℂ F univ := hF.1

/-- A continued transform agrees with the convergent integral. -/
theorem IsRegDirichletContinuation.eq_native {g : (ι → ℝ) → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    F b = regDirichletIntegral b g := hF.2 hb

/-- The entire regularized transform of a given kernel is unique. -/
theorem IsRegDirichletContinuation.eq {g : (ι → ℝ) → ℂ} {F H : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) (hH : IsRegDirichletContinuation g H) : F = H :=
  analyticOnNhd_eq_of_eqOn_mvBetaConvergent hF.1 hH.1
    (fun _ hb => (hF.2 hb).trans (hH.2 hb).symm)

/-- Changing the kernel away from the closed simplex does not change its continuation. -/
theorem IsRegDirichletContinuation.congr {g h : (ι → ℝ) → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F)
    (hgh : EqOn g h (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    IsRegDirichletContinuation h F :=
  ⟨hF.1, fun b hb => (hF.2 hb).trans (regDirichletIntegral_congr b hgh)⟩

/-- Comparison on positive real parameters identifies entire regularized continuations. -/
theorem IsRegDirichletContinuation.mk_of_eqOn_realDirichletDomain
    {g : (ι → ℝ) → ℂ} {F H : (ι → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F univ)
    (hH : IsRegDirichletContinuation g H)
    (hEq : ∀ b : ι → ℝ, b ∈ mvRealBetaDomain →
      F (fun i => (b i : ℂ)) = H (fun i => (b i : ℂ))) :
    IsRegDirichletContinuation g F := by
  rw [analyticOnNhd_eq_of_eqOn_realDirichletDomain hF hH.1 hEq]
  exact hH

/-- Smooth simplex kernels are closed under addition. -/
theorem SmoothNearStdSimplex.add {g h : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (hh : SmoothNearStdSimplex h) :
    SmoothNearStdSimplex (fun u => g u + h u) := by
  intro N
  obtain ⟨U, hU, hKU, hgU⟩ := hg N
  obtain ⟨V, hV, hKV, hhV⟩ := hh N
  exact ⟨U ∩ V, hU.inter hV, fun u hu => ⟨hKU hu, hKV hu⟩,
    (hgU.mono inter_subset_left).add (hhV.mono inter_subset_right)⟩

/-- Smooth simplex kernels are closed under complex scalar multiplication. -/
theorem SmoothNearStdSimplex.smul {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (c : ℂ) : SmoothNearStdSimplex (fun u => c * g u) := by
  intro N
  obtain ⟨U, hU, hKU, hgU⟩ := hg N
  exact ⟨U, hU, hKU, contDiffOn_const.mul hgU⟩

/-- Taking a tangential derivative preserves smoothness near the simplex. -/
theorem SmoothNearStdSimplex.tangentDeriv {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (j i : ι) : SmoothNearStdSimplex (stdSimplexTangentDeriv j i g) :=
  fun N => (hg (N + 1)).tangentDeriv j i

/-- Every smooth simplex kernel has an entire regularized Dirichlet transform. -/
theorem exists_isRegDirichletContinuation {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g) :
    ∃ F, IsRegDirichletContinuation g F :=
  exists_entire_regDirichletContinuation_of_contDiffNear hg

/-- The entire regularized Dirichlet transform of a smooth simplex kernel.
Existence and uniqueness justify the choice; this is not the totalized native integral. -/
def regDirichletTransform (g : (ι → ℝ) → ℂ) (hg : SmoothNearStdSimplex g) : (ι → ℂ) → ℂ :=
  (exists_isRegDirichletContinuation hg).choose

/-- The selected transform satisfies the general continuation specification. -/
theorem isRegDirichletContinuation_transform {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g) :
    IsRegDirichletContinuation g (regDirichletTransform g hg) :=
  (exists_isRegDirichletContinuation hg).choose_spec

/-- Any entire continuation is the selected transform. -/
theorem IsRegDirichletContinuation.eq_transform {g : (ι → ℝ) → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) (hg : SmoothNearStdSimplex g) :
    F = regDirichletTransform g hg := hF.eq (isRegDirichletContinuation_transform hg)

/-- The selected transform is entire in all Dirichlet parameters. -/
theorem analyticOnNhd_regDirichletTransform {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g) :
    AnalyticOnNhd ℂ (regDirichletTransform g hg) univ :=
  (isRegDirichletContinuation_transform hg).1

/-- On the native convergence region, the selected transform is the integral. -/
theorem regDirichletTransform_eq_integral {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regDirichletTransform g hg b = regDirichletIntegral b g :=
  (isRegDirichletContinuation_transform hg).eq_native hb

/-- The transform depends only on the restriction of its kernel to the closed simplex. -/
theorem regDirichletTransform_congr {g h : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (hh : SmoothNearStdSimplex h)
    (hgh : EqOn g h (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regDirichletTransform g hg = regDirichletTransform h hh :=
  ((isRegDirichletContinuation_transform hg).congr hgh).eq
    (isRegDirichletContinuation_transform hh)

/-- Entire continuation preserves addition of continuous simplex kernels. -/
theorem IsRegDirichletContinuation.add {g h : (ι → ℝ) → ℂ} {F H : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) (hH : IsRegDirichletContinuation h H)
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hh : ContinuousOn h (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    IsRegDirichletContinuation (fun u => g u + h u) (fun b => F b + H b) := by
  refine ⟨hF.1.add hH.1, fun b hb => ?_⟩
  dsimp only
  rw [hF.eq_native hb, hH.eq_native hb, regDirichletIntegral_add b hg hh hb]

/-- Entire continuation preserves finite sums of continuous simplex kernels. -/
theorem IsRegDirichletContinuation.sum {α : Type*} (s : Finset α)
    {g : α → (ι → ℝ) → ℂ} {F : α → (ι → ℂ) → ℂ}
    (hF : ∀ n ∈ s, IsRegDirichletContinuation (g n) (F n))
    (hg : ∀ n ∈ s, ContinuousOn (g n) (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    IsRegDirichletContinuation (fun u => ∑ n ∈ s, g n u) (fun b => ∑ n ∈ s, F n b) := by
  refine ⟨fun b _ => Finset.analyticAt_fun_sum _ (fun n hn => (hF n hn).1 b (mem_univ _)),
    fun b hb => ?_⟩
  dsimp only
  calc
    ∑ n ∈ s, F n b = ∑ n ∈ s, regDirichletIntegral b (g n) :=
      Finset.sum_congr rfl fun n hn => (hF n hn).eq_native hb
    _ = regDirichletIntegral b (fun u => ∑ n ∈ s, g n u) := by
      unfold regDirichletIntegral
      rw [← integral_finsetSum]
      · apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
        intro u _
        simp only [Finset.mul_sum]
      · exact fun n hn => integrableOn_regDirichletDensity_mul b hb (hg n hn)

/-- Entire continuation preserves complex scalar multiplication. -/
theorem IsRegDirichletContinuation.smul {g : (ι → ℝ) → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : IsRegDirichletContinuation g F) (c : ℂ) :
    IsRegDirichletContinuation (fun u => c * g u) (fun b => c * F b) := by
  refine ⟨analyticOnNhd_const.mul hF.1, fun b hb => ?_⟩
  dsimp only
  rw [hF.eq_native hb, regDirichletIntegral_smul]

/-- The zero kernel has the zero continuation, including on the empty simplex. -/
theorem isRegDirichletContinuation_zero :
    IsRegDirichletContinuation (fun _ : ι → ℝ => 0) (fun _ => 0) := by
  exact ⟨analyticOnNhd_const, fun b _ => by simp [regDirichletIntegral]⟩

/-- The explicit polynomial transform satisfies the general continuation specification. -/
theorem isRegDirichletContinuation_mvPolynomial (p : MvPolynomial ι ℂ) :
    IsRegDirichletContinuation (fun u => p.eval (fun i => (u i : ℂ)))
      (regDirichletMvPolynomialTransform p) :=
  ⟨analyticOnNhd_regDirichletMvPolynomialTransform p,
    fun b hb => (regDirichletIntegral_mvPolynomial b hb p).symm⟩

/-- The canonical entire transform is additive on smooth kernels. -/
theorem regDirichletTransform_add {g h : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (hh : SmoothNearStdSimplex h) (b : ι → ℂ) :
    regDirichletTransform (fun u => g u + h u) (hg.add hh) b =
      regDirichletTransform g hg b + regDirichletTransform h hh b :=
  (congrFun (((isRegDirichletContinuation_transform hg).add
    (isRegDirichletContinuation_transform hh) hg.continuousOn hh.continuousOn).eq_transform
      (hg.add hh)) b).symm

/-- The canonical entire transform commutes with complex scalar multiplication. -/
theorem regDirichletTransform_smul {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (c : ℂ) (b : ι → ℂ) :
    regDirichletTransform (fun u => c * g u) (hg.smul c) b = c * regDirichletTransform g hg b :=
  (congrFun (((isRegDirichletContinuation_transform hg).smul c).eq_transform (hg.smul c)) b).symm

end Dirichlet
end
