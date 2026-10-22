/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Matrix
public import Dirichlet.Average.JointContinuation

/-!
# Entire parameter continuation of matrix double averages

For a scalar function holomorphic on a convex open domain, its regularized matrix
average continues to every complex row and column parameter, jointly holomorphic
also in the matrix entries in that domain. The construction first continues the
column average, then applies the parametric Dirichlet transform to the row weights.
It does not assert continuation to arbitrary cut-plane configurations.

The native integral and its continuation remain separate functions. Uniqueness
on the two parameter spaces characterizes the selected continuation.
-/

open Complex Set ProbabilityTheory
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- An entire regularized matrix continuation agrees with the native integral when
both independent parameter vectors have positive real parts. -/
def IsRegMatrixContinuation (Z : ι → κ → ℂ) (f : ℂ → ℂ)
    (F : ((ι → ℂ) × (κ → ℂ)) → ℂ) : Prop :=
  AnalyticOnNhd ℂ F univ ∧
    ∀ b β, b ∈ mvBetaConvergent → β ∈ mvBetaConvergent →
      F (b, β) = regMatrixDirichletAverage b β Z f

/-- An entire matrix continuation is unique, by uniqueness in each parameter vector. -/
theorem IsRegMatrixContinuation.eq {Z : ι → κ → ℂ} {f : ℂ → ℂ}
    {F G : ((ι → ℂ) × (κ → ℂ)) → ℂ}
    (hF : IsRegMatrixContinuation Z f F) (hG : IsRegMatrixContinuation Z f G) : F = G := by
  have hfirst (β : κ → ℂ) (hβ : β ∈ mvBetaConvergent) (b : ι → ℂ) :
      F (b, β) = G (b, β) := by
    apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
      (hF.1.comp (analyticOnNhd_id.prod analyticOnNhd_const) (fun _ _ => mem_univ _))
      (hG.1.comp (analyticOnNhd_id.prod analyticOnNhd_const) (fun _ _ => mem_univ _))
      (fun c hc => (hF.2 c β hc hβ).trans (hG.2 c β hc hβ).symm)) b
  funext p
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (hF.1.comp (analyticOnNhd_const.prod analyticOnNhd_id) (fun _ _ => mem_univ _))
    (hG.1.comp (analyticOnNhd_const.prod analyticOnNhd_id) (fun _ _ => mem_univ _))
    (fun β hβ => hfirst β hβ p.1)) p.2

/-- Matrix entries belong to the scalar kernel domain. -/
def matrixNodeDomain (Ω : Set ℂ) : Set (ι → κ → ℂ) := {Z | ∀ i j, Z i j ∈ Ω}

/-- The matrix node domain is open when the scalar domain is open. -/
theorem isOpen_matrixNodeDomain {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    IsOpen (matrixNodeDomain (ι := ι) (κ := κ) Ω) := by
  simp only [matrixNodeDomain, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hΩ.preimage (by fun_prop : Continuous (fun Z : ι → κ → ℂ => Z i j))

/-- Encoded column parameters and the nodes obtained by complex row weights. -/
private def matrixColumnMap (p : ((κ ⊕ (ι × κ)) → ℂ) × (ι → ℂ)) :
    (κ → ℂ) × (κ → ℂ) :=
  ((fun j => p.1 (.inl j)), (fun j => ∑ i, p.2 i * p.1 (.inr (i, j))))

/-- The column map is polynomial in the matrix entries and row weights. -/
private theorem analyticOnNhd_matrixColumnMap :
    AnalyticOnNhd ℂ (matrixColumnMap (ι := ι) (κ := κ)) univ := by
  intro p _
  unfold matrixColumnMap
  apply AnalyticAt.prod
  · apply analyticAt_pi_iff.mpr
    intro j
    exact ((ContinuousLinearMap.proj (.inl j) :
      ((κ ⊕ (ι × κ)) → ℂ) →L[ℂ] ℂ).analyticAt p.1).comp_of_eq analyticAt_fst rfl
  · apply analyticAt_pi_iff.mpr
    intro j
    apply Finset.analyticAt_fun_sum
    intro i _
    apply AnalyticAt.mul
    · exact ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt p.2).comp_of_eq
         analyticAt_snd rfl
    · exact ((ContinuousLinearMap.proj (Sum.inr (i, j) : κ ⊕ (ι × κ)) :
        ((κ ⊕ (ι × κ)) → ℂ) →L[ℂ] ℂ).analyticAt p.1).comp_of_eq
           analyticAt_fst rfl

/-- Encode both parameter vectors and matrix entries for the outer transform. -/
private def matrixParameterMap (p : (ι → ℂ) × (κ → ℂ) × (ι → κ → ℂ)) :
    (ι → ℂ) × ((κ ⊕ (ι × κ)) → ℂ) :=
  (p.1, Sum.elim p.2.1 (fun ij : ι × κ => p.2.2 ij.1 ij.2))

/-- The parameter encoding is complex linear. -/
private theorem analyticOnNhd_matrixParameterMap :
    AnalyticOnNhd ℂ (matrixParameterMap (ι := ι) (κ := κ)) univ := by
  intro p _
  unfold matrixParameterMap
  apply AnalyticAt.prod analyticAt_fst
  apply analyticAt_pi_iff.mpr
  intro k
  cases k with
  | inl j =>
    simp only [Sum.elim_inl]
    have h : AnalyticAt ℂ (fun q : (ι → ℂ) × (κ → ℂ) × (ι → κ → ℂ) => q.2.1) p :=
      analyticAt_fst.comp_of_eq analyticAt_snd rfl
    exact (analyticAt_pi_iff.mp h) j
  | inr ij =>
    simp only [Sum.elim_inr]
    have h : AnalyticAt ℂ (fun q : (ι → ℂ) × (κ → ℂ) × (ι → κ → ℂ) => q.2.2) p :=
      analyticAt_snd.comp_of_eq analyticAt_snd rfl
    exact (analyticAt_pi_iff.mp ((analyticAt_pi_iff.mp h) ij.1)) ij.2

/-- On convergent column parameters, the inner continuation agrees with native averaging. -/
private theorem matrixColumn_native {Ω : Set ℂ} (hΩc : Convex ℝ Ω)
    {f : ℂ → ℂ} {G : ((κ → ℂ) × (κ → ℂ)) → ℂ}
    (hGn : ∀ z, range z ⊆ Ω → IsRegCarlsonContinuation f z (fun β => G (β, z)))
    {Z : ι → κ → ℂ} (hZ : Z ∈ matrixNodeDomain Ω) {β : κ → ℂ}
    (hβ : β ∈ mvBetaConvergent) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    G (β, fun j => ∑ i, (u i : ℂ) * Z i j) =
      regDirichletIntegral β (fun v => f (matrixAffineForm Z u v)) := by
  rw [(hGn _ (fun z hz => by
    obtain ⟨j, rfl⟩ := hz
    exact convexHull_min (fun z hz => by
      obtain ⟨i, rfl⟩ := hz
      exact hZ i j) hΩc (carlsonAffineForm_mem_convexHull (fun i => Z i j) hu))).eq_native hβ]
  unfold regCarlsonDirichletAverage
  apply regDirichletIntegral_congr
  intro v _
  apply congrArg f
  simp only [matrixAffineForm, carlsonAffineForm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Entire continuation in both parameter vectors, jointly with all matrix entries
in a convex open scalar domain. -/
theorem exists_joint_isRegMatrixContinuation
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) :
    ∃ F : ((ι → ℂ) × (κ → ℂ) × (ι → κ → ℂ)) → ℂ,
      AnalyticOnNhd ℂ F {p | p.2.2 ∈ matrixNodeDomain Ω} ∧
      ∀ Z ∈ matrixNodeDomain Ω, IsRegMatrixContinuation Z f (fun p => F (p.1, p.2, Z)) := by
  obtain ⟨G, hG, hGn⟩ := exists_joint_isRegCarlsonContinuation hΩo hΩc hf (ι := κ)
  let U : Set ((κ ⊕ (ι × κ)) → ℂ) := {q | ∀ i j, q (.inr (i, j)) ∈ Ω}
  let A := matrixColumnMap (ι := ι) (κ := κ)
  have hA : AnalyticOnNhd ℂ A univ := analyticOnNhd_matrixColumnMap
  let W := {p : ((κ ⊕ (ι × κ)) → ℂ) × (ι → ℂ) | range (A p).2 ⊆ Ω}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hΩo.preimage (continuous_apply (Sum.inr (i, j) : κ ⊕ (ι × κ)))
  have hW : IsOpen W := by
    simp only [W, range_subset_iff, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => hΩo.preimage
      (((continuous_apply j).comp continuous_snd).comp
        (continuousOn_univ.mp hA.continuousOn))
  have hGA : AnalyticOnNhd ℂ (G ∘ A) W :=
    hG.comp (hA.mono (subset_univ _)) (fun _ hp => hp)
  have hWU : ∀ q ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (q, fun i => (u i : ℂ)) ∈ W := by
    intro q hq u hu j hj
    obtain ⟨j, rfl⟩ := hj
    exact convexHull_min (fun z hz => by
      obtain ⟨i, rfl⟩ := hz
      exact hq i j) hΩc
      (carlsonAffineForm_mem_convexHull (fun i => q (.inr (i, j))) hu)
  obtain ⟨T, hT⟩ := exists_isJointRegDirichletContinuation hU hW hGA hWU
  let E := matrixParameterMap (ι := ι) (κ := κ)
  have hE : AnalyticOnNhd ℂ E univ := analyticOnNhd_matrixParameterMap
  have hTE : AnalyticOnNhd ℂ (T ∘ E) {p | p.2.2 ∈ matrixNodeDomain Ω} :=
    hT.1.comp (hE.mono (subset_univ _)) (fun p hp => ⟨mem_univ _, hp⟩)
  refine ⟨T ∘ E, hTE, ?_⟩
  intro Z hZ
  refine ⟨?_, ?_⟩
  · intro p _
    exact (hTE (p.1, p.2, Z) hZ).comp_of_eq
        (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const)) rfl
  · intro b β hb hβ
    dsimp only [Function.comp_def, E, matrixParameterMap]
    rw [(hT.2 (Sum.elim β (fun ij : ι × κ => Z ij.1 ij.2)) hZ).eq_native hb]
    dsimp only [A, matrixColumnMap, Function.comp_apply, Sum.elim_inl, Sum.elim_inr]
    change regDirichletIntegral b (fun u =>
      G (β, fun j => ∑ i, (u i : ℂ) * Z i j)) = _
    apply regDirichletIntegral_congr
    intro u hu
    change G (β, fun j => ∑ i, (u i : ℂ) * Z i j) =
      regDirichletIntegral β (fun v => f (matrixAffineForm Z u v))
    exact matrixColumn_native hΩc hGn hZ hβ hu

open scoped Classical in
/-- The selected entire matrix continuation, when one exists; zero otherwise.
Native totalized integrals are not used as values outside their convergence region. -/
def continuedRegMatrixDirichletAverage (Z : ι → κ → ℂ) (f : ℂ → ℂ) :
    ((ι → ℂ) × (κ → ℂ)) → ℂ :=
  if h : ∃ F, IsRegMatrixContinuation Z f F then h.choose else fun _ => 0

/-- Existence identifies the selected continuation with its defining specification. -/
theorem isRegMatrixContinuation_selected {Z : ι → κ → ℂ} {f : ℂ → ℂ}
    (h : ∃ F, IsRegMatrixContinuation Z f F) :
    IsRegMatrixContinuation Z f (continuedRegMatrixDirichletAverage Z f) := by
  rw [continuedRegMatrixDirichletAverage, dite_eq_left h]
  exact h.choose_spec

/-- A holomorphic kernel on a convex domain supplies the canonical entire matrix continuation. -/
theorem isRegMatrixContinuation_of_convex
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) {Z : ι → κ → ℂ}
    (hZ : Z ∈ matrixNodeDomain Ω) :
    IsRegMatrixContinuation Z f (continuedRegMatrixDirichletAverage Z f) := by
  obtain ⟨F, _, hF⟩ := exists_joint_isRegMatrixContinuation hΩo hΩc hf (ι := ι) (κ := κ)
  exact isRegMatrixContinuation_selected ⟨_, hF Z hZ⟩

/-- The selected continuation agrees with the native matrix integral on its convergence region. -/
theorem continuedRegMatrixDirichletAverage_eq_native
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) {Z : ι → κ → ℂ}
    (hZ : Z ∈ matrixNodeDomain Ω) {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent) :
    continuedRegMatrixDirichletAverage Z f (b, β) = regMatrixDirichletAverage b β Z f :=
  (isRegMatrixContinuation_of_convex hΩo hΩc hf hZ).2 b β hb hβ

/-- The canonical matrix continuation is jointly holomorphic in parameters and nodes. -/
theorem analyticOnNhd_continuedRegMatrixDirichletAverage
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) :
    AnalyticOnNhd ℂ (fun p : (ι → ℂ) × (κ → ℂ) × (ι → κ → ℂ) =>
      continuedRegMatrixDirichletAverage p.2.2 f (p.1, p.2.1))
        {p | p.2.2 ∈ matrixNodeDomain Ω} := by
  obtain ⟨F, hF, hFn⟩ := exists_joint_isRegMatrixContinuation hΩo hΩc hf (ι := ι) (κ := κ)
  apply hF.congr ((isOpen_matrixNodeDomain hΩo).preimage (by fun_prop))
  intro p hp
  exact congrFun ((hFn p.2.2 hp).eq (isRegMatrixContinuation_of_convex hΩo hΩc hf hp))
    (p.1, p.2.1)

/-- Transposing a continuation and swapping its parameter vectors preserves its specification. -/
theorem IsRegMatrixContinuation.transpose {Z : ι → κ → ℂ} {f : ℂ → ℂ}
    {F : ((ι → ℂ) × (κ → ℂ)) → ℂ} (hF : IsRegMatrixContinuation Z f F)
    (hf : ContinuousOn f (convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2)))) :
    IsRegMatrixContinuation (fun j i => Z i j) f (fun p => F (p.2, p.1)) := by
  refine ⟨hF.1.comp (analyticOnNhd_snd.prod analyticOnNhd_fst) (fun _ _ => mem_univ _), ?_⟩
  intro β b hβ hb
  exact (hF.2 b β hb hβ).trans (regMatrixDirichletAverage_transpose hb hβ Z hf)

/-- Transposition symmetry holds at arbitrary complex row and column parameters. -/
theorem continuedRegMatrixDirichletAverage_transpose
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) {Z : ι → κ → ℂ}
    (hZ : Z ∈ matrixNodeDomain Ω) (b : ι → ℂ) (β : κ → ℂ) :
    continuedRegMatrixDirichletAverage (fun j i => Z i j) f (β, b) =
      continuedRegMatrixDirichletAverage Z f (b, β) := by
  have hfc : ContinuousOn f (convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2))) :=
    hf.continuousOn.mono (convexHull_min (by rintro z ⟨⟨i, j⟩, rfl⟩; exact hZ i j) hΩc)
  have hflip := (isRegMatrixContinuation_of_convex hΩo hΩc hf hZ).transpose hfc
  exact congrFun ((isRegMatrixContinuation_selected ⟨_, hflip⟩).eq hflip) (β, b)

end Dirichlet
