/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.MatrixTaylor
public import Dirichlet.Average.MatrixSeries

/-!
# Identities for continued matrix averages

Row and column permutations and linearity in the scalar kernel extend to every
complex row and column parameter. Analytic uniqueness transfers the native
identities on any convex open scalar kernel domain.
-/

open Complex Set ProbabilityTheory
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Permuting the rows and their parameters preserves the entire matrix continuation. -/
theorem continuedRegMatrixDirichletAverage_perm_rows
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) {Z : ι → κ → ℂ}
    (hZ : Z ∈ matrixNodeDomain Ω) (σ : Equiv.Perm ι) (b : ι → ℂ) (β : κ → ℂ) :
    continuedRegMatrixDirichletAverage (fun i j => Z (σ i) j) f (b ∘ σ, β) =
      continuedRegMatrixDirichletAverage Z f (b, β) := by
  have hperm := isRegMatrixContinuation_of_convex hΩo hΩc hf (fun i j => hZ (σ i) j)
  have hmap : AnalyticOnNhd ℂ (fun p : (ι → ℂ) × (κ → ℂ) => (p.1 ∘ σ, p.2)) univ := by
    intro p _
    apply AnalyticAt.prod _ analyticAt_snd
    apply analyticAt_pi_iff.mpr
    intro i
    exact (analyticAt_pi_iff.mp (show AnalyticAt ℂ
      (fun q : (ι → ℂ) × (κ → ℂ) => q.1) p from analyticAt_fst)) (σ i)
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod
    (hperm.1.comp hmap (fun _ _ => mem_univ _))
    (isRegMatrixContinuation_of_convex hΩo hΩc hf hZ).1 ?_) (b, β)
  intro c γ hc hγ
  change continuedRegMatrixDirichletAverage (fun i j => Z (σ i) j) f (c ∘ σ, γ) =
    continuedRegMatrixDirichletAverage Z f (c, γ)
  rw [hperm.2 (c ∘ σ) γ (fun i => hc (σ i)) hγ,
    (isRegMatrixContinuation_of_convex hΩo hΩc hf hZ).2 c γ hc hγ]
  exact regMatrixDirichletAverage_perm_rows c γ Z f σ

/-- Permuting the columns and their parameters preserves the entire matrix continuation. -/
theorem continuedRegMatrixDirichletAverage_perm_columns
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) {Z : ι → κ → ℂ}
    (hZ : Z ∈ matrixNodeDomain Ω) (σ : Equiv.Perm κ) (b : ι → ℂ) (β : κ → ℂ) :
    continuedRegMatrixDirichletAverage (fun i j => Z i (σ j)) f (b, β ∘ σ) =
      continuedRegMatrixDirichletAverage Z f (b, β) := by
  rw [continuedRegMatrixDirichletAverage_transpose hΩo hΩc hf
    (fun i j => hZ j (σ i)) (β ∘ σ) b]
  rw [continuedRegMatrixDirichletAverage_perm_rows hΩo hΩc hf
    (fun i j => hZ j i) σ β b]
  exact continuedRegMatrixDirichletAverage_transpose hΩo hΩc hf hZ b β

/-- The entire continued average is linear under addition of holomorphic kernels. -/
theorem continuedRegMatrixDirichletAverage_add
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) (hg : AnalyticOnNhd ℂ g Ω)
    {Z : ι → κ → ℂ} (hZ : Z ∈ matrixNodeDomain Ω) (b : ι → ℂ) (β : κ → ℂ) :
    continuedRegMatrixDirichletAverage Z (fun z => f z + g z) (b, β) =
      continuedRegMatrixDirichletAverage Z f (b, β) +
        continuedRegMatrixDirichletAverage Z g (b, β) := by
  have hF := isRegMatrixContinuation_of_convex hΩo hΩc hf hZ
  have hG := isRegMatrixContinuation_of_convex hΩo hΩc hg hZ
  have hfg : AnalyticOnNhd ℂ (fun z => f z + g z) Ω := by
    intro z hz
    exact (hf z hz).add (hg z hz)
  have hsum := isRegMatrixContinuation_of_convex hΩo hΩc hfg hZ
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod hsum.1 (hF.1.add hG.1) ?_)
    (b, β)
  intro c γ hc hγ
  change continuedRegMatrixDirichletAverage Z (fun z => f z + g z) (c, γ) =
    continuedRegMatrixDirichletAverage Z f (c, γ) +
      continuedRegMatrixDirichletAverage Z g (c, γ)
  rw [hsum.2 c γ hc hγ, hF.2 c γ hc hγ, hG.2 c γ hc hγ]
  exact regMatrixDirichletAverage_add hc hγ Z
    (hf.continuousOn.mono (convexHull_min (by rintro z ⟨⟨i, j⟩, rfl⟩; exact hZ i j) hΩc))
    (hg.continuousOn.mono (convexHull_min (by rintro z ⟨⟨i, j⟩, rfl⟩; exact hZ i j) hΩc))

/-- Multiplying a holomorphic scalar kernel by a constant commutes with matrix continuation. -/
theorem continuedRegMatrixDirichletAverage_smul
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) {Z : ι → κ → ℂ}
    (hZ : Z ∈ matrixNodeDomain Ω) (c : ℂ) (b : ι → ℂ) (β : κ → ℂ) :
    continuedRegMatrixDirichletAverage Z (fun z => c * f z) (b, β) =
      c * continuedRegMatrixDirichletAverage Z f (b, β) := by
  have hF := isRegMatrixContinuation_of_convex hΩo hΩc hf hZ
  have hcf : AnalyticOnNhd ℂ (fun z => c * f z) Ω := by
    intro z hz
    exact analyticAt_const.mul (hf z hz)
  have hmul := isRegMatrixContinuation_of_convex hΩo hΩc hcf hZ
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod hmul.1
    ((analyticOnNhd_const (v := c)).mul hF.1) ?_) (b, β)
  intro d γ hd hγ
  change continuedRegMatrixDirichletAverage Z (fun z => c * f z) (d, γ) =
    c * continuedRegMatrixDirichletAverage Z f (d, γ)
  rw [hmul.2 d γ hd hγ, hF.2 d γ hd hγ]
  exact regMatrixDirichletAverage_smul d γ Z f c

/-- Repeated columns merge at arbitrary complex parameters, including exceptional totals. -/
theorem continuedRegMatrixDirichletAverage_aggregate_columns
    {τ : Type*} [Fintype τ] {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) {q : κ → τ} (hq : Function.Surjective q)
    {Z : ι → τ → ℂ} (hZ : Z ∈ matrixNodeDomain Ω) (b : ι → ℂ) (β : κ → ℂ) :
    continuedRegMatrixDirichletAverage (fun i j => Z i (q j)) f (b, β) =
      continuedRegMatrixDirichletAverage Z f (b, stdSimplexAggregate q β) := by
  let L : (κ → ℂ) →L[ℂ] (τ → ℂ) :=
    ⟨FunOnFinite.linearMap ℂ ℂ q, continuous_stdSimplexAggregate q⟩
  have hmap : AnalyticOnNhd ℂ (fun p : (ι → ℂ) × (κ → ℂ) => (p.1, L p.2)) univ := by
    intro p _
    exact analyticAt_fst.prod (L.analyticAt p.2 |>.comp_of_eq analyticAt_snd rfl)
  have hF := isRegMatrixContinuation_of_convex hΩo hΩc hf (fun i j => hZ i (q j))
  have hG := isRegMatrixContinuation_of_convex hΩo hΩc hf hZ
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod hF.1
    (hG.1.comp hmap (fun _ _ => mem_univ _)) ?_) (b, β)
  intro c γ hc hγ
  change continuedRegMatrixDirichletAverage (fun i j => Z i (q j)) f (c, γ) =
    continuedRegMatrixDirichletAverage Z f (c, stdSimplexAggregate q γ)
  rw [hF.2 c γ hc hγ, hG.2 c _ hc (mvBetaConvergent_aggregate hq hγ)]
  exact regMatrixDirichletAverage_aggregate_columns c hγ hq Z
    (hf.continuousOn.mono (convexHull_min (by rintro z ⟨⟨i, j⟩, rfl⟩; exact hZ i j) hΩc))

/-- Repeated rows merge at arbitrary complex parameters by transpose symmetry. -/
theorem continuedRegMatrixDirichletAverage_aggregate_rows
    {τ : Type*} [Fintype τ] {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) {q : ι → τ} (hq : Function.Surjective q)
    {Z : τ → κ → ℂ} (hZ : Z ∈ matrixNodeDomain Ω) (b : ι → ℂ) (β : κ → ℂ) :
    continuedRegMatrixDirichletAverage (fun i j => Z (q i) j) f (b, β) =
      continuedRegMatrixDirichletAverage Z f (stdSimplexAggregate q b, β) := by
  rw [← continuedRegMatrixDirichletAverage_transpose hΩo hΩc hf
    (fun i j => hZ (q i) j) b β]
  rw [continuedRegMatrixDirichletAverage_aggregate_columns hΩo hΩc hf hq
    (fun i j => hZ j i) β b]
  exact continuedRegMatrixDirichletAverage_transpose hΩo hΩc hf hZ
    (stdSimplexAggregate q b) β

end Dirichlet
