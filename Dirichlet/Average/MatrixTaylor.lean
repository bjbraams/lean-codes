/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.MatrixContinuation
public import ToMathlib.Analysis.Analytic.ParameterTaylor

/-!
# Recognition of continued matrix power series

Holomorphic dependence on the nodes makes the scalar Taylor coefficients entire
in both parameter vectors. Thus a native power-series identity whose coefficients
are entire extends to all parameters, without first proving a uniform bound on
that series in parameter space. Mathlib's scalar Taylor theorem supplies convergence.
-/

open Complex Set
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Entire functions on two parameter spaces agree if they agree on the native region. -/
theorem analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod
    {F G : ((ι → ℂ) × (κ → ℂ)) → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (hG : AnalyticOnNhd ℂ G univ)
    (he : ∀ b β, b ∈ mvBetaConvergent → β ∈ mvBetaConvergent → F (b, β) = G (b, β)) :
    F = G := by
  have hfirst (β : κ → ℂ) (hβ : β ∈ mvBetaConvergent) (b : ι → ℂ) :
      F (b, β) = G (b, β) := by
    apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
      (hF.comp (analyticOnNhd_id.prod analyticOnNhd_const) (fun _ _ => mem_univ _))
      (hG.comp (analyticOnNhd_id.prod analyticOnNhd_const) (fun _ _ => mem_univ _))
      (fun c hc => he c β hc hβ)) b
  funext p
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (hF.comp (analyticOnNhd_const.prod analyticOnNhd_id) (fun _ _ => mem_univ _))
    (hG.comp (analyticOnNhd_const.prod analyticOnNhd_id) (fun _ _ => mem_univ _))
    (fun β hβ => hfirst β hβ p.1)) p.2

/-- Affine changes of matrix entries commute with the product-simplex affine form. -/
theorem matrixAffineForm_affine (Z : ι → κ → ℂ) (a t : ℂ)
    {u : ι → ℝ} {v : κ → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι)
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ κ) :
    matrixAffineForm (fun i j => a * Z i j + t) u v =
      a * matrixAffineForm Z u v + t := by
  have hu' : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
  have hv' : ∑ j, (v j : ℂ) = 1 := by exact_mod_cast hv.2
  have hrow (i : ι) : ∑ j, (u i : ℂ) * (a * Z i j + t) * (v j : ℂ) =
      a * (∑ j, (u i : ℂ) * Z i j * (v j : ℂ)) + (u i : ℂ) * t := by
    calc
      _ = a * (∑ j, (u i : ℂ) * Z i j * (v j : ℂ)) +
          (u i : ℂ) * t * (∑ j, (v j : ℂ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hv', mul_one]
  simp only [matrixAffineForm, hrow, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hu', one_mul]

/-- Radial scaling about one multiplies the shifted matrix moment by the same power. -/
theorem regMatrixDirichletAverage_radial_moment (b : ι → ℂ) (β : κ → ℂ)
    (Z : ι → κ → ℂ) (w : ℂ) (n : ℕ) :
    regMatrixDirichletAverage b β (fun i j => 1 + w * (Z i j - 1))
      (fun z => (1 - z) ^ n) =
        w ^ n * regMatrixDirichletAverage b β Z (fun z => (1 - z) ^ n) := by
  rw [← regMatrixDirichletAverage_smul]
  apply regDirichletIntegral_congr
  intro u hu
  dsimp only
  apply regDirichletIntegral_congr
  intro v hv
  dsimp only
  have he : (fun i j => 1 + w * (Z i j - 1)) = fun i j => w * Z i j + (1 - w) := by
    funext i j
    ring
  rw [he, matrixAffineForm_affine Z w (1 - w) hu hv]
  rw [show 1 - (w * matrixAffineForm Z u v + (1 - w)) =
    w * (1 - matrixAffineForm Z u v) by ring, mul_pow]

/-- Native scalar power series with entire coefficients represent the continued matrix
average on the same scalar disk, at arbitrary complex row and column parameters. -/
theorem hasSum_continuedRegMatrixDirichletAverage_of_native_series
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {R : ℝ} (hR : 0 < R) {Z : ℂ → ι → κ → ℂ}
    (hZa : AnalyticOnNhd ℂ Z (Metric.ball 0 R))
    (hZ : ∀ w : ℂ, ‖w‖ < R → Z w ∈ matrixNodeDomain Ω)
    {A : ℕ → ((ι → ℂ) × (κ → ℂ)) → ℂ}
    (hA : ∀ n, AnalyticOnNhd ℂ (A n) univ)
    (hAn : ∀ b β, b ∈ mvBetaConvergent → β ∈ mvBetaConvergent →
      ∀ w : ℂ, ‖w‖ < R → HasSum (fun n => A n (b, β) * w ^ n)
        (regMatrixDirichletAverage b β (Z w) f))
    (b : ι → ℂ) (β : κ → ℂ) {w : ℂ} (hw : ‖w‖ < R) :
    HasSum (fun n => A n (b, β) * w ^ n)
      (continuedRegMatrixDirichletAverage (Z w) f (b, β)) := by
  let F : (((ι → ℂ) × (κ → ℂ)) × ℂ) → ℂ := fun p =>
    continuedRegMatrixDirichletAverage (Z p.2) f (p.1.1, p.1.2)
  have hF : AnalyticOnNhd ℂ F (univ ×ˢ Metric.ball 0 R) := by
    intro p hp
    have hnode := hZ p.2 (by simpa using hp.2)
    have hfst : AnalyticAt ℂ (fun q : (((ι → ℂ) × (κ → ℂ)) × ℂ) => q.1.1) p :=
      analyticAt_fst.comp_of_eq analyticAt_fst rfl
    have hsnd : AnalyticAt ℂ (fun q : (((ι → ℂ) × (κ → ℂ)) × ℂ) => q.1.2) p :=
      analyticAt_snd.comp_of_eq analyticAt_fst rfl
    have hmap : AnalyticAt ℂ (fun q : (((ι → ℂ) × (κ → ℂ)) × ℂ) =>
        (q.1.1, q.1.2, Z q.2)) p :=
      hfst.prod (hsnd.prod ((hZa p.2 hp.2).comp_of_eq analyticAt_snd rfl))
    have H := (analyticOnNhd_continuedRegMatrixDirichletAverage hΩo hΩc hf
      (p.1.1, p.1.2, Z p.2) hnode).comp
        (f := fun q : (((ι → ℂ) × (κ → ℂ)) × ℂ) => (q.1.1, q.1.2, Z q.2)) hmap
    simpa only [F, Function.comp_def] using H
  have hc (n : ℕ) : (fun p => iteratedDeriv n (fun w => F (p, w)) 0 /
      (n.factorial : ℂ)) = A n := by
    apply analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod
      ((analyticOnNhd_iteratedDeriv_parameter hR hF n).div_const) (hA n)
    intro c γ hc hγ
    apply taylorCoeff_eq_of_hasSum hR
    intro v hv
    rw [show F ((c, γ), v) = regMatrixDirichletAverage c γ (Z v) f from
      continuedRegMatrixDirichletAverage_eq_native hΩo hΩc hf (hZ v hv) hc hγ]
    exact hAn c γ hc hγ v hv
  have hslice : DifferentiableOn ℂ (fun v => F ((b, β), v)) (Metric.ball 0 R) :=
    (hF.comp (analyticOnNhd_const.prod analyticOnNhd_id)
      (fun v hv => ⟨mem_univ _, hv⟩)).differentiableOn
  have ht := Complex.hasSum_taylorSeries_on_ball hslice (by simpa using hw)
  convert ht using 1
  funext n
  have hn := congrFun (hc n) (b, β)
  simp only [sub_zero, smul_eq_mul] at ht ⊢
  rw [← hn]
  ring

end Dirichlet
