/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.MatrixIdentities
public import Carlson.RPolynomial.GeneratingIdentities

/-!
# Homogeneity of continued matrix power averages

The local principal-power multiplication theorem for positive real parts
(`mul_cpow_of_re_pos`) supplies the native identity. Entire dependence on
both parameter vectors extends it, with both matrix node domains explicit.
-/

open Complex Set Dirichlet
@[expose] public noncomputable section
namespace Carlson
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Native matrix homogeneity when the scalar and unscaled affine values have positive real part. -/
private theorem native_matrix_homogeneity (r : ι → ℂ) (β : κ → ℂ)
    {Z : ι → κ → ℂ} (hZ : Z ∈ matrixNodeDomain carlsonRightHalfPlane)
    {μ : ℂ} (hμ : 0 < μ.re) (a : ℂ) :
    regMatrixDirichletAverage r β (fun i j => μ * Z i j) (fun z => z ^ (-a)) =
      μ ^ (-a) * regMatrixDirichletAverage r β Z (fun z => z ^ (-a)) := by
  rw [← regMatrixDirichletAverage_smul]
  apply regDirichletIntegral_congr
  intro u hu
  apply regDirichletIntegral_congr
  intro v hv
  have he : matrixAffineForm (fun i j => μ * Z i j) u v = μ * matrixAffineForm Z u v := by
    simpa only [add_zero] using matrixAffineForm_affine Z μ 0 hu hv
  have hz : matrixAffineForm Z u v ∈ carlsonRightHalfPlane :=
    (convexHull_min (by rintro z ⟨⟨i, j⟩, rfl⟩; exact hZ i j)
      convex_carlsonRightHalfPlane) (matrixAffineForm_mem_convexHull Z hu hv)
  change (matrixAffineForm (fun i j => μ * Z i j) u v) ^ (-a) =
    μ ^ (-a) * (matrixAffineForm Z u v) ^ (-a)
  rw [he, mul_cpow_of_re_pos hμ hz (-a)]

/-- Homogeneity of the continued regularized power average, with explicit branch domains.
Both the original and scaled matrices must have entries in the right half-plane. -/
theorem continuedRegMatrixDirichletAverage_mul_cpow_neg
    (r : ι → ℂ) (β : κ → ℂ) {Z : ι → κ → ℂ}
    (hZ : Z ∈ matrixNodeDomain carlsonRightHalfPlane) {μ : ℂ} (hμ : 0 < μ.re)
    (hμZ : (fun i j => μ * Z i j) ∈ matrixNodeDomain carlsonRightHalfPlane) (a : ℂ) :
    continuedRegMatrixDirichletAverage (fun i j => μ * Z i j) (fun z => z ^ (-a)) (r, β) =
      μ ^ (-a) * continuedRegMatrixDirichletAverage Z (fun z => z ^ (-a)) (r, β) := by
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => z ^ (-a)) carlsonRightHalfPlane :=
    fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz)
  have hF := isRegMatrixContinuation_of_convex isOpen_carlsonRightHalfPlane
    convex_carlsonRightHalfPlane hf hμZ
  have hG := isRegMatrixContinuation_of_convex isOpen_carlsonRightHalfPlane
    convex_carlsonRightHalfPlane hf hZ
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod hF.1
    (analyticOnNhd_const.mul hG.1) ?_) (r, β)
  intro s γ hs hγ
  rw [hF.2 s γ hs hγ, hG.2 s γ hs hγ]
  exact native_matrix_homogeneity s γ hZ hμ a

end Carlson
