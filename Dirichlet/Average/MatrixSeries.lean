/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Matrix
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Power series of matrix double averages

Carlson (1971), Section 6, especially (6.2). A scalar power series may be averaged
term by term whenever its absolute majorant is summable on a closed disk containing
the matrix entries. Its coefficients are the double averages of the shifted powers.
The product-measure formulation also gives additivity without assuming continuity
of an iterated integral outside the simplex. Only native convergent parameters are used.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped Topology

@[expose] public noncomputable section
namespace Dirichlet
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The iterated matrix average equals the integral against the product of its densities. -/
theorem regMatrixDirichletAverage_eq_prodIntegral {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (Z : ι → κ → ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2)))) :
    regMatrixDirichletAverage b β Z f =
      ∫ p, regDirichletDensity b p.1 * regDirichletDensity β p.2 *
        f (matrixAffineForm Z p.1 p.2)
        ∂((stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)).prod
          (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ κ))) := by
  rw [integral_prod _
    (integrable_regDirichletDensity_prod_mul hb hβ (continuousOn_matrix_kernel hf))]
  simp only [regMatrixDirichletAverage, regDirichletIntegral,
    ← integral_const_mul, mul_assoc]

/-- A matrix double average is additive for continuous kernels in the convergence region. -/
theorem regMatrixDirichletAverage_add {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (Z : ι → κ → ℂ) {f g : ℂ → ℂ}
    (hf : ContinuousOn f (convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2))))
    (hg : ContinuousOn g (convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2)))) :
    regMatrixDirichletAverage b β Z (fun z => f z + g z) =
      regMatrixDirichletAverage b β Z f + regMatrixDirichletAverage b β Z g := by
  rw [regMatrixDirichletAverage_eq_prodIntegral hb hβ Z
      (f := fun z => f z + g z) (hf.add hg),
    regMatrixDirichletAverage_eq_prodIntegral hb hβ Z hf,
    regMatrixDirichletAverage_eq_prodIntegral hb hβ Z hg]
  simp_rw [mul_add]
  exact integral_add
    (integrable_regDirichletDensity_prod_mul hb hβ (continuousOn_matrix_kernel hf))
    (integrable_regDirichletDensity_prod_mul hb hβ (continuousOn_matrix_kernel hg))

/-- Uniform summable domination permits termwise matrix double averaging. -/
theorem hasSum_regMatrixDirichletAverage {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (Z : ι → κ → ℂ) (g : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (M : ℕ → ℝ)
    (hg : ∀ n, ContinuousOn (g n) (convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2))))
    (hf : ContinuousOn f (convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2))))
    (hM : Summable M)
    (hbound : ∀ n z, z ∈ convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2)) →
      ‖g n z‖ ≤ M n)
    (hsum : ∀ z, z ∈ convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2)) →
      HasSum (fun n => g n z) (f z)) :
    HasSum (fun n => regMatrixDirichletAverage b β Z (g n))
      (regMatrixDirichletAverage b β Z f) := by
  let μ := (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)).prod
    (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ κ))
  let d : (ι → ℝ) × (κ → ℝ) → ℂ :=
    fun p => regDirichletDensity b p.1 * regDirichletDensity β p.2
  let F : ℕ → (ι → ℝ) × (κ → ℝ) → ℂ :=
    fun n p => d p * g n (matrixAffineForm Z p.1 p.2)
  let B : ℕ → (ι → ℝ) × (κ → ℝ) → ℝ := fun n p => M n * ‖d p‖
  have hd : Integrable d μ := (integrableOn_regDirichletDensity b hb).mul_prod
    (integrableOn_regDirichletDensity β hβ)
  have hmem : ∀ᵐ p ∂μ, p.1 ∈ Convexity.StdSimplex.coordinateSet ℝ ι ∧
      p.2 ∈ Convexity.StdSimplex.coordinateSet ℝ κ := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact self_mem_ae_restrict
      ((Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet.prod
        (Convexity.StdSimplex.isClosed_coordinateSet ℝ κ).measurableSet)
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    (integrable_regDirichletDensity_prod_mul hb hβ (continuousOn_matrix_kernel (hg n))).1
  have hB (n : ℕ) : ∀ᵐ p ∂μ, ‖F n p‖ ≤ B n p := by
    filter_upwards [hmem] with p hp
    dsimp only [F, B]
    rw [norm_mul, mul_comm (M n)]
    exact mul_le_mul_of_nonneg_left
      (hbound n _ (matrixAffineForm_mem_convexHull Z hp.1 hp.2)) (norm_nonneg _)
  have hBs : ∀ᵐ p ∂μ, Summable fun n => B n p := by
    filter_upwards with p
    exact hM.mul_right _
  have hBi : Integrable (fun p => ∑' n, B n p) μ := by
    simp only [B, tsum_mul_right]
    exact hd.norm.const_mul _
  have hlim : ∀ᵐ p ∂μ, HasSum (fun n => F n p)
      (d p * f (matrixAffineForm Z p.1 p.2)) := by
    filter_upwards [hmem] with p hp
    exact (hsum _ (matrixAffineForm_mem_convexHull Z hp.1 hp.2)).mul_left (d p)
  have h := hasSum_integral_of_dominated_convergence B hmeas hB hBs hBi hlim
  simpa only [F, d, μ, ← regMatrixDirichletAverage_eq_prodIntegral hb hβ Z hf,
    ← regMatrixDirichletAverage_eq_prodIntegral hb hβ Z (hg _)] using h

/-- **Carlson (1971), (6.2).** A power series on a disk containing the entries
has a matrix-average expansion whose coefficients are the averaged shifted powers. -/
theorem hasSum_regMatrixDirichletAverage_powerSeries {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (Z : ι → κ → ℂ) (a : ℕ → ℂ) (c : ℂ) (r : ℝ)
    (hZ : ∀ i j, ‖Z i j - c‖ ≤ r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall c r))
    (hM : Summable (fun n => ‖a n‖ * r ^ n))
    (hsum : ∀ z ∈ Metric.closedBall c r,
      HasSum (fun n => a n * (z - c) ^ n) (f z)) :
    HasSum (fun n => a n *
      regMatrixDirichletAverage b β Z (fun z => (z - c) ^ n))
      (regMatrixDirichletAverage b β Z f) := by
  have hball : convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2)) ⊆
      Metric.closedBall c r := by
    apply convexHull_min _ (convex_closedBall c r)
    rintro z ⟨⟨i, j⟩, rfl⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hZ i j
  have h := hasSum_regMatrixDirichletAverage hb hβ Z (fun n z => a n * (z - c) ^ n)
    f (fun n => ‖a n‖ * r ^ n) (fun n => by fun_prop) (hf.mono hball) hM
    (fun n z hz => by
      rw [norm_mul, norm_pow]
      have hz' : ‖z - c‖ ≤ r := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hball hz
      gcongr) (fun z hz => hsum z (hball hz))
  simpa only [regMatrixDirichletAverage_smul] using h

/-- The normalized power-series expansion, with the same native parameter domain. -/
theorem hasSum_matrixDirichletAverage_powerSeries {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (Z : ι → κ → ℂ) (a : ℕ → ℂ) (c : ℂ) (r : ℝ)
    (hZ : ∀ i j, ‖Z i j - c‖ ≤ r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall c r))
    (hM : Summable (fun n => ‖a n‖ * r ^ n))
    (hsum : ∀ z ∈ Metric.closedBall c r,
      HasSum (fun n => a n * (z - c) ^ n) (f z)) :
    HasSum (fun n => a n * matrixDirichletAverage b β Z (fun z => (z - c) ^ n))
      (matrixDirichletAverage b β Z f) := by
  have h := hasSum_regMatrixDirichletAverage_powerSeries hb hβ Z a c r hZ hf hM hsum
  have h' := h.mul_left (Gamma (∑ i, b i) * Gamma (∑ j, β j))
  simpa only [matrixDirichletAverage, mul_left_comm] using h'

/-- For a rank-one matrix the affine form factors into the row and column affine forms. -/
theorem matrixAffineForm_mul (z : ι → ℂ) (w : κ → ℂ) (u : ι → ℝ) (v : κ → ℝ) :
    matrixAffineForm (fun i j => z i * w j) u v =
      carlsonAffineForm z u * carlsonAffineForm w v := by
  unfold matrixAffineForm carlsonAffineForm
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Carlson (1971), (6.5), polynomial case.** Rank-one matrix moments factor
into two single-average moments. No branch restriction is needed for natural powers. -/
theorem regMatrixDirichletAverage_mul_pow (b : ι → ℂ) (β : κ → ℂ)
    (z : ι → ℂ) (w : κ → ℂ) (n : ℕ) :
    regMatrixDirichletAverage b β (fun i j => z i * w j) (fun t => t ^ n) =
      regCarlsonDirichletAverage b z (fun t => t ^ n) *
        regCarlsonDirichletAverage β w (fun t => t ^ n) := by
  simp only [regMatrixDirichletAverage, matrixAffineForm_mul, mul_pow,
    regDirichletIntegral_smul]
  simp only [regCarlsonDirichletAverage, regDirichletIntegral, ← mul_assoc,
    integral_mul_const]

/-- The normalized rank-one polynomial moment is the product of the two normalized moments. -/
theorem matrixDirichletAverage_mul_pow (b : ι → ℂ) (β : κ → ℂ)
    (z : ι → ℂ) (w : κ → ℂ) (n : ℕ) :
    matrixDirichletAverage b β (fun i j => z i * w j) (fun t => t ^ n) =
      carlsonDirichletAverage b z (fun t => t ^ n) *
        carlsonDirichletAverage β w (fun t => t ^ n) := by
  rw [matrixDirichletAverage, regMatrixDirichletAverage_mul_pow]
  simp only [carlsonDirichletAverage]
  ring

end Dirichlet
