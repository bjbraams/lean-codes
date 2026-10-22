/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.MatrixSeries
public import Dirichlet.Polynomial

/-!
# Separated kernels and binomial moments of matrix averages

Finite expansions into products of a row kernel and a column kernel may be
integrated termwise. Applying the binomial theorem gives the mixed moments
needed for the Appell `F₂` and `F₃` matrix identifications.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Finset
@[expose] public noncomputable section
namespace Dirichlet
variable {ι κ η : Type*} [Fintype ι] [Fintype κ]

/-- A separated product integrates to the product of the two regularized integrals. -/
theorem integral_regDirichletDensity_prod_separated (b : ι → ℂ) (β : κ → ℂ)
    (U : (ι → ℝ) → ℂ) (V : (κ → ℝ) → ℂ) (c : ℂ) :
    (∫ p, regDirichletDensity b p.1 * regDirichletDensity β p.2 * (c * U p.1 * V p.2)
      ∂((stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)).prod
        (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ κ)))) =
      c * regDirichletIntegral b U * regDirichletIntegral β V := by
  have he : (fun p : (ι → ℝ) × (κ → ℝ) =>
      regDirichletDensity b p.1 * regDirichletDensity β p.2 * (c * U p.1 * V p.2)) =
      fun p => c * ((regDirichletDensity b p.1 * U p.1) *
        (regDirichletDensity β p.2 * V p.2)) := by funext p; ring
  rw [he, integral_const_mul, mul_assoc c]
  apply congrArg (fun z => c * z)
  exact integral_prod_mul (fun u => regDirichletDensity b u * U u)
    (fun v => regDirichletDensity β v * V v)

/-- A finite expansion in separated continuous kernels gives a finite matrix-average formula. -/
theorem regMatrixDirichletAverage_eq_sum_separated {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (Z : ι → κ → ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2))))
    (s : Finset η) (c : η → ℂ) (U : η → (ι → ℝ) → ℂ) (V : η → (κ → ℝ) → ℂ)
    (hU : ∀ k ∈ s, ContinuousOn (U k) (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hV : ∀ k ∈ s, ContinuousOn (V k) (Convexity.StdSimplex.coordinateSet ℝ κ))
    (heq : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      ∀ v ∈ Convexity.StdSimplex.coordinateSet ℝ κ,
      f (matrixAffineForm Z u v) = ∑ k ∈ s, c k * U k u * V k v) :
    regMatrixDirichletAverage b β Z f =
      ∑ k ∈ s, c k * regDirichletIntegral b (U k) * regDirichletIntegral β (V k) := by
  rw [regMatrixDirichletAverage_eq_prodIntegral hb hβ Z hf]
  have he : (fun p : (ι → ℝ) × (κ → ℝ) =>
      regDirichletDensity b p.1 * regDirichletDensity β p.2 *
        f (matrixAffineForm Z p.1 p.2)) =ᵐ[
      (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)).prod
        (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ κ))]
      fun p => ∑ k ∈ s, regDirichletDensity b p.1 * regDirichletDensity β p.2 *
        (c k * U k p.1 * V k p.2) := by
    rw [Measure.prod_restrict]
    filter_upwards [self_mem_ae_restrict
      ((Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet.prod
        (Convexity.StdSimplex.isClosed_coordinateSet ℝ κ).measurableSet)] with p hp
    rw [heq p.1 hp.1 p.2 hp.2, Finset.mul_sum]
  rw [integral_congr_ae he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    exact integral_regDirichletDensity_prod_separated b β (U k) (V k) (c k)
  · intro k hk
    apply integrable_regDirichletDensity_prod_mul hb hβ
      (H := fun p => c k * U k p.1 * V k p.2)
    exact (continuousOn_const.mul ((hU k hk).comp continuousOn_fst (fun p (hp : p ∈
      Convexity.StdSimplex.coordinateSet ℝ ι ×ˢ
        Convexity.StdSimplex.coordinateSet ℝ κ) => hp.1))).mul
      ((hV k hk).comp continuousOn_snd (fun p (hp : p ∈
      Convexity.StdSimplex.coordinateSet ℝ ι ×ˢ
        Convexity.StdSimplex.coordinateSet ℝ κ) => hp.2))

/-- The binomial moment formula when `1 - matrixAffineForm` is a sum of two separated kernels. -/
theorem regMatrixDirichletAverage_binomial_moment {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (Z : ι → κ → ℂ) (U U' : (ι → ℝ) → ℂ) (V V' : (κ → ℝ) → ℂ)
    (hU : Continuous U) (hU' : Continuous U') (hV : Continuous V) (hV' : Continuous V')
    (heq : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      ∀ v ∈ Convexity.StdSimplex.coordinateSet ℝ κ,
      1 - matrixAffineForm Z u v = U u * V v + U' u * V' v) (N : ℕ) :
    regMatrixDirichletAverage b β Z (fun z => (1 - z) ^ N) =
      ∑ p ∈ antidiagonal N, (N.choose p.1 : ℂ) *
        regDirichletIntegral b (fun u => U u ^ p.1 * U' u ^ p.2) *
        regDirichletIntegral β (fun v => V v ^ p.1 * V' v ^ p.2) := by
  apply regMatrixDirichletAverage_eq_sum_separated hb hβ Z (by fun_prop)
    (antidiagonal N) (fun p => (N.choose p.1 : ℂ))
    (fun p u => U u ^ p.1 * U' u ^ p.2) (fun p v => V v ^ p.1 * V' v ^ p.2)
    (fun p _ => ((hU.pow _).mul (hU'.pow _)).continuousOn)
    (fun p _ => ((hV.pow _).mul (hV'.pow _)).continuousOn)
  intro u hu v hv
  rw [heq u hu v hv, (Commute.all (U u * V v) (U' u * V' v)).add_pow']
  apply Finset.sum_congr rfl
  intro p _
  simp only [nsmul_eq_mul, mul_pow]
  ring

/-- The moment of the first coordinate in a two-node regularized Dirichlet integral. -/
theorem regDirichletIntegral_fin_two_pow {b : Fin 2 → ℂ} (hb : b ∈ mvBetaConvergent)
    (n : ℕ) :
    regDirichletIntegral b (fun u => (u 0 : ℂ) ^ n) =
      (ascPochhammer ℂ n).eval (b 0) / Gamma (b 0 + b 1 + n) := by
  have h := regDirichletIntegral_monomial hb ![n, 0]
  simpa [regDirichletMonomialTransform, mvPochhammer, Fin.sum_univ_two,
    Fin.prod_univ_two, div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using h

/-- The mixed moment of two coordinates in a three-node regularized Dirichlet integral. -/
theorem regDirichletIntegral_fin_three_pow_mul {b : Fin 3 → ℂ}
    (hb : b ∈ mvBetaConvergent) (m n : ℕ) :
    regDirichletIntegral b (fun u => (u 0 : ℂ) ^ m * (u 1 : ℂ) ^ n) =
      (ascPochhammer ℂ m).eval (b 0) * (ascPochhammer ℂ n).eval (b 1) /
        Gamma (b 0 + b 1 + b 2 + (m + n : ℕ)) := by
  have h := regDirichletIntegral_monomial hb ![m, n, 0]
  have hs : ∑ i, (b i + (![m, n, 0] i : ℂ)) = b 0 + b 1 + b 2 + (m + n : ℕ) := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    ring
  simpa [regDirichletMonomialTransform, mvPochhammer, Fin.prod_univ_three, hs,
    div_eq_mul_inv] using h

end Dirichlet
