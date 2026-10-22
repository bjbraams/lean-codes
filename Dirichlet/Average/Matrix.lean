/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Basic
public import Dirichlet.Average.Aggregation
public import Dirichlet.Transform.Laws
public import Dirichlet.Complex.Aggregation
public import Dirichlet.Bridge
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Matrix double Dirichlet averages

Carlson (1971), *Appell functions and multiple averages*, Section 2. Independent
Dirichlet weights on the rows and columns average `f (∑ i, ∑ j, u i * Z i j * v j)`.
These are native integrals, regularized by both total-parameter Gamma factors;
no continuation to arbitrary cut-plane matrix entries is implicit in the definition.
Continuous kernels on the convex hull of the entries suffice for Fubini and transpose
symmetry. Row and column permutations, aggregation of repeated rows and columns,
and the one-row/one-column reductions express the basic matrix structure.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped Topology

@[expose] public noncomputable section
namespace Dirichlet
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

/-- The bilinear affine combination of the entries of a matrix. -/
def matrixAffineForm (Z : ι → κ → ℂ) (u : ι → ℝ) (v : κ → ℝ) : ℂ :=
  ∑ i, ∑ j, (u i : ℂ) * Z i j * (v j : ℂ)

/-- The native matrix double average, divided by the two total-parameter Gamma factors. -/
def regMatrixDirichletAverage (b : ι → ℂ) (β : κ → ℂ)
    (Z : ι → κ → ℂ) (f : ℂ → ℂ) : ℂ :=
  regDirichletIntegral b (fun u =>
    regDirichletIntegral β (fun v => f (matrixAffineForm Z u v)))

/-- The normalized matrix double average on the native convergence region. -/
def matrixDirichletAverage (b : ι → ℂ) (β : κ → ℂ)
    (Z : ι → κ → ℂ) (f : ℂ → ℂ) : ℂ :=
  (Gamma (∑ i, b i) * Gamma (∑ j, β j)) * regMatrixDirichletAverage b β Z f

/-- The matrix affine combination depends continuously on both simplex weights. -/
theorem continuous_matrixAffineForm (Z : ι → κ → ℂ) :
    Continuous (fun p : (ι → ℝ) × (κ → ℝ) => matrixAffineForm Z p.1 p.2) := by
  unfold matrixAffineForm
  fun_prop

/-- Transposing the matrix and interchanging the weights leaves its affine form unchanged. -/
theorem matrixAffineForm_transpose (Z : ι → κ → ℂ) (u : ι → ℝ) (v : κ → ℝ) :
    matrixAffineForm (fun j i => Z i j) v u = matrixAffineForm Z u v := by
  unfold matrixAffineForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Each matrix affine combination is a convex combination of all its entries. -/
theorem matrixAffineForm_mem_convexHull (Z : ι → κ → ℂ)
    {u : ι → ℝ} {v : κ → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι)
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ κ) :
    matrixAffineForm Z u v ∈ convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2)) := by
  have h := (convex_convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2))).sum_mem
    (t := Finset.univ) (w := fun p : ι × κ => u p.1 * v p.2)
    (z := fun p : ι × κ => Z p.1 p.2)
    (fun p _ => mul_nonneg (hu.1 _) (hv.1 _))
    (by rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, hu.2, hv.2, mul_one])
    (fun p _ => subset_convexHull ℝ _ ⟨p, rfl⟩)
  convert h using 1
  simp only [matrixAffineForm, Fintype.sum_prod_type, Complex.real_smul, ofReal_mul]
  congr 1
  ext i
  congr 1
  ext j
  ring

/-- A continuous kernel on the entry convex hull is continuous on the product simplex. -/
theorem continuousOn_matrix_kernel {Z : ι → κ → ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2)))) :
    ContinuousOn (fun p : (ι → ℝ) × (κ → ℝ) => f (matrixAffineForm Z p.1 p.2))
      (Convexity.StdSimplex.coordinateSet ℝ ι ×ˢ
        Convexity.StdSimplex.coordinateSet ℝ κ) :=
  hf.comp (continuous_matrixAffineForm Z).continuousOn
    (fun _ hp => matrixAffineForm_mem_convexHull Z hp.1 hp.2)

/-- Product integrability of a continuous kernel with the two regularized densities. -/
theorem integrable_regDirichletDensity_prod_mul {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    {H : (ι → ℝ) × (κ → ℝ) → ℂ}
    (hH : ContinuousOn H (Convexity.StdSimplex.coordinateSet ℝ ι ×ˢ
      Convexity.StdSimplex.coordinateSet ℝ κ)) :
    Integrable (fun p => regDirichletDensity b p.1 * regDirichletDensity β p.2 * H p)
      ((stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)).prod
        (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ κ))) := by
  have hd := (integrableOn_regDirichletDensity b hb).mul_prod
    (integrableOn_regDirichletDensity β hβ)
  rw [Measure.prod_restrict] at hd ⊢
  exact IntegrableOn.mul_continuousOn hd hH
    ((Convexity.StdSimplex.isCompact_coordinateSet ℝ ι).prod
      (Convexity.StdSimplex.isCompact_coordinateSet ℝ κ))

/-- Fubini for two independent regularized Dirichlet integrals. -/
theorem regDirichletIntegral_swap {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    {H : (ι → ℝ) × (κ → ℝ) → ℂ}
    (hH : ContinuousOn H (Convexity.StdSimplex.coordinateSet ℝ ι ×ˢ
      Convexity.StdSimplex.coordinateSet ℝ κ)) :
    regDirichletIntegral b (fun u => regDirichletIntegral β (fun v => H (u, v))) =
      regDirichletIntegral β (fun v => regDirichletIntegral b (fun u => H (u, v))) := by
  have hi := integrable_regDirichletDensity_prod_mul hb hβ hH
  unfold regDirichletIntegral
  simp_rw [← integral_const_mul]
  calc
    _ = ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
        ∫ v in Convexity.StdSimplex.coordinateSet ℝ κ,
          regDirichletDensity b u * regDirichletDensity β v * H (u, v)
            ∂stdSimplexMeasure ∂stdSimplexMeasure := by simp only [mul_assoc]
    _ = ∫ v in Convexity.StdSimplex.coordinateSet ℝ κ,
        ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
          regDirichletDensity b u * regDirichletDensity β v * H (u, v)
            ∂stdSimplexMeasure ∂stdSimplexMeasure := integral_integral_swap hi
    _ = _ := by simp only [mul_left_comm (regDirichletDensity b _), mul_assoc]

/-- **Carlson (1971), (2.9)(iii).** Transposition symmetry of the regularized double average. -/
theorem regMatrixDirichletAverage_transpose {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (Z : ι → κ → ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2)))) :
    regMatrixDirichletAverage b β Z f =
      regMatrixDirichletAverage β b (fun j i => Z i j) f := by
  unfold regMatrixDirichletAverage
  rw [regDirichletIntegral_swap hb hβ (continuousOn_matrix_kernel hf)]
  simp_rw [matrixAffineForm_transpose]

/-- **Carlson (1971), (2.9)(iii).** Transposition also preserves the normalized double average. -/
theorem matrixDirichletAverage_transpose {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (Z : ι → κ → ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2)))) :
    matrixDirichletAverage b β Z f = matrixDirichletAverage β b (fun j i => Z i j) f := by
  rw [matrixDirichletAverage, matrixDirichletAverage,
    regMatrixDirichletAverage_transpose hb hβ Z hf, mul_comm (Gamma (∑ i, b i))]

/-- Permuting rows and their weights leaves the matrix affine form unchanged. -/
theorem matrixAffineForm_perm_rows (Z : ι → κ → ℂ) (σ : Equiv.Perm ι)
    (u : ι → ℝ) (v : κ → ℝ) :
    matrixAffineForm (fun i j => Z (σ i) j) (u ∘ σ) v = matrixAffineForm Z u v := by
  simpa only [matrixAffineForm, Function.comp_apply] using
    Equiv.sum_comp σ (fun i => ∑ j, (u i : ℂ) * Z i j * (v j : ℂ))

/-- Permuting columns and their weights leaves the matrix affine form unchanged. -/
theorem matrixAffineForm_perm_columns (Z : ι → κ → ℂ) (σ : Equiv.Perm κ)
    (u : ι → ℝ) (v : κ → ℝ) :
    matrixAffineForm (fun i j => Z i (σ j)) u (v ∘ σ) = matrixAffineForm Z u v := by
  unfold matrixAffineForm
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp σ (fun j => (u i : ℂ) * Z i j * (v j : ℂ))

/-- **Carlson (1971), (2.9)(i).** Simultaneously permuting rows and their parameters
preserves the native regularized matrix average, even as a totalized integral. -/
theorem regMatrixDirichletAverage_perm_rows (b : ι → ℂ) (β : κ → ℂ)
    (Z : ι → κ → ℂ) (f : ℂ → ℂ) (σ : Equiv.Perm ι) :
    regMatrixDirichletAverage (b ∘ σ) β (fun i j => Z (σ i) j) f =
      regMatrixDirichletAverage b β Z f := by
  unfold regMatrixDirichletAverage
  change (∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
    regDirichletDensity (b ∘ σ) u *
      regDirichletIntegral β (fun v => f (matrixAffineForm (fun i j => Z (σ i) j) u v))
        ∂stdSimplexMeasure) = _
  rw [← integral_stdSimplex_comp_perm σ]
  simp only [regDirichletDensity_perm, matrixAffineForm_perm_rows]
  rfl

/-- **Carlson (1971), (2.9)(ii).** Column symmetry of the regularized matrix average. -/
theorem regMatrixDirichletAverage_perm_columns (b : ι → ℂ) (β : κ → ℂ)
    (Z : ι → κ → ℂ) (f : ℂ → ℂ) (σ : Equiv.Perm κ) :
    regMatrixDirichletAverage b (β ∘ σ) (fun i j => Z i (σ j)) f =
      regMatrixDirichletAverage b β Z f := by
  unfold regMatrixDirichletAverage
  congr 1
  funext u
  unfold regDirichletIntegral
  rw [← integral_stdSimplex_comp_perm σ]
  simp only [regDirichletDensity_perm, matrixAffineForm_perm_columns]

/-- A constant simplex kernel integrates to its reciprocal total Gamma factor. -/
theorem regDirichletIntegral_const {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (c : ℂ) :
    regDirichletIntegral b (fun _ => c) = c / Gamma (∑ i, b i) := by
  unfold regDirichletIntegral
  rw [integral_mul_const, regDirichletIntegral_normalization b hb]
  ring

/-- If all rows coincide, only the column average remains. -/
theorem regMatrixDirichletAverage_identical_rows {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (β : κ → ℂ) (z : κ → ℂ) (f : ℂ → ℂ) :
    regMatrixDirichletAverage b β (fun _ j => z j) f =
      regCarlsonDirichletAverage β z f / Gamma (∑ i, b i) := by
  unfold regMatrixDirichletAverage
  rw [regDirichletIntegral_congr b (g := fun _ => regCarlsonDirichletAverage β z f)]
  · exact regDirichletIntegral_const hb _
  intro u hu
  apply regDirichletIntegral_congr
  intro v _
  change f (matrixAffineForm (fun _ j => z j) u v) = f (carlsonAffineForm z v)
  apply congrArg f
  simp only [matrixAffineForm, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  have hsum : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
  rw [hsum, one_mul]
  simp only [carlsonAffineForm, mul_comm]

/-- If all columns coincide, only the row average remains. -/
theorem regMatrixDirichletAverage_identical_columns (b : ι → ℂ)
    {β : κ → ℂ} (hβ : β ∈ mvBetaConvergent) (z : ι → ℂ) (f : ℂ → ℂ) :
    regMatrixDirichletAverage b β (fun i _ => z i) f =
      regCarlsonDirichletAverage b z f / Gamma (∑ j, β j) := by
  unfold regMatrixDirichletAverage
  have he (u : ι → ℝ) :
      regDirichletIntegral β (fun v => f (matrixAffineForm (fun i _ => z i) u v)) =
        f (carlsonAffineForm z u) / Gamma (∑ j, β j) := by
    rw [regDirichletIntegral_congr β (g := fun _ => f (carlsonAffineForm z u))]
    · exact regDirichletIntegral_const hβ _
    intro v hv
    simp only [matrixAffineForm, ← Finset.mul_sum]
    have hsum : ∑ j, (v j : ℂ) = 1 := by exact_mod_cast hv.2
    simp only [hsum, mul_one, carlsonAffineForm]
  simp_rw [he, div_eq_mul_inv]
  simp only [regCarlsonDirichletAverage, regDirichletIntegral,
    ← mul_assoc, integral_mul_const]

/-- **Carlson (1971), (2.7)** in regularized form. -/
theorem regMatrixDirichletAverage_const {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent) (w : ℂ) (f : ℂ → ℂ) :
    regMatrixDirichletAverage b β (fun _ _ => w) f =
      f w / (Gamma (∑ i, b i) * Gamma (∑ j, β j)) := by
  rw [regMatrixDirichletAverage_identical_rows hb, regCarlsonDirichletAverage_const f w hβ]
  ring

/-- The matrix affine form commutes with grouping equal columns. -/
theorem matrixAffineForm_aggregate_columns (q : κ → τ) (Z : ι → τ → ℂ)
    (u : ι → ℝ) (v : κ → ℝ) :
    matrixAffineForm (fun i j => Z i (q j)) u v =
      matrixAffineForm Z u (stdSimplexAggregate q v) := by
  unfold matrixAffineForm
  apply Finset.sum_congr rfl
  intro i _
  have h := carlsonAffineForm_aggregate q (fun j => (u i : ℂ) * Z i j) v
  simpa only [carlsonAffineForm, Function.comp_apply, mul_comm, mul_left_comm, mul_assoc]
    using h.symm

/-- Repeated columns may be merged, adding their parameters along any surjective partition. -/
theorem regMatrixDirichletAverage_aggregate_columns (b : ι → ℂ) {β : κ → ℂ}
    (hβ : β ∈ mvBetaConvergent) {q : κ → τ} (hq : Function.Surjective q)
    (Z : ι → τ → ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (convexHull ℝ (range (fun p : ι × τ => Z p.1 p.2)))) :
    regMatrixDirichletAverage b β (fun i j => Z i (q j)) f =
      regMatrixDirichletAverage b (stdSimplexAggregate q β) Z f := by
  unfold regMatrixDirichletAverage
  apply regDirichletIntegral_congr
  intro u hu
  simp_rw [matrixAffineForm_aggregate_columns]
  apply regDirichletIntegral_aggregate hq hβ
    (g := fun v => f (matrixAffineForm Z u v))
  exact hf.comp ((continuous_matrixAffineForm Z).comp
    (continuous_const.prodMk continuous_id)).continuousOn
    (fun v hv => matrixAffineForm_mem_convexHull Z hu hv)

/-- Repeated rows may likewise be merged, with their parameters summed. -/
theorem regMatrixDirichletAverage_aggregate_rows {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    {q : ι → τ} (hq : Function.Surjective q) (Z : τ → κ → ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (convexHull ℝ (range (fun p : τ × κ => Z p.1 p.2)))) :
    regMatrixDirichletAverage b β (fun i j => Z (q i) j) f =
      regMatrixDirichletAverage (stdSimplexAggregate q b) β Z f := by
  have hrange : range (fun p : ι × κ => Z (q p.1) p.2) =
      range (fun p : τ × κ => Z p.1 p.2) := by
    ext z
    constructor
    · rintro ⟨⟨i, j⟩, rfl⟩; exact ⟨(q i, j), rfl⟩
    · rintro ⟨⟨i, j⟩, rfl⟩
      obtain ⟨k, rfl⟩ := hq i
      exact ⟨(k, j), rfl⟩
  have htranspose : range (fun p : κ × τ => Z p.2 p.1) =
      range (fun p : τ × κ => Z p.1 p.2) := by
    ext z
    constructor <;> rintro ⟨⟨i, j⟩, rfl⟩ <;> exact ⟨(j, i), rfl⟩
  rw [regMatrixDirichletAverage_transpose hb hβ _ (by simpa only [hrange] using hf),
    regMatrixDirichletAverage_aggregate_columns β hb hq (fun j i => Z i j)
      (by simpa only [htranspose] using hf),
    ← regMatrixDirichletAverage_transpose (mvBetaConvergent_aggregate hq hb) hβ Z hf]

/-- Matrix averaging commutes with multiplication of the kernel by a scalar. -/
theorem regMatrixDirichletAverage_smul (b : ι → ℂ) (β : κ → ℂ)
    (Z : ι → κ → ℂ) (f : ℂ → ℂ) (c : ℂ) :
    regMatrixDirichletAverage b β Z (fun z => c * f z) =
      c * regMatrixDirichletAverage b β Z f := by
  simp only [regMatrixDirichletAverage, regDirichletIntegral_smul]

/-- Row symmetry of the normalized matrix double average. -/
theorem matrixDirichletAverage_perm_rows (b : ι → ℂ) (β : κ → ℂ)
    (Z : ι → κ → ℂ) (f : ℂ → ℂ) (σ : Equiv.Perm ι) :
    matrixDirichletAverage (b ∘ σ) β (fun i j => Z (σ i) j) f =
      matrixDirichletAverage b β Z f := by
  simp only [matrixDirichletAverage, regMatrixDirichletAverage_perm_rows,
    Function.comp_apply, Equiv.sum_comp σ b]

/-- Column symmetry of the normalized matrix double average. -/
theorem matrixDirichletAverage_perm_columns (b : ι → ℂ) (β : κ → ℂ)
    (Z : ι → κ → ℂ) (f : ℂ → ℂ) (σ : Equiv.Perm κ) :
    matrixDirichletAverage b (β ∘ σ) (fun i j => Z i (σ j)) f =
      matrixDirichletAverage b β Z f := by
  simp only [matrixDirichletAverage, regMatrixDirichletAverage_perm_columns,
    Function.comp_apply, Equiv.sum_comp σ β]

/-- The normalized average of repeated rows is the single column average. -/
theorem matrixDirichletAverage_identical_rows [Nonempty ι] {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (β : κ → ℂ) (z : κ → ℂ) (f : ℂ → ℂ) :
    matrixDirichletAverage b β (fun _ j => z j) f = carlsonDirichletAverage β z f := by
  rw [matrixDirichletAverage, regMatrixDirichletAverage_identical_rows hb,
    carlsonDirichletAverage]
  field_simp [Gamma_ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hb)]

/-- The normalized average of repeated columns is the single row average. -/
theorem matrixDirichletAverage_identical_columns [Nonempty κ] (b : ι → ℂ)
    {β : κ → ℂ} (hβ : β ∈ mvBetaConvergent) (z : ι → ℂ) (f : ℂ → ℂ) :
    matrixDirichletAverage b β (fun i _ => z i) f = carlsonDirichletAverage b z f := by
  rw [matrixDirichletAverage, regMatrixDirichletAverage_identical_columns b hβ,
    carlsonDirichletAverage]
  field_simp [Gamma_ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hβ)]

/-- **Carlson (1971), (2.7).** A normalized constant matrix average equals the kernel value. -/
theorem matrixDirichletAverage_const [Nonempty ι] [Nonempty κ]
    {b : ι → ℂ} {β : κ → ℂ} (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (w : ℂ) (f : ℂ → ℂ) :
    matrixDirichletAverage b β (fun _ _ => w) f = f w := by
  rw [matrixDirichletAverage, regMatrixDirichletAverage_const hb hβ]
  field_simp [Gamma_ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hb),
    Gamma_ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hβ)]

/-- Grouping equal columns preserves the normalized double average. -/
theorem matrixDirichletAverage_aggregate_columns (b : ι → ℂ) {β : κ → ℂ}
    (hβ : β ∈ mvBetaConvergent) {q : κ → τ} (hq : Function.Surjective q)
    (Z : ι → τ → ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (convexHull ℝ (range (fun p : ι × τ => Z p.1 p.2)))) :
    matrixDirichletAverage b β (fun i j => Z i (q j)) f =
      matrixDirichletAverage b (stdSimplexAggregate q β) Z f := by
  simp only [matrixDirichletAverage,
    regMatrixDirichletAverage_aggregate_columns b hβ hq Z hf,
    sum_aggregate_dirichletParameters]

/-- Grouping equal rows preserves the normalized double average. -/
theorem matrixDirichletAverage_aggregate_rows {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    {q : ι → τ} (hq : Function.Surjective q) (Z : τ → κ → ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (convexHull ℝ (range (fun p : τ × κ => Z p.1 p.2)))) :
    matrixDirichletAverage b β (fun i j => Z (q i) j) f =
      matrixDirichletAverage (stdSimplexAggregate q b) β Z f := by
  simp only [matrixDirichletAverage,
    regMatrixDirichletAverage_aggregate_rows hb hβ hq Z hf,
    sum_aggregate_dirichletParameters]

/-- The matrix affine form stays within any closed disk containing every entry. -/
theorem norm_matrixAffineForm_sub_le (Z : ι → κ → ℂ) (c : ℂ) (r : ℝ)
    (hZ : ∀ i j, ‖Z i j - c‖ ≤ r) {u : ι → ℝ} {v : κ → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι)
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ κ) :
    ‖matrixAffineForm Z u v - c‖ ≤ r := by
  have hball : convexHull ℝ (range (fun p : ι × κ => Z p.1 p.2)) ⊆
      Metric.closedBall c r := by
    apply convexHull_min _ (convex_closedBall c r)
    rintro z ⟨⟨i, j⟩, rfl⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hZ i j
  simpa only [Metric.mem_closedBall, dist_eq_norm] using
    hball (matrixAffineForm_mem_convexHull Z hu hv)

/-- A convex domain containing the entries contains every matrix affine combination. -/
theorem matrixAffineForm_mem_of_convex {D : Set ℂ} (hD : Convex ℝ D)
    (Z : ι → κ → ℂ) (hZ : ∀ i j, Z i j ∈ D) {u : ι → ℝ} {v : κ → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι)
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ κ) : matrixAffineForm Z u v ∈ D := by
  apply convexHull_min (s := range (fun p : ι × κ => Z p.1 p.2)) _ hD
    (matrixAffineForm_mem_convexHull Z hu hv)
  rintro z ⟨⟨i, j⟩, rfl⟩
  exact hZ i j

/-- **Carlson (1971), (2.8).** The normalized matrix average is an iterated
complex Dirichlet integral with independent parameter vectors. -/
theorem matrixDirichletAverage_eq_iterated (b : ι → ℂ) (β : κ → ℂ)
    (Z : ι → κ → ℂ) (f : ℂ → ℂ) :
    matrixDirichletAverage b β Z f =
      complexDirichletIntegral b (fun u =>
        complexDirichletIntegral β (fun v => f (matrixAffineForm Z u v))) := by
  simp only [matrixDirichletAverage, regMatrixDirichletAverage,
    complexDirichletIntegral_eq_Gamma_mul, regDirichletIntegral_smul, mul_assoc]

/-- At positive real parameters the two weight vectors are independent Dirichlet laws. -/
theorem matrixDirichletAverage_ofReal [Nonempty ι] [Nonempty κ]
    {b : ι → ℝ} {β : κ → ℝ} (hb : b ∈ mvRealBetaDomain) (hβ : β ∈ mvRealBetaDomain)
    (Z : ι → κ → ℂ) (f : ℂ → ℂ) :
    matrixDirichletAverage (fun i => (b i : ℂ)) (fun j => (β j : ℂ)) Z f =
      ∫ u, ∫ v, f (matrixAffineForm Z u v) ∂dirichletMeasure β ∂dirichletMeasure b := by
  simp only [matrixDirichletAverage_eq_iterated, complexDirichletIntegral_ofReal hb,
    complexDirichletIntegral_ofReal hβ]

end Dirichlet
