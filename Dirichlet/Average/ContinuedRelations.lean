/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Continuation
public import Dirichlet.Transform.Laws

/-!
# Associated relations on the full parameter space

The regularized identities of Carlson, Section 5.6, persist under analytic
continuation. All Dirichlet parameters below are arbitrary complex numbers.
The derivative appearing here is the derivative of the function being averaged.

## Main results

* `Dirichlet.IsRegCarlsonContinuation.sum_shift`: Entire-parameter version of Carlson's relation
  5.6-1(4).
* `Dirichlet.IsRegCarlsonContinuation.three_node`: Carlson's three-node associated relation
  5.6-3. No distinctness assumptions on the nodes, indices, or Dirichlet parameters are needed.
* `Dirichlet.regCarlsonDirichletAverage_mul_arg`: Multiplication of the function being averaged
  by its argument is a weighted sum of parameter shifts, on the native integral domain.
* `Dirichlet.IsRegCarlsonContinuation.mul_arg`: Entire-parameter multiplication-by-argument
  identity.
* `Dirichlet.IsRegCarlsonContinuation.associated`: Carlson's relation 5.6-4, in regularized form
  on the entire parameter space. `D` averages `f'`, while `H` averages `w * f'(w)`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/

open Complex Set MeasureTheory ProbabilityTheory
@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]

/-- Entire-parameter version of Carlson's relation 5.6-1(4). -/
theorem IsRegCarlsonContinuation.sum_shift {f : ℂ → ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f z G)
    (hf : ContinuousOn (fun u => f (carlsonAffineForm z u))
        (Convexity.StdSimplex.coordinateSet ℝ ι))
    (b : ι → ℂ) : G b = ∑ i, b i * G (addDirichletUnit b i) :=
  IsRegDirichletContinuation.sum_shift hG hf b

/-- The tangential associated relation, with no restrictions on the parameters.
The coincident-index case is included. -/
theorem IsRegCarlsonContinuation.tangent
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {z : ι → ℂ} (hz : range z ⊆ Ω) {G D : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f z G) (hD : IsRegCarlsonContinuation (deriv f) z D)
    (b : ι → ℂ) (i j : ι) :
    (z i - z j) * D (addDirichletUnit (addDirichletUnit b j) i) =
      G (addDirichletUnit b i) - G (addDirichletUnit b j) := by
  classical
  by_cases hij : i = j
  · subst j; simp
  have heq {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
      fderiv ℝ (fun u => f (carlsonAffineForm z u)) u (Pi.single i 1 - Pi.single j 1) =
        (z i - z j) * deriv f (carlsonAffineForm z u) := by
    have hmem := convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z hu)
    have hd := (hf _ hmem).differentiableAt.hasDerivAt.comp_hasFDerivAt u
      (hasFDerivAt_carlsonSimplex z u)
    erw [hd.fderiv]
    simp [carlsonSimplexCLM_tangent, mul_comm]
  have hdiff : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      DifferentiableAt ℝ (fun u => f (carlsonAffineForm z u)) u := by
    intro u hu
    have hd := (hf _ (convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z
        hu))).differentiableAt
    exact (hd.restrictScalars ℝ).comp u (hasFDerivAt_carlsonSimplex z u).differentiableAt
  have hdc := hf.deriv.continuousOn.comp (continuous_carlsonAffineForm z).continuousOn
    (fun u hu => convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z hu))
  have hdf := (continuousOn_const.mul hdc).congr (fun u hu => heq hu)
  have hderiv := (IsRegDirichletContinuation.smul hD (z i - z j)).congr
    (fun u hu => (heq hu).symm)
  have h := IsRegDirichletContinuation.tangent hG j ⟨i, hij⟩ hderiv hdiff hdf
    (addDirichletUnit (addDirichletUnit b j) i)
  have hshift (c : ι → ℂ) (k : ι) : addDirichletUnit c k = c + Pi.single k 1 := by
    ext l
    by_cases hl : l = k <;> simp [addDirichletUnit, hl]
  have hi : addDirichletUnit (addDirichletUnit b j) i - Pi.single i 1 = addDirichletUnit b j := by
    simp only [hshift]; abel
  have hj : addDirichletUnit (addDirichletUnit b j) i - Pi.single j 1 = addDirichletUnit b i := by
    simp only [hshift]; abel
  simpa only [hi, hj] using h

open scoped Classical in
/-- Carlson's backward-shift relation 5.6-2, in entire regularized form. -/
theorem IsRegCarlsonContinuation.tangent_sub
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {z : ι → ℂ} (hz : range z ⊆ Ω) {G D : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f z G) (hD : IsRegCarlsonContinuation (deriv f) z D)
    (b : ι → ℂ) (i j : ι) :
    (z i - z j) * D b = G (b - Pi.single j 1) - G (b - Pi.single i 1) := by
  by_cases hij : i = j
  · subst j; simp
  have h := hG.tangent hΩconv hf hz hD (b - Pi.single i 1 - Pi.single j 1) i j
  have hi : addDirichletUnit (b - Pi.single i 1 - Pi.single j 1) i = b - Pi.single j 1 := by
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [addDirichletUnit, sub_add_cancel]
  have hj : addDirichletUnit (b - Pi.single i 1 - Pi.single j 1) j = b - Pi.single i 1 := by
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [addDirichletUnit, sub_add_cancel]
  have hij' : addDirichletUnit (b - Pi.single i 1) i = b := by
    ext k
    by_cases hk : k = i <;> simp [addDirichletUnit, hk]
  simpa only [hi, hj, hij'] using h

open scoped Classical in
/-- Carlson's three-node associated relation 5.6-3. No distinctness assumptions
on the nodes, indices, or Dirichlet parameters are needed. -/
theorem IsRegCarlsonContinuation.three_node
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {z : ι → ℂ} (hz : range z ⊆ Ω) {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f z G) (hΩopen : IsOpen Ω)
    (b : ι → ℂ) (i j k : ι) :
    (z i - z j) * G (b - Pi.single k 1) +
      (z j - z k) * G (b - Pi.single i 1) +
      (z k - z i) * G (b - Pi.single j 1) = 0 := by
  obtain ⟨D, hD⟩ := exists_isRegCarlsonContinuation hΩopen hΩconv hf.deriv hz
  have hij := hG.tangent_sub hΩconv hf hz hD b i j
  have hjk := hG.tangent_sub hΩconv hf hz hD b j k
  linear_combination (z j - z k) * hij - (z i - z j) * hjk

/-- Multiplication of the function being averaged by its argument is a weighted
sum of parameter shifts, on the native integral domain. -/
theorem regCarlsonDirichletAverage_mul_arg {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (f : ℂ → ℂ)
    (hf : ContinuousOn (fun u => f (carlsonAffineForm z u))
        (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regCarlsonDirichletAverage b z (fun w => w * f w) =
      ∑ i, z i * (b i * regCarlsonDirichletAverage (addDirichletUnit b i) z f) := by
  simp_rw [regCarlsonDirichletAverage, mul_regDirichletIntegral_addDirichletUnit hb,
    ← regDirichletIntegral_smul]
  unfold regDirichletIntegral
  rw [← integral_finsetSum]
  · apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    intro u _
    dsimp only
    rw [← Finset.mul_sum]
    congr 1
    simp only [carlsonAffineForm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro i _
    exact integrableOn_regDirichletDensity_mul b hb
      (continuousOn_const.mul
        ((Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn.mul hf))

/-- Entire-parameter multiplication-by-argument identity. -/
theorem IsRegCarlsonContinuation.mul_arg {f : ℂ → ℂ} {z : ι → ℂ}
    {G H : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f z G)
    (hH : IsRegCarlsonContinuation (fun w => w * f w) z H)
    (hf : ContinuousOn (fun u => f (carlsonAffineForm z u))
        (Convexity.StdSimplex.coordinateSet ℝ ι))
    (b : ι → ℂ) : H b = ∑ i, z i * (b i * G (addDirichletUnit b i)) := by
  have hs := IsRegDirichletContinuation.sum Finset.univ
    (fun i _ => (IsRegDirichletContinuation.coordinate_mul hG i).smul (z i))
    (fun i _ => continuousOn_const.mul
      ((Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn.mul hf))
  have he : IsRegDirichletContinuation (fun u => carlsonAffineForm z u * f (carlsonAffineForm z u))
      (fun c => ∑ i, z i * (c i * G (addDirichletUnit c i))) := hs.congr (by
    intro u _
    simp only [carlsonAffineForm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring)
  exact congrFun (IsRegDirichletContinuation.eq hH he) b

/-- Carlson's relation 5.6-4, in regularized form on the entire parameter space.
`D` averages `f'`, while `H` averages `w * f'(w)`. -/
theorem IsRegCarlsonContinuation.associated
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {z : ι → ℂ} (hz : range z ⊆ Ω) {G D H : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f z G) (hD : IsRegCarlsonContinuation (deriv f) z D)
    (hH : IsRegCarlsonContinuation (fun w => w * deriv f w) z H)
    (b : ι → ℂ) (i : ι) :
    G b = H (addDirichletUnit b i) - z i * D (addDirichletUnit b i) +
      (∑ j, b j) * G (addDirichletUnit b i) := by
  have hc : ContinuousOn (fun u => f (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    hf.continuousOn.comp (continuous_carlsonAffineForm z).continuousOn
      (fun _ hu => convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z hu))
  have hdc : ContinuousOn (fun u => deriv f (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    hf.deriv.continuousOn.comp (continuous_carlsonAffineForm z).continuousOn
      (fun _ hu => convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z hu))
  have ht (j : ι) : (z j - z i) *
      (addDirichletUnit b i j * D (addDirichletUnit (addDirichletUnit b i) j)) =
      b j * (G (addDirichletUnit b j) - G (addDirichletUnit b i)) := by
    by_cases hji : j = i
    · subst j; simp
    rw [show addDirichletUnit b i j = b j by simp [addDirichletUnit, hji]]
    calc
      _ = b j * ((z j - z i) * D (addDirichletUnit (addDirichletUnit b i) j)) := by ring
      _ = _ := congrArg (b j * ·) (hG.tangent hΩconv hf hz hD b j i)
  have heq : H (addDirichletUnit b i) - z i * D (addDirichletUnit b i) =
      G b - (∑ j, b j) * G (addDirichletUnit b i) := by
    rw [hD.mul_arg hH hdc, hD.sum_shift hdc (addDirichletUnit b i),
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp_rw [← sub_mul, ht]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hG.sum_shift hc b]
  linear_combination -heq

end Dirichlet
end
