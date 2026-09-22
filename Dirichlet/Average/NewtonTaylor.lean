/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Basic
public import Dirichlet.Average.Real
public import ComplexAnalysis.NewtonTaylor
public import ComplexAnalysis.RepeatedIntegral

/-!
# Dirichlet-average identities for divided differences and repeated integrals

Unweighted Dirichlet averages are related to the general Hermite–Genocchi divided
differences, Newton–Taylor formulas, and repeated segment integrals in `ComplexAnalysis`.
The original application statements are retained as wrappers around that theory.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.5 (1977).
-/

open Complex MeasureTheory ProbabilityTheory

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- Carlson's unweighted Dirichlet average, obtained by setting every Dirichlet parameter
equal to one. -/
def carlsonUnweightedAverage (z : ι → ℂ) (f : ℂ → ℂ) : ℂ :=
  realCarlsonDirichletAverage (fun _ ↦ 1) z f

omit [Fintype ι] in
/-- The unweighted Dirichlet parameters belong to the positive real parameter domain. -/
theorem one_mem_mvRealBetaDomain : (fun _ : ι ↦ (1 : ℝ)) ∈ mvRealBetaDomain := by
  intro i
  simp

/-- Averaging at a constant vector of nodes is evaluation at that node. -/
theorem carlsonUnweightedAverage_const [Nonempty ι] (f : ℂ → ℂ) (w : ℂ) :
    carlsonUnweightedAverage (fun _ : ι ↦ w) f = f w := by
  let b : ι → ℝ := fun _ ↦ 1
  let _ : IsProbabilityMeasure (dirichletMeasure b) :=
    isProbabilityMeasure_dirichletMeasure one_mem_mvRealBetaDomain
  unfold carlsonUnweightedAverage realCarlsonDirichletAverage
  change (∫ u, f (carlsonAffineForm (fun _ ↦ w) u) ∂dirichletMeasure b) = f w
  have hrestrict := dirichletMeasure_restrict b
  have hmem : ∀ᵐ u ∂dirichletMeasure b, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
    rw [← hrestrict]
    exact self_mem_ae_restrict (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  calc
    (∫ u, f (carlsonAffineForm (fun _ ↦ w) u) ∂dirichletMeasure b) =
        ∫ _, f w ∂dirichletMeasure b := by
      apply integral_congr_ae
      filter_upwards [hmem] with u hu
      rw [carlsonAffineForm_const hu]
    _ = f w := by simp

/-- Permuting the nodes does not change the unweighted Carlson average. -/
theorem carlsonUnweightedAverage_perm (z : ι → ℂ) (f : ℂ → ℂ)
    (σ : Equiv.Perm ι) :
    carlsonUnweightedAverage (z ∘ σ) f = carlsonUnweightedAverage z f := by
  let b : ι → ℝ := fun _ ↦ 1
  let g : (ι → ℝ) ≃ᵐ (ι → ℝ) := {
    toFun u := u ∘ σ.symm
    invFun u := u ∘ σ
    left_inv u := by funext i; simp
    right_inv u := by funext i; simp
    measurable_toFun := continuous_pi (fun i ↦ continuous_apply (σ.symm i)) |>.measurable
    measurable_invFun := continuous_pi (fun i ↦ continuous_apply (σ i)) |>.measurable
  }
  have hg : MeasurePreserving g (dirichletMeasure b) (dirichletMeasure b) := by
    convert measurePreserving_dirichletMeasure_perm b σ.symm using 1
    simp [b, Function.comp_def]
  unfold carlsonUnweightedAverage realCarlsonDirichletAverage
  rw [← hg.integral_comp' (fun u ↦ f (carlsonAffineForm z u))]
  apply integral_congr_ae
  filter_upwards with u
  congr 1
  simpa [g, Function.comp_def] using
    (carlsonAffineForm_perm (z ∘ σ) σ.symm u).symm

/-- A divided difference of order `n`, expressed as Carlson's unweighted average of the
`n`th derivative divided by `n!`; this is formula (5.5-6). -/
def carlsonDividedDifference (n : ℕ) (f : ℂ → ℂ) (z : Fin (n + 1) → ℂ) : ℂ :=
  carlsonUnweightedAverage z (iteratedDeriv n f) / (n.factorial : ℂ)

/-- Unweighted probability normalization in finite coordinates. -/
theorem carlsonUnweightedAverage_eq_factorial_integral (z : Fin (n + 1) → ℂ) (f : ℂ → ℂ) :
    carlsonUnweightedAverage z f = (n.factorial : ℂ) *
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)),
          f (carlsonAffineForm z u) ∂Measure.stdSimplexMeasure := by
  unfold carlsonUnweightedAverage realCarlsonDirichletAverage
  change (∫ u, f (carlsonAffineForm z u) ∂dirichletMeasureUniform 1) = _
  rw [dirichletMeasureUniform_one, integral_smul_measure]
  simp [Complex.real_smul]

/-- The factorial in the divided difference cancels the probability normalization. -/
theorem carlsonDividedDifference_eq_integral (z : Fin (n + 1) → ℂ) (f : ℂ → ℂ) :
    carlsonDividedDifference n f z =
      ∫ v in posSimplexFin n 1, iteratedDeriv n f (carlsonAffineForm z (finSimplexPoint v)) := by
  rw [carlsonDividedDifference, carlsonUnweightedAverage_eq_factorial_integral]
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast n.factorial_ne_zero)]
  exact integral_stdSimplex_fin _

/-- The Carlson average definition agrees with the general Hermite–Genocchi divided difference. -/
theorem carlsonDividedDifference_eq_dividedDifference (n : ℕ) (f : ℂ → ℂ)
    (z : Fin (n + 1) → ℂ) : carlsonDividedDifference n f z = Complex.dividedDifference n f z := by
  rw [carlsonDividedDifference_eq_integral, Complex.dividedDifference_eq_integral]
  rfl

/-- The unweighted Dirichlet average is the simplex kernel integral multiplied by `n!`. -/
theorem carlsonUnweightedAverage_eq_factorial_simplexIntegral
    (z : Fin (n + 1) → ℂ) (f : ℂ → ℂ) :
    carlsonUnweightedAverage z f = (n.factorial : ℂ) * Complex.simplexIntegral z f :=
  carlsonUnweightedAverage_eq_factorial_integral z f

/-- The simplex fundamental theorem of calculus for a holomorphic kernel. -/
theorem carlson_simplex_integral_sub
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (z : Fin n → ℂ) (hz : Set.range z ⊆ Ω) {x y : ℂ} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    (∫ v in posSimplexFin n 1, f (carlsonAffineForm (Fin.snoc z x) (finSimplexPoint v))) -
      (∫ v in posSimplexFin n 1, f (carlsonAffineForm (Fin.snoc z y) (finSimplexPoint v))) =
      (x - y) * ∫ v in posSimplexFin (n + 1) 1,
        deriv f (carlsonAffineForm (Fin.snoc (Fin.snoc z x) y) (finSimplexPoint v)) := by
  simpa only [Complex.simplexIntegral_eq_integral, carlsonAffineForm] using
    Complex.simplexIntegral_sub hΩconv hf z hz hx hy

/-- Divided differences are invariant under permutations of their nodes. -/
theorem carlsonDividedDifference_perm (n : ℕ) (f : ℂ → ℂ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1))) :
    carlsonDividedDifference n f (z ∘ σ) = carlsonDividedDifference n f z := by
  simpa only [carlsonDividedDifference_eq_dividedDifference] using
    Complex.dividedDifference_perm n f z σ

/-- Exchanging the final two nodes does not change a divided difference. -/
theorem carlsonDividedDifference_snoc_snoc_comm (n : ℕ) (f : ℂ → ℂ)
    (z : Fin n → ℂ) (x y : ℂ) :
    carlsonDividedDifference (n + 1) f (Fin.snoc (Fin.snoc z x) y) =
      carlsonDividedDifference (n + 1) f (Fin.snoc (Fin.snoc z y) x) := by
  simpa only [carlsonDividedDifference_eq_dividedDifference] using
    Complex.dividedDifference_snoc_snoc_comm n f z x y

/-- A divided difference of order zero is evaluation at its unique node. -/
@[simp] theorem carlsonDividedDifference_zero (f : ℂ → ℂ) (z : Fin 1 → ℂ) :
    carlsonDividedDifference 0 f z = f (z 0) := by
  simpa only [carlsonDividedDifference_eq_dividedDifference] using
    Complex.dividedDifference_zero f z

/-- If all nodes coincide, Carlson's divided difference is the corresponding Taylor
coefficient. -/
theorem carlsonDividedDifference_const (n : ℕ) (f : ℂ → ℂ) (w : ℂ) :
    carlsonDividedDifference n f (fun _ ↦ w) =
      iteratedDeriv n f w / (n.factorial : ℂ) := by
  simpa only [carlsonDividedDifference_eq_dividedDifference] using
    Complex.dividedDifference_const n f w

/-- **Carlson 5.5-1.** Divided differences defined by unweighted Dirichlet averages satisfy
the usual first-order recurrence, including at coincident nodes. -/
theorem carlsonDividedDifference_sub
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (z : Fin n → ℂ) (hz : Set.range z ⊆ Ω) {x y : ℂ} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    carlsonDividedDifference n f (Fin.snoc z x) -
        carlsonDividedDifference n f (Fin.snoc z y) =
      (x - y) * carlsonDividedDifference (n + 1) f (Fin.snoc (Fin.snoc z x) y) := by
  simpa only [carlsonDividedDifference_eq_dividedDifference] using
    Complex.dividedDifference_sub hΩconv hf z hz hx hy

/-- **Carlson 5.5-2.** The finite Newton expansion with its Dirichlet-average remainder. -/
theorem newtonTaylor_sum_add_remainder
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (z : Fin p → ℂ) (hz : Set.range z ⊆ Ω) {x : ℂ} (hx : x ∈ Ω) :
    f x =
      (∑ n : Fin p, carlsonDividedDifference n f (newtonPrefix z n) *
        newtonBasis (newtonPrecedingNodes z n) x) +
      carlsonDividedDifference p f (Fin.snoc z x) * newtonBasis z x := by
  simpa only [carlsonDividedDifference_eq_dividedDifference] using
    Complex.newtonTaylor_sum_add_remainder hΩconv hf z hz hx

/-- Taylor's formula with Carlson's unweighted-average remainder, obtained from the
Newton--Taylor formula by coalescing all interpolation nodes. -/
theorem taylor_sum_add_carlsonRemainder
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {a x : ℂ} (ha : a ∈ Ω) (hx : x ∈ Ω) (p : ℕ) :
    f x =
      (∑ n : Fin p, iteratedDeriv n.val f a / (n.val.factorial : ℂ) * (x - a) ^ n.val) +
      carlsonDividedDifference p f (Fin.snoc (fun _ : Fin p => a) x) * (x - a) ^ p := by
  simpa only [carlsonDividedDifference_eq_dividedDifference] using
    Complex.taylor_sum_add_dividedDifference_remainder hΩconv hf ha hx p

/-- Carlson's equation 5.5(10): an `n`-fold repeated integral is an unweighted Dirichlet
average with `n` nodes coalesced at the base point and one node at the endpoint. -/
theorem carlsonRepeatedIntegral_eq_unweightedAverage
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {a x : ℂ} (ha : a ∈ Ω) (hx : x ∈ Ω) (n : ℕ) :
    Complex.repeatedIntegral n a f x =
      (x - a) ^ n / (n.factorial : ℂ) *
        carlsonUnweightedAverage (Fin.snoc (fun _ : Fin n => a) x) f := by
  rw [carlsonUnweightedAverage_eq_factorial_simplexIntegral,
    Complex.repeatedIntegral_eq_simplexIntegral hΩconv hf.continuousOn ha hx]
  field_simp [Nat.factorial_ne_zero]

end Dirichlet
