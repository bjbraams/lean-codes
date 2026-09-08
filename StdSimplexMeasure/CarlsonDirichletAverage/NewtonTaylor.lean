/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.CarlsonDirichletAverage.Deriv
import StdSimplexMeasure.CarlsonDirichletAverage.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Newton--Taylor formulas from Carlson's Dirichlet averages

This file develops Carlson's Section 5.5.  The unweighted Dirichlet average is isolated first,
and divided differences are defined from averages of iterated derivatives.  Canonical finite
index types are used for lists of interpolation nodes; permutation invariance can subsequently
remove any dependence on their chosen ordering.

The central remaining analytic input is Carlson's Lemma 5.5-1, whose proof is a
fundamental-theorem-of-calculus and Fubini argument on a simplex.  The definitions and
normalization lemmas below isolate that input from the finite Newton interpolation induction.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.5,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

public noncomputable section CarlsonNewtonTaylor

namespace DirichletTransform

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
  have hmem : ∀ᵐ u ∂dirichletMeasure b, u ∈ stdSimplex ℝ ι := by
    rw [← hrestrict]
    exact self_mem_ae_restrict (isClosed_stdSimplex ℝ ι).measurableSet
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
    convert measurePreserving_dirichletMeasure_perm b σ.symm using 1 <;>
      simp [g, b, Function.comp_def]
  unfold carlsonUnweightedAverage realCarlsonDirichletAverage
  rw [← hg.integral_comp' (fun u ↦ f (carlsonAffineForm z u))]
  apply integral_congr_ae
  filter_upwards with u
  congr 1
  simpa [g, Function.comp_def] using
    (carlsonAffineForm_perm (z ∘ σ) σ.symm u).symm

/-- The node vector obtained by placing `x` before a vector of `n` nodes. -/
def prependNewtonNode (x : ℂ) (z : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.cons x z

/-- The node vector obtained by placing `x` and `y` before a vector of `n` nodes. -/
def prependTwoNewtonNodes (x y : ℂ) (z : Fin n → ℂ) : Fin (n + 2) → ℂ :=
  Fin.cons x (Fin.cons y z)

/-- A divided difference of order `n`, expressed as Carlson's unweighted average of the
`n`th derivative divided by `n!`; this is formula (5.5-6). -/
def carlsonDividedDifference (n : ℕ) (f : ℂ → ℂ) (z : Fin (n + 1) → ℂ) : ℂ :=
  carlsonUnweightedAverage z (iteratedDeriv n f) / (n.factorial : ℂ)

/-- Divided differences are invariant under permutations of their nodes. -/
theorem carlsonDividedDifference_perm (n : ℕ) (f : ℂ → ℂ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1))) :
    carlsonDividedDifference n f (z ∘ σ) = carlsonDividedDifference n f z := by
  rw [carlsonDividedDifference, carlsonDividedDifference,
    carlsonUnweightedAverage_perm]

/-- A divided difference of order zero is evaluation at its unique node. -/
@[simp] theorem carlsonDividedDifference_zero (f : ℂ → ℂ) (z : Fin 1 → ℂ) :
    carlsonDividedDifference 0 f z = f (z 0) := by
  have hz : z = fun _ ↦ z 0 := by
    funext i
    exact Fin.eq_zero i ▸ rfl
  rw [hz]
  simp [carlsonDividedDifference, carlsonUnweightedAverage_const]

/-- If all nodes coincide, Carlson's divided difference is the corresponding Taylor
coefficient. -/
theorem carlsonDividedDifference_const (n : ℕ) (f : ℂ → ℂ) (w : ℂ) :
    carlsonDividedDifference n f (fun _ ↦ w) =
      iteratedDeriv n f w / (n.factorial : ℂ) := by
  simp [carlsonDividedDifference, carlsonUnweightedAverage_const]

/-- The Newton basis polynomial associated to a finite vector of preceding nodes. -/
def newtonBasis (z : Fin n → ℂ) (x : ℂ) : ℂ :=
  ∏ i, (x - z i)

/-- The empty Newton basis is one. -/
@[simp] theorem newtonBasis_zero (z : Fin 0 → ℂ) (x : ℂ) :
    newtonBasis z x = 1 := by
  simp [newtonBasis]

/-- Prepending a node adds the corresponding linear factor to the Newton basis. -/
@[simp] theorem newtonBasis_prepend (z : Fin n → ℂ) (a x : ℂ) :
    newtonBasis (prependNewtonNode a z) x = (x - a) * newtonBasis z x := by
  simp [newtonBasis, prependNewtonNode, Fin.prod_univ_succ]

/-- The nodes preceding the coefficient indexed by `n` in a finite Newton expansion. -/
def newtonPrecedingNodes {p : ℕ} (z : Fin p → ℂ) (n : Fin p) : Fin n → ℂ :=
  fun i => z ⟨i, lt_trans i.isLt n.isLt⟩

/-- The nodes through the coefficient indexed by `n` in a finite Newton expansion. -/
def newtonPrefix {p : ℕ} (z : Fin p → ℂ) (n : Fin p) : Fin (n + 1) → ℂ :=
  fun i => z ⟨i, lt_of_lt_of_le i.isLt (Nat.succ_le_iff.mpr n.isLt)⟩

/-- **Carlson 5.5-1.** Divided differences defined by unweighted Dirichlet averages satisfy
the usual first-order recurrence, including at coincident nodes. -/
theorem carlsonDividedDifference_sub
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (z : Fin n → ℂ) (hz : Set.range z ⊆ Ω) {x y : ℂ} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    carlsonDividedDifference n f (Fin.snoc z x) -
        carlsonDividedDifference n f (Fin.snoc z y) =
      (x - y) * carlsonDividedDifference (n + 1) f (Fin.snoc (Fin.snoc z x) y) := by
  /- Carlson proves this by writing the unweighted average as a simplex integral, changing one
  coordinate to the affine variable on the segment from `y` to `x`, and applying Fubini and the
  fundamental theorem of calculus. -/
  sorry

/-- **Carlson 5.5-2.** The finite Newton expansion with its Dirichlet-average remainder. -/
theorem newtonTaylor_sum_add_remainder
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (z : Fin p → ℂ) (hz : Set.range z ⊆ Ω) {x : ℂ} (hx : x ∈ Ω) :
    f x =
      (∑ n : Fin p, carlsonDividedDifference n f (newtonPrefix z n) *
        newtonBasis (newtonPrecedingNodes z n) x) +
      carlsonDividedDifference p f (Fin.snoc z x) * newtonBasis z x := by
  /- Once `carlsonDividedDifference_sub` is available, this is Carlson's elementary induction
  on `p`. -/
  sorry

/-- Taylor's formula with Carlson's unweighted-average remainder, obtained from the
Newton--Taylor formula by coalescing all interpolation nodes. -/
theorem taylor_sum_add_carlsonRemainder
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {a x : ℂ} (ha : a ∈ Ω) (hx : x ∈ Ω) (p : ℕ) :
    f x =
      (∑ n : Fin p, iteratedDeriv n.val f a / (n.val.factorial : ℂ) * (x - a) ^ n.val) +
      carlsonDividedDifference p f (Fin.snoc (fun _ : Fin p => a) x) * (x - a) ^ p := by
  have hz : Set.range (fun _ : Fin p => a) ⊆ Ω := by
    rintro y ⟨i, rfl⟩
    exact ha
  have h := newtonTaylor_sum_add_remainder hΩopen hΩconv hf
    (fun _ : Fin p => a) hz hx
  have hprefix (n : Fin p) : newtonPrefix (fun _ : Fin p => a) n = fun _ => a := by
    funext i
    rfl
  simp_rw [hprefix, carlsonDividedDifference_const] at h
  simpa [newtonPrecedingNodes, newtonBasis] using h

/-! ## Repeated integrals -/

/-- Integration of a complex-valued function along the oriented segment from `a` to `x`. -/
def carlsonSegmentIntegral (a x : ℂ) (f : ℂ → ℂ) : ℂ :=
  (x - a) * ∫ t in (0 : ℝ)..1, f (a + (t : ℂ) * (x - a))

/-- Carlson's repeated integration operator based at `a`, defined recursively by segment
integration.  This is the operator in equations 5.5(9) and 5.5(12). -/
def carlsonRepeatedIntegral : ℕ → ℂ → (ℂ → ℂ) → ℂ → ℂ
  | 0, _, f, x => f x
  | n + 1, a, f, x => carlsonSegmentIntegral a x (carlsonRepeatedIntegral n a f)

/-- The zeroth repeated integral is the original function. -/
@[simp] theorem carlsonRepeatedIntegral_zero (a : ℂ) (f : ℂ → ℂ) (x : ℂ) :
    carlsonRepeatedIntegral 0 a f x = f x := rfl

/-- The successor step for Carlson's repeated integration operator. -/
@[simp] theorem carlsonRepeatedIntegral_succ (n : ℕ) (a : ℂ) (f : ℂ → ℂ) (x : ℂ) :
    carlsonRepeatedIntegral (n + 1) a f x =
      carlsonSegmentIntegral a x (carlsonRepeatedIntegral n a f) := rfl

/-- Carlson's equation 5.5(10): an `n`-fold repeated integral is an unweighted Dirichlet
average with `n` nodes coalesced at the base point and one node at the endpoint. -/
theorem carlsonRepeatedIntegral_eq_unweightedAverage
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {a x : ℂ} (ha : a ∈ Ω) (hx : x ∈ Ω) (n : ℕ) :
    carlsonRepeatedIntegral n a f x =
      (x - a) ^ n / (n.factorial : ℂ) *
        carlsonUnweightedAverage (Fin.snoc (fun _ : Fin n => a) x) f := by
  /- The proof is an induction using Fubini on the triangular parameter region.  It is the
  repeated-integral counterpart of `carlsonDividedDifference_sub`. -/
  sorry

end DirichletTransform

end CarlsonNewtonTaylor
