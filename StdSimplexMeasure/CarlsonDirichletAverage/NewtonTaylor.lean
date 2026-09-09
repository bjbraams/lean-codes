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

/-- Exchanging the final two nodes does not change a divided difference. -/
theorem carlsonDividedDifference_snoc_snoc_comm (n : ℕ) (f : ℂ → ℂ)
    (z : Fin n → ℂ) (x y : ℂ) :
    carlsonDividedDifference (n + 1) f (Fin.snoc (Fin.snoc z x) y) =
      carlsonDividedDifference (n + 1) f (Fin.snoc (Fin.snoc z y) x) := by
  let i : Fin (n + 2) := Fin.castSucc (Fin.last n)
  let j : Fin (n + 2) := Fin.last (n + 1)
  let σ : Equiv.Perm (Fin (n + 2)) := Equiv.swap i j
  rw [← carlsonDividedDifference_perm (n + 1) f
    (Fin.snoc (Fin.snoc z x) y) σ]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp [σ, i, j]
  · by_cases hkj : k = j
    · subst k
      simp [σ, i, j]
    · have hklt : k.val < n := by
        simp only [i, j, Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at hki hkj
        omega
      have hkle : k.val ≤ n := Nat.le_of_lt hklt
      simp [Function.comp_apply, σ, Equiv.swap_apply_of_ne_of_ne hki hkj,
        Fin.snoc, hklt, hkle]

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

/-- Appending a node adds its linear factor to the Newton basis. -/
@[simp] theorem newtonBasis_snoc (z : Fin n → ℂ) (a x : ℂ) :
    newtonBasis (Fin.snoc z a) x = newtonBasis z x * (x - a) := by
  simp [newtonBasis, Fin.prod_univ_castSucc]

/-- The nodes preceding the coefficient indexed by `n` in a finite Newton expansion. -/
def newtonPrecedingNodes {p : ℕ} (z : Fin p → ℂ) (n : Fin p) : Fin n → ℂ :=
  fun i => z ⟨i, lt_trans i.isLt n.isLt⟩

/-- The nodes through the coefficient indexed by `n` in a finite Newton expansion. -/
def newtonPrefix {p : ℕ} (z : Fin p → ℂ) (n : Fin p) : Fin (n + 1) → ℂ :=
  fun i => z ⟨i, lt_of_lt_of_le i.isLt (Nat.succ_le_iff.mpr n.isLt)⟩

@[simp] theorem newtonPrecedingNodes_init_castSucc (z : Fin (p + 1) → ℂ)
    (n : Fin p) :
    newtonPrecedingNodes z n.castSucc =
      newtonPrecedingNodes (Fin.init z) n := by
  rfl

@[simp] theorem newtonPrefix_init_castSucc (z : Fin (p + 1) → ℂ)
    (n : Fin p) :
    newtonPrefix z n.castSucc = newtonPrefix (Fin.init z) n := by
  rfl

@[simp] theorem newtonPrecedingNodes_last (z : Fin (p + 1) → ℂ) :
    newtonPrecedingNodes z (Fin.last p) = Fin.init z := by
  rfl

@[simp] theorem newtonPrefix_last (z : Fin (p + 1) → ℂ) :
    newtonPrefix z (Fin.last p) = z := by
  funext i
  rfl

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
  induction p with
  | zero =>
      simpa [newtonBasis, carlsonDividedDifference_zero, Fin.snoc]
  | succ p ih =>
      let z₀ : Fin p → ℂ := Fin.init z
      let a : ℂ := z (Fin.last p)
      have hza : z = Fin.snoc z₀ a := by
        simpa [z₀, a] using (Fin.snoc_init_self z).symm
      have hz₀ : Set.range z₀ ⊆ Ω := by
        rintro w ⟨i, rfl⟩
        exact hz ⟨Fin.castSucc i, rfl⟩
      have ha : a ∈ Ω := hz ⟨Fin.last p, rfl⟩
      have hih := ih z₀ hz₀
      rw [hza]
      rw [hih]
      rw [Fin.sum_univ_castSucc]
      simp only [newtonPrefix_init_castSucc, newtonPrecedingNodes_init_castSucc,
        newtonPrefix_last, newtonPrecedingNodes_last, Fin.init_snoc,
        Fin.val_castSucc, Fin.val_last]
      rw [newtonBasis_snoc]
      have hrec := carlsonDividedDifference_sub hΩopen hΩconv hf z₀ hz₀ hx ha
      rw [carlsonDividedDifference_snoc_snoc_comm] at hrec
      linear_combination newtonBasis z₀ x * hrec

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
