/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.Complex.DividedDifference

/-!
# Newton and Taylor formulas with exact remainders

Finite Newton expansion on a convex complex domain, allowing repeated nodes. Coalescing
the interpolation nodes gives Taylor coefficients and a divided-difference remainder.
Finite-vector and product helpers are kept alongside the formulas they support.

## Main results

* `Complex.newtonBasis_zero`: The empty Newton basis is one.
* `Complex.newtonPrecedingNodes_last`: The nodes preceding the last coefficient are the initial
  nodes.
* `Complex.newtonPrefix_last`: The final prefix is the complete node vector.
* `Complex.newtonTaylor_sum_add_remainder`: The finite Newton expansion with its exact
  divided-difference remainder.
* `Complex.taylor_sum_add_dividedDifference_remainder`: Taylor's formula with a
  divided-difference remainder, obtained from the Newton--Taylor formula by coalescing all
  interpolation nodes.

## References

* `StdSimplexMeasure.Complex.DividedDifference`: formal background used by this module.
-/

open MeasureTheory

@[expose] public noncomputable section

namespace Complex

/-- The node vector obtained by placing `x` before a vector of `n` nodes. -/
def prependNewtonNode (x : ℂ) (z : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.cons x z

/-- The node vector obtained by placing `x` and `y` before a vector of `n` nodes. -/
def prependTwoNewtonNodes (x y : ℂ) (z : Fin n → ℂ) : Fin (n + 2) → ℂ :=
  Fin.cons x (Fin.cons y z)

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

/-- Taking preceding nodes commutes with dropping the final node. -/
@[simp] theorem newtonPrecedingNodes_init_castSucc (z : Fin (p + 1) → ℂ)
    (n : Fin p) :
    newtonPrecedingNodes z n.castSucc =
      newtonPrecedingNodes (Fin.init z) n := by
  rfl

/-- Taking a prefix commutes with dropping the final node. -/
@[simp] theorem newtonPrefix_init_castSucc (z : Fin (p + 1) → ℂ)
    (n : Fin p) :
    newtonPrefix z n.castSucc = newtonPrefix (Fin.init z) n := by
  rfl

/-- The nodes preceding the last coefficient are the initial nodes. -/
@[simp] theorem newtonPrecedingNodes_last (z : Fin (p + 1) → ℂ) :
    newtonPrecedingNodes z (Fin.last p) = Fin.init z := by
  rfl

/-- The final prefix is the complete node vector. -/
@[simp] theorem newtonPrefix_last (z : Fin (p + 1) → ℂ) :
    newtonPrefix z (Fin.last p) = z := by
  funext i
  rfl

/-- The finite Newton expansion with its exact divided-difference remainder. -/
theorem newtonTaylor_sum_add_remainder
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (z : Fin p → ℂ) (hz : Set.range z ⊆ Ω) {x : ℂ} (hx : x ∈ Ω) :
    f x =
      (∑ n : Fin p, dividedDifference n f (newtonPrefix z n) *
        newtonBasis (newtonPrecedingNodes z n) x) +
      dividedDifference p f (Fin.snoc z x) * newtonBasis z x := by
  induction p with
  | zero =>
      simp [newtonBasis, Fin.snoc]
  | succ p ih =>
      let z₀ : Fin p → ℂ := Fin.init z
      let a : ℂ := z (Fin.last p)
      have hza : z = Fin.snoc z₀ a := by
        simp [z₀, a]
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
      have hrec := dividedDifference_sub hΩconv hf z₀ hz₀ hx ha
      rw [dividedDifference_snoc_snoc_comm] at hrec
      linear_combination newtonBasis z₀ x * hrec

/-- Taylor's formula with a divided-difference remainder, obtained from the
Newton--Taylor formula by coalescing all interpolation nodes. -/
theorem taylor_sum_add_dividedDifference_remainder
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {a x : ℂ} (ha : a ∈ Ω) (hx : x ∈ Ω) (p : ℕ) :
    f x =
      (∑ n : Fin p, iteratedDeriv n.val f a / (n.val.factorial : ℂ) * (x - a) ^ n.val) +
      dividedDifference p f (Fin.snoc (fun _ : Fin p => a) x) * (x - a) ^ p := by
  have hz : Set.range (fun _ : Fin p => a) ⊆ Ω := by
    rintro y ⟨i, rfl⟩
    exact ha
  have h := newtonTaylor_sum_add_remainder hΩconv hf
    (fun _ : Fin p => a) hz hx
  have hprefix (n : Fin p) : newtonPrefix (fun _ : Fin p => a) n = fun _ => a := by
    funext i
    rfl
  simp_rw [hprefix, dividedDifference_const] at h
  simpa [newtonPrecedingNodes, newtonBasis] using h


end Complex
