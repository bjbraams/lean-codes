/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.Complex.Integral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Divided differences with coincident nodes

The Hermite–Genocchi simplex integral defines divided differences of complex functions.
We prove permutation symmetry, the coalesced Taylor coefficient, and the recurrence on
convex domains. The definition is total; its interpolation properties require the stated
analyticity hypotheses.

## Main results

* `Complex.dividedDifference`: The Hermite–Genocchi divided difference of order `n`, defined by
  integrating `iteratedDeriv n f` over the simplex of nodes. Analyticity on a convex
  neighborhood of the nodes gives the usual divided-difference recurrence, including coincident
  nodes.
* `Complex.dividedDifference_perm`: Divided differences are invariant under permutations of
  their nodes.
* `Complex.dividedDifference_const`: If all nodes coincide, the divided difference is the
  corresponding Taylor coefficient.
* `Complex.dividedDifference_sub`: The divided-difference recurrence in multiplication form,
  valid also at coincident nodes.

## References

* `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`: formal background used by this module.
-/

open MeasureTheory

@[expose] public noncomputable section

namespace Complex

/-- The Hermite–Genocchi divided difference of order `n`, defined by integrating
`iteratedDeriv n f` over the simplex of nodes. Analyticity on a convex neighborhood of the
nodes gives the usual divided-difference recurrence, including coincident nodes. -/
def dividedDifference (n : ℕ) (f : ℂ → ℂ) (z : Fin (n + 1) → ℂ) : ℂ :=
  simplexIntegral z (iteratedDeriv n f)

/-- The finite-coordinate Hermite–Genocchi formula for a divided difference. -/
theorem dividedDifference_eq_integral (z : Fin (n + 1) → ℂ) (f : ℂ → ℂ) :
    dividedDifference n f z =
      ∫ v in posSimplexFin n 1, iteratedDeriv n f (∑ k, (finSimplexPoint v k : ℂ) * z k) :=
  simplexIntegral_eq_integral _ _

/-- Divided differences are invariant under permutations of their nodes. -/
theorem dividedDifference_perm (n : ℕ) (f : ℂ → ℂ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1))) :
    dividedDifference n f (z ∘ σ) = dividedDifference n f z :=
  simplexIntegral_perm _ _ _

/-- Exchanging the final two nodes does not change a divided difference. -/
theorem dividedDifference_snoc_snoc_comm (n : ℕ) (f : ℂ → ℂ)
    (z : Fin n → ℂ) (x y : ℂ) :
    dividedDifference (n + 1) f (Fin.snoc (Fin.snoc z x) y) =
      dividedDifference (n + 1) f (Fin.snoc (Fin.snoc z y) x) := by
  let i : Fin (n + 2) := Fin.castSucc (Fin.last n)
  let j : Fin (n + 2) := Fin.last (n + 1)
  let σ : Equiv.Perm (Fin (n + 2)) := Equiv.swap i j
  rw [← dividedDifference_perm (n + 1) f
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
@[simp] theorem dividedDifference_zero (f : ℂ → ℂ) (z : Fin 1 → ℂ) :
    dividedDifference 0 f z = f (z 0) := by
  have hz : z = fun _ ↦ z 0 := by
    funext i
    exact Fin.eq_zero i ▸ rfl
  rw [hz]
  simp [dividedDifference, simplexIntegral_const]

/-- If all nodes coincide, the divided difference is the corresponding Taylor
coefficient. -/
theorem dividedDifference_const (n : ℕ) (f : ℂ → ℂ) (w : ℂ) :
    dividedDifference n f (fun _ ↦ w) =
      iteratedDeriv n f w / (n.factorial : ℂ) := by
  simp [dividedDifference, simplexIntegral_const]

/-- The divided-difference recurrence in multiplication form, valid also at coincident nodes. -/
theorem dividedDifference_sub
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (z : Fin n → ℂ) (hz : Set.range z ⊆ Ω) {x y : ℂ} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    dividedDifference n f (Fin.snoc z x) -
        dividedDifference n f (Fin.snoc z y) =
      (x - y) * dividedDifference (n + 1) f (Fin.snoc (Fin.snoc z x) y) := by
  have hfiter : AnalyticOnNhd ℂ (iteratedDeriv n f) Ω := by
    simpa [iteratedDeriv_eq_iterate] using hf.iterated_deriv n
  simp only [dividedDifference, iteratedDeriv_succ]
  exact simplexIntegral_sub hΩconv hfiter z hz hx hy


end Complex
