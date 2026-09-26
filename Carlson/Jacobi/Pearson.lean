/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.Basic
public import Dirichlet.Average.ContinuedRelations

/-!
# Pearson's relation for continued two-node averages

The beta weight's integration-by-parts identity extends to arbitrary complex
parameters when written in terms of regularized Carlson continuations. The
quadratic factor is `(w-r)(w-s)`, and the linear factor is
`(a+b)w-ar-bs`. No division by a parameter or by the endpoint difference is
needed, so coincident endpoints and exceptional parameters are included.

## Main results

* `carlsonAverage_pearson`: the continued Pearson relation for a function
  holomorphic near the endpoint segment and its derivative.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §§5.6 and 7.1.
-/

public noncomputable section
namespace Carlson.TwoVariable
open Dirichlet Set

/-- Pearson's identity for regularized two-node Carlson averages, at all complex
parameters. The four continuations average `f`, `f'`, the quadratic times `f'`,
and the argument times `f`, respectively. -/
theorem carlsonAverage_pearson {r s : ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (segment ℝ r s))
    {G D A W : (Fin 2 → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f (pair r s) G)
    (hD : IsRegCarlsonContinuation (deriv f) (pair r s) D)
    (hA : IsRegCarlsonContinuation (fun w => (w - r) * (w - s) * deriv f w) (pair r s) A)
    (hW : IsRegCarlsonContinuation (fun w => w * f w) (pair r s) W) (a b : ℂ) :
    A (pair a b) + (a + b) * W (pair a b) - (a * r + b * s) * G (pair a b) = 0 := by
  have hz : range (pair r s) ⊆ segment ℝ r s := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact left_mem_segment ℝ r s
    · exact right_mem_segment ℝ r s
  have hc := hf.continuousOn.comp (continuous_carlsonAffineForm (pair r s)).continuousOn
    (fun _ hu => convexHull_min hz (convex_segment r s)
      (carlsonAffineForm_mem_convexHull (pair r s) hu))
  have he := ((IsRegDirichletContinuation.coordinate_mul hD (1 : Fin 2)).coordinate_mul 0).smul
    (-(r - s) ^ 2)
  have he' : IsRegCarlsonContinuation (fun w => (w - r) * (w - s) * deriv f w) (pair r s)
      (fun c => -(r - s) ^ 2 * (c 0 * (addDirichletUnit c 0 1 *
        D (addDirichletUnit (addDirichletUnit c 0) 1)))) := he.congr (by
    intro u hu
    have hu1 : (u 1 : ℂ) = 1 - (u 0 : ℂ) := by
      have hu' : (u 0 : ℂ) + (u 1 : ℂ) = 1 := by
        exact_mod_cast (show u 0 + u 1 = 1 by simpa only [Fin.sum_univ_two] using hu.2)
      linear_combination hu'
    simp only [carlsonAffineForm, Fin.sum_univ_two, pair_zero, pair_one]
    rw [hu1]
    ring)
  have ha := congrFun (hA.eq he') (pair a b)
  have ht := hG.tangent (convex_segment r s) hf hz hD (pair a b) 0 1
  have hw := hG.mul_arg hW hc (pair a b)
  have hs := hG.sum_shift hc (pair a b)
  have h0 (u v : ℂ) : addDirichletUnit (pair u v) 0 = pair (u + 1) v := by
    ext i
    fin_cases i <;> simp [addDirichletUnit, pair]
  have h1 (u v : ℂ) : addDirichletUnit (pair u v) 1 = pair u (v + 1) := by
    ext i
    fin_cases i <;> simp [addDirichletUnit, pair]
  simp only [h0, h1, Fin.sum_univ_two, pair_zero, pair_one] at ha ht hw hs
  linear_combination ha + (a + b) * hw - (a * r + b * s) * hs - a * b * (r - s) * ht

end Carlson.TwoVariable
