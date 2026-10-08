/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Iterated derivatives of finitely differentiable functions on open sets

For a function of one variable that is `C^n` on an open set, `n : ℕ∞ω`, the global iterated
derivatives `iteratedDeriv k f` behave as expected there: they are `C^m` for `m + k ≤ n`,
continuous for `k ≤ n`, and have `iteratedDeriv (k + 1) f` as derivative for `k < n`. On an open
set they agree with Mathlib's `iteratedDerivWithin` (`iteratedDerivWithin_of_isOpen`), and the
continuity and differentiability statements are transferred from there.

## Main results

* `ContDiffOn.contDiffOn_iteratedDeriv_of_isOpen`
* `ContDiffOn.hasDerivAt_iteratedDeriv_of_isOpen`
* `ContDiffOn.continuousOn_iteratedDeriv_of_isOpen`
-/

@[expose] public section

open scoped ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {s : Set 𝕜} {f : 𝕜 → F} {n : ℕ∞ω} {k : ℕ}

namespace ContDiffOn

/-- Iterated derivatives of a `Cⁿ` function on an open set are `C^m` there when `m + k ≤ n`. -/
theorem contDiffOn_iteratedDeriv_of_isOpen {m : ℕ∞ω} (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hmn : m + k ≤ n) : ContDiffOn 𝕜 m (iteratedDeriv k f) s := by
  induction k generalizing m with
  | zero => simpa using hf.of_le (by simpa using hmn)
  | succ k ih =>
    rw [iteratedDeriv_succ]
    refine (ih (m := m + 1) ?_).deriv_of_isOpen hs le_rfl
    calc m + 1 + k = m + (k + 1 : ℕ) := by push_cast; ring
      _ ≤ n := hmn

/-- Up to the order of smoothness, the iterated derivatives of a `Cⁿ` function on an open set
are continuous there. -/
theorem continuousOn_iteratedDeriv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hk : k ≤ n) : ContinuousOn (iteratedDeriv k f) s :=
  (hf.continuousOn_iteratedDerivWithin hk hs.uniqueDiffOn).congr
    (iteratedDerivWithin_of_isOpen hs).symm

/-- Below the order of smoothness, the iterated derivatives of a `Cⁿ` function on an open set
have the next iterated derivative as derivative. -/
theorem hasDerivAt_iteratedDeriv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hk : k < n) {x : 𝕜} (hx : x ∈ s) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
  have hd := ((hf.differentiableOn_iteratedDerivWithin hk hs.uniqueDiffOn).congr
    (iteratedDerivWithin_of_isOpen hs).symm).differentiableAt (hs.mem_nhds hx)
  rw [iteratedDeriv_succ]
  exact hd.hasDerivAt

end ContDiffOn
