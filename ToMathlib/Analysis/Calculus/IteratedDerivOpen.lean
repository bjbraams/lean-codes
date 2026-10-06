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

For a function of one variable that is `n` times continuously differentiable on an open set,
the global iterated derivatives `iteratedDeriv k f` behave as expected there: they are
`C^(n-k)`, continuous for `k ≤ n`, and have `iteratedDeriv (k + 1) f` as derivative for `k < n`.

## Main results

* `ContDiffOn.contDiffOn_iteratedDeriv_of_isOpen`
* `ContDiffOn.hasDerivAt_iteratedDeriv_of_isOpen`
* `ContDiffOn.continuousOn_iteratedDeriv_of_isOpen`
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {s : Set 𝕜} {f : 𝕜 → F} {n k : ℕ}

namespace ContDiffOn

/-- Iterated derivatives of a `Cⁿ` function on an open set are `C^(n-k)` there. -/
theorem contDiffOn_iteratedDeriv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hk : k ≤ n) : ContDiffOn 𝕜 (n - k : ℕ) (iteratedDeriv k f) s := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact (ih (by omega)).deriv_of_isOpen hs (by
      rw [show n - k = (n - (k + 1)) + 1 by omega]; push_cast; exact le_rfl)

/-- Below the order of smoothness, the iterated derivatives of a `Cⁿ` function on an open set
have the next iterated derivative as derivative. -/
theorem hasDerivAt_iteratedDeriv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hk : k < n) {x : 𝕜} (hx : x ∈ s) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
  have hd := ((hf.contDiffOn_iteratedDeriv_of_isOpen hs hk.le).differentiableOn
    (by rw [Nat.cast_ne_zero]; omega)).differentiableAt (hs.mem_nhds hx)
  rw [iteratedDeriv_succ]
  exact hd.hasDerivAt

/-- Up to the order of smoothness, the iterated derivatives of a `Cⁿ` function on an open set
are continuous there. -/
theorem continuousOn_iteratedDeriv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hk : k ≤ n) : ContinuousOn (iteratedDeriv k f) s :=
  (hf.contDiffOn_iteratedDeriv_of_isOpen hs hk).continuousOn

end ContDiffOn
