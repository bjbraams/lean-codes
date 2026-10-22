/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Iterated derivatives of principal complex powers

The generic form of the helper previously used in Carlson's Gauss-function proof,
using Mathlib's derivative of `cpow` and descending Pochhammer recurrence.
-/

open Polynomial Filter
open scoped Topology

public noncomputable section

namespace Complex

/-- Iterated derivatives of a principal power on the slit plane. -/
theorem iteratedDeriv_cpow_const (A : ℂ) (n : ℕ) {x : ℂ} (hx : x ∈ slitPlane) :
    iteratedDeriv n (fun w : ℂ => w ^ A) x = (descPochhammer ℂ n).eval A * x ^ (A - n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have he : iteratedDeriv n (fun w : ℂ => w ^ A) =ᶠ[𝓝 x]
        fun w => (descPochhammer ℂ n).eval A * w ^ (A - n) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hx] with w hw using ih hw
    have hd := ((hasDerivAt_id x).cpow_const (c := A - n) hx).const_mul
      ((descPochhammer ℂ n).eval A)
    simp only [id] at hd
    rw [iteratedDeriv_succ, he.deriv_eq, hd.deriv, descPochhammer_succ_eval]
    push_cast
    ring_nf

end Complex
