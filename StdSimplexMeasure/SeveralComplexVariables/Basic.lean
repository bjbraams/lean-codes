/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import StdSimplexMeasure.SeveralComplexVariables.Hartogs

/-!
# Analyticity of holomorphic maps in finite dimension

This file is the proposed home for the several-complex-variables theorem that a complex
Fréchet-differentiable map on an open subset of a finite-dimensional complex normed space is
analytic.  Mathlib presently provides this implication when the source is `ℂ`; the intended
result extends it to finite-dimensional complex source spaces.

The file is independent of simplex measures and Carlson functions.  It is a temporary project
home for material ultimately intended for a Mathlib location such as
`Mathlib.Analysis.Complex.SeveralVariables.Basic`.

## Main results

`DifferentiableOn.analyticOnNhd_pi` and `differentiableOn_iff_analyticOnNhd_pi` provide the
finite-coordinate form needed by the present applications.

The proof may be obtained either from a finite-dimensional Hartogs theorem or directly from
Cauchy's formula on sufficiently small polydiscs.  The theorem should not require a chosen basis
in its final statement.
-/

public section

open Set
open scoped Classical

namespace SeveralComplexVariables

/-! Auxiliary basis-dependent constructions used in a proof may live in this namespace.  The
main user-facing implications should extend `DifferentiableOn` in the root namespace. -/

end SeveralComplexVariables

variable {ι F : Type*} [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A complex Fréchet-differentiable map on an open subset of a finite complex coordinate
space is analytic there. -/
theorem DifferentiableOn.analyticOnNhd_pi {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) : AnalyticOnNhd ℂ f U := by
  apply SeveralComplexVariables.analyticOnNhd_pi_of_analyticOnNhd_update hU
  intro z hz i
  let V : Set ℂ := {w | Function.update z i w ∈ U}
  have hupdate : Continuous (fun w : ℂ ↦ Function.update z i w) := by fun_prop
  have hupdate_diff : Differentiable ℂ (fun w : ℂ ↦ Function.update z i w) := by
    rw [show (fun w : ℂ ↦ Function.update z i w) = fun w ↦
        z + ContinuousLinearMap.single ℂ (fun _ : ι ↦ ℂ) i (w - z i) by
      funext w j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]]
    fun_prop
  have hV : IsOpen V := hU.preimage hupdate
  have hd : DifferentiableOn ℂ (fun w ↦ f (Function.update z i w)) V := by
    intro w hw
    exact (((hf _ hw).differentiableAt (hU.mem_nhds hw)).comp w
      hupdate_diff.differentiableAt).differentiableWithinAt
  exact hd.analyticAt (hV.mem_nhds (by simpa [V] using hz))

/-- On an open subset of a finite complex coordinate space, complex Fréchet differentiability
and analyticity are equivalent. -/
theorem differentiableOn_iff_analyticOnNhd_pi {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hU : IsOpen U) : DifferentiableOn ℂ f U ↔ AnalyticOnNhd ℂ f U :=
  ⟨fun hf ↦ hf.analyticOnNhd_pi hU, fun hf ↦ hf.differentiableOn⟩

end
