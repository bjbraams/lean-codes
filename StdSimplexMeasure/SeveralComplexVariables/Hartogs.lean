/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Separate and joint analyticity in finite products

This file is the proposed home for a finite-product form of Hartogs' theorem.  Its immediate
application is to functions on `ι → ℂ`: analyticity of every one-coordinate update should imply
joint analyticity on an open product domain.  More general binary-product and finite-product
forms can be added as the proof architecture becomes clear.

This is a temporary project home for material ultimately intended for a Mathlib location such as
`Mathlib.Analysis.Complex.SeveralVariables.Hartogs`.

## Main result

`analyticOnNhd_pi_of_analyticOnNhd_update` is a finite-product form of Hartogs' theorem.

Depending on the chosen version of Hartogs' theorem, the hypotheses may initially include local
boundedness, continuity, or a literal product domain.  Such an additional hypothesis should not
be retained in the final theorem if the proof establishes that separate holomorphy supplies it.

The converse direction, extracting separate analyticity from joint analyticity, is already
largely supplied by composition with continuous linear coordinate maps.
-/

public section

open Set
open scoped Classical

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Hartogs' theorem, finite-product form.** A function on a finite product of copies of
`ℂ` is jointly analytic on an open set when all of its one-coordinate restrictions are
analytic. -/
theorem analyticOnNhd_pi_of_analyticOnNhd_update
    {ι : Type*} [Fintype ι] {U : Set (ι → ℂ)} {f : (ι → ℂ) → E}
    (hU : IsOpen U)
    (hf : ∀ z ∈ U, ∀ i,
      AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  /- A proof can be organized through Cauchy's formula on a closed polydisc contained in `U`.
  Separate analyticity gives the iterated Cauchy formula; uniform bounds on the distinguished
  boundary then give the convergent joint Taylor expansion. -/
  sorry

end SeveralComplexVariables

end
