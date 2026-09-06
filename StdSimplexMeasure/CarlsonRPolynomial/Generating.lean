/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonRPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Generating functions of Carlson's R-polynomials

This file develops [Carl77, Section 6.6].  The scalar geometric kernel is recorded separately
from the subsequent coefficient and convergence argument.
-/

open Complex Filter
open scoped Classical Topology
public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The scalar kernels used in Carlson's generating relation converge to the exponential
kernel under confluence. -/
theorem tendsto_carlsonGeneratingKernel (w : ℂ) :
    Tendsto (fun n : ℕ ↦ (1 + w / n) ^ n) atTop (𝓝 (exp w)) :=
  Complex.tendsto_one_add_div_pow_exp w

/- TODO: Generating Relation 6.6-1 is

  `∏ i, (1 - t * z i) ^ (-b i) =
    ∑' n, (ascPochhammer ℂ n).eval (∑ i, b i) / n! * Rₙ(b,z) * t^n`.

For the regularized polynomial the Gamma factor should first be cancelled algebraically.  A
proof needs the absolutely convergent complex binomial series and a theorem rearranging the
finite product of these series by total multi-index degree. -/

end DirichletTransform
end CarlsonRPolynomial
