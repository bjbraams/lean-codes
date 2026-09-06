/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonTwoVariable.RPolynomial
import StdSimplexMeasure.CarlsonTwoVariable.R
import StdSimplexMeasure.CarlsonTwoVariable.S

/-!
# Quadratic transformations of two-variable Carlson functions

This is the home for Carlson's Sections 6.9 and 6.10.  Their polynomial forms will be proved
before the branch-sensitive complex-power forms.  In particular, the hypotheses `x,y ∈ C₀`
in Carlson's statements must be translated into an explicit square-root branch domain rather
than suppressed by notation.
-/

open Complex
open scoped Classical
public noncomputable section CarlsonTwoVariable
namespace DirichletTransform.TwoVariable

/-- The squared arithmetic mean occurring in Carlson's first quadratic transformation. -/
def arithmeticMeanSq (x y : ℂ) : ℂ := ((x + y) / 2) ^ 2

/-- The squared geometric mean occurring in Carlson's first quadratic transformation. -/
def geometricMeanSq (x y : ℂ) : ℂ := x * y

/-- The arithmetic mean is symmetric in its arguments. -/
theorem arithmeticMeanSq_comm (x y : ℂ) : arithmeticMeanSq x y = arithmeticMeanSq y x := by
  simp [arithmeticMeanSq, add_comm]

/-- The squared geometric mean is symmetric in its arguments. -/
theorem geometricMeanSq_comm (x y : ℂ) : geometricMeanSq x y = geometricMeanSq y x := by
  simp [geometricMeanSq, mul_comm]

/- The transformations 6.9-3 and 6.10-1 involve nonintegral powers and principal square roots.
They will be stated after a reusable domain ensuring Carlson's chosen square roots lie in the
right half-plane has been introduced.  Their terminating polynomial consequences then extend
globally by polynomial identity. -/

end DirichletTransform.TwoVariable
end CarlsonTwoVariable
