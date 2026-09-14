/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import Carlson.TwoVariable.Basic
public import Carlson.RPolynomial.Basic

/-! # Two-variable RPolynomial definitions -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

/-- The canonical two-variable specialization of the regularized Carlson polynomial. -/
abbrev regRPolynomial (n : ℕ) (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  regCarlsonRPolynomial n (pair b₀ b₁) (pair z₀ z₁)

end DirichletTransform.TwoVariable
