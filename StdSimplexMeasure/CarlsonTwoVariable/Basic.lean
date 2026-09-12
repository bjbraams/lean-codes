/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import StdSimplexMeasure.CarlsonRPolynomial.Basic
public import StdSimplexMeasure.CarlsonR.Basic
public import StdSimplexMeasure.CarlsonS

/-! # Two-variable Carlson functions -/

open Complex
open scoped Classical Matrix
@[expose] public noncomputable section CarlsonTwoVariable
namespace DirichletTransform.TwoVariable

/-- A pair, represented as a function on the canonical two-element index type. -/
def pair (x y : ℂ) : Fin 2 → ℂ := ![x, y]

/-- The zeroth entry of a pair is its first argument. -/
@[simp] theorem pair_zero (x y : ℂ) : pair x y 0 = x := rfl

/-- The first entry of a pair is its second argument. -/
@[simp] theorem pair_one (x y : ℂ) : pair x y 1 = y := rfl

/-- The sum of the entries of a pair. -/
@[simp] theorem sum_pair (x y : ℂ) : ∑ i, pair x y i = x + y := by
  simp [pair, Fin.sum_univ_two]

/-- The transposition of the two coordinates of `Fin 2`. -/
def swap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- Composing a pair with the two-coordinate transposition exchanges its entries. -/
@[simp] theorem pair_comp_swap (x y : ℂ) : pair x y ∘ swap = pair y x := by
  funext i
  fin_cases i <;> rfl

/-- The canonical two-variable specialization of the regularized Carlson polynomial. -/
abbrev regRPolynomial (n : ℕ) (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  regCarlsonRPolynomial n (pair b₀ b₁) (pair z₀ z₁)

/-- The canonical two-variable specialization of the native regularized Carlson R-integral. -/
abbrev regRIntegral (t b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  regCarlsonRIntegral t (pair b₀ b₁) (pair z₀ z₁)

/-- The canonical two-variable specialization of the native Carlson R-integral. -/
abbrev rIntegral (t b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  carlsonRIntegral t (pair b₀ b₁) (pair z₀ z₁)

/-- The canonical two-variable specialization of the native regularized Carlson S-integral. -/
abbrev regSIntegral (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  regCarlsonSIntegral (pair b₀ b₁) (pair z₀ z₁)

/-- The canonical two-variable specialization of the native Carlson S-integral. -/
abbrev sIntegral (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  carlsonSIntegral (pair b₀ b₁) (pair z₀ z₁)

/-- The canonical two-variable specialization of Carlson's entire regularized S-series. -/
abbrev regSSeries (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  regCarlsonSSeries (pair z₀ z₁) (pair b₀ b₁)

end DirichletTransform.TwoVariable
end CarlsonTwoVariable
