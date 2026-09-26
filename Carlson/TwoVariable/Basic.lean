/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Two-variable Carlson functions

The two-coordinate index type `Fin 2` and the elementary API used by all two-variable
specializations: pairs `![x, y]` as functions on `Fin 2` and the coordinate transposition.

## Main definitions

* `Carlson.TwoVariable.pair`: the function `![x, y] : Fin 2 → ℂ`.
* `Carlson.TwoVariable.swap`: the transposition of the two coordinates.

## Main results

* `Carlson.TwoVariable.pair_zero`: The zeroth entry of a pair is its first argument.
* `Carlson.TwoVariable.pair_one`: The first entry of a pair is its second argument.
* `Carlson.TwoVariable.sum_pair`: The sum of the entries of a pair.
* `Carlson.TwoVariable.pair_comp_swap`: Composing a pair with the two-coordinate transposition
  exchanges its entries.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Complex
open scoped Matrix
@[expose] public noncomputable section CarlsonTwoVariable
namespace Carlson.TwoVariable

/-- A pair, represented as a function on the canonical two-element index type. -/
def pair (x y : ℂ) : Fin 2 → ℂ := ![x, y]

/-- The zeroth entry of a pair is its first argument. -/
@[simp] theorem pair_zero (x y : ℂ) : pair x y 0 = x := rfl

/-- The first entry of a pair is its second argument. -/
@[simp] theorem pair_one (x y : ℂ) : pair x y 1 = y := rfl

/-- The sum of the entries of a pair. -/
theorem sum_pair (x y : ℂ) : ∑ i, pair x y i = x + y := by
  simp [pair, Fin.sum_univ_two]

/-- The transposition of the two coordinates of `Fin 2`. -/
def swap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- Composing a pair with the two-coordinate transposition exchanges its entries. -/
@[simp] theorem pair_comp_swap (x y : ℂ) : pair x y ∘ swap = pair y x := by
  funext i
  fin_cases i <;> rfl

end Carlson.TwoVariable
end CarlsonTwoVariable
