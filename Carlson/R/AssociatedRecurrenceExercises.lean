/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Recurrence.Coefficients

/-!
# Exercise on the recurrence for associated R-functions (Carlson, Section 8.4)

## Main results

* `Carlson.carlsonAssociatedRecurrenceCoeff_const`: Exercise 8.4-1, for equal Dirichlet
  parameters the coefficient `Aₙ` of Relation 8.4-1 is a multiple of `Eₙ(z)`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.4.
-/

@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- **Exercise 8.4-1**: if all Dirichlet parameters equal `β`, the coefficient `Aₙ(a, b, z)` of
Relation 8.4-1 is `(a)ₙ (a' - k)_{k-n}/(a (a' - k)) (a + n - nβ) Eₙ(z)`, a multiple of the
elementary symmetric function `Eₙ(z)`. -/
theorem carlsonAssociatedRecurrenceCoeff_const (n : ℕ) (a a' β : ℂ) (z : ι → ℂ) :
    carlsonAssociatedRecurrenceCoeff n a a' (fun _ => β) z =
      (ascPochhammer ℂ n).eval a *
        (ascPochhammer ℂ (Fintype.card ι - n)).eval (a' - Fintype.card ι) /
          (a * (a' - Fintype.card ι)) * (a + n - n * β) * carlsonElementarySymmetric n z := by
  have h := carlsonElementarySymmetric_euler (ι := ι) n z
  have hs : (∑ i, β * z i * (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z) =
      β * (n * carlsonElementarySymmetric n z) := by
    rw [← h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [carlsonAssociatedRecurrenceCoeff, hs]
  ring

end Carlson
