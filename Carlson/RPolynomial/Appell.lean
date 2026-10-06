/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.Binomial
public import ToMathlib.Analysis.AppellSequence
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Carlson's R-polynomials as Appell sequences

Carlson's Theorem 6.4-1, the binomial theorem `Rₙ(b, z + λ) = ∑ₘ (n choose m) λ^(n-m) Rₘ(b, z)`,
says that for fixed parameters the R-polynomials form a sequence in Carlson's class `A_k`
(`Appell.IsAppell`). By the general characterization `Appell.isAppell_iff_hasDiagonalDeriv`
(Carlson (1970), Theorem 1) it is equivalent to the differential relation (6.4-4),
`∑ᵢ ∂ᵢ Rₙ(b, z) = n Rₙ₋₁(b, z)`; the corresponding statement for the R-function, (6.4-6), is
`Carlson.sum_carlsonPartialDeriv_regCarlsonR`.

## Main results

* `Carlson.isAppell_regCarlsonRPolynomial`: the regularized R-polynomials lie in `A_k`
  (Theorem 6.4-1; Carlson (1970), Example 19).
* `Carlson.hasDiagonalDeriv_regCarlsonRPolynomial`: the relation (6.4-4).
* `Carlson.isAppell_carlsonRPolynomialNumerator_div`: Carlson's normalized polynomials
  `Rₙ(b, z) = Nₙ(b, z) / (∑ b)ₙ` lie in `A_k` whenever `∑ b` is not a nonpositive integer.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Section 6.4.
* [Carl70] B. C. Carlson, *Polynomials satisfying a binomial theorem*, J. Math. Anal. Appl. 32
  (1970), 543–558.
-/

@[expose] public noncomputable section

open Complex Finset

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- **Theorem 6.4-1** ([Carl70], Example 19): for fixed parameters the regularized
R-polynomials satisfy the binomial theorem, so they form a sequence in Carlson's class `A_k`. -/
theorem isAppell_regCarlsonRPolynomial (b : ι → ℂ) :
    Appell.IsAppell fun n z => regCarlsonRPolynomial n b z := fun n z μ =>
  regCarlsonRPolynomial_add_const n μ z b

/-- **(6.4-4)**: the derivative of `Rₙ(b, z)` along the diagonal direction `(1, …, 1)`, that is
`∑ᵢ ∂Rₙ/∂zᵢ`, equals `n Rₙ₋₁(b, z)`. -/
theorem hasDiagonalDeriv_regCarlsonRPolynomial (b : ι → ℂ) :
    Appell.HasDiagonalDeriv fun n z => regCarlsonRPolynomial n b z :=
  Appell.isAppell_iff_hasDiagonalDeriv.mp (isAppell_regCarlsonRPolynomial b)

/-- Carlson's normalized R-polynomial is the Gamma multiple of the regularized one:
`Nₙ(b, z) / (c)ₙ = Γ(c) · Rₙ(b, z) / Γ(c)` with `c = ∑ b`, if `c` is not a nonpositive
integer. -/
theorem carlsonRPolynomialNumerator_div_eq (n : ℕ) {b : ι → ℂ}
    (hb : ∀ m : ℕ, ∑ i, b i ≠ -m) (z : ι → ℂ) :
    carlsonRPolynomialNumerator n b z / (ascPochhammer ℂ n).eval (∑ i, b i) =
      Gamma (∑ i, b i) * regCarlsonRPolynomial n b z := by
  have hG : Gamma (∑ i, b i) ≠ 0 := Gamma_ne_zero hb
  have hP := Gamma_add_nat_div_Gamma_eq (n := n) _ hb
  have hGn : Gamma ((∑ i, b i) + n) ≠ 0 := by
    refine Gamma_ne_zero fun m h => hb (m + n) ?_
    push_cast; linear_combination h
  rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, ← hP]
  field_simp

/-- [Carl70], Example 19 in Carlson's normalization: if `∑ b` is not a nonpositive integer,
the polynomials `Rₙ(b, z) = Nₙ(b, z) / (∑ b)ₙ` satisfy the binomial theorem. -/
theorem isAppell_carlsonRPolynomialNumerator_div {b : ι → ℂ} (hb : ∀ m : ℕ, ∑ i, b i ≠ -m) :
    Appell.IsAppell fun n z =>
      carlsonRPolynomialNumerator n b z / (ascPochhammer ℂ n).eval (∑ i, b i) := by
  simp_rw [carlsonRPolynomialNumerator_div_eq _ hb]
  exact (isAppell_regCarlsonRPolynomial b).const_mul _

end Carlson
