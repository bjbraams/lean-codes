/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import StdSimplexMeasure.CarlsonRPolynomial.Binomial

import Pochhammer.Gamma
import Pochhammer.Vandermonde

/-!
# Linear transformations of Carlson's R-polynomials

This file contains the algebraic infrastructure for [Carl77, Section 6.5].
The Pochhammer reflection identity used in the book's proof is
`Complex.ascPochhammer_eval_split_reflection` in `Pochhammer.Gamma`.
-/

open Complex Finset
open scoped Classical
@[expose] public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Scaling all Carlson variables scales their degree-`n` polynomial kernel by `a ^ n`. -/
theorem eval_carlsonPowerPolynomial_smul (n : ℕ) (a : ℂ) (z x : ι → ℂ) :
    (carlsonPowerPolynomial n (fun i ↦ a * z i)).eval x =
      a ^ n * (carlsonPowerPolynomial n z).eval x := by
  rw [carlsonPowerPolynomial_smul]
  simp

/-- Carlson's transformed Dirichlet parameters for degree `n`, with `i` chosen as the
distinguished coordinate in Relation 6.5-3. -/
def carlsonRTransformParameters (n : ℕ) (i : ι) (b : ι → ℂ) : ι → ℂ :=
  Function.update b i (1 - (∑ j, b j) - n)

/-- Carlson's transformed variables for Relation 6.5-3.  The distinguished variable stays
fixed and every other variable is replaced by its difference from that variable. -/
def carlsonRTransformVariables (i : ι) (z : ι → ℂ) : ι → ℂ :=
  fun j => if j = i then z i else z i - z j

/-- The sum of Carlson's transformed parameters is `1 - b i - n`. -/
theorem sum_carlsonRTransformParameters (n : ℕ) (i : ι) (b : ι → ℂ) :
    ∑ j, carlsonRTransformParameters n i b j = 1 - b i - n := by
  classical
  unfold carlsonRTransformParameters
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hs : ∑ x ∈ Finset.univ \ {i}, b x + b i = ∑ x, b x := by
    simpa only [Finset.sdiff_singleton_eq_erase] using
      Finset.sum_erase_add Finset.univ b (Finset.mem_univ i)
  rw [← hs]
  ring

/-- The Pochhammer numerator of a constant vector of variables is a single Pochhammer
symbol, by the multinomial Chu–Vandermonde identity. -/
theorem carlsonRPolynomialNumerator_const (n : ℕ) (b : ι → ℂ) (w : ℂ) :
    carlsonRPolynomialNumerator n b (fun _ => w) =
      (ascPochhammer ℂ n).eval (∑ i, b i) * w ^ n := by
  rw [carlsonRPolynomialNumerator_eq_multinomial_sum, ascPochhammer_eval_sum univ b n]
  rw [sum_mul]
  refine sum_congr rfl fun m hm => ?_
  have hpow : (∏ i, (w : ℂ) ^ m i) = w ^ n := by
    rw [prod_pow_eq_pow_sum]
    have : ∑ i, m i = n := (mem_piAntidiag.mp hm).1
    simp [this]
  rw [hpow]
  ring

/-- Division-free form of Carlson's multivariate linear transformation 6.5-3.

Using the Pochhammer numerator avoids hypotheses excluding exceptional parameters.  Carlson's
usual identity follows after division by the relevant total-parameter Pochhammer symbols. -/
theorem carlsonRPolynomialNumerator_transform (n : ℕ) (i : ι) (b z : ι → ℂ) :
    carlsonRPolynomialNumerator n b z =
      (-1 : ℂ) ^ n * carlsonRPolynomialNumerator n
        (carlsonRTransformParameters n i b) (carlsonRTransformVariables i z) := by
  -- Both sides are polynomials of degree `n`.  The constant-variable case is
  -- `carlsonRPolynomialNumerator_const` together with Pochhammer reflection
  -- `Complex.ascPochhammer_eval_split_reflection`.  The general case follows by
  -- differentiating in the non-distinguished variables and evaluating on the
  -- line concentrated at `i`, but the coordinatewise derivative identification
  -- has not yet been completed.
  sorry

/- The two-variable transformations 6.5-1 are specializations of
`carlsonRPolynomialNumerator_transform`. -/

end DirichletTransform
end CarlsonRPolynomial
