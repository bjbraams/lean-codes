/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonRPolynomial.Binomial

/-!
# Linear transformations of Carlson's R-polynomials

This file contains the algebraic infrastructure for [Carl77, Section 6.5].
-/

open Complex
open scoped Classical
public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Splitting an ascending Pochhammer symbol and reflecting the remaining factors.

This is the cancellation identity used in Carlson's proof of the linear transformation
6.5-1.  Its multiplicative formulation remains valid when one of the Pochhammer factors
vanishes, unlike the corresponding quotient identity. -/
theorem ascPochhammer_eval_split_reflection (c : ℂ) {m n : ℕ} (hmn : m ≤ n) :
    (ascPochhammer ℂ n).eval c =
      (-1 : ℂ) ^ (n - m) * (ascPochhammer ℂ m).eval c *
        (ascPochhammer ℂ (n - m)).eval (1 - c - n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  simp only [Nat.add_sub_cancel_left]
  have hmul := congrArg (Polynomial.eval c) (ascPochhammer_mul ℂ m d)
  simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_natCast] at hmul
  rw [← hmul]
  have href := ascPochhammer_eval_neg_eq_descPochhammer ℂ (c + m + d - 1) d
  rw [descPochhammer_eval_eq_ascPochhammer] at href
  have harg : -(c + (m : ℂ) + d - 1) = 1 - c - (m + d : ℕ) := by
    rw [Nat.cast_add]
    ring
  have harg' : c + (m : ℂ) + d - 1 - d + 1 = c + m := by ring
  rw [harg, harg'] at href
  rw [href]
  ring_nf
  simp

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

/-- Division-free form of Carlson's multivariate linear transformation 6.5-3.

Using the Pochhammer numerator avoids hypotheses excluding exceptional parameters.  Carlson's
usual identity follows after division by the relevant total-parameter Pochhammer symbols. -/
theorem carlsonRPolynomialNumerator_transform (n : ℕ) (i : ι) (b z : ι → ℂ) :
    carlsonRPolynomialNumerator n b z =
      (-1 : ℂ) ^ n * carlsonRPolynomialNumerator n
        (carlsonRTransformParameters n i b) (carlsonRTransformVariables i z) := by
  sorry

/- The two-variable transformations 6.5-1 are specializations of
`carlsonRPolynomialNumerator_transform`. -/

end DirichletTransform
end CarlsonRPolynomial
