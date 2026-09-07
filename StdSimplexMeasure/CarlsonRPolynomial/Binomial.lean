/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonRPolynomial.Coefficients
import Mathlib.RingTheory.Binomial
/-! # The binomial theorem for Carlson's R-polynomials

Home for Carlson's Section 6.4 and its differential-difference consequences.
-/

open Complex
open scoped Classical
public noncomputable section CarlsonRPolynomial
namespace DirichletTransform

/-- The ascending-Pochhammer form of the Chu--Vandermonde identity. This is the
coefficient identity underlying Carlson's binomial theorem for R-polynomials. -/
theorem ascPochhammer_eval_add (r s : ℂ) (k : ℕ) :
    (ascPochhammer ℂ k).eval (r + s) =
      ∑ ij ∈ Finset.antidiagonal k,
        (Nat.choose k ij.1 : ℂ) *
          ((ascPochhammer ℂ ij.1).eval r *
            (ascPochhammer ℂ ij.2).eval s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ih,
      Finset.sum_antidiagonal_choose_succ_mul
        (fun i j ↦ (ascPochhammer ℂ i).eval r * (ascPochhammer ℂ j).eval s),
      ← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    have hijsum : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    rw [← hijsum, Nat.choose_symm_add]
    push_cast
    ring

/-- An ascending Pochhammer symbol splits at any intermediate index. -/
theorem ascPochhammer_eval_add_nat (c : ℂ) (m d : ℕ) :
    (ascPochhammer ℂ (m + d)).eval c =
      (ascPochhammer ℂ m).eval c * (ascPochhammer ℂ d).eval (c + m) := by
  have h := congrArg (Polynomial.eval c) (ascPochhammer_mul ℂ m d)
  simpa only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_natCast] using h.symm

end DirichletTransform
end CarlsonRPolynomial
