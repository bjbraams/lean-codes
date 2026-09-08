/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonRPolynomial.Coefficients
import StdSimplexMeasure.CarlsonRPolynomial.Basic
import Mathlib.RingTheory.Binomial
/-! # The binomial theorem for Carlson's R-polynomials

Home for Carlson's Section 6.4 and its differential-difference consequences.
-/

open Complex
open scoped Classical
public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

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

/-- Carlson's binomial translation formula for R-polynomials on the native convergence
domain; this is the polynomial identity in [Carl77, Section 6.4]. -/
theorem regCarlsonR_add_const_of_mem_mvBetaConvergent (n : ℕ) (a : ℂ) (z : ι → ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonR n (fun i => z i + a) b =
      ∑ m ∈ Finset.range (n + 1),
        (Nat.choose n m : ℂ) * a ^ (n - m) * regCarlsonR m z b := by
  rw [← regCarlsonDirichletAverage_pow n _ hb]
  calc
    regCarlsonDirichletAverage b (fun i => z i + a) (fun w => w ^ n) =
        regCarlsonDirichletAverage b z (fun w => (w + a) ^ n) := by
      simpa using (regCarlsonDirichletAverage_comp_affine b z
        (fun w : ℂ => w ^ n) 1 a).symm
    _ = regCarlsonDirichletAverage b z (fun w =>
          ∑ m ∈ Finset.range (n + 1),
            ((Nat.choose n m : ℂ) * a ^ (n - m)) * w ^ m) := by
      congr 1
      funext w
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = ∑ m ∈ Finset.range (n + 1),
          regCarlsonDirichletAverage b z
            (fun w => ((Nat.choose n m : ℂ) * a ^ (n - m)) * w ^ m) := by
      apply regCarlsonDirichletAverage_finsetSum hb
      intro m hm
      exact (continuous_const.mul
        ((continuous_carlsonAffineForm z).pow m)).continuousOn
    _ = ∑ m ∈ Finset.range (n + 1),
          (Nat.choose n m : ℂ) * a ^ (n - m) * regCarlsonR m z b := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [regCarlsonDirichletAverage_const_mul,
        regCarlsonDirichletAverage_pow m z hb]

end DirichletTransform
end CarlsonRPolynomial
