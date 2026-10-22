/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.HypergeometricBeta
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Appell's first hypergeometric function

The double series in Carlson (1977), (2.4-25). Regularization by `Γ(c)`
allows every complex denominator parameter. Absolute convergence on the unit
bidisc follows by comparing the total-degree coefficient with a Gauss series
at a slightly larger radius and the two remaining factors with binomial series.
This uses Mathlib's convergence-radius theorem and scalar-series bounds.
-/

open Polynomial Filter
open scoped Topology

@[expose] public noncomputable section

namespace Complex

/-- The regularized coefficient of Appell's first double hypergeometric series.
The factorization uses one Gauss coefficient and two binomial coefficients. -/
def regularizedAppellF1Coeff (a b₁ b₂ c : ℂ) (p : ℕ × ℕ) : ℂ :=
  regularizedHGFunCoeff {a, 1} {c} (p.1 + p.2) *
    regularizedHGFunCoeff {b₁} 0 p.1 * regularizedHGFunCoeff {b₂} 0 p.2

/-- The explicit Pochhammer form of the regularized Appell coefficient. -/
theorem regularizedAppellF1Coeff_eq (a b₁ b₂ c : ℂ) (m n : ℕ) :
    regularizedAppellF1Coeff a b₁ b₂ c (m, n) =
      (ascPochhammer ℂ (m + n)).eval a * (ascPochhammer ℂ m).eval b₁ *
        (ascPochhammer ℂ n).eval b₂ /
        ((m.factorial : ℂ) * n.factorial * Gamma (c + (m + n : ℕ))) := by
  simp only [regularizedAppellF1Coeff, regularizedHGFunCoeff, Multiset.map_cons,
    Multiset.insert_eq_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
    Multiset.map_zero, Multiset.prod_zero, ascPochhammer_eval_one, mul_one]
  rw [mul_comm _ ((m + n).factorial : ℂ),
    mul_div_mul_left _ _ (by exact_mod_cast (m + n).factorial_ne_zero)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Appell's first hypergeometric function, regularized by the denominator Gamma factor. -/
def regularizedAppellF1 (a b₁ b₂ c x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, regularizedAppellF1Coeff a b₁ b₂ c p * x ^ p.1 * y ^ p.2

/-- Appell's first hypergeometric function with ordinary normalization.
The usual series interpretation requires `c` to avoid nonpositive integers. -/
def appellF1 (a b₁ b₂ c x y : ℂ) : ℂ :=
  Gamma c * regularizedAppellF1 a b₁ b₂ c x y

/-- Gauss-type scalar series converge at every argument in the open unit disk. -/
private theorem summable_HG_unit {A C : Multiset ℂ} (hcard : A.card = C.card + 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => regularizedHGFunCoeff A C n * z ^ n) := by
  apply (hasSum_regularizedHGFun_of_mem_eball ?_).summable
  rw [Metric.mem_eball, edist_zero_right]
  apply lt_of_lt_of_le ?_ (radius_regularizedHGFunSeries_ge_one hcard)
  rw [← ofReal_norm, ENNReal.ofReal_lt_one]
  exact hz

/-- **Carlson (2.4-25), absolute convergence.** The regularized Appell double
series converges absolutely on the whole unit bidisc, for all complex parameters. -/
theorem summable_norm_regularizedAppellF1 {a b₁ b₂ c x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Summable (fun p : ℕ × ℕ =>
      ‖regularizedAppellF1Coeff a b₁ b₂ c p * x ^ p.1 * y ^ p.2‖) := by
  obtain ⟨r, hr, hr1⟩ := exists_between (max_lt hx hy)
  have hr0 : 0 < r := (norm_nonneg x).trans_lt ((le_max_left _ _).trans_lt hr)
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  let A : ℕ → ℂ := fun n => regularizedHGFunCoeff {a, 1} {c} n * (r : ℂ) ^ n
  let B : ℕ → ℂ := fun n => regularizedHGFunCoeff {b₁} 0 n * (x / (r : ℂ)) ^ n
  let D : ℕ → ℂ := fun n => regularizedHGFunCoeff {b₂} 0 n * (y / (r : ℂ)) ^ n
  have hA : Summable A := summable_HG_unit (by simp) (by simpa [abs_of_pos hr0] using hr1)
  have hB : Summable B := summable_HG_unit (by simp) (by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact (div_lt_one hr0).mpr ((le_max_left _ _).trans_lt hr))
  have hD : Summable D := summable_HG_unit (by simp) (by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact (div_lt_one hr0).mpr ((le_max_right _ _).trans_lt hr))
  obtain ⟨M, hM⟩ := exists_norm_le_of_cauchySeq hA.hasSum.tendsto_sum_nat.cauchySeq
  have hBD := (hB.norm.mul_of_nonneg hD.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg
    _)).mul_left M
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (f := fun p : ℕ × ℕ =>
    M * (‖B p.1‖ * ‖D p.2‖)) ?_ hBD
  intro p
  have he : regularizedAppellF1Coeff a b₁ b₂ c p * x ^ p.1 * y ^ p.2 =
      A (p.1 + p.2) * B p.1 * D p.2 := by
    dsimp [regularizedAppellF1Coeff, A, B, D]
    rw [pow_add, div_pow, div_pow]
    field_simp
  rw [he, norm_mul, norm_mul]
  calc
    _ ≤ M * ‖B p.1‖ * ‖D p.2‖ := by gcongr; exact hM _
    _ = _ := by ring

/-- **Carlson (2.4-25).** The regularized function is the sum of its double series. -/
theorem hasSum_regularizedAppellF1 {a b₁ b₂ c x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun p : ℕ × ℕ => regularizedAppellF1Coeff a b₁ b₂ c p * x ^ p.1 * y ^ p.2)
      (regularizedAppellF1 a b₁ b₂ c x y) :=
  (summable_norm_regularizedAppellF1 hx hy).of_norm.hasSum

/-- Grouping the absolutely convergent Appell double series by total degree. -/
theorem hasSum_regularizedAppellF1_antidiagonal {a b₁ b₂ c x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun n : ℕ => ∑ p ∈ Finset.antidiagonal n,
        regularizedAppellF1Coeff a b₁ b₂ c p * x ^ p.1 * y ^ p.2)
      (regularizedAppellF1 a b₁ b₂ c x y) := by
  classical
  have hs := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr
    (hasSum_regularizedAppellF1 (a := a) (b₁ := b₁) (b₂ := b₂) (c := c) hx hy)
  apply hs.sigma
  intro n
  change HasSum (fun p : Finset.antidiagonal n =>
    regularizedAppellF1Coeff a b₁ b₂ c p * x ^ (p : ℕ × ℕ).1 * y ^ (p : ℕ × ℕ).2) _
  rw [← Finset.sum_coe_sort]
  exact hasSum_fintype _

/-- **Carlson (2.4-25), ordinary normalization.** Away from the denominator poles,
the ordinary Appell function has the textbook Pochhammer double series. -/
theorem hasSum_appellF1 {a b₁ b₂ c x y : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun p : ℕ × ℕ =>
      ((ascPochhammer ℂ (p.1 + p.2)).eval a * (ascPochhammer ℂ p.1).eval b₁ *
        (ascPochhammer ℂ p.2).eval b₂ /
        ((ascPochhammer ℂ (p.1 + p.2)).eval c * p.1.factorial * p.2.factorial)) *
          x ^ p.1 * y ^ p.2) (appellF1 a b₁ b₂ c x y) := by
  rw [appellF1]
  have hs := (hasSum_regularizedAppellF1 (a := a) (b₁ := b₁) (b₂ := b₂) (c := c) hx hy).mul_left
    (Gamma c)
  convert hs using 1
  funext p
  rcases p with ⟨m, n⟩
  rw [regularizedAppellF1Coeff_eq, ← Gamma_add_nat_div_Gamma_eq c hc]
  have hcn : Gamma (c + (m + n : ℕ)) ≠ 0 := Gamma_ne_zero (fun k hk => by
    apply hc (k + (m + n))
    push_cast at hk ⊢
    linear_combination hk)
  field_simp [Gamma_ne_zero hc, hcn]

end Complex
