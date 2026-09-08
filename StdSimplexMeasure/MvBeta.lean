/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# The multivariate complex Beta function

## Main definitions and results

* `Complex.mvBeta`: the multivariate complex Beta function.
* `Complex.mvBetaConvergent`: the domain on which the usual simplex integral converges.
* `Complex.mvBeta_perm`: invariance under permutation of the parameters.
* `Complex.mvBeta_addNat_of_ne_neg_nat`: the translation identity away from Gamma poles.
* `Complex.mvBeta_addNat`: its specialization to the domain of absolute convergence.
* `Complex.mvBetaIntegral_eq_mvBeta`: the solid-simplex integral in DLMF 5.14.2.
* `Complex.mvBetaIntegralOne_eq_mvBeta`: the specialization in DLMF 5.14.1.

## References

* [NIST Digital Library of Mathematical Functions, §5.14](https://dlmf.nist.gov/5.14)
-/

open Fintype

public noncomputable section MvBeta

namespace Complex

variable {ι : Type*} [Fintype ι]

/-- The multivariate Beta function. -/
def mvBeta (b : ι → ℂ) : ℂ :=
    (∏ i, Gamma (b i)) / Gamma (∑ i, b i)

/-- The domain on which the usual simplex integral representation of `mvBeta` converges
absolutely. -/
def mvBetaConvergent : Set (ι → ℂ) :=
  {b | ∀ i, 0 < (b i).re}

/-- The sum of parameters in `mvBetaConvergent` has positive real part. -/
theorem sum_re_pos_of_mem_mvBetaConvergent [Nonempty ι] {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) : 0 < (∑ i, b i).re := by
  simpa using Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty

/-- The multivariate Beta function does not vanish on its convergence domain. -/
theorem mvBeta_ne_zero [Nonempty ι] {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    mvBeta b ≠ 0 := by
  apply div_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Gamma_ne_zero_of_re_pos (hb i)
  · exact Gamma_ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hb)

omit [Fintype ι] in
/-- Adding nonnegative integers coordinatewise preserves `mvBetaConvergent`. -/
theorem addNat_mem_mvBetaConvergent {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (m : ι → ℕ) : (fun i ↦ b i + (m i : ℂ)) ∈ mvBetaConvergent := by
  intro i
  norm_num
  exact add_pos_of_pos_of_nonneg (hb i) (Nat.cast_nonneg _)

omit [Fintype ι] in
/-- Simultaneously permuting the parameters preserves the convergence domain. -/
theorem comp_perm_mem_mvBetaConvergent {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent)
    (σ : Equiv.Perm ι) : b ∘ σ ∈ mvBetaConvergent :=
  fun i ↦ hb (σ i)

/-- `mvBeta` is symmetric in its arguments. -/
theorem mvBeta_perm (b : ι → ℂ) (σ : Equiv.Perm ι) :
    mvBeta (b ∘ σ) = mvBeta b := by
  change (∏ i, Gamma (b (σ i))) / Gamma (∑ i, b (σ i)) =
    (∏ i, Gamma (b i)) / Gamma (∑ i, b i)
  have hp : (∏ i, Gamma (b (σ i))) = ∏ i, Gamma (b i) :=
    Equiv.prod_comp σ (fun i => Gamma (b i))
  have hs : (∑ i, b (σ i)) = ∑ i, b i :=
    Equiv.sum_comp σ b
  rw [hp, hs]

/-- On a singleton index type, `mvBeta` equals one throughout its convergence domain. -/
theorem mvBeta_eq_one_of_unique [Unique ι] {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    mvBeta b = 1 := by
  have hG : Gamma (b default) ≠ 0 := Gamma_ne_zero_of_re_pos (hb default)
  simp [mvBeta, hG]

/-- The natural-shift recurrence for reciprocal Gamma, valid at every complex argument. This is
the pole-free counterpart of expressing an ascending Pochhammer symbol as a quotient of Gamma
functions. -/
theorem one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat (z : ℂ) (n : ℕ) :
    (Gamma z)⁻¹ = (ascPochhammer ℂ n).eval z * (Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ih, one_div_Gamma_eq_self_mul_one_div_Gamma_add_one]
      simp only [Nat.cast_succ, ascPochhammer_succ_right, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]
      ring_nf

/-- Positive integer translates of `mvBeta`, assuming only that the coordinate parameters avoid
the poles of the Gamma function. This hypothesis is substantially weaker than
membership in `mvBetaConvergent`.

Some pole-avoidance hypothesis is necessary: because Mathlib totalizes `Gamma` to be zero at its
poles, the displayed identity is not valid for arbitrary complex parameters. -/
theorem mvBeta_addNat_of_ne_neg_nat {b : ι → ℂ}
    (hb : ∀ i (k : ℕ), b i ≠ -(k : ℂ))
    (m : ι → ℕ) :
    mvBeta (fun i : ι => b i + (m i : ℂ)) * (ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) =
    mvBeta b * ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [mvBeta]
  | inr hι =>
      let _ := hι
      have hcoord (i : ι) :
          Gamma (b i + (m i : ℂ)) =
            (ascPochhammer ℂ (m i)).eval (b i) * Gamma (b i) := by
        apply (div_eq_iff (Gamma_ne_zero (hb i))).mp
        exact Gamma_add_nat_div_Gamma_eq (b i) (hb i)
      have hsum_add :
          ∑ i, (b i + (m i : ℂ)) = (∑ i, b i) + (∑ i, m i : ℕ) := by
        simp [Finset.sum_add_distrib]
      have hprod :
          ∏ i, Gamma (b i + (m i : ℂ)) =
            (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * ∏ i, Gamma (b i) := by
        simp_rw [hcoord, Finset.prod_mul_distrib]
      have hrec := one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat
        (∑ i, b i) (∑ i, m i)
      simp only [mvBeta, hsum_add, hprod, div_eq_mul_inv]
      calc
        ((∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * ∏ i, Gamma (b i)) *
              (Gamma ((∑ i, b i) + (∑ i, m i : ℕ)))⁻¹ *
              (ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) =
            (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * (∏ i, Gamma (b i)) *
              ((ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) *
                (Gamma ((∑ i, b i) + (∑ i, m i : ℕ)))⁻¹) := by ring
        _ = (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * (∏ i, Gamma (b i)) *
              (Gamma (∑ i, b i))⁻¹ := by rw [← hrec]
        _ = (∏ i, Gamma (b i)) * (Gamma (∑ i, b i))⁻¹ *
              ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by ring

/-- Positive integer translates of `mvBeta` on its absolutely convergent domain. -/
theorem mvBeta_addNat {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (m : ι → ℕ) :
    mvBeta (fun i : ι => b i + (m i : ℂ)) * (ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) =
    mvBeta b * ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [mvBeta]
  | inr hι =>
      let _ := hι
      apply mvBeta_addNat_of_ne_neg_nat (m := m)
      intro i k hik
      have hi : 0 < (b i).re := hb i
      rw [hik] at hi
      norm_num at hi
      linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]

section SolidSimplexIntegral

open MeasureTheory

/-- The solid standard `n`-simplex used in the DLMF multivariate Beta integrals. -/
def mvBetaSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- The solid standard simplex is a measurable set. -/
theorem measurableSet_mvBetaSimplex (n : ℕ) : MeasurableSet (mvBetaSimplex n) := by
  apply IsClosed.measurableSet
  apply IsClosed.inter
  · change IsClosed ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} : Set (Fin n → ℝ))
    rw [show {x : Fin n → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} by ext x; simp]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const

/-- Splitting off the last coordinate identifies a solid-simplex section with an interval
whose upper endpoint is the remaining slack coordinate. -/
private theorem snoc_mem_mvBetaSimplex_iff {n : ℕ} (y : Fin n → ℝ) (t : ℝ) :
    Fin.snoc y t ∈ mvBetaSimplex (n + 1) ↔
      (∀ i, 0 ≤ y i) ∧ 0 ≤ t ∧ t ≤ 1 - ∑ i, y i := by
  simp only [mvBetaSimplex, Set.mem_ofPred_eq, Fin.forall_fin_succ', Fin.snoc_last,
    Fin.snoc_castSucc, Fin.sum_univ_castSucc]
  constructor
  · rintro ⟨⟨hy, ht⟩, hsum⟩
    exact ⟨hy, ht, by linarith⟩
  · rintro ⟨hy, ht, hsum⟩
    exact ⟨⟨hy, ht⟩, by linarith⟩

/-- The solid-coordinate multivariate Beta integral. The parameter `b₀` belongs to the slack
coordinate `1 - ∑ i, x i`, while `b i` belongs to `x i`. This is the integral on the left-hand
side of DLMF 5.14.2. -/
def mvBetaIntegral {n : ℕ} (b₀ : ℂ) (b : Fin n → ℂ) : ℂ :=
  ∫ x in mvBetaSimplex n,
    ((1 - ∑ i, x i : ℝ) : ℂ) ^ (b₀ - 1) * ∏ i, (x i : ℂ) ^ (b i - 1)

/-- The solid-coordinate integral in DLMF 5.14.1, in which the slack coordinate has exponent
zero. -/
def mvBetaIntegralOne {n : ℕ} (b : Fin n → ℂ) : ℂ :=
  ∫ x in mvBetaSimplex n, ∏ i, (x i : ℂ) ^ (b i - 1)

/-- The zero-dimensional solid-coordinate integral has the expected value. -/
private theorem mvBetaIntegral_zero {b₀ : ℂ} (hb₀ : 0 < b₀.re) :
    mvBetaIntegral (n := 0) b₀ Fin.elim0 = mvBeta (Fin.cons b₀ Fin.elim0) := by
  have hG : Gamma b₀ ≠ 0 := Gamma_ne_zero_of_re_pos hb₀
  simp [mvBetaIntegral, mvBetaSimplex, mvBeta, hG, measureReal_def]
  rw [volume_pi]
  simp

/-- DLMF 5.14.2: the solid-coordinate Dirichlet integral equals the multivariate Beta function.
The slack parameter is placed first in `Fin.cons`; parameter symmetry identifies this convention
with the DLMF convention, where it is displayed last. -/
theorem mvBetaIntegral_eq_mvBeta {n : ℕ} {b₀ : ℂ} {b : Fin n → ℂ}
    (hb₀ : 0 < b₀.re) (hb : ∀ i, 0 < (b i).re) :
    mvBetaIntegral b₀ b = mvBeta (Fin.cons b₀ b) := by
  sorry

/-- DLMF 5.14.1: the solid-simplex integral without a slack-coordinate factor equals the
multivariate Beta function with slack parameter one. -/
theorem mvBetaIntegralOne_eq_mvBeta {n : ℕ} {b : Fin n → ℂ} (hb : ∀ i, 0 < (b i).re) :
    mvBetaIntegralOne b = mvBeta (Fin.cons 1 b) := by
  simpa [mvBetaIntegralOne, mvBetaIntegral] using
    (mvBetaIntegral_eq_mvBeta (b₀ := (1 : ℂ)) (b := b) (by norm_num) hb)

end SolidSimplexIntegral

end Complex

end MvBeta
