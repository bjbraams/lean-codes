/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF4GeneralMatrix
public import Carlson.Jacobi.AppellF4
public import Carlson.TwoVariable.RPolynomial.Hypergeometric
public import Pochhammer.Convolution

/-!
# Burchnall–Chaundy coefficients for the unrestricted F₄ matrix

The coefficient of `x^M y^N` after substituting `x(1-y), y(1-x)` in F₄
is a finite binomial sum. Gamma's reciprocal recurrence and Chu–Vandermonde
collapse it; the finite Pochhammer transformation identifies the result with
the matrix coefficient. Reciprocal Gamma, rather than division by nonzero
Gamma values, keeps all complex parameters, including denominator poles.
-/

open Complex Polynomial Finset Set Dirichlet
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The coefficient obtained by the formal substitution `x(1-y), y(1-x)` in regularized F₄. -/
def appellF4SubstitutionCoeff (a b c d : ℂ) (M N : ℕ) : ℂ :=
  ∑ p ∈ antidiagonal M, ∑ q ∈ antidiagonal N,
    regularizedAppellF4Coeff a b c d (p.1, q.1) *
      (q.1.choose p.2 : ℂ) * (p.1.choose q.2 : ℂ) * (-1 : ℂ) ^ (p.2 + q.2)

/-- Invalid binomial indices contribute zero to the formal substitution. -/
private theorem substitution_sum_filter (f : ℕ → ℕ → ℂ) (M N : ℕ) :
    ∑ v ∈ (antidiagonal M ×ˢ antidiagonal N).filter
        (fun v => v.2.2 ≤ v.1.1 ∧ v.1.2 ≤ v.2.1),
      f v.1.1 v.2.1 * (v.2.1.choose v.1.2 : ℂ) *
        (v.1.1.choose v.2.2 : ℂ) * (-1 : ℂ) ^ (v.1.2 + v.2.2) =
      ∑ v ∈ (antidiagonal M ×ˢ antidiagonal N),
        f v.1.1 v.2.1 * (v.2.1.choose v.1.2 : ℂ) *
          (v.1.1.choose v.2.2 : ℂ) * (-1 : ℂ) ^ (v.1.2 + v.2.2) := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hnot
  have hbad : ¬(v.2.2 ≤ v.1.1 ∧ v.1.2 ≤ v.2.1) := by
    simpa only [Finset.mem_filter, hv, true_and] using hnot
  by_cases h : v.2.2 ≤ v.1.1
  · have hzero := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge (fun h' => hbad ⟨h, h'⟩))
    rw [hzero]; simp
  · have hzero := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)
    rw [hzero]; simp

/-- Reindexing the two binomial expansions by their common degree loss. -/
private theorem substitution_sum_reindex (f : ℕ → ℕ → ℂ) (M N : ℕ) :
    ∑ p ∈ antidiagonal M, ∑ q ∈ antidiagonal N,
      f p.1 q.1 * (q.1.choose p.2 : ℂ) * (p.1.choose q.2 : ℂ) * (-1 : ℂ) ^ (p.2 + q.2) =
      ∑ k ∈ range (min M N + 1), ∑ q ∈ antidiagonal k,
        f (M - q.1) (N - q.2) * ((N - q.2).choose q.1 : ℂ) *
          ((M - q.1).choose q.2 : ℂ) * (-1 : ℂ) ^ k := by
  classical
  rw [← Finset.sum_product']
  trans ∑ v ∈ (antidiagonal M ×ˢ antidiagonal N).filter
      (fun v => v.2.2 ≤ v.1.1 ∧ v.1.2 ≤ v.2.1),
    f v.1.1 v.2.1 * (v.2.1.choose v.1.2 : ℂ) *
      (v.1.1.choose v.2.2 : ℂ) * (-1 : ℂ) ^ (v.1.2 + v.2.2)
  · exact (substitution_sum_filter f M N).symm
  rw [Finset.sum_sigma']
  let e : (ℕ × ℕ) × (ℕ × ℕ) → (Σ _ : ℕ, ℕ × ℕ) :=
    fun v => ⟨v.1.2 + v.2.2, (v.1.2, v.2.2)⟩
  let j : (Σ _ : ℕ, ℕ × ℕ) → (ℕ × ℕ) × (ℕ × ℕ) :=
    fun v => ((M - v.2.1, v.2.1), (N - v.2.2, v.2.2))
  apply Finset.sum_nbij' e j
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_product, mem_antidiagonal] at hv
    simp only [Finset.mem_sigma, Finset.mem_range, mem_antidiagonal, Nat.lt_succ_iff, Nat.le_min]
    dsimp [e]
    omega
  · intro v hv
    simp only [Finset.mem_sigma, Finset.mem_range, mem_antidiagonal,
      Nat.lt_succ_iff, Nat.le_min] at hv
    simp only [Finset.mem_filter, Finset.mem_product, mem_antidiagonal]
    dsimp [j]
    omega
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_product, mem_antidiagonal] at hv
    apply Prod.ext <;> apply Prod.ext <;> dsimp [j, e] <;> omega
  · intro v hv
    simp only [Finset.mem_sigma, Finset.mem_range, mem_antidiagonal,
      Nat.lt_succ_iff, Nat.le_min] at hv
    apply Sigma.ext
    · dsimp [e, j]; omega
    · exact heq_of_eq rfl
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_product, mem_antidiagonal] at hv
    dsimp [e]
    rw [show M - v.1.2 = v.1.1 by omega, show N - v.2.2 = v.2.1 by omega]

/-- A reciprocal Gamma shift reflected about its final index, valid also at Gamma poles. -/
private theorem inv_Gamma_shift_reflect (z : ℂ) (m s : ℕ) :
    (Gamma (z + m))⁻¹ = (-1 : ℂ) ^ s *
      (ascPochhammer ℂ s).eval (1 - z - (m + s : ℕ)) * (Gamma (z + (m + s : ℕ)))⁻¹ := by
  have h := one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat (z + m) s
  rw [show z + m + s = z + (m + s : ℕ) by push_cast; ring] at h
  have hp : (ascPochhammer ℂ s).eval (z + m) =
      (-1 : ℂ) ^ s * (ascPochhammer ℂ s).eval (1 - z - (m + s : ℕ)) := by
    conv_lhs => arg 1; rw [show z + m =
      1 - (1 - z - (m + s : ℕ)) - s by push_cast; ring]
    rw [ascPochhammer_eval_reflect]
  simpa only [hp, one_div] using h

/-- The weighted matrix moment expanded into monomials. Its terms are the ones collected
in `appellF4MatrixSeriesCoeff`; this is an identity of finite sums for all parameters. -/
theorem appellF4MatrixMoment_weighted_eq_sum (a b c d x y : ℂ) (J : ℕ) :
    (ascPochhammer ℂ J).eval a / (J.factorial : ℂ) *
      appellF4MatrixMoment x y J
        (appellF2Parameters b c, appellF4ColumnParameters a b c d) =
      ∑ q ∈ antidiagonal J, ∑ r ∈ antidiagonal q.1,
        ((ascPochhammer ℂ J).eval a * (ascPochhammer ℂ q.1).eval b *
          (q.1.choose r.1 : ℂ) * (-1 : ℂ) ^ r.1 *
          (ascPochhammer ℂ r.1).eval (c + d - a - 1) *
          (ascPochhammer ℂ q.2).eval (b + r.1) /
          ((q.1.factorial : ℂ) * q.2.factorial * Gamma (c + q.1) *
            Gamma (d + (r.1 + q.2 : ℕ)))) * x ^ q.1 * y ^ (r.1 + q.2) := by
  have hcol : appellF4ColumnParameters a b c d 0 +
      appellF4ColumnParameters a b c d 1 + appellF4ColumnParameters a b c d 2 = d := by
    simp only [appellF4ColumnParameters, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    ring
  rw [appellF4MatrixMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [appellF4ColumnMoment, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hdeg := mem_antidiagonal.mp hq
  rw [hcol, appellF4ColumnParameters_add]
  simp only [appellF2Parameters, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show b + (c - b) + q.1 = c + q.1 by ring]
  simp only [appellF4ColumnParameters, Matrix.cons_val_zero]
  rw [← hdeg, Nat.cast_add_choose ℂ]
  rw [neg_pow, pow_add]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm,
    mul_assoc, Nat.cast_ne_zero.mpr (q.1 + q.2).factorial_ne_zero]

/-- The factorial and reciprocal-Gamma cancellations for one substituted coefficient. -/
private theorem substitution_summand (a b c d : ℂ) (L R s t : ℕ) :
    regularizedAppellF4Coeff a b c d (L + t, R + s) *
        ((R + s).choose s : ℂ) * ((L + t).choose t : ℂ) * (-1 : ℂ) ^ (s + t) =
      ((ascPochhammer ℂ (L + R + s + t)).eval a *
          (ascPochhammer ℂ (L + R + s + t)).eval b /
        (((s + t).factorial : ℂ) * L.factorial * R.factorial *
          Gamma (c + (L + s + t : ℕ)) * Gamma (d + (R + s + t : ℕ)))) *
        ((s + t).choose s : ℂ) *
        ((ascPochhammer ℂ s).eval (1 - c - (L + s + t : ℕ)) *
          (ascPochhammer ℂ t).eval (1 - d - (R + s + t : ℕ))) := by
  rw [regularizedAppellF4Coeff_eq,
    Nat.cast_choose ℂ (Nat.le_add_left s R),
    Nat.cast_choose ℂ (Nat.le_add_left t L), Nat.add_sub_cancel_right,
    Nat.add_sub_cancel_right, Nat.cast_add_choose ℂ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  rw [inv_Gamma_shift_reflect c (L + t) s, inv_Gamma_shift_reflect d (R + s) t]
  simp only [show L + t + (R + s) = L + R + s + t by omega,
    show L + t + s = L + s + t by omega, add_assoc]
  have hs : (-1 : ℂ) ^ (s + t) * ((-1) ^ s * (-1) ^ t) = 1 := by
    rw [← pow_add, ← mul_pow]; norm_num
  generalize (ascPochhammer ℂ (L + (R + (s + t)))).eval a = A
  generalize (ascPochhammer ℂ (L + (R + (s + t)))).eval b = B
  generalize (ascPochhammer ℂ s).eval (1 - c - (L + (s + t) : ℕ)) = C
  generalize (ascPochhammer ℂ t).eval (1 - d - (R + (s + t) : ℕ)) = D
  generalize (Gamma (c + (L + (s + t) : ℕ)))⁻¹ = G
  generalize (Gamma (d + (R + (s + t) : ℕ)))⁻¹ = H
  have hfac : ∀ n : ℕ, (n.factorial : ℂ) ≠ 0 :=
    fun n => Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp [hfac]
  linear_combination A * B * C * D * G * H * hs

/-- **Burchnall–Chaundy substitution, collapsed coefficient formula.**
The double binomial sum reduces to one sum, without excluding denominator poles. -/
theorem appellF4SubstitutionCoeff_eq_sum (a b c d : ℂ) (M N : ℕ) :
    appellF4SubstitutionCoeff a b c d M N =
      ∑ k ∈ range (min M N + 1),
        (ascPochhammer ℂ (M + N - k)).eval a *
          (ascPochhammer ℂ (M + N - k)).eval b *
          (ascPochhammer ℂ k).eval (2 - c - d - M - N) /
        ((k.factorial : ℂ) * (M - k).factorial * (N - k).factorial *
          Gamma (c + M) * Gamma (d + N)) := by
  rw [appellF4SubstitutionCoeff,
    substitution_sum_reindex (fun m n => regularizedAppellF4Coeff a b c d (m, n))]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ M := (Nat.le_min.mp (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).1
  have hkn : k ≤ N := (Nat.le_min.mp (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).2
  let T := (ascPochhammer ℂ (M + N - k)).eval a *
    (ascPochhammer ℂ (M + N - k)).eval b /
      ((k.factorial : ℂ) * (M - k).factorial * (N - k).factorial *
        Gamma (c + M) * Gamma (d + N))
  calc
    _ = T * ∑ q ∈ antidiagonal k, (k.choose q.1 : ℂ) *
        ((ascPochhammer ℂ q.1).eval (1 - c - M) *
          (ascPochhammer ℂ q.2).eval (1 - d - N)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hdeg := mem_antidiagonal.mp hq
      have h := substitution_summand a b c d (M - k) (N - k) q.1 q.2
      have h1 : M - k + q.2 = M - q.1 := by omega
      have h2 : N - k + q.1 = N - q.2 := by omega
      have h3 : M - k + q.1 + q.2 = M := by omega
      have h4 : N - k + q.1 + q.2 = N := by omega
      have h5 : M - k + (N - k) + q.1 + q.2 = M + N - k := by omega
      rw [h3, h4, h5, hdeg] at h
      simpa only [h1, h2, T, mul_assoc] using h
    _ = _ := by
      rw [← ascPochhammer_eval_add]
      rw [show 1 - c - M + (1 - d - N) = 2 - c - d - M - N by ring]
      dsimp [T]
      ring

/-- Normalization of a terminating binomial convolution by numerical factorials. -/
private theorem terminating_convolution (f : ℕ → ℕ → ℂ) (M N : ℕ) :
    ∑ p ∈ antidiagonal N, (N.choose p.1 : ℂ) *
        (ascPochhammer ℂ p.1).eval (-(M : ℂ)) * (-1 : ℂ) ^ p.1 * f p.1 p.2 /
          ((M.factorial : ℂ) * N.factorial) =
      ∑ k ∈ range (min M N + 1),
        f k (N - k) / ((k.factorial : ℂ) * (M - k).factorial * (N - k).factorial) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  trans ∑ k ∈ range (min M N + 1), (N.choose k : ℂ) *
    (ascPochhammer ℂ k).eval (-(M : ℂ)) * (-1 : ℂ) ^ k * f k (N - k) /
      ((M.factorial : ℂ) * N.factorial)
  · apply Finset.sum_congr rfl
    intro k hk
    have hkm : k ≤ M := (Nat.le_min.mp (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).1
    have hkn : k ≤ N := (Nat.le_min.mp (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).2
    rw [ascPochhammer_eval_neg_natCast, Nat.cast_choose ℂ hkm, Nat.cast_choose ℂ hkn]
    have hs : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    generalize f k (N - k) = F
    have hfac : ∀ n : ℕ, (n.factorial : ℂ) ≠ 0 :=
      fun n => Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp [hfac]
    linear_combination -F * hs
  · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.min_le_right M N)))
    intro k hk hnot
    have hkn : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hkm : M < k := by
      simp only [Finset.mem_range] at hnot
      omega
    rw [ascPochhammer_eval_neg_natCast, Nat.choose_eq_zero_of_lt hkm]
    simp

/-- The collapsed coefficient in terminating-convolution form. -/
private theorem substitutionCoeff_eq_convolution (a b c d : ℂ) (M N : ℕ) :
    appellF4SubstitutionCoeff a b c d M N =
      ∑ p ∈ antidiagonal N, (N.choose p.1 : ℂ) *
        (ascPochhammer ℂ p.1).eval (-(M : ℂ)) * (-1 : ℂ) ^ p.1 *
        ((ascPochhammer ℂ (M + p.2)).eval a *
          (ascPochhammer ℂ (M + p.2)).eval b *
          (ascPochhammer ℂ p.1).eval (2 - c - d - M - N) /
            (Gamma (c + M) * Gamma (d + N))) /
        ((M.factorial : ℂ) * N.factorial) := by
  rw [terminating_convolution (fun k l =>
    (ascPochhammer ℂ (M + l)).eval a * (ascPochhammer ℂ (M + l)).eval b *
      (ascPochhammer ℂ k).eval (2 - c - d - M - N) /
        (Gamma (c + M) * Gamma (d + N))) M N, appellF4SubstitutionCoeff_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ N := (Nat.le_min.mp (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).2
  rw [show M + (N - k) = M + N - k by omega]
  ring

/-- The coefficient transformation from the substituted F₄ series to the unrestricted matrix
convolution. Every complex parameter is allowed, including denominator poles. -/
theorem appellF4SubstitutionCoeff_eq_burchnallChaundy (a b c d : ℂ) (M N : ℕ) :
    appellF4SubstitutionCoeff a b c d M N =
      ∑ p ∈ antidiagonal N, (N.choose p.1 : ℂ) *
        (ascPochhammer ℂ p.1).eval (-(M : ℂ)) *
        (ascPochhammer ℂ (M + p.2)).eval a *
        (ascPochhammer ℂ p.1).eval (c + d - a - 1) *
        ((ascPochhammer ℂ M).eval b * (ascPochhammer ℂ p.2).eval (b + p.1)) /
        ((M.factorial : ℂ) * N.factorial * Gamma (c + M) * Gamma (d + N)) := by
  rw [← Finset.sum_div, ascPochhammer_eval_burchnallChaundy_reflect]
  rw [show 1 - a - (c + d - a - 1) - M - N = 2 - c - d - M - N by ring,
    Finset.sum_div, substitutionCoeff_eq_convolution]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Coefficients of the scalar kernel expansion of the unrestricted F₄ matrix, collected
by the powers of `x` and `y`. The column parameter is `c+d-a-1`. -/
def appellF4MatrixSeriesCoeff (a b c d : ℂ) (M N : ℕ) : ℂ :=
  ∑ p ∈ antidiagonal N,
    (ascPochhammer ℂ (M + p.2)).eval a * (ascPochhammer ℂ M).eval b *
      (M.choose p.1 : ℂ) * (-1 : ℂ) ^ p.1 *
      (ascPochhammer ℂ p.1).eval (c + d - a - 1) *
      (ascPochhammer ℂ p.2).eval (b + p.1) /
      ((M.factorial : ℂ) * p.2.factorial * Gamma (c + M) * Gamma (d + N))

/-- Numerical weights converting matrix binomials into the terminating convolution. -/
private theorem matrix_convolution_weight (M k l : ℕ) :
    ((k + l).choose k : ℂ) * (ascPochhammer ℂ k).eval (-(M : ℂ)) /
        ((M.factorial : ℂ) * (k + l).factorial) =
      (M.choose k : ℂ) * (-1 : ℂ) ^ k / ((M.factorial : ℂ) * l.factorial) := by
  rw [ascPochhammer_eval_neg_natCast, Nat.cast_add_choose ℂ]
  have hfac : ∀ n : ℕ, (n.factorial : ℂ) ≠ 0 :=
    fun n => Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp [hfac]

/-- **Burchnall–Chaundy coefficient identity.** The formal substitution in F₄ and the
unrestricted matrix kernel expansion have identical coefficients, at all parameters. -/
theorem appellF4SubstitutionCoeff_eq_matrixSeriesCoeff (a b c d : ℂ) (M N : ℕ) :
    appellF4SubstitutionCoeff a b c d M N = appellF4MatrixSeriesCoeff a b c d M N := by
  rw [appellF4SubstitutionCoeff_eq_burchnallChaundy, appellF4MatrixSeriesCoeff]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := mem_antidiagonal.mp hp
  have hw := matrix_convolution_weight M p.1 p.2
  rw [hdeg] at hw
  simp only [div_eq_mul_inv, mul_inv_rev] at hw ⊢
  linear_combination
    ((ascPochhammer ℂ (M + p.2)).eval a * (ascPochhammer ℂ M).eval b *
      (ascPochhammer ℂ p.1).eval (c + d - a - 1) *
      (ascPochhammer ℂ p.2).eval (b + p.1) *
      (Gamma (c + M))⁻¹ * (Gamma (d + N))⁻¹) * hw

/-- The balanced column parameters separate the finite convolution into Gauss factors. -/
private theorem balanced_convolution (a b : ℂ) (M N : ℕ) :
    ∑ p ∈ antidiagonal N, (N.choose p.1 : ℂ) *
        (ascPochhammer ℂ p.1).eval (-(M : ℂ)) *
        (ascPochhammer ℂ (M + p.2)).eval a * (ascPochhammer ℂ p.1).eval b *
        ((ascPochhammer ℂ M).eval b * (ascPochhammer ℂ p.2).eval (b + p.1)) =
      (ascPochhammer ℂ M).eval a * (ascPochhammer ℂ M).eval b *
        (ascPochhammer ℂ N).eval a * (ascPochhammer ℂ N).eval b := by
  have hs := ascPochhammer_eval_add (-(M : ℂ)) (a + M) N
  rw [show -(M : ℂ) + (a + M) = a by ring] at hs
  calc
    _ = ((ascPochhammer ℂ M).eval a * (ascPochhammer ℂ M).eval b *
        (ascPochhammer ℂ N).eval b) *
        ∑ p ∈ antidiagonal N, (N.choose p.1 : ℂ) *
          ((ascPochhammer ℂ p.1).eval (-(M : ℂ)) *
            (ascPochhammer ℂ p.2).eval (a + M)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hb : (ascPochhammer ℂ N).eval b = (ascPochhammer ℂ p.1).eval b *
          (ascPochhammer ℂ p.2).eval (b + p.1) := by
        rw [← mem_antidiagonal.mp hp, ascPochhammer_add_eval]
      rw [ascPochhammer_add_eval, hb]
      ring
    _ = _ := by rw [← hs]; ring

/-- **Carlson (1975), (4.1), coefficient form.** Under the balance condition the
substituted F₄ coefficients are products of regularized Gauss coefficients. -/
theorem appellF4SubstitutionCoeff_balanced {a b c d : ℂ} (h : c + d = a + b + 1)
    (M N : ℕ) :
    appellF4SubstitutionCoeff a b c d M N =
      ((ascPochhammer ℂ M).eval a * (ascPochhammer ℂ M).eval b /
        ((M.factorial : ℂ) * Gamma (c + M))) *
      ((ascPochhammer ℂ N).eval a * (ascPochhammer ℂ N).eval b /
        ((N.factorial : ℂ) * Gamma (d + N))) := by
  rw [appellF4SubstitutionCoeff_eq_burchnallChaundy,
    show c + d - a - 1 = b by rw [h]; ring,
    ← Finset.sum_div, balanced_convolution]
  ring

/-- **Carlson (1975), (4.3), coefficient form.** A zero first column parameter reduces
the substituted F₄ coefficients to the regularized F₂ coefficients. -/
theorem appellF4SubstitutionCoeff_eq_F2 {a b c d : ℂ} (h : c + d = a + 1) (M N : ℕ) :
    appellF4SubstitutionCoeff a b c d M N = regularizedAppellF2Coeff a b b c d (M, N) := by
  rw [appellF4SubstitutionCoeff_eq_matrixSeriesCoeff, appellF4MatrixSeriesCoeff,
    show c + d - a - 1 = 0 by rw [h]; ring, Finset.sum_eq_single (0, N)]
  · simp only [regularizedAppellF2Coeff_eq, Nat.choose_zero_right, Nat.cast_one,
      pow_zero, ascPochhammer_zero, Polynomial.eval_one, Nat.cast_zero, add_zero, mul_one]
  · intro p hp hne
    have hp0 : p.1 ≠ 0 := by
      intro hz
      apply hne
      have hdeg := mem_antidiagonal.mp hp
      exact Prod.ext hz (by omega)
    rw [ascPochhammer_ne_zero_eval_zero ℂ hp0]
    simp
  · simp

end Carlson.TwoVariable
