/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF4Restricted
public import Carlson.TwoVariable.AppellF1
public import Carlson.R.BinomialSeries
public import Carlson.R.Homogeneity

/-!
# The F₁ reduction of F₄ with equal numerator and denominator parameters

The repeated-row matrix collapses to a three-node R-function. Its reciprocal
Gamma factor remains explicit at exceptional column totals. Homogeneity and
the existing F₁ identification give the customary scalar reduction.
-/

open Complex Polynomial Set Finset Dirichlet
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The three nodes obtained by collapsing the repeated-row F₁ matrix. -/
def appellF4F1Nodes (x y : ℂ) : Fin 2 ⊕ Unit → ℂ :=
  Sum.elim (pair (1 - x - y) ((1 - x) * (1 - y))) (fun _ => 1 - y)

/-- The two-node polynomial at `1,1-y` has an entire beta-coordinate expansion. -/
private theorem regRPolynomial_one_one_sub (m : ℕ) (B A y : ℂ) :
    regRPolynomial m B A 1 (1 - y) =
      ∑ k ∈ antidiagonal m, (m.choose k.1 : ℂ) * (-y) ^ k.1 *
        ((ascPochhammer ℂ k.1).eval A / Gamma (B + A + k.1)) := by
  have hc (k : ℕ) : regRPolynomial k B A 0 (-y) =
      (-y) ^ k * (ascPochhammer ℂ k).eval A / Gamma (B + A + k) := by
    rw [regRPolynomial_swap k A B (-y) 0,
      regRPolynomial_eq_numerator₂_mul_one_div_Gamma, carlsonRPolynomialNumerator₂_zero_right,
      show A + B + k = B + A + k by ring]
    ring
  have h := regCarlsonRPolynomial_add_const m 1 (pair 0 (-y)) (pair B A)
  change regRPolynomial m B A (0 + 1) (-y + 1) =
    ∑ k ∈ range (m + 1), (m.choose k : ℂ) * 1 ^ (m - k) * regRPolynomial k B A 0 (-y) at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa only [zero_add, show -y + 1 = 1 - y by ring, one_pow, mul_one, hc,
    mul_div_assoc, mul_assoc] using h

/-- The shifted three-node moment expanded around its repeated node. -/
private theorem F1_nodes_moment (B A c x y : ℂ) (N : ℕ) :
    regCarlsonRPolynomial N (appellDirichletParameters B A c) (fun i => 1 - appellF4F1Nodes x y i) =
      ∑ q ∈ antidiagonal N, (N.choose q.1 : ℂ) * x ^ q.1 * y ^ q.2 *
        (carlsonRPolynomialNumerator₂ q.1 B A 1 (1 - y) / Gamma (c + q.1)) := by
  let z : Fin 2 ⊕ Unit → ℂ := Sum.elim (pair x (x * (1 - y))) (fun _ => 0)
  have he : (fun i => 1 - appellF4F1Nodes x y i) = fun i => z i + y := by
    funext i
    cases i with
    | inl i => fin_cases i <;> simp [appellF4F1Nodes, z, pair] <;> ring
    | inr i => simp [appellF4F1Nodes, z]
  have hc : ∑ i, appellDirichletParameters B A c i = c := by
    simp [appellDirichletParameters, Fintype.sum_sum_type]
  have hn (m : ℕ) : regCarlsonRPolynomial m (appellDirichletParameters B A c) z =
      x ^ m * carlsonRPolynomialNumerator₂ m B A 1 (1 - y) / Gamma (c + m) := by
    rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, hc]
    change carlsonRPolynomialNumerator m (Sum.elim (pair B A) (fun _ => c - B - A))
      (Sum.elim (pair x (x * (1 - y))) (fun _ => 0)) * (Gamma (c + m))⁻¹ = _
    rw [numerator_sumElim_zero, carlsonRPolynomialNumerator_pair]
    have hs : pair x (x * (1 - y)) = fun i => x * pair 1 (1 - y) i := by
      funext i; fin_cases i <;> simp [pair]
    rw [← carlsonRPolynomialNumerator_pair, hs, carlsonRPolynomialNumerator_smul,
      carlsonRPolynomialNumerator_pair]
    ring
  rw [he, regCarlsonRPolynomial_add_const, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro m _
  rw [hn]
  ring

/-- The repeated-row moments collapse to a three-node moment, with the reciprocal
column-total Gamma factor retained at its zeros. -/
theorem appellF4F1Moment_eq_three_node (B A c x y : ℂ) (N : ℕ) :
    appellF4F1Moment x y N (appellF2Parameters (B + A) c, pair B A) =
      (Gamma (B + A))⁻¹ * regCarlsonRPolynomial N (appellDirichletParameters B A c)
        (fun i => 1 - appellF4F1Nodes x y i) := by
  rw [F1_nodes_moment, Finset.mul_sum, appellF4F1Moment]
  apply Finset.sum_congr rfl
  intro q _
  simp only [appellF2Parameters, Matrix.cons_val_zero, Matrix.cons_val_one,
    pair_zero, pair_one, show B + A + (c - (B + A)) = c by ring]
  have hi : (∑ k ∈ antidiagonal q.1, (q.1.choose k.1 : ℂ) * (-y) ^ k.1 * y ^ q.2 *
      ((ascPochhammer ℂ k.1).eval A / Gamma (B + A + k.1))) =
        y ^ q.2 * regRPolynomial q.1 B A 1 (1 - y) := by
    rw [regRPolynomial_one_one_sub, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hi, regRPolynomial_eq_numerator₂_mul_one_div_Gamma]
  have hG := one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat (B + A) q.1
  simp only [div_eq_mul_inv] at hG ⊢
  linear_combination
    -((N.choose q.1 : ℂ) * x ^ q.1 * y ^ q.2 *
      (Gamma (c + q.1))⁻¹ * carlsonRPolynomialNumerator₂ q.1 B A 1 (1 - y)) * hG

/-- The collapsed three-node variables lie in the same entry disk as the unrestricted matrix. -/
private theorem F1_nodes_entry_bound (x y : ℂ) (i : Fin 2 ⊕ Unit) :
    ‖appellF4F1Nodes x y i - 1‖ ≤ appellF4MatrixRadius x y := by
  cases i with
  | inl i =>
    fin_cases i
    · exact norm_appellF4Matrix_sub_one_le x y 0 1
    · exact norm_appellF4Matrix_sub_one_le x y 0 0
  | inr i => exact norm_appellF4Matrix_sub_one_le x y 1 0

/-- The repeated-row matrix is a three-node R-function at every complex parameter.
This division-free formula includes nonpositive integral column totals. -/
theorem continued_appellF4F1Matrix_eq_three_node (a B A c : ℂ) {x y : ℂ}
    (hxy : appellF4MatrixRadius x y < 1) :
    continuedRegMatrixDirichletAverage (appellF4F1Matrix x y) (fun z => z ^ (-a))
      (appellF2Parameters (B + A) c, pair B A) =
        (Gamma (B + A))⁻¹ * regCarlsonR (-a) (appellDirichletParameters B A c)
          (appellF4F1Nodes x y) := by
  have hL := hasSum_appellF4Matrix_moments a (appellF2Parameters (B + A) c) ![A, B, 0] hxy
  have hR := (hasSum_regCarlsonR_cpow_neg a (appellDirichletParameters B A c)
    (fun i => (F1_nodes_entry_bound x y i).trans_lt hxy)).mul_left ((Gamma (B + A))⁻¹)
  have hm : ![A, B, 0] = ![(pair B A) 1, (pair B A) 0, 0] := rfl
  rw [hm] at hL
  simp only [appellF4MatrixMoment_zero_last, appellF4F1Moment_eq_three_node] at hL
  rw [continuedRegMatrixDirichletAverage_appellF4_zero_last a _ _ hxy] at hL
  apply hL.unique
  convert hR using 1
  funext n
  ring

/-- The standard F₁ reduction arguments lie in their full bidisk on the original diamond. -/
private theorem F1_reduction_arguments {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    ‖x / (1 - y)‖ < 1 ∧ ‖x‖ < 1 ∧ 0 < (1 - y).re := by
  have hlow : 1 - ‖y‖ ≤ ‖1 - y‖ := by simpa using norm_sub_norm_le (1 : ℂ) y
  have hden : 0 < ‖1 - y‖ := lt_of_lt_of_le (by linarith [norm_nonneg x]) hlow
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_div]
    exact (div_lt_one hden).mpr (by linarith)
  · linarith [norm_nonneg y]
  · simp only [sub_re, one_re]
    linarith [re_le_norm y, norm_nonneg x]

/-- Homogeneity identifies the three-node collapse with the regularized F₁ series. -/
theorem regCarlsonR_appellF4F1Nodes (a B A c : ℂ) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    regCarlsonR (-a) (appellDirichletParameters B A c) (appellF4F1Nodes x y) =
      (1 - y) ^ (-a) * regularizedAppellF1 a B A c (x / (1 - y)) x := by
  obtain ⟨hX, hx, hr⟩ := F1_reduction_arguments hxy
  have hden : 1 - y ≠ 0 := fun h => by rw [h] at hr; simp at hr
  have hz : appellCarlsonNodes (x / (1 - y)) x ∈ carlsonRVariableDomain := by
    intro i
    cases i with
    | inl i =>
      fin_cases i
      · change 0 < (1 - x / (1 - y)).re
        simp only [sub_re, one_re]
        linarith [re_le_norm (x / (1 - y))]
      · change 0 < (1 - x).re
        simp only [sub_re, one_re]
        linarith [re_le_norm x]
    | inr i => norm_num [appellCarlsonNodes, carlsonRightHalfPlane]
  have he : appellF4F1Nodes x y =
      fun i => (1 - y) * appellCarlsonNodes (x / (1 - y)) x i := by
    funext i
    cases i with
    | inl i =>
      fin_cases i
      · change 1 - x - y = (1 - y) * (1 - x / (1 - y))
        rw [mul_sub, mul_one, mul_div_cancel₀ x hden]
        ring
      · change (1 - x) * (1 - y) = (1 - y) * (1 - x)
        ring
    | inr i => simp [appellF4F1Nodes, appellCarlsonNodes]
  rw [he, regCarlsonR_mul_of_re_pos (-a) _ hz hr,
    regCarlsonR_eq_regularizedAppellF1 a B A c hX hx]

/-- **Carlson (1975), (4.2), scalar F₁ reduction.** The reciprocal `Γ(b)` factor
is retained, so the regularized identity includes every complex parameter. -/
theorem regularizedAppellF4_eq_F1 (a b c : ℂ) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    regularizedAppellF4 a b c b (x * (1 - y)) (y * (1 - x)) =
      (Gamma b)⁻¹ * ((1 - y) ^ (-a) *
        regularizedAppellF1 a (1 + a - c) (c + b - a - 1) c (x / (1 - y)) x) := by
  have hreg := appellF4_reassembly_kernel_bound hxy
  have hd : ‖x‖ + ‖y‖ < 1 := by nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
  have hp : pair (1 + a - c) (c + b - a - 1) = appellF2Parameters (1 + a - c) b := by
    funext i
    fin_cases i
    · simp [pair, appellF2Parameters]
    · simp [pair, appellF2Parameters]; ring
  have H := continued_appellF4F1Matrix_eq_three_node a (1 + a - c) (c + b - a - 1) c
    ((appellF4MatrixRadius_le_sum_norm x y).trans_lt hreg)
  rw [show 1 + a - c + (c + b - a - 1) = b by ring, hp] at H
  rw [← continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_F1 a b c hxy, H,
    regCarlsonR_appellF4F1Nodes a (1 + a - c) (c + b - a - 1) c hd]

/-- Ordinary F₁ reduction when the cancelled `Γ(b)` factor is nonzero.
The regularized theorem supplies the exceptional-parameter values. -/
theorem appellF4_eq_F1 (a b c : ℂ) (hb : ∀ k : ℕ, b ≠ -(k : ℂ)) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    appellF4 a b c b (x * (1 - y)) (y * (1 - x)) =
      (1 - y) ^ (-a) * appellF1 a (1 + a - c) (c + b - a - 1) c (x / (1 - y)) x := by
  rw [appellF4, regularizedAppellF4_eq_F1 a b c hxy, Complex.appellF1]
  have hb0 := Gamma_ne_zero hb
  field_simp

end Carlson.TwoVariable
