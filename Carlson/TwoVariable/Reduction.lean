/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.QuadraticHybrid
public import Carlson.TwoVariable.R.Associated
public import Carlson.R.IntegerParameters
public import Carlson.R.IntegralEvaluation
public import Carlson.R.Homogeneity

/-!
# Reduction of two-variable R-functions to `R_C` (Table 8.5-1, Example 8.5-5)

When `a` and `b₁` are half-odd integers and `b₂` is an integer, `R_{-a}(b₁, b₂; x, y)` is a
combination of `R_C(x, y) = R_{-1/2}(1/2, 1; x, y)` and `x^{-1/2}` with polynomial coefficients
(Theorem 8.5-4). Carlson's Table 8.5-1 lists the coefficients in the cases `a', b₂ ∈ {1, 2}`,
`a, b₁ ∈ {-1/2, 1/2, 3/2}`, as identities `C R_{-a}(b₁, b₂; x, y) = C_C R_C(x, y) + C_A x^{-1/2}`.

Each row follows from the two contiguous relations, the parameter-raising relation and the
elementary values `R_{-b-b'}(b, b'; x, y) = x^{-b} y^{-b'}` (5.9-22), here for nodes in the right
half-plane.

## Main results

* `Carlson.TwoVariable.regCarlsonR_pair_neg_sum`: (5.9-22) for two nodes.
* `Carlson.TwoVariable.carlsonR_table_row_one` through `carlsonR_table_row_seven`: the seven rows
  of Table 8.5-1.
* `Carlson.TwoVariable.integral_sqrt_div_sqrt_affine`: Example 8.5-5, equation (6), from
  Formula 8.1-1 and the sixth row of the table.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.5.
-/

open Complex Set MeasureTheory Dirichlet
open scoped Real
@[expose] public noncomputable section

namespace Carlson.TwoVariable

variable {x y : ℂ}

/-- Carlson's (5.9-22) for two slit-plane nodes: `R_{-b-b'}(b, b'; x, y) = x^{-b} y^{-b'}`,
regularized. -/
theorem regCarlsonR_pair_neg_sum (b₀ b₁ : ℂ) (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    regCarlsonR (-(b₀ + b₁)) (pair b₀ b₁) (pair x y) =
      x ^ (-b₀) * y ^ (-b₁) * (Gamma (b₀ + b₁))⁻¹ := by
  have hz : pair x y ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hx
    · exact hy
  have h := regCarlsonR_neg_sum_sub_nat 0 (pair b₀ b₁) hz
  simp only [sum_pair, Nat.cast_zero, sub_zero, regCarlsonRPolynomial_zero, Fin.prod_univ_two,
    pair_zero, pair_one] at h
  exact h

/-- Right-half-plane nodes lie in the slit domain. -/
private theorem slit_of_re (hx : 0 < x.re) (hy : 0 < y.re) : pair x y ∈ carlsonRSlitDomain := by
  intro i; fin_cases i
  · exact mem_slitPlane_iff.mpr (Or.inl hx)
  · exact mem_slitPlane_iff.mpr (Or.inl hy)

/-- `Γ(3/2) = Γ(1/2)/2`. -/
private theorem Gamma_three_halves : Gamma (3 / 2 : ℂ) = Gamma (1 / 2) / 2 := by
  rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]; ring

/-- `Γ(5/2) = (3/2) Γ(3/2)`. -/
private theorem Gamma_five_halves : Gamma (5 / 2 : ℂ) = 3 / 2 * Gamma (3 / 2) := by
  rw [show (5 / 2 : ℂ) = 3 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]

/-- `Γ(7/2) = (5/2) Γ(5/2)`. -/
private theorem Gamma_seven_halves : Gamma (7 / 2 : ℂ) = 5 / 2 * Gamma (5 / 2) := by
  rw [show (7 / 2 : ℂ) = 5 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]

/-- The relations behind Table 8.5-1, collected. -/
private theorem table_relations (hx : 0 < x.re) (hy : 0 < y.re) :
    let r := fun t u v => regCarlsonR t (pair u v) (pair x y)
    (r (1 / 2) (1 / 2) 0 = r (1 / 2) (1 / 2) 1 - 1 / 2 * y * r (-1 / 2) (1 / 2) 1) ∧
    (0 = x * r (-1 / 2) (1 / 2) 0 - r (1 / 2) (1 / 2) 0) ∧
    (r (-1 / 2) (1 / 2) 0 = x ^ (-1 / 2 : ℂ) * (Gamma (1 / 2))⁻¹) ∧
    (r (-3 / 2) (1 / 2) 1 = x ^ (-1 / 2 : ℂ) * y ^ (-1 : ℂ) * (Gamma (3 / 2))⁻¹) ∧
    (r (-1 / 2) (-1 / 2) 1 = x * x ^ (-1 / 2 : ℂ) * y ^ (-1 : ℂ) * (Gamma (1 / 2))⁻¹) ∧
    (1 / 2 * (y - x) * r (-1 / 2) (3 / 2) 1 = y * r (-1 / 2) (1 / 2) 1 - r (1 / 2) (1 / 2) 1) ∧
    (1 / 2 * (y - x) * r (-3 / 2) (3 / 2) 1 = y * r (-3 / 2) (1 / 2) 1 - r (-1 / 2) (1 / 2) 1) ∧
    (r (-1 / 2) (-1 / 2) 1 = -1 / 2 * r (-1 / 2) (1 / 2) 1 + r (-1 / 2) (-1 / 2) 2) ∧
    ((x - y) * r (-1 / 2) (1 / 2) 2 = x * r (-1 / 2) (1 / 2) 1 - r (1 / 2) (1 / 2) 1) ∧
    ((x - y) * r (-3 / 2) (1 / 2) 2 = x * r (-3 / 2) (1 / 2) 1 - r (-1 / 2) (1 / 2) 1) ∧
    (1 / 2 * (y - x) * r (-3 / 2) (3 / 2) 2 = y * r (-3 / 2) (1 / 2) 2 - r (-1 / 2) (1 / 2) 2) := by
  intro r
  have hs := slit_of_re hx hy
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hE := regCarlsonR_eq_addDirichletUnit (1 / 2 : ℂ) (pair (1 / 2) 0) hs 1
    have hunit : addDirichletUnit (pair (1 / 2 : ℂ) 0) 1 = pair (1 / 2) 1 := by
      ext i; fin_cases i <;> simp [addDirichletUnit, pair]
    rw [hunit, sum_pair, pair_one, show (1 / 2 : ℂ) - 1 = -1 / 2 by norm_num] at hE
    simp only [r]; linear_combination hE
  · have hC := regCarlsonR_pair_contiguous_last (-1 / 2) (1 / 2) 0 hs
    rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num] at hC
    simp only [r]; linear_combination hC
  · have hV := regCarlsonR_pair_neg_sum (1 / 2) 0
      (carlsonRightHalfPlane_subset_slitPlane hx) (carlsonRightHalfPlane_subset_slitPlane hy)
    rw [show -(1 / 2 + 0 : ℂ) = -1 / 2 by ring, neg_zero, cpow_zero, mul_one, add_zero,
      show -(1 / 2 : ℂ) = -1 / 2 by ring] at hV
    exact hV
  · have hV := regCarlsonR_pair_neg_sum (1 / 2) 1
      (carlsonRightHalfPlane_subset_slitPlane hx) (carlsonRightHalfPlane_subset_slitPlane hy)
    rw [show -(1 / 2 + 1 : ℂ) = -3 / 2 by ring, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num,
      show -(1 / 2 : ℂ) = -1 / 2 by ring] at hV
    exact hV
  · have hV := regCarlsonR_pair_neg_sum (-1 / 2) 1
      (carlsonRightHalfPlane_subset_slitPlane hx) (carlsonRightHalfPlane_subset_slitPlane hy)
    rw [show -(-1 / 2 + 1 : ℂ) = -1 / 2 by ring, show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num,
      show -(-1 / 2 : ℂ) = 1 + -1 / 2 by ring, cpow_add _ _ hx0, cpow_one] at hV
    exact hV
  · have hC := regCarlsonR_pair_contiguous (-1 / 2) (1 / 2) 1 hs
    rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num] at hC
    exact hC
  · have hC := regCarlsonR_pair_contiguous (-3 / 2) (1 / 2) 1 hs
    rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, show (-3 / 2 : ℂ) + 1 = -1 / 2 by norm_num] at hC
    exact hC
  · have hS := regCarlsonR_eq_sum_addDirichletUnit (-1 / 2 : ℂ) (pair (-1 / 2) 1) hs
    have h0 : addDirichletUnit (pair (-1 / 2 : ℂ) 1) 0 = pair (1 / 2) 1 := by
      ext i; fin_cases i <;> simp [addDirichletUnit, pair]; norm_num
    have h1 : addDirichletUnit (pair (-1 / 2 : ℂ) 1) 1 = pair (-1 / 2) 2 := by
      ext i; fin_cases i <;> simp [addDirichletUnit, pair]; norm_num
    rw [Fin.sum_univ_two, h0, h1, pair_zero, pair_one] at hS
    simp only [r]; linear_combination hS
  · have hC := regCarlsonR_pair_contiguous_last (-1 / 2) (1 / 2) 1 hs
    rw [show (1 : ℂ) + 1 = 2 by norm_num, show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num] at hC
    simp only [r]; linear_combination hC
  · have hC := regCarlsonR_pair_contiguous_last (-3 / 2) (1 / 2) 1 hs
    rw [show (1 : ℂ) + 1 = 2 by norm_num, show (-3 / 2 : ℂ) + 1 = -1 / 2 by norm_num] at hC
    simp only [r]; linear_combination hC
  · have hC := regCarlsonR_pair_contiguous (-3 / 2) (1 / 2) 2 hs
    rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, show (-3 / 2 : ℂ) + 1 = -1 / 2 by norm_num] at hC
    exact hC

/-- Table 8.5-1, row `(b₁, b₂) = (1/2, 1)`, `(a, a') = (-1/2, 2)`:
`2 R_{1/2}(1/2, 1; x, y) = y R_C(x, y) + x x^{-1/2}`. -/
theorem carlsonR_table_row_one (hx : 0 < x.re) (hy : 0 < y.re) :
    2 * carlsonR (1 / 2) (pair (1 / 2) 1) (pair x y) = y * carlsonRC x y + x
        * x ^ (-1 / 2 : ℂ) := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  obtain ⟨hE1, hC1, hA, hB, hD, c2, c3, c4, c5, c6, c7⟩ := table_relations hx hy
  beta_reduce at hE1 hC1 hA hB hD c2 c3 c4 c5 c6 c7
  have hG : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have gG : Gamma (3 / 2 : ℂ) = Gamma (1 / 2) / 2 := Gamma_three_halves
  have g5r : Gamma (5 / 2 : ℂ) = 3 / 2 * Gamma (3 / 2) := Gamma_five_halves
  have g7r : Gamma (7 / 2 : ℂ) = 5 / 2 * Gamma (5 / 2) := Gamma_seven_halves
  have inv : Gamma (1 / 2 : ℂ) * (Gamma (1 / 2))⁻¹ = 1 := mul_inv_cancel₀ hG
  have Gg : Gamma (1 / 2 : ℂ) * (Gamma (3 / 2))⁻¹ = 2 := by rw [gG]; field_simp
  have yY : y * y ^ (-1 : ℂ) = 1 := by rw [cpow_neg_one, mul_inv_cancel₀ hy0]
  have RCd : carlsonRC x y = Gamma (3 / 2) * regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y) := by
    unfold carlsonRC carlsonR; rw [sum_pair, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num]
  unfold carlsonR
  rw [sum_pair, show (1 / 2 + 1 : ℂ) = 3 / 2 by norm_num]
  set K := regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y)
  set r1 := regCarlsonR (1 / 2) (pair (1 / 2) 1) (pair x y)
  set P := regCarlsonR (1 / 2) (pair (1 / 2) 0) (pair x y)
  set A := regCarlsonR (-1 / 2) (pair (1 / 2) 0) (pair x y)
  set r2 := regCarlsonR (-1 / 2) (pair (3 / 2) 1) (pair x y)
  set r3 := regCarlsonR (-3 / 2) (pair (3 / 2) 1) (pair x y)
  set B := regCarlsonR (-3 / 2) (pair (1 / 2) 1) (pair x y)
  set r4 := regCarlsonR (-1 / 2) (pair (-1 / 2) 2) (pair x y)
  set D := regCarlsonR (-1 / 2) (pair (-1 / 2) 1) (pair x y)
  set r5 := regCarlsonR (-1 / 2) (pair (1 / 2) 2) (pair x y)
  set r6 := regCarlsonR (-3 / 2) (pair (1 / 2) 2) (pair x y)
  set r7 := regCarlsonR (-3 / 2) (pair (3 / 2) 2) (pair x y)
  set s := x ^ (-1 / 2 : ℂ)
  set Y := y ^ (-1 : ℂ)
  set G := Gamma (1 / 2 : ℂ)
  set Gi := (Gamma (1 / 2 : ℂ))⁻¹
  set g3 := Gamma (3 / 2 : ℂ)
  set g3i := (Gamma (3 / 2 : ℂ))⁻¹
  set g5 := Gamma (5 / 2 : ℂ)
  set g7 := Gamma (7 / 2 : ℂ)
  set RC := carlsonRC x y
  linear_combination (-2*g3) * hE1 + (2*g3) * hC1 + (2*g3*x) * hA + (2*Gi*s*x) * gG + (s*x)
      * inv + (-y) * RCd

/-- Table 8.5-1, row `(3/2, 1)`, `(1/2, 2)`:
`2 (x - y) R_{-1/2}(3/2, 1) = -3y R_C + 3x x^{-1/2}`. -/
theorem carlsonR_table_row_two (hx : 0 < x.re) (hy : 0 < y.re) :
    2 * (x - y) * carlsonR (-1 / 2) (pair (3 / 2) 1) (pair x y) = -3 * y * carlsonRC x y + 3 * x
        * x ^ (-1 / 2 : ℂ) := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  obtain ⟨hE1, hC1, hA, hB, hD, c2, c3, c4, c5, c6, c7⟩ := table_relations hx hy
  beta_reduce at hE1 hC1 hA hB hD c2 c3 c4 c5 c6 c7
  have hG : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have gG : Gamma (3 / 2 : ℂ) = Gamma (1 / 2) / 2 := Gamma_three_halves
  have g5r : Gamma (5 / 2 : ℂ) = 3 / 2 * Gamma (3 / 2) := Gamma_five_halves
  have g7r : Gamma (7 / 2 : ℂ) = 5 / 2 * Gamma (5 / 2) := Gamma_seven_halves
  have inv : Gamma (1 / 2 : ℂ) * (Gamma (1 / 2))⁻¹ = 1 := mul_inv_cancel₀ hG
  have Gg : Gamma (1 / 2 : ℂ) * (Gamma (3 / 2))⁻¹ = 2 := by rw [gG]; field_simp
  have yY : y * y ^ (-1 : ℂ) = 1 := by rw [cpow_neg_one, mul_inv_cancel₀ hy0]
  have RCd : carlsonRC x y = Gamma (3 / 2) * regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y) := by
    unfold carlsonRC carlsonR; rw [sum_pair, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num]
  unfold carlsonR
  rw [sum_pair, show (3 / 2 + 1 : ℂ) = 5 / 2 by norm_num]
  set K := regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y)
  set r1 := regCarlsonR (1 / 2) (pair (1 / 2) 1) (pair x y)
  set P := regCarlsonR (1 / 2) (pair (1 / 2) 0) (pair x y)
  set A := regCarlsonR (-1 / 2) (pair (1 / 2) 0) (pair x y)
  set r2 := regCarlsonR (-1 / 2) (pair (3 / 2) 1) (pair x y)
  set r3 := regCarlsonR (-3 / 2) (pair (3 / 2) 1) (pair x y)
  set B := regCarlsonR (-3 / 2) (pair (1 / 2) 1) (pair x y)
  set r4 := regCarlsonR (-1 / 2) (pair (-1 / 2) 2) (pair x y)
  set D := regCarlsonR (-1 / 2) (pair (-1 / 2) 1) (pair x y)
  set r5 := regCarlsonR (-1 / 2) (pair (1 / 2) 2) (pair x y)
  set r6 := regCarlsonR (-3 / 2) (pair (1 / 2) 2) (pair x y)
  set r7 := regCarlsonR (-3 / 2) (pair (3 / 2) 2) (pair x y)
  set s := x ^ (-1 / 2 : ℂ)
  set Y := y ^ (-1 : ℂ)
  set G := Gamma (1 / 2 : ℂ)
  set Gi := (Gamma (1 / 2 : ℂ))⁻¹
  set g3 := Gamma (3 / 2 : ℂ)
  set g3i := (Gamma (3 / 2 : ℂ))⁻¹
  set g5 := Gamma (5 / 2 : ℂ)
  set g7 := Gamma (7 / 2 : ℂ)
  set RC := carlsonRC x y
  linear_combination (-4*g5) * hE1 + (4*g5) * hC1 + (4*g5*x) * hA + (-4*g5) * c2 + (6*Gi*s*x)
      * gG + (2*(2*Gi*s*x - K*y)) * g5r + (3*s*x) * inv + (3*y) * RCd

/-- Table 8.5-1, row `(3/2, 1)`, `(3/2, 1)`: `(x - y) R_{-3/2}(3/2, 1) = 3 R_C - 3 x^{-1/2}`. -/
theorem carlsonR_table_row_three (hx : 0 < x.re) (hy : 0 < y.re) :
    (x - y) * carlsonR (-3 / 2) (pair (3 / 2) 1) (pair x y) = 3 * carlsonRC x y - 3
        * x ^ (-1 / 2 : ℂ) := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  obtain ⟨hE1, hC1, hA, hB, hD, c2, c3, c4, c5, c6, c7⟩ := table_relations hx hy
  beta_reduce at hE1 hC1 hA hB hD c2 c3 c4 c5 c6 c7
  have hG : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have gG : Gamma (3 / 2 : ℂ) = Gamma (1 / 2) / 2 := Gamma_three_halves
  have g5r : Gamma (5 / 2 : ℂ) = 3 / 2 * Gamma (3 / 2) := Gamma_five_halves
  have g7r : Gamma (7 / 2 : ℂ) = 5 / 2 * Gamma (5 / 2) := Gamma_seven_halves
  have inv : Gamma (1 / 2 : ℂ) * (Gamma (1 / 2))⁻¹ = 1 := mul_inv_cancel₀ hG
  have Gg : Gamma (1 / 2 : ℂ) * (Gamma (3 / 2))⁻¹ = 2 := by rw [gG]; field_simp
  have yY : y * y ^ (-1 : ℂ) = 1 := by rw [cpow_neg_one, mul_inv_cancel₀ hy0]
  have RCd : carlsonRC x y = Gamma (3 / 2) * regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y) := by
    unfold carlsonRC carlsonR; rw [sum_pair, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num]
  unfold carlsonR
  rw [sum_pair, show (3 / 2 + 1 : ℂ) = 5 / 2 by norm_num]
  set K := regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y)
  set r1 := regCarlsonR (1 / 2) (pair (1 / 2) 1) (pair x y)
  set P := regCarlsonR (1 / 2) (pair (1 / 2) 0) (pair x y)
  set A := regCarlsonR (-1 / 2) (pair (1 / 2) 0) (pair x y)
  set r2 := regCarlsonR (-1 / 2) (pair (3 / 2) 1) (pair x y)
  set r3 := regCarlsonR (-3 / 2) (pair (3 / 2) 1) (pair x y)
  set B := regCarlsonR (-3 / 2) (pair (1 / 2) 1) (pair x y)
  set r4 := regCarlsonR (-1 / 2) (pair (-1 / 2) 2) (pair x y)
  set D := regCarlsonR (-1 / 2) (pair (-1 / 2) 1) (pair x y)
  set r5 := regCarlsonR (-1 / 2) (pair (1 / 2) 2) (pair x y)
  set r6 := regCarlsonR (-3 / 2) (pair (1 / 2) 2) (pair x y)
  set r7 := regCarlsonR (-3 / 2) (pair (3 / 2) 2) (pair x y)
  set s := x ^ (-1 / 2 : ℂ)
  set Y := y ^ (-1 : ℂ)
  set G := Gamma (1 / 2 : ℂ)
  set Gi := (Gamma (1 / 2 : ℂ))⁻¹
  set g3 := Gamma (3 / 2 : ℂ)
  set g3i := (Gamma (3 / 2 : ℂ))⁻¹
  set g5 := Gamma (5 / 2 : ℂ)
  set g7 := Gamma (7 / 2 : ℂ)
  set RC := carlsonRC x y
  linear_combination (-2*g5*y) * hB + (-2*g5) * c3 + (-3*Y*g3i*s*y) * gG + (-2*(-K + Y*g3i*s*y))
      * g5r + (-3*Y*s*y/2) * Gg + (-3*s) * yY + (-3) * RCd

/-- Table 8.5-1, row `(-1/2, 2)`, `(1/2, 1)`: `2y R_{-1/2}(-1/2, 2) = y R_C + x x^{-1/2}`. -/
theorem carlsonR_table_row_four (hx : 0 < x.re) (hy : 0 < y.re) :
    2 * y * carlsonR (-1 / 2) (pair (-1 / 2) 2) (pair x y) = y * carlsonRC x y + x
        * x ^ (-1 / 2 : ℂ) := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  obtain ⟨hE1, hC1, hA, hB, hD, c2, c3, c4, c5, c6, c7⟩ := table_relations hx hy
  beta_reduce at hE1 hC1 hA hB hD c2 c3 c4 c5 c6 c7
  have hG : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have gG : Gamma (3 / 2 : ℂ) = Gamma (1 / 2) / 2 := Gamma_three_halves
  have g5r : Gamma (5 / 2 : ℂ) = 3 / 2 * Gamma (3 / 2) := Gamma_five_halves
  have g7r : Gamma (7 / 2 : ℂ) = 5 / 2 * Gamma (5 / 2) := Gamma_seven_halves
  have inv : Gamma (1 / 2 : ℂ) * (Gamma (1 / 2))⁻¹ = 1 := mul_inv_cancel₀ hG
  have Gg : Gamma (1 / 2 : ℂ) * (Gamma (3 / 2))⁻¹ = 2 := by rw [gG]; field_simp
  have yY : y * y ^ (-1 : ℂ) = 1 := by rw [cpow_neg_one, mul_inv_cancel₀ hy0]
  have RCd : carlsonRC x y = Gamma (3 / 2) * regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y) := by
    unfold carlsonRC carlsonR; rw [sum_pair, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num]
  unfold carlsonR
  rw [sum_pair, show (-1 / 2 + 2 : ℂ) = 3 / 2 by norm_num]
  set K := regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y)
  set r1 := regCarlsonR (1 / 2) (pair (1 / 2) 1) (pair x y)
  set P := regCarlsonR (1 / 2) (pair (1 / 2) 0) (pair x y)
  set A := regCarlsonR (-1 / 2) (pair (1 / 2) 0) (pair x y)
  set r2 := regCarlsonR (-1 / 2) (pair (3 / 2) 1) (pair x y)
  set r3 := regCarlsonR (-3 / 2) (pair (3 / 2) 1) (pair x y)
  set B := regCarlsonR (-3 / 2) (pair (1 / 2) 1) (pair x y)
  set r4 := regCarlsonR (-1 / 2) (pair (-1 / 2) 2) (pair x y)
  set D := regCarlsonR (-1 / 2) (pair (-1 / 2) 1) (pair x y)
  set r5 := regCarlsonR (-1 / 2) (pair (1 / 2) 2) (pair x y)
  set r6 := regCarlsonR (-3 / 2) (pair (1 / 2) 2) (pair x y)
  set r7 := regCarlsonR (-3 / 2) (pair (3 / 2) 2) (pair x y)
  set s := x ^ (-1 / 2 : ℂ)
  set Y := y ^ (-1 : ℂ)
  set G := Gamma (1 / 2 : ℂ)
  set Gi := (Gamma (1 / 2 : ℂ))⁻¹
  set g3 := Gamma (3 / 2 : ℂ)
  set g3i := (Gamma (3 / 2 : ℂ))⁻¹
  set g5 := Gamma (5 / 2 : ℂ)
  set g7 := Gamma (7 / 2 : ℂ)
  set RC := carlsonRC x y
  linear_combination (2*g3*y) * hD + (-2*g3*y) * c4 + (2*Gi*Y*s*x*y) * gG + (Y*s*x*y) * inv
      + (s*x) * yY + (-y) * RCd

/-- Table 8.5-1, row `(1/2, 2)`, `(1/2, 2)`:
`4 (x - y) R_{-1/2}(1/2, 2) = 3(2x - y) R_C - 3x x^{-1/2}`. -/
theorem carlsonR_table_row_five (hx : 0 < x.re) (hy : 0 < y.re) :
    4 * (x - y) * carlsonR (-1 / 2) (pair (1 / 2) 2) (pair x y) = 3 * (2 * x - y)
        * carlsonRC x y - 3 * x * x ^ (-1 / 2 : ℂ) := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  obtain ⟨hE1, hC1, hA, hB, hD, c2, c3, c4, c5, c6, c7⟩ := table_relations hx hy
  beta_reduce at hE1 hC1 hA hB hD c2 c3 c4 c5 c6 c7
  have hG : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have gG : Gamma (3 / 2 : ℂ) = Gamma (1 / 2) / 2 := Gamma_three_halves
  have g5r : Gamma (5 / 2 : ℂ) = 3 / 2 * Gamma (3 / 2) := Gamma_five_halves
  have g7r : Gamma (7 / 2 : ℂ) = 5 / 2 * Gamma (5 / 2) := Gamma_seven_halves
  have inv : Gamma (1 / 2 : ℂ) * (Gamma (1 / 2))⁻¹ = 1 := mul_inv_cancel₀ hG
  have Gg : Gamma (1 / 2 : ℂ) * (Gamma (3 / 2))⁻¹ = 2 := by rw [gG]; field_simp
  have yY : y * y ^ (-1 : ℂ) = 1 := by rw [cpow_neg_one, mul_inv_cancel₀ hy0]
  have RCd : carlsonRC x y = Gamma (3 / 2) * regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y) := by
    unfold carlsonRC carlsonR; rw [sum_pair, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num]
  unfold carlsonR
  rw [sum_pair, show (1 / 2 + 2 : ℂ) = 5 / 2 by norm_num]
  set K := regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y)
  set r1 := regCarlsonR (1 / 2) (pair (1 / 2) 1) (pair x y)
  set P := regCarlsonR (1 / 2) (pair (1 / 2) 0) (pair x y)
  set A := regCarlsonR (-1 / 2) (pair (1 / 2) 0) (pair x y)
  set r2 := regCarlsonR (-1 / 2) (pair (3 / 2) 1) (pair x y)
  set r3 := regCarlsonR (-3 / 2) (pair (3 / 2) 1) (pair x y)
  set B := regCarlsonR (-3 / 2) (pair (1 / 2) 1) (pair x y)
  set r4 := regCarlsonR (-1 / 2) (pair (-1 / 2) 2) (pair x y)
  set D := regCarlsonR (-1 / 2) (pair (-1 / 2) 1) (pair x y)
  set r5 := regCarlsonR (-1 / 2) (pair (1 / 2) 2) (pair x y)
  set r6 := regCarlsonR (-3 / 2) (pair (1 / 2) 2) (pair x y)
  set r7 := regCarlsonR (-3 / 2) (pair (3 / 2) 2) (pair x y)
  set s := x ^ (-1 / 2 : ℂ)
  set Y := y ^ (-1 : ℂ)
  set G := Gamma (1 / 2 : ℂ)
  set Gi := (Gamma (1 / 2 : ℂ))⁻¹
  set g3 := Gamma (3 / 2 : ℂ)
  set g3i := (Gamma (3 / 2 : ℂ))⁻¹
  set g5 := Gamma (5 / 2 : ℂ)
  set g7 := Gamma (7 / 2 : ℂ)
  set RC := carlsonRC x y
  linear_combination (4*g5) * hE1 + (-4*g5) * hC1 + (-4*g5*x) * hA + (4*g5) * c5 + (-6*Gi*s*x)
      * gG + (-2*(2*Gi*s*x - 2*K*x + K*y)) * g5r + (-3*s*x) * inv + (-3*(2*x - y)) * RCd

/-- Table 8.5-1, row `(1/2, 2)`, `(3/2, 1)`:
`2 (x - y) y R_{-3/2}(1/2, 2) = -3y R_C + 3x x^{-1/2}`. -/
theorem carlsonR_table_row_six (hx : 0 < x.re) (hy : 0 < y.re) :
    2 * (x - y) * y * carlsonR (-3 / 2) (pair (1 / 2) 2) (pair x y) = -3 * y * carlsonRC x y + 3
        * x * x ^ (-1 / 2 : ℂ) := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  obtain ⟨hE1, hC1, hA, hB, hD, c2, c3, c4, c5, c6, c7⟩ := table_relations hx hy
  beta_reduce at hE1 hC1 hA hB hD c2 c3 c4 c5 c6 c7
  have hG : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have gG : Gamma (3 / 2 : ℂ) = Gamma (1 / 2) / 2 := Gamma_three_halves
  have g5r : Gamma (5 / 2 : ℂ) = 3 / 2 * Gamma (3 / 2) := Gamma_five_halves
  have g7r : Gamma (7 / 2 : ℂ) = 5 / 2 * Gamma (5 / 2) := Gamma_seven_halves
  have inv : Gamma (1 / 2 : ℂ) * (Gamma (1 / 2))⁻¹ = 1 := mul_inv_cancel₀ hG
  have Gg : Gamma (1 / 2 : ℂ) * (Gamma (3 / 2))⁻¹ = 2 := by rw [gG]; field_simp
  have yY : y * y ^ (-1 : ℂ) = 1 := by rw [cpow_neg_one, mul_inv_cancel₀ hy0]
  have RCd : carlsonRC x y = Gamma (3 / 2) * regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y) := by
    unfold carlsonRC carlsonR; rw [sum_pair, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num]
  unfold carlsonR
  rw [sum_pair, show (1 / 2 + 2 : ℂ) = 5 / 2 by norm_num]
  set K := regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y)
  set r1 := regCarlsonR (1 / 2) (pair (1 / 2) 1) (pair x y)
  set P := regCarlsonR (1 / 2) (pair (1 / 2) 0) (pair x y)
  set A := regCarlsonR (-1 / 2) (pair (1 / 2) 0) (pair x y)
  set r2 := regCarlsonR (-1 / 2) (pair (3 / 2) 1) (pair x y)
  set r3 := regCarlsonR (-3 / 2) (pair (3 / 2) 1) (pair x y)
  set B := regCarlsonR (-3 / 2) (pair (1 / 2) 1) (pair x y)
  set r4 := regCarlsonR (-1 / 2) (pair (-1 / 2) 2) (pair x y)
  set D := regCarlsonR (-1 / 2) (pair (-1 / 2) 1) (pair x y)
  set r5 := regCarlsonR (-1 / 2) (pair (1 / 2) 2) (pair x y)
  set r6 := regCarlsonR (-3 / 2) (pair (1 / 2) 2) (pair x y)
  set r7 := regCarlsonR (-3 / 2) (pair (3 / 2) 2) (pair x y)
  set s := x ^ (-1 / 2 : ℂ)
  set Y := y ^ (-1 : ℂ)
  set G := Gamma (1 / 2 : ℂ)
  set Gi := (Gamma (1 / 2 : ℂ))⁻¹
  set g3 := Gamma (3 / 2 : ℂ)
  set g3i := (Gamma (3 / 2 : ℂ))⁻¹
  set g5 := Gamma (5 / 2 : ℂ)
  set g7 := Gamma (7 / 2 : ℂ)
  set RC := carlsonRC x y
  linear_combination (2*g5*x*y) * hB + (2*g5*y) * c6 + (3*Y*g3i*s*x*y) * gG + (2*y*(-K
      + Y*g3i*s*x)) * g5r + (3*Y*s*x*y/2) * Gg + (3*s*x) * yY + (3*y) * RCd

/-- Table 8.5-1, row `(3/2, 2)`, `(3/2, 2)`:
`4 (x - y)² R_{-3/2}(3/2, 2) = 15(2x + y) R_C - 45x x^{-1/2}`. -/
theorem carlsonR_table_row_seven (hx : 0 < x.re) (hy : 0 < y.re) :
    4 * (x - y) ^ 2 * carlsonR (-3 / 2) (pair (3 / 2) 2) (pair x y) = 15 * (2 * x + y)
        * carlsonRC x y - 45 * x * x ^ (-1 / 2 : ℂ) := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  obtain ⟨hE1, hC1, hA, hB, hD, c2, c3, c4, c5, c6, c7⟩ := table_relations hx hy
  beta_reduce at hE1 hC1 hA hB hD c2 c3 c4 c5 c6 c7
  have hG : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have gG : Gamma (3 / 2 : ℂ) = Gamma (1 / 2) / 2 := Gamma_three_halves
  have g5r : Gamma (5 / 2 : ℂ) = 3 / 2 * Gamma (3 / 2) := Gamma_five_halves
  have g7r : Gamma (7 / 2 : ℂ) = 5 / 2 * Gamma (5 / 2) := Gamma_seven_halves
  have inv : Gamma (1 / 2 : ℂ) * (Gamma (1 / 2))⁻¹ = 1 := mul_inv_cancel₀ hG
  have Gg : Gamma (1 / 2 : ℂ) * (Gamma (3 / 2))⁻¹ = 2 := by rw [gG]; field_simp
  have yY : y * y ^ (-1 : ℂ) = 1 := by rw [cpow_neg_one, mul_inv_cancel₀ hy0]
  have RCd : carlsonRC x y = Gamma (3 / 2) * regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y) := by
    unfold carlsonRC carlsonR; rw [sum_pair, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num]
  unfold carlsonR
  rw [sum_pair, show (3 / 2 + 2 : ℂ) = 7 / 2 by norm_num]
  set K := regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair x y)
  set r1 := regCarlsonR (1 / 2) (pair (1 / 2) 1) (pair x y)
  set P := regCarlsonR (1 / 2) (pair (1 / 2) 0) (pair x y)
  set A := regCarlsonR (-1 / 2) (pair (1 / 2) 0) (pair x y)
  set r2 := regCarlsonR (-1 / 2) (pair (3 / 2) 1) (pair x y)
  set r3 := regCarlsonR (-3 / 2) (pair (3 / 2) 1) (pair x y)
  set B := regCarlsonR (-3 / 2) (pair (1 / 2) 1) (pair x y)
  set r4 := regCarlsonR (-1 / 2) (pair (-1 / 2) 2) (pair x y)
  set D := regCarlsonR (-1 / 2) (pair (-1 / 2) 1) (pair x y)
  set r5 := regCarlsonR (-1 / 2) (pair (1 / 2) 2) (pair x y)
  set r6 := regCarlsonR (-3 / 2) (pair (1 / 2) 2) (pair x y)
  set r7 := regCarlsonR (-3 / 2) (pair (3 / 2) 2) (pair x y)
  set s := x ^ (-1 / 2 : ℂ)
  set Y := y ^ (-1 : ℂ)
  set G := Gamma (1 / 2 : ℂ)
  set Gi := (Gamma (1 / 2 : ℂ))⁻¹
  set g3 := Gamma (3 / 2 : ℂ)
  set g3i := (Gamma (3 / 2 : ℂ))⁻¹
  set g5 := Gamma (5 / 2 : ℂ)
  set g7 := Gamma (7 / 2 : ℂ)
  set RC := carlsonRC x y
  linear_combination (8*g7) * hE1 + (-8*g7) * hC1 + (-8*g7*x) * hA + (-8*g7*x*y) * hB + (8*g7)
      * c5 + (-8*g7*y) * c6 + (-8*g7*(x - y)) * c7 + (-30*s*x*(Gi + Y*g3i*y)) * gG
      + (-10*(2*Gi*s*x - 2*K*x - K*y + 2*Y*g3i*s*x*y)) * g5r + (-4*(2*Gi*s*x - 2*K*x - K*y
      + 2*Y*g3i*s*x*y)) * g7r + (-15*s*x) * inv + (-15*Y*s*x*y) * Gg + (-30*s*x) * yY
      + (-15*(2*x + y)) * RCd

/-- Homogeneity of `R_C` under positive real scaling: `R_C(l x, l y) = l^{-1/2} R_C(x, y)`. -/
theorem carlsonRC_mul_of_pos {l : ℝ} (hl : 0 < l) {x y : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) : carlsonRC (l * x) (l * y) = (l : ℂ) ^ (-1 / 2 : ℂ) * carlsonRC x y := by
  have hz : pair x y ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hx
    · exact hy
  have h := regCarlsonR_smul_of_pos (-1 / 2) (pair (1 / 2) 1) hl hz
  have hp : (fun i => (l : ℂ) * pair x y i) = pair (l * x) (l * y) := by
    funext i; fin_cases i <;> rfl
  rw [hp] at h
  unfold carlsonRC carlsonR
  rw [h]; ring

/-- A change of variables mapping `(0, 1)` onto `(α, x)`. -/
theorem integral_Ioo_eq_integral_Ioo_affine (f : ℝ → ℝ) {α x : ℝ} (h : α < x) :
    ∫ t in Ioo α x, f t = ∫ u in Ioo (0 : ℝ) 1, (x - α) * f (α + u * (x - α)) := by
  have hd : 0 < x - α := by linarith
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
    (f := fun u => α + u * (x - α)) (f' := fun _ => x - α)
    (fun u _ => (((hasDerivAt_id u).mul_const (x - α)).const_add α).hasDerivWithinAt.congr_deriv
      (by simp)) (fun a _ b _ hab => by
        have : a * (x - α) = b * (x - α) := by linarith [hab]
        exact mul_right_cancel₀ hd.ne' this) f
  rw [show (fun u => α + u * (x - α)) '' Ioo (0 : ℝ) 1 = Ioo α x by
    ext t; simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩; constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      exact ⟨(t - α) / (x - α), ⟨div_pos (by linarith) hd, (div_lt_one hd).mpr (by linarith)⟩,
        by field_simp; ring⟩] at hsub
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
  simp [abs_of_pos hd]

/-- **Carlson's Example 8.5-5**, equation (6): for real `λ ≠ 0`, `α < x`, and `β + λt > 0` on
`[α, x]`,
`∫_α^x (t - α)^{1/2} (β + λt)^{-1/2} dt
  = λ⁻¹ (x - α)^{1/2} [(β + λx)^{1/2} - (β + λα) R_C(β + λx, β + λα)]`. -/
theorem integral_sqrt_div_sqrt_affine {α x β l : ℝ} (hαx : α < x) (hl : l ≠ 0)
    (hA : 0 < β + l * x) (hB : 0 < β + l * α) :
    ((∫ t in Ioo α x, (t - α) ^ (1 / 2 : ℝ) * (β + l * t) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      ((l⁻¹ * (x - α) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        (((β + l * x) ^ (1 / 2 : ℝ) : ℝ) -
          ((β + l * α : ℝ) : ℂ) * carlsonRC ((β + l * x : ℝ) : ℂ) ((β + l * α : ℝ) : ℂ)) := by
  set A := β + l * x
  set B := β + l * α
  set d := x - α with hd_def
  have hd : 0 < d := by simp only [d]; linarith
  have hpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < β + l * (α + u * d) := by
    intro u hu
    have : β + l * (α + u * d) = (1 - u) * B + u * A := by simp only [A, B, d]; ring
    rw [this]
    rcases eq_or_lt_of_le hu.1 with h | h
    · subst h; simpa using hB
    · have := mul_pos h hA
      nlinarith [hu.2, mul_nonneg (by linarith [hu.2] : (0 : ℝ) ≤ 1 - u) hB.le]
  rw [integral_Ioo_eq_integral_Ioo_affine _ hαx]
  have hseg : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, pair (β : ℂ) 1 i + pair (l : ℂ) 0 i *
      ((α : ℂ) + u * ((x : ℂ) - α)) ∈ slitPlane := by
    intro i u hu; fin_cases i
    · show (β : ℂ) + l * ((α : ℂ) + u * ((x : ℂ) - α)) ∈ slitPlane
      rw [show (β : ℂ) + l * ((α : ℂ) + u * ((x : ℂ) - α)) = ((β + l * (α + u * d) : ℝ) : ℂ) by
        simp only [d]; push_cast; ring]
      exact ofReal_mem_slitPlane.mpr (hpos u hu)
    · simp [pair]
  have H := integral_segment_eq_regCarlsonR (ι := Fin 2) (a := 3 / 2) (a' := 1)
    (b := pair (1 / 2) 2) (z := pair (β : ℂ) 1) (w := pair (l : ℂ) 0) (x := (α : ℂ)) (y := (x : ℂ))
    (by norm_num) (by norm_num) (by simp [pair]; norm_num) (by exact_mod_cast hαx.ne) hseg
  have hxa : (x : ℂ) - α = (d : ℂ) := by simp only [d]; push_cast; ring
  -- the left side
  have hL : ((∫ u in Ioo (0 : ℝ) 1, d * ((α + u * d - α) ^ (1 / 2 : ℝ) *
      (β + l * (α + u * d)) ^ (-1 / 2 : ℝ)) : ℝ) : ℂ) =
      ((x : ℂ) - α) * ∫ u in Ioo (0 : ℝ) 1, ((α : ℂ) + u * ((x : ℂ) - α) - α) ^ ((3 / 2 : ℂ) - 1) *
        ((x : ℂ) - ((α : ℂ) + u * ((x : ℂ) - α))) ^ ((1 : ℂ) - 1) *
        ∏ i, (pair (β : ℂ) 1 i + pair (l : ℂ) 0 i * ((α : ℂ) + u * ((x : ℂ) - α))) ^
          (-pair (1 / 2 : ℂ) 2 i) := by
    rw [← integral_complex_ofReal, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hud : 0 ≤ u * d := mul_nonneg hu.1.le hd.le
    have hT := hpos u (Ioo_subset_Icc_self hu)
    rw [Fin.prod_univ_two, hxa]
    simp only [pair, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [show (α : ℂ) + u * d - α = ((u * d : ℝ) : ℂ) by push_cast; ring,
      show (β : ℂ) + l * ((α : ℂ) + u * d) = ((β + l * (α + u * d) : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) + 0 * ((α : ℂ) + u * d) = 1 by ring, one_cpow, mul_one, sub_self, cpow_zero,
      mul_one, show α + u * d - α = u * d by ring]
    push_cast
    rw [ofReal_cpow hud, ofReal_cpow hT.le]
    push_cast
    norm_num
  rw [← hd_def, hL, H, hxa, Fin.prod_univ_two]
  have hratio : (fun i => (pair (β : ℂ) 1 i + pair (l : ℂ) 0 i * x) /
      (pair (β : ℂ) 1 i + pair (l : ℂ) 0 i * α)) = pair ((A / B : ℝ) : ℂ) 1 := by
    funext i; fin_cases i
    · simp only [pair, A, B]; push_cast; ring
    · simp [pair]
  rw [hratio]
  simp only [pair, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [show (1 : ℂ) + 0 * α = 1 by ring, one_cpow, mul_one, Gamma_one, mul_one,
    show (β : ℂ) + l * α = (B : ℂ) by simp only [B]; push_cast; ring,
    show (3 / 2 : ℂ) + 1 - 1 = 3 / 2 by ring]
  -- row 6 of Table 8.5-1 at the nodes `(A/B, 1)`
  have hAB : 0 < A / B := div_pos hA hB
  have R6 := carlsonR_table_row_six (x := ((A / B : ℝ) : ℂ)) (y := 1) (by simpa using hAB)
    (by norm_num)
  unfold carlsonR at R6
  rw [sum_pair, show (1 / 2 : ℂ) + 2 = 5 / 2 by norm_num] at R6
  have hRC : carlsonRC ((A / B : ℝ) : ℂ) 1 = ((B⁻¹ : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
      carlsonRC (A : ℂ) (B : ℂ) := by
    rw [← carlsonRC_mul_of_pos (inv_pos.mpr hB) (ofReal_mem_slitPlane.mpr hA)
      (ofReal_mem_slitPlane.mpr hB)]
    congr 1
    · push_cast; ring
    · push_cast; exact (inv_mul_cancel₀ (by exact_mod_cast hB.ne')).symm
  rw [hRC] at R6
  simp only [pair] at R6
  -- real square roots
  set sA := Real.sqrt A
  set sB := Real.sqrt B
  set sd := Real.sqrt d
  have hsA : 0 < sA := Real.sqrt_pos.mpr hA
  have hsB : 0 < sB := Real.sqrt_pos.mpr hB
  have hsd : 0 < sd := Real.sqrt_pos.mpr hd
  have hr : ∀ {r : ℝ}, 0 < r → r ^ (1 / 2 : ℝ) = Real.sqrt r := fun _ => (Real.sqrt_eq_rpow _).symm
  have hri : ∀ {r : ℝ}, 0 < r → r ^ (-(1 / 2) : ℝ) = (Real.sqrt r)⁻¹ := fun h => by
    rw [Real.rpow_neg h.le, Real.sqrt_eq_rpow]
  have c1 : (d : ℂ) ^ (3 / 2 : ℂ) = d * sd := by
    rw [show (3 / 2 : ℂ) = ((1 + 1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hd.le,
      Real.rpow_add hd, Real.rpow_one, hr hd]; push_cast; rfl
  have c2 : (B : ℂ) ^ (-(1 / 2) : ℂ) = (sB : ℂ)⁻¹ := by
    rw [show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hB.le,
      hri hB]; push_cast; rfl
  have c3 : ((B⁻¹ : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = sB := by
    rw [show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      hri (inv_pos.mpr hB), Real.sqrt_inv, inv_inv]
  have c4 : ((A / B : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = sB / sA := by
    rw [show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hAB.le,
      hri hAB, Real.sqrt_div' _ hB.le, inv_div]; push_cast; rfl
  rw [c1, c2, show A ^ (1 / 2 : ℝ) = sA from hr hA, show d ^ (1 / 2 : ℝ) = sd from hr hd]
  rw [c3, c4] at R6
  have hG5 : Gamma (5 / 2 : ℂ) = 3 / 2 * Gamma (3 / 2) := by
    rw [show (5 / 2 : ℂ) = 3 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
  rw [hG5] at R6
  have hAsq : (A : ℂ) = (sA : ℂ) ^ 2 := by rw [← ofReal_pow, Real.sq_sqrt hA.le]
  have hBsq : (B : ℂ) = (sB : ℂ) ^ 2 := by rw [← ofReal_pow, Real.sq_sqrt hB.le]
  have hABl : (sA : ℂ) ^ 2 - (sB : ℂ) ^ 2 = l * d := by
    rw [← hAsq, ← hBsq]; simp only [A, B, d]; push_cast; ring
  push_cast at R6 ⊢
  rw [hAsq, hBsq] at R6
  rw [hAsq, hBsq]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  have hsA' : (sA : ℂ) ≠ 0 := by exact_mod_cast hsA.ne'
  have hsB' : (sB : ℂ) ≠ 0 := by exact_mod_cast hsB.ne'
  field_simp at R6 ⊢
  linear_combination (sd : ℂ) * R6 - Gamma (3 / 2) * regCarlsonR (-(3 / 2)) ![1 / 2, 2]
    ![(sA : ℂ) ^ 2 / (sB : ℂ) ^ 2, 1] * (sd : ℂ) * hABl

end Carlson.TwoVariable
