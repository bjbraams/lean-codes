/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.ReductionRelations
public import Carlson.Aggregation

/-!
# Carlson's reduction tables 9.3-1 to 9.3-4

Each row of Carlson's Tables 9.3-1 to 9.3-4 expresses an R-function with half-odd (and, for the
third kind, one integral) Dirichlet parameters as a linear combination of the standard functions
`R_F`, `R_G`, `R_H` (incomplete) or `R_K`, `R_E`, `R_L` (complete) and an algebraic term. Each
regularized identity is a finite linear combination, with polynomial coefficients, of instances
of the contiguous relations of `Carlson.Elliptic.ReductionRelations` and of the deletion of a
zero parameter. The combinations were found by exact linear algebra over `ℚ` and are checked here
by `linear_combination`. All nodes may lie anywhere in the slit plane; no distinctness is assumed.

The row `2b = (1, 3, 3)` of Table 9.3-1 has a sign error in the book (see its docstring).

## Main results

* `Carlson.carlsonR_table_9_3_1_row1` to `Carlson.carlsonR_table_9_3_1_row5`: Table 9.3-1.
* `Carlson.carlsonR_table_9_3_2_row1` to `Carlson.carlsonR_table_9_3_2_row4`: Table 9.3-2.
* `Carlson.carlsonR_table_9_3_3_row1`, `Carlson.carlsonR_table_9_3_3_row3`: the rows of
  Table 9.3-3 not already in `Carlson.Elliptic.LegendreThird`.
* `Carlson.carlsonR_table_9_3_4_row2`, `Carlson.carlsonR_table_9_3_4_row3`,
  `Carlson.carlsonR_table_9_3_4_row5`: the rows of Table 9.3-4 not already in
  `Carlson.Elliptic.LegendreThird`.
* `Carlson.carlsonRH_self_right_eq`: Exercise 9.3-3.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §9.3.
-/

open Complex

@[expose] public noncomputable section

namespace Carlson

variable {x y z : ℂ}

/-- Table 9.3-1, `2b = (-1, 1, 3)`, regularized form. -/
private theorem row1_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    (-y + z) *
      regCarlsonR (-1 / 2) ![-1 / 2, 1 / 2, 3 / 2] ![x, y, z] =
      2 * regCarlsonR (1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      -y * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      (-2*y) * regCarlsonR (-1 / 2) ![-1 / 2, 1 / 2, 1 / 2] ![x, y, z] := by
  have h0 := regR3_sum hx hy hz (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h1 := regR3_raise₀ hx hy hz (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h2 := regR3_raise₀ hx hy hz (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h3 := regR3_sum hx hy hz (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h4 := regR3_shift hx hy hz (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h5 := regR3_raise₁ hx hy hz (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h6 := regR3_raise₂ hx hy hz (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have := slitPlane_ne_zero hx; have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  norm_num at *
  linear_combination (2*y) * h0 + z * h1 + y * h2 + (2*x) * h3 + -2 * h4 + -x * h5 +
    -x * h6

/-- **Carlson's Table 9.3-1**, row `2b = (-1, 1, 3)`, with `a' = 1`, on slit-plane nodes;
`(xyz)^{-1/2}` is read as `x^{-1/2} y^{-1/2} z^{-1/2}`. -/
theorem carlsonR_table_9_3_1_row1 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    (-y + z) * carlsonR (-1 / 2) ![-1 / 2, 1 / 2, 3 / 2] ![x, y, z] =
      2 * carlsonRG x y z + -y * carlsonRF x y z +
        (-x*y) * (x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ)) := by
  have h := row1_reg hx hy hz
  have c0 := regR3_closed_half hx hy hz (-1) (0) (0)
  have hfun : (fun _ : Fin 3 => (1 / 2 : ℂ)) = ![1 / 2, 1 / 2, 1 / 2] := by
    funext i; fin_cases i <;> rfl
  have := slitPlane_ne_zero hx; have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  unfold carlsonRG carlsonRF carlsonR
  rw [hfun]
  norm_num [Fin.sum_univ_three] at *
  simp only [Gamma_three_halves] at *
  linear_combination (norm := skip) (Gamma (1 / 2)/2) * h + (-Gamma (1 / 2)*y) * c0
  field_simp
  ring

/-- Table 9.3-1, `2b = (-1, 3, 3)`, regularized form. -/
private theorem row2_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    ((y - z)^2) *
      regCarlsonR (-3 / 2) ![-1 / 2, 3 / 2, 3 / 2] ![x, y, z] =
      -8 * regCarlsonR (1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      (2*(y + z)) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      (2*x*(y + z)) * regCarlsonR (-3 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] := by
  have h0 := regR3_raise₀ hx hy hz (-3 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h1 := regR3_sum hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h2 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h3 := regR3_sum hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h4 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h5 := regR3_raise₀ hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h6 := regR3_raise₁ hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h7 := regR3_sum hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h8 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h9 := regR3_raise₀ hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h10 := regR3_raise₂ hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h11 := regR3_sum hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h12 := regR3_shift hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h13 := regR3_raise₁ hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h14 := regR3_raise₂ hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h15 := regR3_shift hx hy hz (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have := slitPlane_ne_zero hx; have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  norm_num at *
  linear_combination ((y - z)^2) * h0 + (-2*x*(y + z)) * h1 + (-2*(y + z)) * h2 + (-4*z^2) * h3 +
    (4*z) * h4 + (-2*z*(x - z)) * h5 + (-(x + z)*(y - z)) * h6 + (-4*y^2) * h7 + (4*y) * h8 +
    (-2*y*(x - y)) * h9 + ((x + y)*(y - z)) * h10 + (-4*x^2) * h11 + (4*x) * h12 +
    (2*x*(x - y)) * h13 + (2*x*(x - z)) * h14 + 8 * h15

/-- **Carlson's Table 9.3-1**, row `2b = (-1, 3, 3)`, with `a' = 1`, on slit-plane nodes;
`(xyz)^{-1/2}` is read as `x^{-1/2} y^{-1/2} z^{-1/2}`. -/
theorem carlsonR_table_9_3_1_row2 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    ((y - z)^2/3) * carlsonR (-3 / 2) ![-1 / 2, 3 / 2, 3 / 2] ![x, y, z] =
      -4 * carlsonRG x y z + (y + z) * carlsonRF x y z +
        (x*(y + z)) * (x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ)) := by
  have h := row2_reg hx hy hz
  have c0 := regR3_closed_half hx hy hz (0) (0) (0)
  have hfun : (fun _ : Fin 3 => (1 / 2 : ℂ)) = ![1 / 2, 1 / 2, 1 / 2] := by
    funext i; fin_cases i <;> rfl
  have := slitPlane_ne_zero hx; have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  unfold carlsonRG carlsonRF carlsonR
  rw [hfun]
  norm_num [Fin.sum_univ_three] at *
  simp only [Gamma_five_halves, Gamma_three_halves] at *
  linear_combination (norm := skip) (Gamma (1 / 2)/4) * h + (Gamma (1 / 2)*x*(y + z)/2) * c0
  field_simp
  ring

/-- Table 9.3-1, `2b = (1, 1, 3)`, regularized form. -/
private theorem row3_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    ((x - z)*(y - z)) *
      regCarlsonR (-3 / 2) ![1 / 2, 1 / 2, 3 / 2] ![x, y, z] =
      -4 * regCarlsonR (1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      (2*z) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      (2*x*y) * regCarlsonR (-3 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] := by
  have h0 := regR3_sum hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h1 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h2 := regR3_sum hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h3 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h4 := regR3_raise₀ hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h5 := regR3_raise₁ hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h6 := regR3_sum hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h7 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h8 := regR3_raise₀ hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h9 := regR3_raise₂ hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h10 := regR3_sum hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h11 := regR3_shift hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h12 := regR3_raise₁ hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h13 := regR3_raise₂ hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h14 := regR3_shift hx hy hz (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have := slitPlane_ne_zero hx; have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  norm_num at *
  linear_combination (-2*x*y) * h0 + (-2*z) * h1 + (-2*z^2) * h2 + (2*z) * h3 + (-z*(x - z)) * h4 +
    (-z*(y - z)) * h5 + (-2*y^2) * h6 + (2*y) * h7 + (-y*(x - y)) * h8 + (y*(y - z)) * h9 +
    (-2*x^2) * h10 + (2*x) * h11 + (x*(x - y)) * h12 + (x*(x - z)) * h13 + 4 * h14

/-- **Carlson's Table 9.3-1**, row `2b = (1, 1, 3)`, with `a' = 1`, on slit-plane nodes;
`(xyz)^{-1/2}` is read as `x^{-1/2} y^{-1/2} z^{-1/2}`. -/
theorem carlsonR_table_9_3_1_row3 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    ((x - z)*(y - z)/3) * carlsonR (-3 / 2) ![1 / 2, 1 / 2, 3 / 2] ![x, y, z] =
      -2 * carlsonRG x y z + z * carlsonRF x y z +
        (x*y) * (x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ)) := by
  have h := row3_reg hx hy hz
  have c0 := regR3_closed_half hx hy hz (0) (0) (0)
  have hfun : (fun _ : Fin 3 => (1 / 2 : ℂ)) = ![1 / 2, 1 / 2, 1 / 2] := by
    funext i; fin_cases i <;> rfl
  have := slitPlane_ne_zero hx; have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  unfold carlsonRG carlsonRF carlsonR
  rw [hfun]
  norm_num [Fin.sum_univ_three] at *
  simp only [Gamma_five_halves, Gamma_three_halves] at *
  linear_combination (norm := skip) (Gamma (1 / 2)/4) * h + (Gamma (1 / 2)*x*y/2) * c0
  field_simp
  ring

set_option maxHeartbeats 2000000 in
/-- Table 9.3-1, `2b = (1, 3, 3)`, regularized form. -/
private theorem row4_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    (-3*y*(x - y)*(x - z)*(y - z)^2) *
      regCarlsonR (-5 / 2) ![1 / 2, 3 / 2, 3 / 2] ![x, y, z] =
      (8*y*(2*x - y - z)) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      (-4*y*(x*y + x*z - 2*y*z)) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      (-2*x*z*(2*x^3 - 6*x^2*y - 2*x^2*z + 2*x*y^2 + 10*x*y*z - 3*y^2*z - 3*y*z^2)) * regCarlsonR
          (-5 / 2) ![1 / 2, 1 / 2, 3 / 2] ![x, y, z] +
      (2*x*y*(2*x^3 - 2*x^2*y - 2*x^2*z - 4*x*y^2 + 4*x*y*z + 3*y^3 - y^2*z)) * regCarlsonR (-5 /
          2) ![1 / 2, 3 / 2, 1 / 2] ![x, y, z] +
      (-2*x^2*y*(4*x^2 - 3*x*y - 3*x*z + 2*y*z)) * regCarlsonR (-5 / 2) ![3 / 2, 1 / 2, 1 / 2]
          ![x, y, z] := by
  have h0 := regR3_sum hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h1 := regR3_shift hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h2 := regR3_sum hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ)
  have h3 := regR3_shift hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ)
  have h4 := regR3_raise₀ hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ)
  have h5 := regR3_raise₁ hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ)
  have h6 := regR3_sum hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h7 := regR3_shift hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h8 := regR3_sum hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h9 := regR3_shift hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h10 := regR3_raise₀ hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h11 := regR3_raise₁ hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h12 := regR3_raise₂ hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h13 := regR3_sum hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ)
  have h14 := regR3_shift hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ)
  have h15 := regR3_raise₀ hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ)
  have h16 := regR3_raise₂ hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ)
  have h17 := regR3_sum hx hy hz (-5 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h18 := regR3_shift hx hy hz (-5 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h19 := regR3_sum hx hy hz (-5 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h20 := regR3_shift hx hy hz (-5 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h21 := regR3_raise₁ hx hy hz (-5 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h22 := regR3_raise₂ hx hy hz (-5 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h23 := regR3_sum hx hy hz (-5 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h24 := regR3_shift hx hy hz (-5 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h25 := regR3_raise₁ hx hy hz (-5 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h26 := regR3_sum hx hy hz (-5 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h27 := regR3_shift hx hy hz (-5 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h28 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h29 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h30 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h31 := regR3_shift hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h32 := regR3_shift hx hy hz (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have := slitPlane_ne_zero hx; have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  norm_num at *
  linear_combination (2*x*z*(2*x^3 - 6*x^2*y - 2*x^2*z + 2*x*y^2 +
    10*x*y*z - 3*y^2*z - 3*y*z^2)) * h0 + (2*y*z*(x*y + x*z - 2*y*z)) * h1 +
    (6*y*z^3*(2*x - y - z)) * h2 + (-6*y*z^2*(2*x - y - z)) * h3 +
    (-3*y*z*(x - z)^2*(2*x - y - z)) * h4 + (3*z*(x - z)*(2*x^3 - 4*x^2*y + x*y^2 + x*y*z +
    y^2*z - y*z^2)) * h5 + (-2*x*y*(2*x^3 - 2*x^2*y - 2*x^2*z - 4*x*y^2 + 4*x*y*z +
    3*y^3 - y^2*z)) * h6 + (2*y^2*(x*y + x*z - 2*y*z)) * h7 + (2*(2*x^4*y - 2*x^4*z - 4*x^3*y^2 +
    2*x^3*y*z + 2*x^3*z^2 + x^2*y^3 + 4*x^2*y^2*z - 5*x^2*y*z^2 + 4*x*y^2*z^2 - 4*y^3*z^2)) * h8 +
    (-4*y^2*z*(2*x - y - z)) * h9 + (-2*y*(x - y)*(x - z)*(x*y + x*z - 2*y*z)) * h10 +
    (3*z*(x - y)^2*(2*x^2 - 2*x*z - y^2 + y*z)) * h11 + (-3*y*(x - z)*(2*x^3 - 4*x^2*y + x*y^2 +
    x*y*z + y^2*z - y*z^2)) * h12 + (6*y^4*(2*x - y - z)) * h13 + (-6*y^3*(2*x - y - z)) * h14 +
    (-3*y^2*(x - y)^2*(2*x - y - z)) * h15 + (-3*y*(x - y)^2*(2*x^2 - 2*x*z - y^2 + y*z)) * h16 +
    (2*x^2*y*(4*x^2 - 3*x*y - 3*x*z + 2*y*z)) * h17 + (2*x*y*(x*y + x*z - 2*y*z)) * h18 +
    (-2*x^2*y*(x - 3*z)*(2*x - y - z)) * h19 + (-4*x*y*z*(2*x - y - z)) * h20 +
    (2*x*(x - y)*(x - z)*(x*y + x*z - 2*y*z)) * h21 + (3*x*y*(x - z)^2*(2*x - y - z)) * h22 +
    (-2*x^2*y*(x - 3*y)*(2*x - y - z)) * h23 + (-4*x*y^2*(2*x - y - z)) * h24 +
    (3*x*y*(x - y)^2*(2*x - y - z)) * h25 + (6*x^3*y*(2*x - y - z)) * h26 +
    (-6*x^2*y*(2*x - y - z)) * h27 + (4*y*(x*y + x*z - 2*y*z)) * h28 +
    (-4*y*z*(2*x - y - z)) * h29 + (-4*y^2*(2*x - y - z)) * h30 + (-4*x*y*(2*x - y - z)) * h31 +
    (-8*y*(2*x - y - z)) * h32

/-- **Carlson's Table 9.3-1**, row `2b = (1, 3, 3)`, with `a' = 1`, on slit-plane nodes;
`(xyz)^{-1/2}` is read as `x^{-1/2} y^{-1/2} z^{-1/2}`, and `d = (x - y)(y - z)(z - x)`. Carlson
prints `C = (z - y) d/5`; the correct sign is `C = (y - z) d/5`, as the formal proof and a
numerical check confirm. -/
theorem carlsonR_table_9_3_1_row4 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    (-(x - y)*(x - z)*(y - z)^2/5) * carlsonR (-5 / 2) ![1 / 2, 3 / 2, 3 / 2] ![x, y, z] =
      (2*(2*x - y - z)) * carlsonRG x y z + (-x*y - x*z + 2*y*z) * carlsonRF x y z +
        (-x*(x*y + x*z - y^2 - z^2)) *
          (x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ)) := by
  have h := row4_reg hx hy hz
  have c0 := regR3_closed_half hx hy hz (0) (0) (1)
  have c1 := regR3_closed_half hx hy hz (0) (1) (0)
  have c2 := regR3_closed_half hx hy hz (1) (0) (0)
  have hfun : (fun _ : Fin 3 => (1 / 2 : ℂ)) = ![1 / 2, 1 / 2, 1 / 2] := by
    funext i; fin_cases i <;> rfl
  have := slitPlane_ne_zero hx; have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  unfold carlsonRG carlsonRF carlsonR
  rw [hfun]
  norm_num [Fin.sum_univ_three] at *
  simp only [Gamma_five_halves, Gamma_seven_halves, Gamma_three_halves] at *
  linear_combination (norm := skip) (Gamma (1 / 2)/(8*y)) * h +
    (-Gamma (1 / 2)*x*z*(2*x^3 - 6*x^2*y - 2*x^2*z + 2*x*y^2 +
    10*x*y*z - 3*y^2*z - 3*y*z^2)/(4*y)) * c0 +
    (Gamma (1 / 2)*x*(2*x^3 - 2*x^2*y - 2*x^2*z - 4*x*y^2 + 4*x*y*z + 3*y^3 - y^2*z)/4) * c1 +
    (-Gamma (1 / 2)*x^2*(4*x^2 - 3*x*y - 3*x*z + 2*y*z)/4) * c2
  field_simp
  ring

set_option maxHeartbeats 4000000 in
/-- Table 9.3-1, `2b = (3, 3, 3)`, regularized form. -/
private theorem row5_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    (15*(x - y)^2*(x - z)^2*(y - z)^2) *
      regCarlsonR (-7 / 2) ![3 / 2, 3 / 2, 3 / 2] ![x, y, z] =
      (-32*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x,
          y, z] +
      (8*(x^2*y + x^2*z + x*y^2 - 6*x*y*z + x*z^2 + y^2*z + y*z^2)) * regCarlsonR (-1 / 2) ![1 /
          2, 1 / 2, 1 / 2] ![x, y, z] +
      (-6*z^3*(x^2*y - 3*x^2*z + x*y^2 - 2*x*y*z + 5*x*z^2 - 3*y^2*z + 5*y*z^2 - 4*z^3)) *
          regCarlsonR (-7 / 2) ![1 / 2, 1 / 2, 5 / 2] ![x, y, z] +
      (2*(2*x^5*y + 2*x^5*z - 3*x^4*y^2 - 14*x^4*y*z - 3*x^4*z^2 + x^3*y^3 + 19*x^3*y^2*z +
          19*x^3*y*z^2 + x^3*z^3 - 15*x^2*y^3*z - 6*x^2*y^2*z^2 - 15*x^2*y*z^3 + 6*x*y^4*z +
              6*x*y*z^4 - 6*y^5*z + 24*y^4*z^2 - 36*y^3*z^3 + 24*y^2*z^4 - 6*y*z^5)) * regCarlsonR
                  (-7 / 2) ![1 / 2, 3 / 2, 3 / 2] ![x, y, z] +
      (6*y^3*(3*x^2*y - x^2*z - 5*x*y^2 + 2*x*y*z - x*z^2 + 4*y^3 - 5*y^2*z + 3*y*z^2)) *
          regCarlsonR (-7 / 2) ![1 / 2, 5 / 2, 1 / 2] ![x, y, z] +
      (-2*x*(2*x^5 - 3*x^4*y - x^4*z + x^3*y^2 + 5*x^3*y*z - 16*x^3*z^2 + 4*x^2*y^2*z -
          3*x^2*y*z^2 + 29*x^2*z^3 - 15*x*y^2*z^2 + 15*x*y*z^3 - 24*x*z^4 + 6*y^2*z^3 - 6*y*z^4 +
              6*z^5)) * regCarlsonR (-7 / 2) ![3 / 2, 1 / 2, 3 / 2] ![x, y, z] +
      (-2*x*(2*x^5 - x^4*y - 3*x^4*z - 16*x^3*y^2 + 5*x^3*y*z + x^3*z^2 + 29*x^2*y^3 - 3*x^2*y^2*z
          + 4*x^2*y*z^2 - 24*x*y^4 + 15*x*y^3*z - 15*x*y^2*z^2 + 6*y^5 - 6*y^4*z + 6*y^3*z^2)) *
              regCarlsonR (-7 / 2) ![3 / 2, 3 / 2, 1 / 2] ![x, y, z] +
      (6*x^3*(4*x^3 - 5*x^2*y - 5*x^2*z + 3*x*y^2 + 2*x*y*z + 3*x*z^2 - y^2*z - y*z^2)) *
          regCarlsonR (-7 / 2) ![5 / 2, 1 / 2, 1 / 2] ![x, y, z] := by
  have h0 := regR3_sum hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ)
  have h1 := regR3_shift hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ)
  have h2 := regR3_sum hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h3 := regR3_shift hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h4 := regR3_sum hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (5 / 2 : ℂ)
  have h5 := regR3_shift hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (5 / 2 : ℂ)
  have h6 := regR3_raise₀ hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (5 / 2 : ℂ)
  have h7 := regR3_raise₁ hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (5 / 2 : ℂ)
  have h8 := regR3_sum hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ)
  have h9 := regR3_shift hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ)
  have h10 := regR3_sum hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ) (3 / 2 : ℂ)
  have h11 := regR3_shift hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ) (3 / 2 : ℂ)
  have h12 := regR3_raise₀ hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ) (3 / 2 : ℂ)
  have h13 := regR3_raise₂ hx hy hz (-7 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ) (3 / 2 : ℂ)
  have h14 := regR3_sum hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h15 := regR3_shift hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h16 := regR3_sum hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ)
  have h17 := regR3_shift hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ)
  have h18 := regR3_raise₀ hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ)
  have h19 := regR3_raise₁ hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ)
  have h20 := regR3_sum hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h21 := regR3_shift hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h22 := regR3_sum hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h23 := regR3_shift hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h24 := regR3_raise₁ hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h25 := regR3_raise₂ hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h26 := regR3_sum hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ)
  have h27 := regR3_shift hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ)
  have h28 := regR3_raise₀ hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ)
  have h29 := regR3_raise₂ hx hy hz (-7 / 2 : ℂ) (3 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ)
  have h30 := regR3_sum hx hy hz (-7 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h31 := regR3_shift hx hy hz (-7 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h32 := regR3_sum hx hy hz (-7 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h33 := regR3_shift hx hy hz (-7 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h34 := regR3_raise₂ hx hy hz (-7 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h35 := regR3_sum hx hy hz (-7 / 2 : ℂ) (5 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h36 := regR3_shift hx hy hz (-7 / 2 : ℂ) (5 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h37 := regR3_raise₁ hx hy hz (-7 / 2 : ℂ) (5 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h38 := regR3_shift hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h39 := regR3_sum hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ)
  have h40 := regR3_shift hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ)
  have h41 := regR3_shift hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h42 := regR3_shift hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ)
  have h43 := regR3_sum hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ)
  have h44 := regR3_shift hx hy hz (-5 / 2 : ℂ) (1 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ)
  have h45 := regR3_shift hx hy hz (-5 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h46 := regR3_shift hx hy hz (-5 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h47 := regR3_shift hx hy hz (-5 / 2 : ℂ) (3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h48 := regR3_sum hx hy hz (-5 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h49 := regR3_shift hx hy hz (-5 / 2 : ℂ) (5 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h50 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h51 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h52 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h53 := regR3_shift hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h54 := regR3_shift hx hy hz (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have := slitPlane_ne_zero hx; have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  norm_num at *
  linear_combination (6*z^3*(x^2*y - 3*x^2*z + x*y^2 - 2*x*y*z + 5*x*z^2 - 3*y^2*z +
    5*y*z^2 - 4*z^3)) * h0 + (-6*z^2*(x^2*y - 3*x^2*z + x*y^2 - 2*x*y*z + 5*x*z^2 - 3*y^2*z +
    5*y*z^2 - 4*z^3)) * h1 + (-2*(2*x^5*y + 2*x^5*z - 3*x^4*y^2 - 14*x^4*y*z - 3*x^4*z^2 + x^3*y^3 +
    19*x^3*y^2*z + 19*x^3*y*z^2 + x^3*z^3 - 15*x^2*y^3*z - 6*x^2*y^2*z^2 - 15*x^2*y*z^3 +
    6*x*y^4*z + 6*x*y*z^4 - 6*y^5*z + 24*y^4*z^2 - 36*y^3*z^3 + 24*y^2*z^4 - 6*y*z^5)) * h2 +
    (-4*y*z*(x^2*y + x^2*z + x*y^2 - 6*x*y*z + x*z^2 + y^2*z + y*z^2)) * h3 +
    (-12*z^3*(3*y - z)*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h4 +
    (12*z^2*(3*y - z)*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h5 + (-3*(x - z)^2*(2*x^3*y +
    2*x^3*z - 3*x^2*y^2 - 10*x^2*y*z + x^2*z^2 + x*y^3 + 13*x*y^2*z - 3*x*y*z^2 + x*z^3 - 7*y^3*z +
    8*y^2*z^2 - 7*y*z^3 + 2*z^4)) * h6 + (18*z*(y - z)^3*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h7 +
    (-6*y^3*(3*x^2*y - x^2*z - 5*x*y^2 + 2*x*y*z - x*z^2 + 4*y^3 - 5*y^2*z + 3*y*z^2)) * h8 +
    (6*y^2*(3*x^2*y - x^2*z - 5*x*y^2 + 2*x*y*z - x*z^2 + 4*y^3 - 5*y^2*z + 3*y*z^2)) * h9 +
    (12*y^3*(y - 3*z)*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h10 +
    (-12*y^2*(y - 3*z)*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h11 + (-3*(x - y)^2*(2*x^3*y +
    2*x^3*z + x^2*y^2 - 10*x^2*y*z - 3*x^2*z^2 + x*y^3 - 3*x*y^2*z + 13*x*y*z^2 + x*z^3 +
    2*y^4 - 7*y^3*z + 8*y^2*z^2 - 7*y*z^3)) * h12 + (-18*y*(y - z)^3*(x^2 - x*y - x*z + y^2 - y*z +
    z^2)) * h13 + (2*x*(2*x^5 - 3*x^4*y - x^4*z + x^3*y^2 + 5*x^3*y*z - 16*x^3*z^2 +
    4*x^2*y^2*z - 3*x^2*y*z^2 + 29*x^2*z^3 - 15*x*y^2*z^2 + 15*x*y*z^3 - 24*x*z^4 +
    6*y^2*z^3 - 6*y*z^4 + 6*z^5)) * h14 + (-4*x*z*(x^2*y + x^2*z + x*y^2 - 6*x*y*z + x*z^2 + y^2*z +
    y*z^2)) * h15 + (-12*z^3*(3*x - z)*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h16 +
    (12*z^2*(3*x - z)*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h17 +
    (18*z*(x - z)^3*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h18 +
    (3*(x - z)^3*(2*x^3 - 3*x^2*y - x^2*z + x*y^2 + 2*x*y*z - x*z^2 + y^2*z - 3*y*z^2 +
    2*z^3)) * h19 + (2*x*(2*x^5 - x^4*y - 3*x^4*z - 16*x^3*y^2 + 5*x^3*y*z + x^3*z^2 +
    29*x^2*y^3 - 3*x^2*y^2*z + 4*x^2*y*z^2 - 24*x*y^4 + 15*x*y^3*z - 15*x*y^2*z^2 +
    6*y^5 - 6*y^4*z + 6*y^3*z^2)) * h20 + (-4*x*y*(x^2*y + x^2*z + x*y^2 - 6*x*y*z + x*z^2 + y^2*z +
    y*z^2)) * h21 + (-8*x^2*(x^2 - 2*x*y - 2*x*z + 6*y*z)*(x^2 - x*y - x*z + y^2 - y*z +
    z^2)) * h22 + (24*x*y*z*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h23 + (3*(x - y)^2*(2*x^4 +
    x^3*y - 7*x^3*z + x^2*y^2 - 3*x^2*y*z + 8*x^2*z^2 + 2*x*y^3 - 10*x*y^2*z +
    13*x*y*z^2 - 7*x*z^3 + 2*y^3*z - 3*y^2*z^2 + y*z^3)) * h24 + (3*(x - z)^2*(2*x^4 - 7*x^3*y +
    x^3*z + 8*x^2*y^2 - 3*x^2*y*z + x^2*z^2 - 7*x*y^3 + 13*x*y^2*z - 10*x*y*z^2 + 2*x*z^3 +
    y^3*z - 3*y^2*z^2 + 2*y*z^3)) * h25 + (-12*y^3*(3*x - y)*(x^2 - x*y - x*z + y^2 - y*z +
    z^2)) * h26 + (12*y^2*(3*x - y)*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h27 +
    (18*y*(x - y)^3*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h28 +
    (3*(x - y)^3*(2*x^3 - x^2*y - 3*x^2*z - x*y^2 + 2*x*y*z + x*z^2 + 2*y^3 - 3*y^2*z +
    y*z^2)) * h29 + (-6*x^3*(4*x^3 - 5*x^2*y - 5*x^2*z + 3*x*y^2 + 2*x*y*z +
    3*x*z^2 - y^2*z - y*z^2)) * h30 + (6*x^2*(4*x^3 - 5*x^2*y - 5*x^2*z + 3*x*y^2 + 2*x*y*z +
    3*x*z^2 - y^2*z - y*z^2)) * h31 + (12*x^3*(x - 3*z)*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h32 +
    (-12*x^2*(x - 3*z)*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h33 +
    (-18*x*(x - z)^3*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h34 +
    (12*x^3*(x - 3*y)*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h35 +
    (-12*x^2*(x - 3*y)*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h36 +
    (-18*x*(x - y)^3*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h37 + (-4*z*(x^2*y + x^2*z +
    x*y^2 - 6*x*y*z + x*z^2 + y^2*z + y*z^2)) * h38 + (-24*z^3*(x^2 - x*y - x*z + y^2 - y*z +
    z^2)) * h39 + (24*z^2*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h40 + (-4*y*(x^2*y + x^2*z +
    x*y^2 - 6*x*y*z + x*z^2 + y^2*z + y*z^2)) * h41 + (16*y*z*(x^2 - x*y - x*z + y^2 - y*z +
    z^2)) * h42 + (-24*y^3*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h43 + (24*y^2*(x^2 - x*y - x*z +
    y^2 - y*z + z^2)) * h44 + (-4*x*(x^2*y + x^2*z + x*y^2 - 6*x*y*z + x*z^2 + y^2*z +
    y*z^2)) * h45 + (16*x*z*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h46 + (16*x*y*(x^2 - x*y - x*z +
    y^2 - y*z + z^2)) * h47 + (-24*x^3*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h48 +
    (24*x^2*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h49 + (-8*(x^2*y + x^2*z + x*y^2 - 6*x*y*z +
    x*z^2 + y^2*z + y*z^2)) * h50 + (16*z*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h51 +
    (16*y*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h52 + (16*x*(x^2 - x*y - x*z + y^2 - y*z +
    z^2)) * h53 + (32*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * h54

/-- **Carlson's Table 9.3-1**, row `2b = (3, 3, 3)`, with `a' = 1`, on slit-plane nodes;
`(xyz)^{-1/2}` is read as `x^{-1/2} y^{-1/2} z^{-1/2}`. -/
theorem carlsonR_table_9_3_1_row5 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    ((x - y)^2*(x - z)^2*(y - z)^2/7) * carlsonR (-7 / 2) ![3 / 2, 3 / 2, 3 / 2] ![x, y, z] =
      (-4*(x^2 - x*y - x*z + y^2 - y*z + z^2)) * carlsonRG x y z + (x^2*y + x^2*z + x*y^2 -
          6*x*y*z + x*z^2 + y^2*z + y*z^2) * carlsonRF x y z +
        (x^3*y + x^3*z - 2*x^2*y^2 - 2*x^2*z^2 + x*y^3 + x*z^3 + y^3*z - 2*y^2*z^2 + y*z^3) * (x ^
            (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ)) := by
  have h := row5_reg hx hy hz
  have c0 := regR3_closed_half hx hy hz (0) (0) (2)
  have c1 := regR3_closed_half hx hy hz (0) (1) (1)
  have c2 := regR3_closed_half hx hy hz (0) (2) (0)
  have c3 := regR3_closed_half hx hy hz (1) (0) (1)
  have c4 := regR3_closed_half hx hy hz (1) (1) (0)
  have c5 := regR3_closed_half hx hy hz (2) (0) (0)
  have hfun : (fun _ : Fin 3 => (1 / 2 : ℂ)) = ![1 / 2, 1 / 2, 1 / 2] := by
    funext i; fin_cases i <;> rfl
  have := slitPlane_ne_zero hx; have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  unfold carlsonRG carlsonRF carlsonR
  rw [hfun]
  norm_num [Fin.sum_univ_three] at *
  simp only [Gamma_nine_halves, Gamma_seven_halves, Gamma_three_halves] at *
  linear_combination (norm := skip) (Gamma (1 / 2)/16) * h +
    (-3*Gamma (1 / 2)*z^3*(x^2*y - 3*x^2*z + x*y^2 - 2*x*y*z + 5*x*z^2 - 3*y^2*z +
    5*y*z^2 - 4*z^3)/8) * c0 + (Gamma (1 / 2)*(2*x^5*y +
    2*x^5*z - 3*x^4*y^2 - 14*x^4*y*z - 3*x^4*z^2 + x^3*y^3 + 19*x^3*y^2*z + 19*x^3*y*z^2 +
    x^3*z^3 - 15*x^2*y^3*z - 6*x^2*y^2*z^2 - 15*x^2*y*z^3 + 6*x*y^4*z + 6*x*y*z^4 - 6*y^5*z +
    24*y^4*z^2 - 36*y^3*z^3 + 24*y^2*z^4 - 6*y*z^5)/8) * c1 +
    (3*Gamma (1 / 2)*y^3*(3*x^2*y - x^2*z - 5*x*y^2 + 2*x*y*z - x*z^2 + 4*y^3 - 5*y^2*z +
    3*y*z^2)/8) * c2 + (-Gamma (1 / 2)*x*(2*x^5 - 3*x^4*y - x^4*z + x^3*y^2 +
    5*x^3*y*z - 16*x^3*z^2 + 4*x^2*y^2*z - 3*x^2*y*z^2 + 29*x^2*z^3 - 15*x*y^2*z^2 +
    15*x*y*z^3 - 24*x*z^4 + 6*y^2*z^3 - 6*y*z^4 + 6*z^5)/8) * c3 +
    (-Gamma (1 / 2)*x*(2*x^5 - x^4*y - 3*x^4*z - 16*x^3*y^2 + 5*x^3*y*z + x^3*z^2 +
    29*x^2*y^3 - 3*x^2*y^2*z + 4*x^2*y*z^2 - 24*x*y^4 + 15*x*y^3*z - 15*x*y^2*z^2 +
    6*y^5 - 6*y^4*z + 6*y^3*z^2)/8) * c4 + (3*Gamma (1 / 2)*x^3*(4*x^3 - 5*x^2*y - 5*x^2*z +
    3*x*y^2 + 2*x*y*z + 3*x*z^2 - y^2*z - y*z^2)/8) * c5
  field_simp
  ring

/-- Exercise 9.3-3, regularized form. -/
private theorem ex933_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    (2*(x - z)*(y - z)) *
      regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 3 / 2] ![x, y, z] =
      (4*z) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      (2*(x*y - x*z - y*z)) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      (-2*x*y*z) * regCarlsonR (-3 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] := by
  have h0 := regR3_sum hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h1 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h2 := regR3_sum hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h3 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h4 := regR3_raise₀ hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h5 := regR3_raise₁ hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h6 := regR3_sum hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h7 := regR3_shift hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h8 := regR3_raise₀ hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h9 := regR3_raise₂ hx hy hz (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h10 := regR3_sum hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h11 := regR3_shift hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h12 := regR3_raise₁ hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h13 := regR3_raise₂ hx hy hz (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h14 := regR3_shift hx hy hz (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have := slitPlane_ne_zero hx; have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  norm_num at *
  linear_combination (2*x*y*z) * h0 + (-2*(x*y - x*z - y*z)) * h1 + (-2*z*(x*y - x*z - y*z)) * h2 +
    (2*(x*y - x*z - y*z)) * h3 + (y*z*(x - z)) * h4 + (x*z*(y - z)) * h5 + (2*y^2*z) * h6 +
    (-2*y*z) * h7 + (y*z*(x - y)) * h8 + (-x*y*(y - z)) * h9 + (2*x^2*z) * h10 + (-2*x*z) * h11 +
    (-x*z*(x - y)) * h12 + (-x*y*(x - z)) * h13 + (-4*z) * h14

/-- The identity behind Exercise 9.3-3, for `R_{-1/2}(1/2, 1/2, 3/2; x, y, z) = R_H(x, y, z, z)`. -/
theorem carlsonR_neg_half_half_half_three_halves (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    (2*(x - z)*(y - z)/3) * carlsonR (-1 / 2) ![1 / 2, 1 / 2, 3 / 2] ![x, y, z] =
      (2*z) * carlsonRG x y z + (x*y - x*z - y*z) * carlsonRF x y z +
        (-x*y*z) * (x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ)) := by
  have h := ex933_reg hx hy hz
  have c0 := regR3_closed_half hx hy hz (0) (0) (0)
  have hfun : (fun _ : Fin 3 => (1 / 2 : ℂ)) = ![1 / 2, 1 / 2, 1 / 2] := by
    funext i; fin_cases i <;> rfl
  have := slitPlane_ne_zero hx; have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  unfold carlsonRG carlsonRF carlsonR
  rw [hfun]
  norm_num [Fin.sum_univ_three] at *
  simp only [Gamma_five_halves, Gamma_three_halves] at *
  linear_combination (norm := skip) (Gamma (1 / 2)/4) * h + (-Gamma (1 / 2)*x*y*z/2) * c0
  field_simp
  ring

/-- `R_H(x, y, z, z) = R_{-1/2}(1/2, 1/2, 3/2; x, y, z)`, by merging the equal nodes. -/
theorem carlsonRH_self_right (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    carlsonRH x y z z = carlsonR (-1 / 2) ![1 / 2, 1 / 2, 3 / 2] ![x, y, z] := by
  have hs : (![x, y, z] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  have hq : Function.Surjective (![0, 1, 2, 2] : Fin 4 → Fin 3) := by
    intro k; fin_cases k
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hcomp : (![x, y, z, z] : Fin 4 → ℂ) = ![x, y, z] ∘ ![0, 1, 2, 2] := by
    funext i; fin_cases i <;> rfl
  have hagg : stdSimplexAggregate (![0, 1, 2, 2] : Fin 4 → Fin 3)
      (![1 / 2, 1 / 2, 1 / 2, 1] : Fin 4 → ℂ) = ![1 / 2, 1 / 2, 3 / 2] := by
    classical
    funext k
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    fin_cases k <;> (simp [Finset.sum_filter, Fin.sum_univ_four]; try norm_num)
  unfold carlsonRH carlsonR
  rw [hcomp, regCarlsonR_aggregate_of_slit hq _ hs, hagg]
  congr 1
  simp [Fin.sum_univ_four, Fin.sum_univ_three]; norm_num

/-- **Exercise 9.3-3**: for `x, y, z` in the slit plane,
`(2/3)(z - x)(z - y) R_H(x, y, z, z) = (xy - xz - yz) R_F(x, y, z) + 2z R_G(x, y, z) - (xyz)^{1/2}`,
with `(xyz)^{1/2}` read as `x^{1/2} y^{1/2} z^{1/2}`. -/
theorem carlsonRH_self_right_eq (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    2 / 3 * (z - x) * (z - y) * carlsonRH x y z z =
      (x * y - x * z - y * z) * carlsonRF x y z + 2 * z * carlsonRG x y z -
        x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) := by
  have half : ∀ {w : ℂ}, w ∈ slitPlane → w ^ (1 / 2 : ℂ) = w * w ^ (-1 / 2 : ℂ) := fun {w} hw => by
    rw [show (1 / 2 : ℂ) = 1 + -1 / 2 by norm_num, cpow_add _ _ (slitPlane_ne_zero hw), cpow_one]
  rw [carlsonRH_self_right hx hy hz, half hx, half hy, half hz]
  have h := carlsonR_neg_half_half_half_three_halves hx hy hz
  linear_combination h


/-! ### Table 9.3-2: complete integrals of the second kind -/

section Table2

variable {x y : ℂ}

/-- **Carlson's Table 9.3-2**, row `2b = (-1, 3)`, `2a = 1`, on slit-plane nodes, regularized
    form. -/
private theorem carlsonR_table_9_3_2_row1_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (y) * regCarlsonR (-1 / 2) ![-1 / 2, 3 / 2] ![x, y] =
      (1) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2] ![x, y] +
      (0) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2] ![x, y] := by
  have h0 := regR2_shift hx hy (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ)
  have h1 := regR2_raise₀ hx hy (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ)
  norm_num at *
  linear_combination (-2) * h0 + (2) * h1

/-- **Carlson's Table 9.3-2**, row `2b = (-1, 3)`, `2a = 1`, on slit-plane nodes. -/
theorem carlsonR_table_9_3_2_row1 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (y) * carlsonR (-1 / 2) ![-1 / 2, 3 / 2] ![x, y] =
      (1) * carlsonRE x y +
      (0) * TwoVariable.carlsonRK x y := by
  have h := carlsonR_table_9_3_2_row1_reg hx hy
  unfold carlsonRE TwoVariable.carlsonRK carlsonR
  simp only [TwoVariable.pair]
  norm_num [Fin.sum_univ_succ] at h ⊢
  try simp only [Gamma_one, Gamma_two', Gamma_three'] at h ⊢
  linear_combination (1) * h

/-- **Carlson's Table 9.3-2**, row `2b = (-1, 3)`, `2a = -1`, on slit-plane nodes, regularized
    form. -/
private theorem carlsonR_table_9_3_2_row2_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (1) * regCarlsonR (1 / 2) ![-1 / 2, 3 / 2] ![x, y] =
      (2) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2] ![x, y] +
      (-x) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2] ![x, y] := by
  have h0 := regR2_sum hx hy (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ)
  have h1 := regR2_raise₀ hx hy (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ)
  norm_num at *
  linear_combination (-2) * h0 + (2) * h1

/-- **Carlson's Table 9.3-2**, row `2b = (-1, 3)`, `2a = -1`, on slit-plane nodes. -/
theorem carlsonR_table_9_3_2_row2 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (1) * carlsonR (1 / 2) ![-1 / 2, 3 / 2] ![x, y] =
      (2) * carlsonRE x y +
      (-x) * TwoVariable.carlsonRK x y := by
  have h := carlsonR_table_9_3_2_row2_reg hx hy
  unfold carlsonRE TwoVariable.carlsonRK carlsonR
  simp only [TwoVariable.pair]
  norm_num [Fin.sum_univ_succ] at h ⊢
  try simp only [Gamma_one, Gamma_two', Gamma_three'] at h ⊢
  linear_combination (1) * h

/-- **Carlson's Table 9.3-2**, row `2b = (1, 3)`, `2a = 1`, on slit-plane nodes, regularized form.
    -/
private theorem carlsonR_table_9_3_2_row3_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (x - y) * regCarlsonR (-1 / 2) ![1 / 2, 3 / 2] ![x, y] =
      (-2) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2] ![x, y] +
      (2*x) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2] ![x, y] := by
  have h0 := regR2_shift hx hy (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h1 := regR2_sum hx hy (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ)
  have h2 := regR2_raise₀ hx hy (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ)
  have h3 := regR2_raise₀ hx hy (1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ)
  have h4 := regR2_sum hx hy (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h5 := regR2_raise₀ hx hy (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  norm_num at *
  linear_combination (2) * h0 + (4) * h1 + (-4) * h2 + (2) * h3 + (-6) * h4 + (2) * h5

/-- **Carlson's Table 9.3-2**, row `2b = (1, 3)`, `2a = 1`, on slit-plane nodes. -/
theorem carlsonR_table_9_3_2_row3 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (x - y) * carlsonR (-1 / 2) ![1 / 2, 3 / 2] ![x, y] =
      (-2) * carlsonRE x y +
      (2*x) * TwoVariable.carlsonRK x y := by
  have h := carlsonR_table_9_3_2_row3_reg hx hy
  unfold carlsonRE TwoVariable.carlsonRK carlsonR
  simp only [TwoVariable.pair]
  norm_num [Fin.sum_univ_succ] at h ⊢
  try simp only [Gamma_one, Gamma_two', Gamma_two', Gamma_three'] at h ⊢
  linear_combination (1) * h

/-- **Carlson's Table 9.3-2**, row `2b = (3, 3)`, `2a = 3`, on slit-plane nodes, regularized form.
    -/
private theorem carlsonR_table_9_3_2_row4_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (2*(x - y)^2) * regCarlsonR (-3 / 2) ![3 / 2, 3 / 2] ![x, y] =
      (-16) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2] ![x, y] +
      (8*(x + y)) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2] ![x, y] := by
  have h0 := regR2_shift hx hy (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h1 := regR2_shift hx hy (-3 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h2 := regR2_shift hx hy (-3 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h3 := regR2_sum hx hy (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ)
  have h4 := regR2_raise₀ hx hy (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ)
  have h5 := regR2_raise₀ hx hy (-1 / 2 : ℂ) (-1 / 2 : ℂ) (5 / 2 : ℂ)
  have h6 := regR2_sum hx hy (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h7 := regR2_shift hx hy (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h8 := regR2_raise₀ hx hy (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ)
  have h9 := regR2_sum hx hy (-1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h10 := regR2_raise₀ hx hy (-1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ)
  have h11 := regR2_sum hx hy (-1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  have h12 := regR2_raise₀ hx hy (-1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ)
  norm_num at *
  linear_combination (8*x) * h0 + (-4*x) * h1 + (-4*y) * h2 + (8*y) * h3 + (-8*y) * h4 + (12*y) *
      h5 + (-8*(x + y)) * h6 + (16) * h7 + (-8*x) * h8 + (-12*y) * h9 + (8*y) * h10 + (-12*y) *
          h11 + (12*y) * h12

/-- **Carlson's Table 9.3-2**, row `2b = (3, 3)`, `2a = 3`, on slit-plane nodes. -/
theorem carlsonR_table_9_3_2_row4 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    ((x - y)^2) * carlsonR (-3 / 2) ![3 / 2, 3 / 2] ![x, y] =
      (-16) * carlsonRE x y +
      (8*(x + y)) * TwoVariable.carlsonRK x y := by
  have h := carlsonR_table_9_3_2_row4_reg hx hy
  unfold carlsonRE TwoVariable.carlsonRK carlsonR
  simp only [TwoVariable.pair]
  norm_num [Fin.sum_univ_succ] at h ⊢
  try simp only [Gamma_one, Gamma_three', Gamma_two', Gamma_three'] at h ⊢
  linear_combination (1) * h

/-- `R_{1/2}(3/2, -1/2; x, y) = 2 R_E(x, y) - y R_K(x, y)` on slit-plane nodes (used for the
    Landen transformation of `R_E`), regularized form. -/
private theorem carlsonR_half_three_halves_neg_half_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (1) * regCarlsonR (1 / 2) ![3 / 2, -1 / 2] ![x, y] =
      (2) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2] ![x, y] +
      (-y) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2] ![x, y] := by
  have h0 := regR2_shift hx hy (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ)
  have h1 := regR2_sum hx hy (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ)
  have h2 := regR2_raise₀ hx hy (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ)
  norm_num at *
  linear_combination (2) * h0 + (-4) * h1 + (2) * h2

/-- `R_{1/2}(3/2, -1/2; x, y) = 2 R_E(x, y) - y R_K(x, y)` on slit-plane nodes (used for the
    Landen transformation of `R_E`). -/
theorem carlsonR_half_three_halves_neg_half (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (1) * carlsonR (1 / 2) ![3 / 2, -1 / 2] ![x, y] =
      (2) * carlsonRE x y +
      (-y) * TwoVariable.carlsonRK x y := by
  have h := carlsonR_half_three_halves_neg_half_reg hx hy
  unfold carlsonRE TwoVariable.carlsonRK carlsonR
  simp only [TwoVariable.pair]
  norm_num [Fin.sum_univ_succ] at h ⊢
  try simp only [Gamma_one, Gamma_two', Gamma_three'] at h ⊢
  linear_combination (1) * h

end Table2

/-! ### Table 9.3-3: integrals of the third kind -/

section Table3

variable {x y z ρ : ℂ}

/-- **Carlson's Table 9.3-3**, row `2(b₁, b₂, b₃) = (-1, -1, 3)`, `b₄ = 1`, on slit-plane nodes;
    `(xyz)^{-1/2}` is read as `x^{-1/2} y^{-1/2} z^{-1/2}`, regularized form. -/
private theorem carlsonR_table_9_3_3_row1_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈
    slitPlane) (hρ : ρ ∈ slitPlane) :
    (ρ*(z - ρ)/2) * regCarlsonR (-1 / 2) ![-1 / 2, -1 / 2, 3 / 2, 1] ![x, y, z, ρ] =
      (-(x - ρ)*(y - ρ)/2) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2, 1] ![x, y, z, ρ] +
      (ρ) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      ((x*y - x*ρ - y*ρ)/2) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      (2*ρ) * regCarlsonR (1 / 2) ![-1 / 2, -1 / 2, 1 / 2] ![x, y, z] := by
  have h0 := regR4_shift hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h1 := regR4_sum hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h2 := regR4_sum hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h3 := regR4_raise₁ hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h4 := regR4_raise₂ hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h5 := regR4_raise₁ hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (2 : ℂ)
  have h6 := regR4_raise₃ hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (0 : ℂ)
  have h7 := regR4_raise₁ hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (1 : ℂ)
  have h8 := regR4_sum hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h9 := regR4_raise₀ hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h10 := regR4_raise₃ hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h11 := regR4_sum hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h12 := regR4_raise₀ hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h13 := regR4_raise₁ hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h14 := regR4_raise₂ hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h15 := regR4_raise₃ hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (0 : ℂ)
  have h16 := regR4_raise₃ hx hy hz hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h17 := regR4_raise₁ hx hy hz hρ (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h18 := regR4_raise₁ hx hy hz hρ (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h19 := regR4_raise₃ hx hy hz hρ (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  norm_num at *
  simp only [regR4_zero hx hy hz hρ] at *
  linear_combination (y) * h0 + (-2*ρ) * h1 + (2*ρ) * h2 + (-3*ρ) * h3 + (ρ) * h4 + (2*ρ) * h5 +
      (-ρ) * h6 + (ρ) * h7 + (-2*y) * h8 + (-y + ρ) * h9 + (3*y) * h10 + (-4*ρ) * h11 + (-ρ) * h12
          + (y + ρ) * h13 + (y) * h14 + (-y) * h15 + (-y) * h16 + (ρ) * h17 + (-ρ) * h18 + (ρ) * h19

/-- **Carlson's Table 9.3-3**, row `2(b₁, b₂, b₃) = (-1, -1, 3)`, `b₄ = 1`, on slit-plane nodes;
    `(xyz)^{-1/2}` is read as `x^{-1/2} y^{-1/2} z^{-1/2}`. -/
theorem carlsonR_table_9_3_3_row1 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hρ : ρ ∈ slitPlane) :
    (ρ*(z - ρ)) * carlsonR (-1 / 2) ![-1 / 2, -1 / 2, 3 / 2, 1] ![x, y, z, ρ] =
      (-2*(x - ρ)*(y - ρ)/3) * carlsonRH x y z ρ +
      (2*ρ) * carlsonRG x y z +
      (x*y - x*ρ - y*ρ) * carlsonRF x y z +
      (-x*y*ρ) * (x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ)) := by
  have h := carlsonR_table_9_3_3_row1_reg hx hy hz hρ
  have c0 := regR3_closed_half hx hy hz (-1) (-1) (0)
  norm_num at c0
  try simp only [Gamma_neg_half] at c0
  have hfun : (fun _ : Fin 3 => (1 / 2 : ℂ)) = ![1 / 2, 1 / 2, 1 / 2] := by
    funext i; fin_cases i <;> rfl
  unfold carlsonRH carlsonRG carlsonRF carlsonR
  simp only [hfun]
  norm_num [Fin.sum_univ_succ] at h ⊢
  try simp only [Gamma_five_halves, Gamma_three_halves] at h ⊢
  have := slitPlane_ne_zero hx
  have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  have := slitPlane_ne_zero hρ
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  linear_combination (norm := skip) (Gamma (1 / 2)) * h + ((2*ρ) * Gamma (1 / 2)) * c0
  field_simp
  ring

/-- **Carlson's Table 9.3-3**, row `2(b₁, b₂, b₃) = (-1, 1, 3)`, `b₄ = 1`, on slit-plane nodes;
    `(xyz)^{-1/2}` is read as `x^{-1/2} y^{-1/2} z^{-1/2}`, regularized form. -/
private theorem carlsonR_table_9_3_3_row3_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈
    slitPlane) (hρ : ρ ∈ slitPlane) :
    (ρ*(y - z)*(z - ρ)/4) * regCarlsonR (-3 / 2) ![-1 / 2, 1 / 2, 3 / 2, 1] ![x, y, z, ρ] =
      (-(x - ρ)*(y - z)/2) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2, 1] ![x, y, z, ρ] +
      (ρ) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      ((x*y - x*z - y*ρ)/2) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, z] +
      (-ρ*(x - z)) * regCarlsonR (-1 / 2) ![-1 / 2, -1 / 2, 1 / 2, 1] ![x, y, z, ρ] +
      (ρ*(x - y)) * regCarlsonR (-1 / 2) ![-1 / 2, 1 / 2, -1 / 2, 1] ![x, y, z, ρ] +
      (x*y - x*z - y*ρ) * regCarlsonR (-1 / 2) ![-1 / 2, 1 / 2, 1 / 2] ![x, y, z] := by
  have h0 := regR4_shift hx hy hz hρ (-3 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h1 := regR4_shift hx hy hz hρ (-3 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h2 := regR4_shift hx hy hz hρ (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h3 := regR4_shift hx hy hz hρ (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h4 := regR4_sum hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h5 := regR4_raise₀ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (2 : ℂ)
  have h6 := regR4_raise₁ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (2 : ℂ)
  have h7 := regR4_raise₁ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (1 : ℂ)
  have h8 := regR4_sum hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h9 := regR4_raise₀ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (2 : ℂ)
  have h10 := regR4_raise₂ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (2 : ℂ)
  have h11 := regR4_sum hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h12 := regR4_raise₀ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h13 := regR4_raise₁ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h14 := regR4_raise₂ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h15 := regR4_raise₀ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (0 : ℂ)
  have h16 := regR4_raise₃ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (3 / 2 : ℂ) (0 : ℂ)
  have h17 := regR4_raise₂ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h18 := regR4_raise₀ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h19 := regR4_raise₃ hx hy hz hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h20 := regR4_raise₁ hx hy hz hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (2 : ℂ)
  have h21 := regR4_raise₂ hx hy hz hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (2 : ℂ)
  have h22 := regR4_sum hx hy hz hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h23 := regR4_raise₀ hx hy hz hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h24 := regR4_raise₂ hx hy hz hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h25 := regR4_sum hx hy hz hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h26 := regR4_raise₀ hx hy hz hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h27 := regR4_raise₁ hx hy hz hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h28 := regR4_shift hx hy hz hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h29 := regR4_raise₀ hx hy hz hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  norm_num at *
  simp only [regR4_zero hx hy hz hρ] at *
  linear_combination (-(x - ρ)*(y - z)/2) * h0 + (-ρ*(x - z)/2) * h1 + (ρ*(x - y)/2) * h2 +
      (-x*ρ/2) * h3 + (ρ*(x - z)) * h4 + (-ρ*(z - ρ)) * h5 + (ρ*(x - ρ)) * h6 + (ρ*(x - z)/2) * h7
          + (-ρ*(x - y)) * h8 + (ρ*(y - ρ)) * h9 + (-ρ*(x - ρ)) * h10 + (-x*y + x*z + y*ρ) * h11 +
            (-x*(y - z)/2) * h12 + ((x*y - x*z + x*ρ - y*ρ)/2) * h13 + ((x*y - x*z - x*ρ - y*ρ +
            2*z*ρ)/2) * h14 + (z*ρ/2) * h15 + (-(x - ρ)*(y - z)/2) * h16 + (-ρ*(x - y)/2) * h17 +
            (y*ρ/2) * h18 + (-x*(y - z)/2) * h19 + (-ρ*(x - ρ)) * h20 + (ρ*(x - ρ)) * h21 + (-ρ*(x
            - z)) * h22 + (ρ*(x - z)/2) * h23 + (ρ*(x - z)/2) * h24 + (ρ*(x - y)) * h25 + (-ρ*(x -
            y)/2) * h26 + (-ρ*(x - y)/2) * h27 + (-ρ) * h28 + (x*ρ/2) * h29

/-- **Carlson's Table 9.3-3**, row `2(b₁, b₂, b₃) = (-1, 1, 3)`, `b₄ = 1`, on slit-plane nodes;
    `(xyz)^{-1/2}` is read as `x^{-1/2} y^{-1/2} z^{-1/2}`. -/
theorem carlsonR_table_9_3_3_row3 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hρ : ρ ∈ slitPlane) :
    (ρ*(y - z)*(z - ρ)/3) * carlsonR (-3 / 2) ![-1 / 2, 1 / 2, 3 / 2, 1] ![x, y, z, ρ] =
      (-2*(x - ρ)*(y - z)/3) * carlsonRH x y z ρ +
      (2*ρ) * carlsonRG x y z +
      (x*y - x*z - y*ρ) * carlsonRF x y z +
      (-x*y*ρ) * (x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ)) := by
  have h := carlsonR_table_9_3_3_row3_reg hx hy hz hρ
  have c0 := regR4_closed_half hx hy hz hρ (-1) (-1) (0) (1)
  norm_num at c0
  try simp only [Gamma_neg_half, Gamma_three_halves, Gamma_five_halves, Gamma_seven_halves] at c0
  have c1 := regR4_closed_half hx hy hz hρ (-1) (0) (-1) (1)
  norm_num at c1
  try simp only [Gamma_neg_half, Gamma_three_halves, Gamma_five_halves, Gamma_seven_halves] at c1
  have c2 := regR3_closed_half hx hy hz (-1) (0) (0)
  norm_num at c2
  try simp only [Gamma_neg_half, Gamma_three_halves, Gamma_five_halves, Gamma_seven_halves] at c2
  have hfun : (fun _ : Fin 3 => (1 / 2 : ℂ)) = ![1 / 2, 1 / 2, 1 / 2] := by
    funext i; fin_cases i <;> rfl
  unfold carlsonRH carlsonRG carlsonRF carlsonR
  simp only [hfun]
  norm_num [Fin.sum_univ_succ] at h ⊢
  try simp only [Gamma_five_halves, Gamma_three_halves] at h ⊢
  have := slitPlane_ne_zero hx
  have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hz
  have := slitPlane_ne_zero hρ
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  linear_combination (norm := skip) (Gamma (1 / 2)) * h + ((-ρ*(x - z)) * Gamma (1 / 2)) * c0 +
      ((ρ*(x - y)) * Gamma (1 / 2)) * c1 + ((x*y - x*z - y*ρ) * Gamma (1 / 2)) * c2
  field_simp
  ring

end Table3

/-! ### Table 9.3-4: complete integrals of the third kind -/

section Table4

variable {x y ρ : ℂ}

/-- **Carlson's Table 9.3-4**, row `2(b₁, b₂) = (-1, 3)`, `2a = 1`, `b₃ = 1`, on slit-plane nodes,
    regularized form. -/
private theorem carlsonR_table_9_3_4_row2_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ : ρ ∈
    slitPlane) :
    (y - ρ) * regCarlsonR (-1 / 2) ![-1 / 2, 3 / 2, 1] ![x, y, ρ] =
      (x - ρ) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1] ![x, y, ρ] +
      (2) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2] ![x, y] +
      (-2*x) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2] ![x, y] := by
  have h0 := regR3_sum hx hy hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h1 := regR3_raise₀ hx hy hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h2 := regR3_raise₀ hx hy hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h3 := regR3_raise₁ hx hy hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h4 := regR3_raise₂ hx hy hρ (1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (0 : ℂ)
  have h5 := regR3_raise₂ hx hy hρ (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  norm_num at *
  simp only [regR3_zero hx hy hρ] at *
  linear_combination (-4) * h0 + (4) * h1 + (-2) * h2 + (2) * h3 + (-2) * h4 + (2) * h5

/-- **Carlson's Table 9.3-4**, row `2(b₁, b₂) = (-1, 3)`, `2a = 1`, `b₃ = 1`, on slit-plane nodes.
    -/
theorem carlsonR_table_9_3_4_row2 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ : ρ ∈ slitPlane) :
    (y - ρ) * carlsonR (-1 / 2) ![-1 / 2, 3 / 2, 1] ![x, y, ρ] =
      (x - ρ) * carlsonRL x y ρ +
      (2) * carlsonRE x y +
      (-2*x) * TwoVariable.carlsonRK x y := by
  have h := carlsonR_table_9_3_4_row2_reg hx hy hρ
  unfold carlsonRL carlsonRE TwoVariable.carlsonRK carlsonR
  simp only [TwoVariable.pair]
  norm_num [Fin.sum_univ_succ] at h ⊢
  try simp only [Gamma_one, Gamma_two', Gamma_two', Gamma_three'] at h ⊢
  linear_combination (1) * h

/-- **Carlson's Table 9.3-4**, row `2(b₁, b₂) = (-1, 3)`, `2a = 3`, `b₃ = 1`, on slit-plane nodes,
    regularized form. -/
private theorem carlsonR_table_9_3_4_row3_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ : ρ ∈
    slitPlane) :
    (y*ρ*(y - ρ)) * regCarlsonR (-3 / 2) ![-1 / 2, 3 / 2, 1] ![x, y, ρ] =
      (-y*(x - ρ)) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1] ![x, y, ρ] +
      (-2*ρ) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2] ![x, y] +
      (2*x*y) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2] ![x, y] := by
  have h0 := regR3_shift hx hy hρ (-3 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h1 := regR3_shift hx hy hρ (-3 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (0 : ℂ)
  have h2 := regR3_shift hx hy hρ (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h3 := regR3_sum hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h4 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h5 := regR3_raise₁ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (2 : ℂ)
  have h6 := regR3_sum hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h7 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h8 := regR3_sum hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h9 := regR3_raise₁ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h10 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (0 : ℂ)
  have h11 := regR3_raise₂ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (0 : ℂ)
  have h12 := regR3_sum hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (0 : ℂ)
  have h13 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (0 : ℂ)
  have h14 := regR3_raise₂ hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (0 : ℂ)
  have h15 := regR3_raise₁ hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h16 := regR3_shift hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h17 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  norm_num at *
  simp only [regR3_zero hx hy hρ] at *
  linear_combination (-2*y^2) * h0 + (4*x*y) * h1 + (2*x*ρ) * h2 + (4*y*ρ) * h3 + (-4*y*ρ) * h4 +
      (4*y*ρ) * h5 + (-4*y^2) * h6 + (4*y^2) * h7 + (-2*y*ρ) * h8 + (2*y^2) * h9 + (-2*y*ρ) * h10
          + (-2*y*(y - ρ)) * h11 + (-4*x*y) * h12 + (-4*x*y) * h13 + (4*x*y) * h14 + (-2*x*y) *
            h15 + (2*ρ) * h16 + (-2*x*ρ) * h17

/-- **Carlson's Table 9.3-4**, row `2(b₁, b₂) = (-1, 3)`, `2a = 3`, `b₃ = 1`, on slit-plane nodes.
    -/
theorem carlsonR_table_9_3_4_row3 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ : ρ ∈ slitPlane) :
    (y*ρ*(y - ρ)) * carlsonR (-3 / 2) ![-1 / 2, 3 / 2, 1] ![x, y, ρ] =
      (-y*(x - ρ)) * carlsonRL x y ρ +
      (-2*ρ) * carlsonRE x y +
      (2*x*y) * TwoVariable.carlsonRK x y := by
  have h := carlsonR_table_9_3_4_row3_reg hx hy hρ
  unfold carlsonRL carlsonRE TwoVariable.carlsonRK carlsonR
  simp only [TwoVariable.pair]
  norm_num [Fin.sum_univ_succ] at h ⊢
  try simp only [Gamma_one, Gamma_two', Gamma_two', Gamma_three'] at h ⊢
  linear_combination (1) * h

/-- **Carlson's Table 9.3-4**, row `2(b₁, b₂) = (1, 3)`, `2a = 3`, `b₃ = 1`, on slit-plane nodes,
    regularized form. -/
private theorem carlsonR_table_9_3_4_row5_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ : ρ ∈
    slitPlane) :
    ((x - y)*(y - ρ)/2) * regCarlsonR (-3 / 2) ![1 / 2, 3 / 2, 1] ![x, y, ρ] =
      (x - y) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1] ![x, y, ρ] +
      (2) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2] ![x, y] +
      (-2*x) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2] ![x, y] := by
  have h0 := regR3_shift hx hy hρ (-3 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (0 : ℂ)
  have h1 := regR3_shift hx hy hρ (-3 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h2 := regR3_shift hx hy hρ (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h3 := regR3_shift hx hy hρ (-3 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h4 := regR3_sum hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h5 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h6 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ) (2 : ℂ)
  have h7 := regR3_sum hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h8 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h9 := regR3_sum hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h10 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h11 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ) (2 : ℂ)
  have h12 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (0 : ℂ)
  have h13 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (-1 / 2 : ℂ) (3 / 2 : ℂ) (1 : ℂ)
  have h14 := regR3_sum hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (0 : ℂ)
  have h15 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (0 : ℂ)
  have h16 := regR3_raise₂ hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (0 : ℂ)
  have h17 := regR3_sum hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h18 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 : ℂ)
  have h19 := regR3_raise₁ hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (2 : ℂ)
  have h20 := regR3_shift hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h21 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (0 : ℂ)
  have h22 := regR3_sum hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h23 := regR3_raise₀ hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  have h24 := regR3_raise₁ hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (1 : ℂ)
  norm_num at *
  simp only [regR3_zero hx hy hρ] at *
  linear_combination (-4*x) * h0 + (2*x) * h1 + (-2*x) * h2 + (-x + y) * h3 + (-4*ρ) * h4 + (4*ρ)
      * h5 + (-4*ρ) * h6 + (4*y) * h7 + (-4*y) * h8 + (-2*(y - ρ)) * h9 + (2*y) * h10 + (-2*(y -
          ρ)) * h11 + (2*y) * h12 + (-y + ρ) * h13 + (4*x) * h14 + (4*x) * h15 + (-4*x) * h16 +
            (2*x) * h17 + (-2*x) * h18 + (2*(x - ρ)) * h19 + (-2) * h20 + (2*x) * h21 + (-3*(x -
            y)) * h22 + (x - y) * h23 + (x - ρ) * h24

/-- **Carlson's Table 9.3-4**, row `2(b₁, b₂) = (1, 3)`, `2a = 3`, `b₃ = 1`, on slit-plane nodes. -/
theorem carlsonR_table_9_3_4_row5 (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ : ρ ∈ slitPlane) :
    ((x - y)*(y - ρ)/4) * carlsonR (-3 / 2) ![1 / 2, 3 / 2, 1] ![x, y, ρ] =
      (x - y) * carlsonRL x y ρ +
      (2) * carlsonRE x y +
      (-2*x) * TwoVariable.carlsonRK x y := by
  have h := carlsonR_table_9_3_4_row5_reg hx hy hρ
  unfold carlsonRL carlsonRE TwoVariable.carlsonRK carlsonR
  simp only [TwoVariable.pair]
  norm_num [Fin.sum_univ_succ] at h ⊢
  try simp only [Gamma_one, Gamma_three', Gamma_two', Gamma_two', Gamma_three'] at h ⊢
  linear_combination (1) * h

end Table4

/-! ### Two identities used for the Landen transformation of `R_G` -/

section LandenG

variable {x y ρ : ℂ}

/-- `R_{1/2}(1/2, 1/2, -1/2; x, y, z) = 2 R_G(x, y, z) - z R_F(x, y, z)` on slit-plane nodes,
    regularized form. -/
private theorem carlsonR_half_half_half_neg_half_reg (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ
    : ρ ∈ slitPlane) :
    (1) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2, -1 / 2] ![x, y, ρ] =
      (1) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, ρ] +
      (-ρ/2) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, ρ] := by
  have h0 := regR3_shift hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ)
  have h1 := regR3_sum hx hy hρ (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ)
  have h2 := regR3_raise₀ hx hy hρ (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ)
  have h3 := regR3_raise₁ hx hy hρ (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ)
  norm_num at *
  linear_combination (1) * h0 + (-2) * h1 + (1) * h2 + (1) * h3

/-- `R_{1/2}(1/2, 1/2, -1/2; x, y, z) = 2 R_G(x, y, z) - z R_F(x, y, z)` on slit-plane nodes. -/
theorem carlsonR_half_half_half_neg_half (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ : ρ ∈
    slitPlane) :
    (1) * carlsonR (1 / 2) ![1 / 2, 1 / 2, -1 / 2] ![x, y, ρ] =
      (2) * carlsonRG x y ρ +
      (-ρ) * carlsonRF x y ρ := by
  have h := carlsonR_half_half_half_neg_half_reg hx hy hρ
  have hfun : (fun _ : Fin 3 => (1 / 2 : ℂ)) = ![1 / 2, 1 / 2, 1 / 2] := by
    funext i; fin_cases i <;> rfl
  unfold carlsonRG carlsonRF carlsonR
  simp only [hfun]
  norm_num [Fin.sum_univ_succ] at h ⊢
  try simp only [Gamma_three_halves] at h ⊢
  linear_combination (Gamma (1 / 2)) * h

/-- `R_{1/2}(3/2, -1/2, -1/2; x, y, z) = 4 R_G(x, y, z) - (y + z) R_F(x, y, z) - yz (xyz)^{-1/2}`
    on slit-plane nodes, regularized form. -/
private theorem carlsonR_half_three_halves_neg_half_neg_half_reg (hx : x ∈ slitPlane) (hy : y ∈
    slitPlane) (hρ : ρ ∈ slitPlane) :
    (1) * regCarlsonR (1 / 2) ![3 / 2, -1 / 2, -1 / 2] ![x, y, ρ] =
      (2) * regCarlsonR (1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, ρ] +
      (-(y + ρ)/2) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2] ![x, y, ρ] +
      (2) * regCarlsonR (1 / 2) ![1 / 2, -1 / 2, -1 / 2] ![x, y, ρ] := by
  have h0 := regR3_shift hx hy hρ (-1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ)
  have h1 := regR3_sum hx hy hρ (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (-1 / 2 : ℂ)
  have h2 := regR3_raise₁ hx hy hρ (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ) (1 / 2 : ℂ)
  have h3 := regR3_sum hx hy hρ (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ)
  have h4 := regR3_raise₀ hx hy hρ (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ)
  have h5 := regR3_raise₁ hx hy hρ (1 / 2 : ℂ) (1 / 2 : ℂ) (1 / 2 : ℂ) (-1 / 2 : ℂ)
  norm_num at *
  linear_combination (1) * h0 + (-2) * h1 + (1) * h2 + (-2) * h3 + (1) * h4 + (1) * h5

/-- `R_{1/2}(3/2, -1/2, -1/2; x, y, z) = 4 R_G(x, y, z) - (y + z) R_F(x, y, z) - yz (xyz)^{-1/2}`
    on slit-plane nodes. -/
theorem carlsonR_half_three_halves_neg_half_neg_half (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ
    : ρ ∈ slitPlane) :
    (1) * carlsonR (1 / 2) ![3 / 2, -1 / 2, -1 / 2] ![x, y, ρ] =
      (4) * carlsonRG x y ρ +
      (-y - ρ) * carlsonRF x y ρ +
      (-y*ρ) * (x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * ρ ^ (-1 / 2 : ℂ)) := by
  have h := carlsonR_half_three_halves_neg_half_neg_half_reg hx hy hρ
  have c0 := regR3_closed_half hx hy hρ (0) (-1) (-1)
  norm_num at c0
  try simp only [Gamma_neg_half] at c0
  have hfun : (fun _ : Fin 3 => (1 / 2 : ℂ)) = ![1 / 2, 1 / 2, 1 / 2] := by
    funext i; fin_cases i <;> rfl
  unfold carlsonRG carlsonRF carlsonR
  simp only [hfun]
  norm_num [Fin.sum_univ_succ] at h ⊢
  try simp only [Gamma_three_halves] at h ⊢
  have := slitPlane_ne_zero hx
  have := slitPlane_ne_zero hy
  have := slitPlane_ne_zero hρ
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  linear_combination (norm := skip) (Gamma (1 / 2)) * h + ((2) * Gamma (1 / 2)) * c0
  field_simp
  ring

end LandenG

end Carlson
