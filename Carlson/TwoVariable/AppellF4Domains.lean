/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF4F1
public import Carlson.TwoVariable.AppellF4SecondQuadratic

/-!
# Concrete continuation domains for the F₄ matrices

The positive triangle is larger than the absolute binomial reexpansion region.
Mathlib's connected-image theorem and the local scaling continuation theorem
extend Carlson (1975), (3.5), to this triangle. The restricted matrices inherit
these identities through the already proved zero-column reductions.
-/

open Complex Set Dirichlet
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The nonlinear F₄ arguments lie in the convergence region on the positive triangle. -/
theorem appellF4_substitution_region_of_real_nonneg {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    Real.sqrt ‖(x : ℂ) * (1 - y)‖ + Real.sqrt ‖(y : ℂ) * (1 - x)‖ < 1 := by
  have hX : Real.sqrt (x * (1 - y)) < (x + 1 - y) / 2 := by
    apply (Real.sqrt_lt' (by linarith)).mpr
    nlinarith [sq_pos_of_pos (show 0 < 1 - x - y by linarith)]
  have hY : Real.sqrt (y * (1 - x)) < (y + 1 - x) / 2 := by
    apply (Real.sqrt_lt' (by linarith)).mpr
    nlinarith [sq_pos_of_pos (show 0 < 1 - x - y by linarith)]
  have he (u v : ℝ) (hu : 0 ≤ u) (hv : v < 1) :
      ‖(u : ℂ) * (1 - v)‖ = u * (1 - v) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_mul, norm_real,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu (by linarith))]
  rw [he x y hx (by linarith), he y x hy (by linarith)]
  linarith

/-- The exact unrestricted matrix radius on the positive triangle. -/
theorem appellF4MatrixRadius_of_real_nonneg {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    appellF4MatrixRadius x y = x + y := by
  have hprod : 0 ≤ x + y - x * y := by
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - y by linarith)]
  simp only [appellF4MatrixRadius, ← ofReal_add, ← ofReal_mul, ← ofReal_sub,
    norm_real, Real.norm_eq_abs, abs_of_nonneg hprod, abs_of_nonneg (add_nonneg hx hy),
    abs_of_nonneg hx, abs_of_nonneg hy]
  rw [max_eq_left (show max x y ≤ x + y from max_le (by linarith) (by linarith)),
    max_eq_right (by nlinarith [mul_nonneg hx hy])]

/-- The unrestricted matrix has positive real entries throughout the positive triangle. -/
theorem appellF4Matrix_mem_rightHalfPlane_of_real_nonneg {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    appellF4Matrix x y ∈ matrixNodeDomain carlsonRightHalfPlane := by
  intro i j
  have h := (norm_appellF4Matrix_sub_one_le (x : ℂ) y i j).trans_lt
    (by rw [appellF4MatrixRadius_of_real_nonneg hx hy hxy]; exact hxy)
  have hr := (abs_re_le_norm (appellF4Matrix x y i j - 1)).trans_lt h
  simp only [sub_re, one_re] at hr
  change 0 < (appellF4Matrix x y i j).re
  linarith [neg_abs_le ((appellF4Matrix x y i j).re - 1)]

/-- Real scaling preserves the positive triangle, including its coordinate axes. -/
private theorem scale_positive_triangle {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y < 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ s * x ∧ 0 ≤ s * y ∧ s * x + s * y < 1 := by
  refine ⟨mul_nonneg hs.1 hx, mul_nonneg hs.1 hy, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (add_nonneg hx hy)]

/-- **Carlson (1975), (3.5), on the full positive triangle.** Every complex parameter
is allowed; the coordinate axes are included. No absolute reexpansion bound is needed. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_of_real_nonneg
    (a b c d : ℂ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    continuedRegMatrixDirichletAverage (appellF4Matrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, appellF4ColumnParameters a b c d) =
        regularizedAppellF4 a b c d ((x : ℂ) * (1 - y)) ((y : ℂ) * (1 - x)) := by
  apply continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_of_scale_domain
    a b c d x y (U := ofReal '' Icc (0 : ℝ) 1)
    (isPreconnected_Icc.image ofReal continuous_ofReal.continuousOn)
    (by exact ⟨0, by simp, by simp⟩) (by exact ⟨1, by simp, by simp⟩)
  · rintro w ⟨s, hs, rfl⟩
    obtain ⟨hX, hY, hXY⟩ := scale_positive_triangle hx hy hxy hs
    simpa only [ofReal_mul] using appellF4Matrix_mem_rightHalfPlane_of_real_nonneg hX hY hXY
  · rintro w ⟨s, hs, rfl⟩
    obtain ⟨hX, hY, hXY⟩ := scale_positive_triangle hx hy hxy hs
    simpa only [ofReal_mul] using appellF4_substitution_region_of_real_nonneg hX hY hXY

/-- The positive-triangle product matrix represents balanced F₄ at every parameter. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_product_of_real_nonneg
    {a b c d : ℂ} (h : c + d = a + b + 1) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    continuedRegMatrixDirichletAverage (appellF4ProductMatrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, appellF2Parameters b d) =
        regularizedAppellF4 a b c d ((x : ℂ) * (1 - y)) ((y : ℂ) * (1 - x)) := by
  have hp : appellF4ColumnParameters a b c d =
      ![appellF2Parameters b d 0, 0, appellF2Parameters b d 1] := by
    funext i
    fin_cases i
    · simp [appellF4ColumnParameters, appellF2Parameters]; linear_combination h
    · simp [appellF4ColumnParameters, appellF2Parameters]; linear_combination -h
    · simp [appellF4ColumnParameters, appellF2Parameters]
  rw [← continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_of_real_nonneg
    a b c d hx hy hxy, hp,
    continuedRegMatrixDirichletAverage_appellF4_zero_middle a _ _
      (by rw [appellF4MatrixRadius_of_real_nonneg hx hy hxy]; exact hxy)]

/-- The positive-triangle repeated-row matrix represents F₄ with `d=b`. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_F1_of_real_nonneg
    (a b c : ℂ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    continuedRegMatrixDirichletAverage (appellF4F1Matrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, appellF2Parameters (1 + a - c) b) =
        regularizedAppellF4 a b c b ((x : ℂ) * (1 - y)) ((y : ℂ) * (1 - x)) := by
  have hp : appellF4ColumnParameters a b c b =
      ![appellF2Parameters (1 + a - c) b 1, appellF2Parameters (1 + a - c) b 0, 0] := by
    funext i
    fin_cases i <;> simp [appellF4ColumnParameters, appellF2Parameters] <;> ring
  rw [← continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_of_real_nonneg
    a b c b hx hy hxy, hp,
    continuedRegMatrixDirichletAverage_appellF4_zero_last a _ _
      (by rw [appellF4MatrixRadius_of_real_nonneg hx hy hxy]; exact hxy)]

/-- The F₄-to-F₂ reduction on the whole positive triangle, including denominator poles. -/
theorem regularizedAppellF4_eq_F2_of_real_nonneg {a b c d : ℂ}
    (h : c + d = a + 1) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    regularizedAppellF4 a b c d ((x : ℂ) * (1 - y)) ((y : ℂ) * (1 - x)) =
      regularizedAppellF2 a b b c d x y := by
  have hp : appellF4ColumnParameters a b c d = ![0, b, d - b] := by
    funext i
    fin_cases i
    · simp [appellF4ColumnParameters]; linear_combination h
    · simp [appellF4ColumnParameters]; linear_combination -h
    · simp [appellF4ColumnParameters]
  rw [← continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_of_real_nonneg
    a b c d hx hy hxy, hp,
    continuedRegMatrixDirichletAverage_appellF4_zero_first_eq_F2 a b b c d
      (by simpa only [norm_real, Real.norm_eq_abs, abs_of_nonneg hx, abs_of_nonneg hy] using hxy)
      (by rw [appellF4MatrixRadius_of_real_nonneg hx hy hxy]; exact hxy)]

/-- The explicit F₂ matrix represents F₄ on the whole positive triangle. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_F2_of_real_nonneg
    {a b c d : ℂ} (h : c + d = a + 1) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    continuedRegMatrixDirichletAverage (appellF2Matrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, appellF2Parameters b d) =
        regularizedAppellF4 a b c d ((x : ℂ) * (1 - y)) ((y : ℂ) * (1 - x)) := by
  rw [regularizedAppellF4_eq_F2_of_real_nonneg h hx hy hxy,
    continuedRegMatrixDirichletAverage_eq_regularizedAppellF2 a b b c d
      (by simpa only [norm_real, Real.norm_eq_abs, abs_of_nonneg hx, abs_of_nonneg hy] using hxy)]

/-- The scalar F₁ reduction on the whole positive triangle at every complex parameter. -/
theorem regularizedAppellF4_eq_F1_of_real_nonneg (a b c : ℂ) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    regularizedAppellF4 a b c b ((x : ℂ) * (1 - y)) ((y : ℂ) * (1 - x)) =
      (Gamma b)⁻¹ * ((1 - (y : ℂ)) ^ (-a) *
        regularizedAppellF1 a (1 + a - c) (c + b - a - 1) c ((x : ℂ) / (1 - y)) x) := by
  have hp : pair (1 + a - c) (c + b - a - 1) = appellF2Parameters (1 + a - c) b := by
    funext i
    fin_cases i
    · simp [pair, appellF2Parameters]
    · simp [pair, appellF2Parameters]; ring
  have H := continued_appellF4F1Matrix_eq_three_node a (1 + a - c) (c + b - a - 1) c
    (x := x) (y := y) (by rw [appellF4MatrixRadius_of_real_nonneg hx hy hxy]; exact hxy)
  rw [show 1 + a - c + (c + b - a - 1) = b by ring, hp] at H
  rw [← continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_F1_of_real_nonneg
    a b c hx hy hxy, H, regCarlsonR_appellF4F1Nodes a (1 + a - c) (c + b - a - 1) c
      (by simpa only [norm_real, Real.norm_eq_abs, abs_of_nonneg hx, abs_of_nonneg hy] using hxy)]

/-- The second quadratic matrix stays in the right half-plane along real radial segments,
provided its endpoint is there and the squared F₄ arguments are in their convergence region. -/
theorem appellF4SecondMatrix_scale_mem_rightHalfPlane {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1)
    (hZ : appellF4SecondMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    appellF4SecondMatrix (s * x) (s * y) ∈ matrixNodeDomain carlsonRightHalfPlane := by
  intro i j
  let Q : ℂ := if i = 0 then y ^ 2 - x ^ 2 else y ^ 2
  have hQ : Q.re < 1 := by
    have hn : ‖x‖ ^ 2 + ‖y‖ ^ 2 < 1 := by
      nlinarith [norm_nonneg x, norm_nonneg y, mul_nonneg (norm_nonneg x) (norm_nonneg y)]
    apply (re_le_norm Q).trans_lt
    dsimp [Q]
    split_ifs
    · exact (norm_sub_le _ _).trans_lt (by simpa only [norm_pow, add_comm] using hn)
    · rw [norm_pow]; nlinarith [sq_nonneg ‖x‖]
  have he : appellF4SecondMatrix (s * x) (s * y) i j =
      (1 - (s : ℂ)) * (1 - s * Q) + s * appellF4SecondMatrix x y i j := by
    fin_cases i <;> fin_cases j <;> simp [appellF4SecondMatrix, Q] <;> ring
  have hpos : 0 < 1 - s * Q.re := by
    by_cases h : 0 ≤ Q.re
    · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) h]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.1 (le_of_not_ge h)]
  change 0 < (appellF4SecondMatrix (s * x) (s * y) i j).re
  rw [he]
  simp only [add_re, mul_re, sub_re, one_re, ofReal_re, sub_im, one_im, ofReal_im,
    zero_sub, zero_mul, sub_zero]
  have hz : 0 < (appellF4SecondMatrix x y i j).re := hZ i j
  by_cases hs1 : s = 1
  · simpa [hs1] using hz
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr (lt_of_le_of_ne hs.2 hs1)) hpos)
      (mul_nonneg hs.1 hz.le)

/-- **Carlson (1975), (4.5), on its full right-half-plane series domain.**
The entry-disk bound is replaced by the endpoint branch condition and `‖x‖+‖y‖<1`.
The continuation preserves all complex parameters and the duplication ratio. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_second_of_rightHalfPlane
    (a b c : ℂ) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1)
    (hZ : appellF4SecondMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane) :
    continuedRegMatrixDirichletAverage (appellF4SecondMatrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, pair (a - b + 1 / 2) (a - b + 1 / 2)) =
        quadraticGammaRatio (a - b + 1 / 2) *
          regularizedAppellF4 a b c (a - b + 1) (x ^ 2) (y ^ 2) := by
  have H := continued_appellF4SecondMatrix_eq_F4_on_scale_domain a b c x y
    (U := ofReal '' Icc (0 : ℝ) 1)
    (isPreconnected_Icc.image ofReal continuous_ofReal.continuousOn)
    (by exact ⟨0, by simp, by simp⟩)
    (by rintro w ⟨s, hs, rfl⟩; exact appellF4SecondMatrix_scale_mem_rightHalfPlane hxy hZ hs)
    (by
      rintro w ⟨s, hs, rfl⟩
      simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (add_nonneg (norm_nonneg x) (norm_nonneg y))])
    (show (1 : ℂ) ∈ ofReal '' Icc (0 : ℝ) 1 from ⟨1, by simp, by simp⟩)
  simpa only [one_mul] using H

/-- The Gauss function is holomorphic throughout its unit disk, including denominator poles. -/
private theorem analyticAt_gauss_disk (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (regularizedGaussHGFun a b c) z := by
  apply ((regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall
    (lt_of_lt_of_le zero_lt_one
      (radius_regularizedGaussHGFunSeries_ge_one a b c))).analyticAt_of_mem
  rw [Metric.mem_eball, edist_zero_right]
  apply lt_of_lt_of_le _ (radius_regularizedGaussHGFunSeries_ge_one a b c)
  rw [← ofReal_norm, ENNReal.ofReal_lt_one]
  exact hz

/-- The balanced product-of-Gauss reduction on the whole positive triangle. -/
theorem regularizedAppellF4_eq_gauss_mul_gauss_of_real_nonneg {a b c d : ℂ}
    (h : c + d = a + b + 1) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    regularizedAppellF4 a b c d ((x : ℂ) * (1 - y)) ((y : ℂ) * (1 - x)) =
      regularizedGaussHGFun a b c x * regularizedGaussHGFun a b d y := by
  let U : Set ℂ := ofReal '' Icc (0 : ℝ) 1
  have hL : AnalyticOnNhd ℂ (fun w => regularizedAppellF4 a b c d
      ((w * x) * (1 - w * y)) ((w * y) * (1 - w * x))) U := by
    rintro w ⟨s, hs, rfl⟩
    obtain ⟨hX, hY, hXY⟩ := scale_positive_triangle hx hy hxy hs
    apply analyticAt_regularizedAppellF4_comp a b c d (by fun_prop) (by fun_prop)
    simpa only [ofReal_mul] using appellF4_substitution_region_of_real_nonneg hX hY hXY
  have hR : AnalyticOnNhd ℂ (fun w => regularizedGaussHGFun a b c (w * x) *
      regularizedGaussHGFun a b d (w * y)) U := by
    rintro w ⟨s, hs, rfl⟩
    obtain ⟨hX, hY, hXY⟩ := scale_positive_triangle hx hy hxy hs
    have hnx : ‖(s : ℂ) * x‖ < 1 := by
      rw [← ofReal_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hX]; linarith
    have hny : ‖(s : ℂ) * y‖ < 1 := by
      rw [← ofReal_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hY]; linarith
    exact ((analyticAt_gauss_disk a b c hnx).comp (f := fun v : ℂ => v * (x : ℂ)) (by fun_prop)).mul
      ((analyticAt_gauss_disk a b d hny).comp (f := fun v : ℂ => v * (y : ℂ)) (by fun_prop))
  have hsmall : ∀ᶠ w : ℂ in 𝓝 0,
      Real.sqrt (‖w * x‖ * (1 + ‖w * y‖)) + Real.sqrt (‖w * y‖ * (1 + ‖w * x‖)) < 1 :=
    (show ContinuousAt (fun w : ℂ => Real.sqrt (‖w * x‖ * (1 + ‖w * y‖)) +
      Real.sqrt (‖w * y‖ * (1 + ‖w * x‖))) 0 by fun_prop).eventually
        (Iio_mem_nhds (by simp))
  have H := hL.eqOn_of_preconnected_of_eventuallyEq hR
    (isPreconnected_Icc.image ofReal continuous_ofReal.continuousOn)
    (show (0 : ℂ) ∈ U from ⟨0, by simp, by simp⟩)
    (hsmall.mono fun w hw => regularizedAppellF4_eq_gauss_mul_gauss h hw)
    (show (1 : ℂ) ∈ U from ⟨1, by simp, by simp⟩)
  simpa only [one_mul] using H

/-- The ordinary F₁ reduction on the positive triangle, with a nonzero cancelled Gamma factor. -/
theorem appellF4_eq_F1_of_real_nonneg (a b c : ℂ) (hb : ∀ k : ℕ, b ≠ -(k : ℂ))
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    appellF4 a b c b ((x : ℂ) * (1 - y)) ((y : ℂ) * (1 - x)) =
      (1 - (y : ℂ)) ^ (-a) * appellF1 a (1 + a - c) (c + b - a - 1) c
        ((x : ℂ) / (1 - y)) x := by
  rw [appellF4, regularizedAppellF4_eq_F1_of_real_nonneg a b c hx hy hxy, Complex.appellF1]
  have hb0 := Gamma_ne_zero hb
  field_simp

/-- Native normalization of a continued power matrix average on its branch domain. -/
private theorem native_normalization {κ : Type*} [Fintype κ] (a : ℂ)
    {r : Fin 2 → ℂ} {β : κ → ℂ} (hr : r ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    {Z : Fin 2 → κ → ℂ} (hZ : Z ∈ matrixNodeDomain carlsonRightHalfPlane) :
    matrixDirichletAverage r β Z (fun z => z ^ (-a)) =
      Gamma (∑ i, r i) * Gamma (∑ j, β j) *
        continuedRegMatrixDirichletAverage Z (fun z => z ^ (-a)) (r, β) := by
  rw [matrixDirichletAverage, continuedRegMatrixDirichletAverage_eq_native
    (f := fun z : ℂ => z ^ (-a)) isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane
    (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz)) hZ hr hβ]

/-- The unrestricted native matrix identity on the positive triangle. -/
theorem matrixDirichletAverage_eq_appellF4_of_real_nonneg (a b c d : ℂ)
    (hr : appellF2Parameters b c ∈ mvBetaConvergent)
    (hβ : appellF4ColumnParameters a b c d ∈ mvBetaConvergent)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    matrixDirichletAverage (appellF2Parameters b c) (appellF4ColumnParameters a b c d)
      (appellF4Matrix x y) (fun z => z ^ (-a)) =
        appellF4 a b c d ((x : ℂ) * (1 - y)) ((y : ℂ) * (1 - x)) := by
  rw [native_normalization a hr hβ (appellF4Matrix_mem_rightHalfPlane_of_real_nonneg hx hy hxy),
    sum_appellF2Parameters, sum_appellF4ColumnParameters,
    continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_of_real_nonneg a b c d hx hy hxy,
    appellF4]

/-- The restricted matrices inherit their branch domain by column selection. -/
private theorem restricted_positive_domains {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    appellF4ProductMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane ∧
      appellF4F1Matrix x y ∈ matrixNodeDomain carlsonRightHalfPlane := by
  have H := appellF4Matrix_mem_rightHalfPlane_of_real_nonneg hx hy hxy
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · exact H 0 0
    · exact H 0 2
    · exact H 1 0
    · exact H 1 2
  · intro i j
    fin_cases i <;> fin_cases j
    · exact H 0 1
    · exact H 0 0
    · exact H 1 1
    · exact H 1 0

/-- Native product-matrix identity on the positive triangle. -/
theorem matrixDirichletAverage_eq_appellF4_product_of_real_nonneg {a b c d : ℂ}
    (h : c + d = a + b + 1) (hr : appellF2Parameters b c ∈ mvBetaConvergent)
    (hβ : appellF2Parameters b d ∈ mvBetaConvergent)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    matrixDirichletAverage (appellF2Parameters b c) (appellF2Parameters b d)
      (appellF4ProductMatrix x y) (fun z => z ^ (-a)) =
        appellF4 a b c d ((x : ℂ) * (1 - y)) ((y : ℂ) * (1 - x)) := by
  rw [native_normalization a hr hβ (restricted_positive_domains hx hy hxy).1,
    sum_appellF2Parameters, sum_appellF2Parameters,
    continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_product_of_real_nonneg h hx hy hxy,
    appellF4]

/-- Native repeated-row matrix identity on the positive triangle. -/
theorem matrixDirichletAverage_eq_appellF4_F1_of_real_nonneg (a b c : ℂ)
    (hr : appellF2Parameters b c ∈ mvBetaConvergent)
    (hβ : appellF2Parameters (1 + a - c) b ∈ mvBetaConvergent)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    matrixDirichletAverage (appellF2Parameters b c) (appellF2Parameters (1 + a - c) b)
      (appellF4F1Matrix x y) (fun z => z ^ (-a)) =
        appellF4 a b c b ((x : ℂ) * (1 - y)) ((y : ℂ) * (1 - x)) := by
  rw [native_normalization a hr hβ (restricted_positive_domains hx hy hxy).2,
    sum_appellF2Parameters, sum_appellF2Parameters,
    continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_F1_of_real_nonneg a b c hx hy hxy,
    appellF4]

/-- Native F₂-matrix identity on the positive triangle. -/
theorem matrixDirichletAverage_eq_appellF4_F2_of_real_nonneg {a b c d : ℂ}
    (h : c + d = a + 1) (hr : appellF2Parameters b c ∈ mvBetaConvergent)
    (hβ : appellF2Parameters b d ∈ mvBetaConvergent)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 1) :
    matrixDirichletAverage (appellF2Parameters b c) (appellF2Parameters b d)
      (appellF2Matrix x y) (fun z => z ^ (-a)) =
        appellF4 a b c d ((x : ℂ) * (1 - y)) ((y : ℂ) * (1 - x)) := by
  rw [matrixDirichletAverage_eq_appellF2 a b b c d hr hβ
    (by simpa only [norm_real, Real.norm_eq_abs, abs_of_nonneg hx, abs_of_nonneg hy] using hxy),
    appellF2, ← regularizedAppellF4_eq_F2_of_real_nonneg h hx hy hxy, appellF4]

/-- Native second quadratic identity on the full right-half-plane series domain. -/
theorem matrixDirichletAverage_eq_appellF4_second_of_rightHalfPlane (a b c : ℂ)
    (hr : appellF2Parameters b c ∈ mvBetaConvergent) (hβ : 0 < (a - b + 1 / 2).re)
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1)
    (hZ : appellF4SecondMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane) :
    matrixDirichletAverage (appellF2Parameters b c)
      (pair (a - b + 1 / 2) (a - b + 1 / 2)) (appellF4SecondMatrix x y)
      (fun z => z ^ (-a)) = appellF4 a b c (a - b + 1) (x ^ 2) (y ^ 2) := by
  have hp : pair (a - b + 1 / 2) (a - b + 1 / 2) ∈ mvBetaConvergent := by
    intro i; fin_cases i <;> exact hβ
  rw [native_normalization a hr hp hZ, sum_appellF2Parameters, sum_pair,
    continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_second_of_rightHalfPlane a b c hxy hZ,
    appellF4, ← mul_assoc, mul_assoc (Gamma c), Gamma_mul_quadraticGammaRatio hβ,
    show a - b + 1 / 2 + 1 / 2 = a - b + 1 by ring]

end Carlson.TwoVariable
