/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF4MatrixBounds
public import Carlson.TwoVariable.GaussHypergeometric
public import ToMathlib.Analysis.SpecialFunctions.AppellF4Analytic
public import ToMathlib.Analysis.InfiniteSum.BinomialSubstitution

/-!
# Reassembling the unrestricted F₄ matrix series

Absolute binomial majorants justify the nonlinear argument substitution and
the regrouping of the matrix moments. Reciprocal Gamma coefficients retain
all complex parameters throughout.
-/

open Complex Polynomial Finset Set Dirichlet
open scoped Topology NNReal ENNReal
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- Absolute reassembly of the substituted F₄ series in its original variables.
The displayed square-root region is the absolute binomial reexpansion domain. -/
theorem hasSum_appellF4SubstitutionCoeff (a b c d : ℂ) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    HasSum (fun p : ℕ × ℕ => appellF4SubstitutionCoeff a b c d p.1 p.2 * x ^ p.1 * y ^ p.2)
      (regularizedAppellF4 a b c d (x * (1 - y)) (y * (1 - x))) := by
  have hX : 0 ≤ ‖x‖ * (1 + ‖y‖) := by positivity
  have hY : 0 ≤ ‖y‖ * (1 + ‖x‖) := by positivity
  have h := summable_norm_regularizedAppellF4 a b c d
    (x := (‖x‖ * (1 + ‖y‖) : ℝ)) (y := (‖y‖ * (1 + ‖x‖) : ℝ)) (by
      simpa only [norm_real, Real.norm_eq_abs, abs_of_nonneg hX, abs_of_nonneg hY] using hxy)
  have hs : Summable (fun p : ℕ × ℕ => ‖regularizedAppellF4Coeff a b c d p‖ *
      (‖x‖ * (1 + ‖y‖)) ^ p.1 * (‖y‖ * (1 + ‖x‖)) ^ p.2) := by
    simpa only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_norm,
      abs_of_nonneg (by positivity : 0 ≤ 1 + ‖x‖),
      abs_of_nonneg (by positivity : 0 ≤ 1 + ‖y‖)] using h
  exact hasSum_binomialSubstitution hs

/-- The finite coefficient identity can now be summed: the matrix series coefficients
represent the substituted regularized F₄ function on the absolute reexpansion domain. -/
theorem hasSum_appellF4MatrixSeriesCoeff (a b c d : ℂ) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    HasSum (fun p : ℕ × ℕ => appellF4MatrixSeriesCoeff a b c d p.1 p.2 * x ^ p.1 * y ^ p.2)
      (regularizedAppellF4 a b c d (x * (1 - y)) (y * (1 - x))) := by
  simpa only [← appellF4SubstitutionCoeff_eq_matrixSeriesCoeff] using
    hasSum_appellF4SubstitutionCoeff a b c d hxy

/-- The three-term absolute kernel bound controls the exact matrix entry radius. -/
theorem appellF4MatrixRadius_le_sum_norm (x y : ℂ) :
    appellF4MatrixRadius x y ≤ ‖x‖ + ‖y‖ + ‖x‖ * ‖y‖ := by
  have hab : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  have hx : ‖x‖ ≤ ‖x‖ + ‖y‖ + ‖x‖ * ‖y‖ := by linarith [norm_nonneg y]
  have hy : ‖y‖ ≤ ‖x‖ + ‖y‖ + ‖x‖ * ‖y‖ := by linarith [norm_nonneg x]
  apply max_le _ (max_le _ (max_le hx hy))
  · exact (norm_sub_le (x + y) (x * y)).trans
      (by rw [norm_mul]; linarith [norm_add_le x y])
  · exact (norm_add_le x y).trans (by linarith)

/-- The matrix expansion has finite support in the extra binomial index. -/
private theorem hasSum_matrixTerm_extra (a b c d x y : ℂ) (p : ℕ × ℕ) :
    HasSum (fun k => appellF4MatrixSeriesTerm a b c d x y (p, k))
      (∑ k ∈ range (p.1 + 1), appellF4MatrixSeriesTerm a b c d x y (p, k)) := by
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  have hpk : p.1 < k := by simpa using hk
  simp only [appellF4MatrixSeriesTerm, Nat.choose_eq_zero_of_lt hpk, Nat.cast_zero,
    mul_zero, zero_mul]

/-- Regrouping the expanded matrix by kernel degree recovers its scalar binomial moments. -/
private theorem hasSum_matrixTerm_by_kernel (a b c d x y : ℂ)
    (h : Summable (appellF4MatrixSeriesTerm a b c d x y)) :
    HasSum (fun J => (ascPochhammer ℂ J).eval a / (J.factorial : ℂ) *
      appellF4MatrixMoment x y J (appellF2Parameters b c, appellF4ColumnParameters a b c d))
      (∑' v, appellF4MatrixSeriesTerm a b c d x y v) := by
  have hp := h.hasSum.prod_fiberwise (hasSum_matrixTerm_extra a b c d x y)
  have hs := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr hp
  have H := hs.sigma (fun _ => hasSum_fintype _)
  convert H using 1
  funext J
  change _ = ∑ p : ↥(antidiagonal J), ∑ k ∈ range (p.val.1 + 1),
    appellF4MatrixSeriesTerm a b c d x y (p.val, k)
  rw [appellF4MatrixMoment_weighted_eq_sum]
  rw [Finset.sum_coe_sort (antidiagonal J) (fun p : ℕ × ℕ =>
    ∑ k ∈ range (p.1 + 1), appellF4MatrixSeriesTerm a b c d x y (p, k))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k _
  rw [appellF4MatrixSeriesTerm_eq, mem_antidiagonal.mp hp]

/-- Regrouping the same absolutely convergent matrix expansion by its output powers. -/
private theorem hasSum_matrixTerm_by_output (a b c d x y : ℂ)
    (h : Summable (appellF4MatrixSeriesTerm a b c d x y)) :
    HasSum (fun p : ℕ × ℕ => appellF4MatrixSeriesCoeff a b c d p.1 p.2 * x ^ p.1 * y ^ p.2)
      (∑' v, appellF4MatrixSeriesTerm a b c d x y v) := by
  classical
  let e (M : ℕ) : (ℕ × ℕ) ↪ (ℕ × ℕ) × ℕ :=
    ⟨fun p => ((M, p.2), p.1), fun _ _ h =>
      Prod.ext (congrArg Prod.snd h) (congrArg (fun v => v.1.2) h)⟩
  let s (p : ℕ × ℕ) := (antidiagonal p.2).map (e p.1)
  have hf : ∀ i p, i ∈ s p ↔ (i.1.1, i.2 + i.1.2) = p := by
    intro i p
    simp only [s, Finset.mem_map, mem_antidiagonal]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact Prod.ext rfl hq
    · intro h
      refine ⟨(i.2, i.1.2), congrArg Prod.snd h, ?_⟩
      exact Prod.ext (Prod.ext (congrArg Prod.fst h).symm rfl) rfl
  have H := h.hasSum.sum_finite_fibers (fun i => (i.1.1, i.2 + i.1.2)) s hf
  convert H using 1
  funext p
  simp only [s, Finset.sum_map, appellF4MatrixSeriesCoeff, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  change _ = appellF4MatrixSeriesTerm a b c d x y ((p.1, q.2), q.1)
  rw [appellF4MatrixSeriesTerm_eq, mem_antidiagonal.mp hq]

/-- On the absolute kernel region the matrix series coefficients represent the continued
regularized matrix average, without restrictions on its complex parameters. -/
theorem hasSum_appellF4MatrixSeriesCoeff_continued (a b c d : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ + ‖x‖ * ‖y‖ < 1) :
    HasSum (fun p : ℕ × ℕ => appellF4MatrixSeriesCoeff a b c d p.1 p.2 * x ^ p.1 * y ^ p.2)
      (continuedRegMatrixDirichletAverage (appellF4Matrix x y) (fun z => z ^ (-a))
        (appellF2Parameters b c, appellF4ColumnParameters a b c d)) := by
  have h := (summable_norm_appellF4MatrixSeriesTerm a b c d hxy).of_norm
  have he := (hasSum_matrixTerm_by_kernel a b c d x y h).unique
    (hasSum_appellF4Matrix_moments a (appellF2Parameters b c) (appellF4ColumnParameters a b c d)
      ((appellF4MatrixRadius_le_sum_norm x y).trans_lt hxy))
  rw [← he]
  exact hasSum_matrixTerm_by_output a b c d x y h

/-- The absolute F₄ reexpansion region lies in the three-term matrix kernel region. -/
theorem appellF4_reassembly_kernel_bound {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    ‖x‖ + ‖y‖ + ‖x‖ * ‖y‖ < 1 := by
  have hX : 0 ≤ ‖x‖ * (1 + ‖y‖) := by positivity
  have hY : 0 ≤ ‖y‖ * (1 + ‖x‖) := by positivity
  have hs : (Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖))) ^ 2 < 1 := by
    nlinarith [Real.sqrt_nonneg (‖x‖ * (1 + ‖y‖)), Real.sqrt_nonneg (‖y‖ * (1 + ‖x‖))]
  nlinarith [Real.sq_sqrt hX, Real.sq_sqrt hY,
    mul_nonneg (Real.sqrt_nonneg (‖x‖ * (1 + ‖y‖)))
      (Real.sqrt_nonneg (‖y‖ * (1 + ‖x‖))), mul_nonneg (norm_nonneg x) (norm_nonneg y)]

/-- **Carlson (1975), (3.5), regularized analytic identity near the origin.**
The unrestricted matrix represents F₄ after the Burchnall–Chaundy substitution.
All complex parameters are included. The displayed domain justifies absolute reexpansion. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4
    (a b c d : ℂ) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    continuedRegMatrixDirichletAverage (appellF4Matrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, appellF4ColumnParameters a b c d) =
        regularizedAppellF4 a b c d (x * (1 - y)) (y * (1 - x)) :=
  (hasSum_appellF4MatrixSeriesCoeff_continued a b c d (appellF4_reassembly_kernel_bound hxy)).unique
    (hasSum_appellF4MatrixSeriesCoeff a b c d hxy)

/-- Ordinary Gamma normalization of the unrestricted matrix identity.
The usual Pochhammer-denominator interpretation additionally excludes denominator poles. -/
theorem Gamma_mul_Gamma_mul_continuedRegMatrixDirichletAverage_eq_appellF4
    (a b c d : ℂ) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    (Gamma c * Gamma d) *
      continuedRegMatrixDirichletAverage (appellF4Matrix x y) (fun z => z ^ (-a))
        (appellF2Parameters b c, appellF4ColumnParameters a b c d) =
          appellF4 a b c d (x * (1 - y)) (y * (1 - x)) := by
  rw [continuedRegMatrixDirichletAverage_eq_regularizedAppellF4 a b c d hxy, appellF4]

/-- In the absolute kernel region all unrestricted matrix entries lie in the right half-plane. -/
private theorem appellF4Matrix_mem_rightHalfPlane {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ + ‖x‖ * ‖y‖ < 1) :
    appellF4Matrix x y ∈ matrixNodeDomain carlsonRightHalfPlane := by
  intro i j
  have h := (norm_appellF4Matrix_sub_one_le x y i j).trans_lt
    ((appellF4MatrixRadius_le_sum_norm x y).trans_lt hxy)
  have hre := (abs_re_le_norm (appellF4Matrix x y i j - 1)).trans_lt h
  simp only [sub_re, one_re] at hre
  change 0 < (appellF4Matrix x y i j).re
  linarith [neg_abs_le ((appellF4Matrix x y i j).re - 1)]

/-- Native regularized form of the unrestricted F₄ matrix identity, on the positive
row and column parameter region. Only native row and column positivity is required. -/
theorem regMatrixDirichletAverage_eq_regularizedAppellF4 (a b c d : ℂ)
    (hr : appellF2Parameters b c ∈ mvBetaConvergent)
    (hβ : appellF4ColumnParameters a b c d ∈ mvBetaConvergent) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    regMatrixDirichletAverage (appellF2Parameters b c) (appellF4ColumnParameters a b c d)
      (appellF4Matrix x y) (fun z => z ^ (-a)) =
        regularizedAppellF4 a b c d (x * (1 - y)) (y * (1 - x)) := by
  rw [← continuedRegMatrixDirichletAverage_eq_regularizedAppellF4 a b c d hxy]
  symm
  exact continuedRegMatrixDirichletAverage_eq_native isOpen_carlsonRightHalfPlane
    convex_carlsonRightHalfPlane (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz))
    (appellF4Matrix_mem_rightHalfPlane (appellF4_reassembly_kernel_bound hxy)) hr hβ

/-- **Carlson (1975), (3.5), native normalized form.** The unrestricted F₄ function
is the normalized double Dirichlet average on its native parameter region. -/
theorem matrixDirichletAverage_eq_appellF4 (a b c d : ℂ)
    (hr : appellF2Parameters b c ∈ mvBetaConvergent)
    (hβ : appellF4ColumnParameters a b c d ∈ mvBetaConvergent) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    matrixDirichletAverage (appellF2Parameters b c) (appellF4ColumnParameters a b c d)
      (appellF4Matrix x y) (fun z => z ^ (-a)) =
        appellF4 a b c d (x * (1 - y)) (y * (1 - x)) := by
  rw [matrixDirichletAverage, sum_appellF2Parameters, sum_appellF4ColumnParameters,
    regMatrixDirichletAverage_eq_regularizedAppellF4 a b c d hr hβ hxy, appellF4]

/-- **Carlson (1975), (4.3), analytic F₂ transformation near the origin.**
This follows by absolutely summing the coefficient reduction and includes every parameter. -/
theorem regularizedAppellF4_eq_F2 {a b c d : ℂ} (h : c + d = a + 1) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    regularizedAppellF4 a b c d (x * (1 - y)) (y * (1 - x)) =
      regularizedAppellF2 a b b c d x y := by
  have hreg := appellF4_reassembly_kernel_bound hxy
  have hdiamond : ‖x‖ + ‖y‖ < 1 := by nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
  have H := hasSum_appellF4SubstitutionCoeff a b c d hxy
  simp only [appellF4SubstitutionCoeff_eq_F2 h] at H
  exact H.unique (hasSum_regularizedAppellF2 a b b c d hdiamond)

/-- **Carlson (1975), (4.1), analytic product-of-Gauss transformation near the origin.**
The balanced parameter identity holds also at the regularized denominator poles. -/
theorem regularizedAppellF4_eq_gauss_mul_gauss {a b c d : ℂ}
    (h : c + d = a + b + 1) {x y : ℂ}
    (hxy : Real.sqrt (‖x‖ * (1 + ‖y‖)) + Real.sqrt (‖y‖ * (1 + ‖x‖)) < 1) :
    regularizedAppellF4 a b c d (x * (1 - y)) (y * (1 - x)) =
      regularizedGaussHGFun a b c x * regularizedGaussHGFun a b d y := by
  have hreg := appellF4_reassembly_kernel_bound hxy
  have hdiamond : ‖x‖ + ‖y‖ < 1 := by nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
  have hx : ‖x‖ < 1 := by linarith [norm_nonneg y]
  have hy : ‖y‖ < 1 := by linarith [norm_nonneg x]
  have H : HasSum (fun p : ℕ × ℕ =>
      (gaussCoeff a b c p.1 * x ^ p.1) * (gaussCoeff a b d p.2 * y ^ p.2))
      (regularizedAppellF4 a b c d (x * (1 - y)) (y * (1 - x))) := by
    apply (hasSum_appellF4SubstitutionCoeff a b c d hxy).congr_fun
    intro p
    rw [appellF4SubstitutionCoeff_balanced h]
    dsimp only [gaussCoeff]
    ring
  exact H.unique ((hasSum_gaussCoeff_mul_pow a b c hx).mul
    (hasSum_gaussCoeff_mul_pow a b d hy) H.summable)

/-- The unrestricted matrix depends holomorphically on a common scalar multiplier. -/
private theorem analyticAt_appellF4Matrix_scale (x y w : ℂ) :
    AnalyticAt ℂ (fun v : ℂ => appellF4Matrix (v * x) (v * y)) w := by
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_pi_iff.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp [appellF4Matrix] <;> fun_prop

/-- The continued scalar family is holomorphic wherever all matrix entries lie in the
right half-plane, preserving the branch of the original complex power kernel. -/
private theorem analyticOnNhd_appellF4Matrix_scale (a b c d x y : ℂ) {U : Set ℂ}
    (hZ : ∀ w ∈ U, appellF4Matrix (w * x) (w * y) ∈ matrixNodeDomain carlsonRightHalfPlane) :
    AnalyticOnNhd ℂ (fun w =>
      continuedRegMatrixDirichletAverage (appellF4Matrix (w * x) (w * y))
        (fun z => z ^ (-a)) (appellF2Parameters b c, appellF4ColumnParameters a b c d)) U := by
  intro w hw
  have hmap : AnalyticAt ℂ (fun v : ℂ =>
      (appellF2Parameters b c, appellF4ColumnParameters a b c d,
        appellF4Matrix (v * x) (v * y))) w :=
    analyticAt_const.prod (analyticAt_const.prod (analyticAt_appellF4Matrix_scale x y w))
  have H := analyticOnNhd_continuedRegMatrixDirichletAverage (f := fun z : ℂ => z ^ (-a))
    isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane
    (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz))
    (appellF2Parameters b c, appellF4ColumnParameters a b c d, appellF4Matrix (w * x) (w * y))
    (hZ w hw)
  simpa only [Function.comp_def] using H.comp
    (f := fun v : ℂ => (appellF2Parameters b c, appellF4ColumnParameters a b c d,
      appellF4Matrix (v * x) (v * y))) hmap

/-- **Analytic continuation of Carlson (1975), (3.5).** The identity propagates from
zero along any preconnected scalar domain on which the transformed F₄ series converges
and the matrix entries stay in the right half-plane. All parameters remain arbitrary. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_on_scale_domain
    (a b c d x y : ℂ) {U : Set ℂ} (hU : IsPreconnected U) (h0 : 0 ∈ U)
    (hZ : ∀ w ∈ U, appellF4Matrix (w * x) (w * y) ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hF : ∀ w ∈ U, Real.sqrt ‖(w * x) * (1 - w * y)‖ +
      Real.sqrt ‖(w * y) * (1 - w * x)‖ < 1) :
    EqOn (fun w =>
      continuedRegMatrixDirichletAverage (appellF4Matrix (w * x) (w * y))
        (fun z => z ^ (-a)) (appellF2Parameters b c, appellF4ColumnParameters a b c d))
      (fun w => regularizedAppellF4 a b c d ((w * x) * (1 - w * y))
        ((w * y) * (1 - w * x))) U := by
  have hGa : AnalyticOnNhd ℂ (fun w =>
      regularizedAppellF4 a b c d ((w * x) * (1 - w * y)) ((w * y) * (1 - w * x))) U := by
    intro w hw
    exact analyticAt_regularizedAppellF4_comp a b c d (by fun_prop) (by fun_prop) (hF w hw)
  have hsmall : ∀ᶠ w : ℂ in 𝓝 0,
      Real.sqrt (‖w * x‖ * (1 + ‖w * y‖)) + Real.sqrt (‖w * y‖ * (1 + ‖w * x‖)) < 1 :=
    (show ContinuousAt (fun w : ℂ => Real.sqrt (‖w * x‖ * (1 + ‖w * y‖)) +
      Real.sqrt (‖w * y‖ * (1 + ‖w * x‖))) 0 by fun_prop).eventually
        (Iio_mem_nhds (by simp))
  apply (analyticOnNhd_appellF4Matrix_scale a b c d x y hZ).eqOn_of_preconnected_of_eventuallyEq
    hGa hU h0
  filter_upwards [hsmall] with w hw
  exact continuedRegMatrixDirichletAverage_eq_regularizedAppellF4 a b c d hw

/-- Endpoint form of the continuation theorem: any admissible preconnected scalar
set containing zero and one suffices, without the absolute reexpansion bound at one. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_of_scale_domain
    (a b c d x y : ℂ) {U : Set ℂ} (hU : IsPreconnected U) (h0 : 0 ∈ U) (h1 : 1 ∈ U)
    (hZ : ∀ w ∈ U, appellF4Matrix (w * x) (w * y) ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hF : ∀ w ∈ U, Real.sqrt ‖(w * x) * (1 - w * y)‖ +
      Real.sqrt ‖(w * y) * (1 - w * x)‖ < 1) :
    continuedRegMatrixDirichletAverage (appellF4Matrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, appellF4ColumnParameters a b c d) =
        regularizedAppellF4 a b c d (x * (1 - y)) (y * (1 - x)) := by
  simpa only [one_mul] using
    continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_on_scale_domain
      a b c d x y hU h0 hZ hF h1

end Carlson.TwoVariable
