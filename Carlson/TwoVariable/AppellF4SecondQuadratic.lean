/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellSlicedSeries
public import Carlson.TwoVariable.QuadraticContinuation
public import Carlson.MatrixHomogeneity
public import Carlson.R.Homogeneity

/-!
# The second quadratic F₄ matrix

Carlson (1975), equation (4.5). Gauss slices of F₂ and F₄ are related by
the local second quadratic R-transformation. Matrix homogeneity then identifies
the explicit two-by-two matrix. Mathlib's analytic identity theorem extends the
result from the common series region along preconnected scaling domains.
Duplication ratios stay explicit at their zeros.
-/

open Complex Polynomial Finset Set Dirichlet
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The second quadratic matrix in Carlson (1975), equation (4.5). -/
def appellF4SecondMatrix (x y : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![(1 + y) ^ 2 - x ^ 2, (1 - y) ^ 2 - x ^ 2], ![(1 + y) ^ 2, (1 - y) ^ 2]]

/-- The scalar second quadratic transformation in the normalization needed by F₂ slices. -/
theorem regularizedGaussHGFun_secondQuadratic (α β : ℂ) {y : ℂ}
    (hy : ‖y‖ < 1) (hq : SecondQuadraticDomain (1 + y) (1 - y))
    (hT : ‖4 * y / (1 + y) ^ 2‖ < 1) :
    ((1 + y) ^ 2) ^ (-α) * regularizedGaussHGFun α β (β + β) (4 * y / (1 + y) ^ 2) =
      quadraticGammaRatio β * regularizedGaussHGFun α (α + 1 / 2 - β) (β + 1 / 2) (y ^ 2) := by
  let T := 4 * y / (1 + y) ^ 2
  have hμ : 0 < ((1 + y) ^ 2).re := by simpa [pair, carlsonRightHalfPlane] using hq.1 0
  have hμ0 : (1 + y) ^ 2 ≠ 0 := fun h => by rw [h] at hμ; simp at hμ
  have hz : pair (1 : ℂ) (1 - T) ∈ carlsonRVariableDomain := by
    intro i
    fin_cases i
    · norm_num [pair, carlsonRightHalfPlane]
    · change 0 < (1 - T).re
      simp only [sub_re, one_re]
      linarith [(re_le_norm T).trans_lt hT]
  have hG : regularizedGaussHGFun α β (β + β) T =
      regCarlsonR (-α) (pair β β) (pair 1 (1 - T)) := by
    simpa only [show β + β - β = β by ring] using
      (regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun α β (β + β) hT).symm
  have he : (fun i => (1 + y) ^ 2 * pair 1 (1 - T) i) =
      pair ((1 + y) ^ 2) ((1 - y) ^ 2) := by
    funext i
    fin_cases i
    · change (1 + y) ^ 2 * 1 = (1 + y) ^ 2
      ring
    · change (1 + y) ^ 2 * (1 - 4 * y / (1 + y) ^ 2) = (1 - y) ^ 2
      rw [mul_sub, mul_one, mul_div_cancel₀ (4 * y) hμ0]
      ring
  rw [hG, ← regCarlsonR_mul_of_re_pos (-α) (pair β β) hz hμ, he,
    regCarlsonR_pair_secondQuadratic (-α) β (1 + y) (1 - y) hq,
    show arithmeticMeanSq (1 + y) (1 - y) = 1 by unfold arithmeticMeanSq; ring,
    show geometricMeanSq (1 + y) (1 - y) = 1 - y ^ 2 by unfold geometricMeanSq; ring]
  have hp : pair (2 * β + -α) (1 / 2 - β - -α) =
      pair (β + 1 / 2 - (α + 1 / 2 - β)) (α + 1 / 2 - β) := by
    funext i; fin_cases i <;> simp [pair] <;> ring
  rw [hp, regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun]
  rw [norm_pow]
  nlinarith [norm_nonneg y]

/-- The second quadratic F₂/F₄ transformation, in division-free regularized form,
on the common series region and the original quadratic branch domain. -/
theorem regularizedAppellF2_eq_F4_secondQuadratic (a b c : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1) (hq : SecondQuadraticDomain (1 + y) (1 - y))
    (hF2 : ‖x ^ 2 / (1 + y) ^ 2‖ + ‖4 * y / (1 + y) ^ 2‖ < 1) :
    ((1 + y) ^ 2) ^ (-a) * regularizedAppellF2 a b (a - b + 1 / 2) c
        ((a - b + 1 / 2) + (a - b + 1 / 2))
        (x ^ 2 / (1 + y) ^ 2) (4 * y / (1 + y) ^ 2) =
      quadraticGammaRatio (a - b + 1 / 2) *
        regularizedAppellF4 a b c (a - b + 1) (x ^ 2) (y ^ 2) := by
  let β := a - b + 1 / 2
  let μ := (1 + y) ^ 2
  have hμ : 0 < μ.re := by simpa [μ, pair, carlsonRightHalfPlane] using hq.1 0
  have hμ0 : μ ≠ 0 := fun h => by rw [h] at hμ; simp at hμ
  have hy : ‖y‖ < 1 := by linarith [norm_nonneg x]
  have hT : ‖4 * y / μ‖ < 1 := by dsimp [μ]; linarith [norm_nonneg (x ^ 2 / (1 + y) ^ 2)]
  have hroot : Real.sqrt ‖x ^ 2‖ + Real.sqrt ‖y ^ 2‖ < 1 := by
    simpa only [norm_pow, Real.sqrt_sq (norm_nonneg _)] using hxy
  have H := (hasSum_regularizedAppellF2_gauss a b β c (β + β) hF2).mul_left (μ ^ (-a))
  have R := (hasSum_regularizedAppellF4_gauss a b c (a - b + 1) hroot).mul_left
    (quadraticGammaRatio β)
  apply H.unique
  convert R using 1
  funext m
  have hQ := regularizedGaussHGFun_secondQuadratic (a + m) β hy hq hT
  rw [show a + m + 1 / 2 - β = b + m by dsimp [β]; ring,
    show β + 1 / 2 = a - b + 1 by dsimp [β]; ring] at hQ
  have hp : μ ^ (-(a + m)) = μ ^ (-a) / μ ^ m := by
    rw [neg_add, cpow_add _ _ hμ0]
    simp only [cpow_neg, cpow_natCast, div_eq_mul_inv]
  rw [hp] at hQ
  simp only [div_eq_mul_inv] at hQ ⊢
  linear_combination
    ((ascPochhammer ℂ m).eval a * (ascPochhammer ℂ m).eval b /
      ((m.factorial : ℂ) * Gamma (c + m)) * (x ^ 2) ^ m) * hQ

/-- The second quadratic matrix is a scalar multiple of the column-reversed F₂ matrix. -/
private theorem secondMatrix_eq_scaled_F2 (x y : ℂ) (hμ : (1 + y) ^ 2 ≠ 0) :
    appellF4SecondMatrix x y = fun i j => (1 + y) ^ 2 *
      appellF2Matrix (x ^ 2 / (1 + y) ^ 2) (4 * y / (1 + y) ^ 2) i
        ((Equiv.swap (0 : Fin 2) 1) j) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [appellF4SecondMatrix, appellF2Matrix]
  all_goals simp only [mul_sub, mul_one, mul_div_cancel₀ _ hμ]
  all_goals ring

/-- The F₂ parallelogram stays in the right half-plane on its full convergence diamond. -/
private theorem F2Matrix_mem_rightHalfPlane {X Y : ℂ} (hXY : ‖X‖ + ‖Y‖ < 1) :
    appellF2Matrix X Y ∈ matrixNodeDomain carlsonRightHalfPlane := by
  intro i j
  have h := (abs_re_le_norm (appellF2Matrix X Y i j - 1)).trans
    (norm_appellF2Matrix_sub_one_le X Y i j)
  have h' := h.trans_lt hXY
  simp only [sub_re, one_re] at h'
  change 0 < (appellF2Matrix X Y i j).re
  linarith [neg_abs_le ((appellF2Matrix X Y i j).re - 1)]

/-- The second quadratic matrix equals the scaled F₂ average wherever that series converges.
Both original and normalized matrix branches are accounted for explicitly. -/
theorem continued_appellF4SecondMatrix_eq_F2 (a b c β : ℂ) {x y : ℂ}
    (hZ : appellF4SecondMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hF2 : ‖x ^ 2 / (1 + y) ^ 2‖ + ‖4 * y / (1 + y) ^ 2‖ < 1) :
    continuedRegMatrixDirichletAverage (appellF4SecondMatrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, pair β β) =
        ((1 + y) ^ 2) ^ (-a) * regularizedAppellF2 a b β c (β + β)
          (x ^ 2 / (1 + y) ^ 2) (4 * y / (1 + y) ^ 2) := by
  let σ := Equiv.swap (0 : Fin 2) 1
  let Z := appellF2Matrix (x ^ 2 / (1 + y) ^ 2) (4 * y / (1 + y) ^ 2)
  have hμ : 0 < ((1 + y) ^ 2).re := hZ 1 0
  have hμ0 : (1 + y) ^ 2 ≠ 0 := fun h => by rw [h] at hμ; simp at hμ
  have hbZ : Z ∈ matrixNodeDomain carlsonRightHalfPlane := F2Matrix_mem_rightHalfPlane hF2
  have hperm := continuedRegMatrixDirichletAverage_perm_columns isOpen_carlsonRightHalfPlane
    convex_carlsonRightHalfPlane (f := fun z : ℂ => z ^ (-a))
    (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz)) hbZ σ
    (appellF2Parameters b c) (pair β β)
  have hconst : pair β β = fun _ => β := by funext i; fin_cases i <;> rfl
  have heq : continuedRegMatrixDirichletAverage (fun i j => Z i (σ j)) (fun z => z ^ (-a))
      (appellF2Parameters b c, pair β β) =
        continuedRegMatrixDirichletAverage Z (fun z => z ^ (-a))
          (appellF2Parameters b c, pair β β) := by
    simpa only [hconst, Function.comp_def] using hperm
  have hp : pair β β = appellF2Parameters β (β + β) := by
    funext i; fin_cases i <;> simp [pair, appellF2Parameters]
  rw [secondMatrix_eq_scaled_F2 x y hμ0,
    continuedRegMatrixDirichletAverage_mul_cpow_neg (appellF2Parameters b c) (pair β β)
      (fun i j => hbZ i (σ j)) hμ (by
        rw [← secondMatrix_eq_scaled_F2 x y hμ0]
        exact hZ) a, heq, hp]
  rw [continuedRegMatrixDirichletAverage_eq_regularizedAppellF2 a b β c (β + β) hF2]

/-- The quadratic branch condition follows from the matrix's bottom row and `‖y‖<1`. -/
private theorem secondQuadraticDomain_of_matrix {x y : ℂ} (hy : ‖y‖ < 1)
    (hZ : appellF4SecondMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane) :
    SecondQuadraticDomain (1 + y) (1 - y) := by
  constructor
  · intro i
    fin_cases i
    · exact hZ 1 0
    · exact hZ 1 1
  · rw [show arithmeticMeanSq (1 + y) (1 - y) = 1 by unfold arithmeticMeanSq; ring,
      show geometricMeanSq (1 + y) (1 - y) = 1 - y ^ 2 by unfold geometricMeanSq; ring]
    intro i
    fin_cases i
    · norm_num [pair, carlsonRightHalfPlane]
    · change 0 < (1 - y ^ 2).re
      simp only [sub_re, one_re]
      have hn : ‖y ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg y]
      linarith [re_le_norm (y ^ 2)]

/-- The second quadratic matrix identity on the common F₂/F₄ series region. -/
theorem continued_appellF4SecondMatrix_eq_F4_of_F2_region (a b c : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1)
    (hZ : appellF4SecondMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hF2 : ‖x ^ 2 / (1 + y) ^ 2‖ + ‖4 * y / (1 + y) ^ 2‖ < 1) :
    continuedRegMatrixDirichletAverage (appellF4SecondMatrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, pair (a - b + 1 / 2) (a - b + 1 / 2)) =
        quadraticGammaRatio (a - b + 1 / 2) *
          regularizedAppellF4 a b c (a - b + 1) (x ^ 2) (y ^ 2) := by
  rw [continued_appellF4SecondMatrix_eq_F2 a b c (a - b + 1 / 2) hZ hF2]
  exact regularizedAppellF2_eq_F4_secondQuadratic a b c hxy
    (secondQuadraticDomain_of_matrix (by linarith [norm_nonneg x]) hZ) hF2

/-- Every node of the second quadratic matrix has this uniform distance from one. -/
theorem norm_appellF4SecondMatrix_sub_one_le (x y : ℂ) (i j : Fin 2) :
    ‖appellF4SecondMatrix x y i j - 1‖ ≤ ‖x‖ ^ 2 + 2 * ‖y‖ + ‖y‖ ^ 2 := by
  have h (z : ℂ) (hz : ‖z‖ = ‖y‖) :
      ‖(1 + z) ^ 2 - x ^ 2 - 1‖ ≤ ‖x‖ ^ 2 + 2 * ‖y‖ + ‖y‖ ^ 2 ∧
      ‖(1 + z) ^ 2 - 1‖ ≤ ‖x‖ ^ 2 + 2 * ‖y‖ + ‖y‖ ^ 2 := by
    have hb := norm_add_le (2 * z) (z ^ 2)
    have ht := (norm_sub_le (2 * z + z ^ 2) (x ^ 2)).trans
      (add_le_add hb le_rfl)
    simp only [norm_mul, norm_ofNat, norm_pow, hz] at hb ht
    rw [show (1 + z) ^ 2 - x ^ 2 - 1 = 2 * z + z ^ 2 - x ^ 2 by ring,
      show (1 + z) ^ 2 - 1 = 2 * z + z ^ 2 by ring]
    constructor <;> nlinarith [sq_nonneg ‖x‖]
  have hp := h y rfl
  have hn := h (-y) (norm_neg y)
  fin_cases i <;> fin_cases j
  · exact hp.1
  · simpa [appellF4SecondMatrix, sub_eq_add_neg] using hn.1
  · exact hp.2
  · simpa [appellF4SecondMatrix, sub_eq_add_neg] using hn.2

/-- The entry-disk bound implies both the branch domain and the F₄ convergence diamond. -/
private theorem secondMatrix_domains {x y : ℂ}
    (h : ‖x‖ ^ 2 + 2 * ‖y‖ + ‖y‖ ^ 2 < 1) :
    appellF4SecondMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane ∧
      ‖x‖ + ‖y‖ < 1 := by
  constructor
  · intro i j
    have hr := (abs_re_le_norm (appellF4SecondMatrix x y i j - 1)).trans_lt
      ((norm_appellF4SecondMatrix_sub_one_le x y i j).trans_lt h)
    simp only [sub_re, one_re] at hr
    change 0 < (appellF4SecondMatrix x y i j).re
    linarith [neg_abs_le ((appellF4SecondMatrix x y i j).re - 1)]
  · have hx : ‖x‖ < 1 := by nlinarith [norm_nonneg x, norm_nonneg y, sq_nonneg ‖y‖]
    nlinarith [norm_nonneg x, norm_nonneg y, mul_nonneg (norm_nonneg y) (le_of_lt (sub_pos.mpr hx))]

/-- Holomorphy of the second quadratic matrix average along a scalar family. -/
private theorem analyticOnNhd_secondMatrix_scale (a b c x y : ℂ) {U : Set ℂ}
    (hZ : ∀ w ∈ U, appellF4SecondMatrix (w * x) (w * y) ∈
      matrixNodeDomain carlsonRightHalfPlane) :
    AnalyticOnNhd ℂ (fun w =>
      continuedRegMatrixDirichletAverage (appellF4SecondMatrix (w * x) (w * y))
        (fun z => z ^ (-a))
        (appellF2Parameters b c, pair (a - b + 1 / 2) (a - b + 1 / 2))) U := by
  intro w hw
  let β := a - b + 1 / 2
  have hm : AnalyticAt ℂ (fun v : ℂ => appellF4SecondMatrix (v * x) (v * y)) w := by
    apply analyticAt_pi_iff.mpr
    intro i
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp [appellF4SecondMatrix] <;> fun_prop
  have H := analyticOnNhd_continuedRegMatrixDirichletAverage (f := fun z : ℂ => z ^ (-a))
    isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane
    (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz))
    (appellF2Parameters b c, pair β β, appellF4SecondMatrix (w * x) (w * y)) (hZ w hw)
  simpa only [Function.comp_def] using H.comp
    (f := fun v : ℂ => (appellF2Parameters b c, pair β β,
      appellF4SecondMatrix (v * x) (v * y)))
    (analyticAt_const.prod (analyticAt_const.prod hm))

/-- **Carlson (1975), (4.5), continued matrix form.** The second quadratic identity
propagates along any preconnected scalar domain containing zero on which the matrix
stays in the right half-plane and the F₄ series converges. All parameters are arbitrary. -/
theorem continued_appellF4SecondMatrix_eq_F4_on_scale_domain
    (a b c x y : ℂ) {U : Set ℂ} (hU : IsPreconnected U) (h0 : 0 ∈ U)
    (hZ : ∀ w ∈ U, appellF4SecondMatrix (w * x) (w * y) ∈
      matrixNodeDomain carlsonRightHalfPlane)
    (hF : ∀ w ∈ U, ‖w * x‖ + ‖w * y‖ < 1) :
    EqOn (fun w =>
      continuedRegMatrixDirichletAverage (appellF4SecondMatrix (w * x) (w * y))
        (fun z => z ^ (-a))
        (appellF2Parameters b c, pair (a - b + 1 / 2) (a - b + 1 / 2)))
      (fun w => quadraticGammaRatio (a - b + 1 / 2) *
        regularizedAppellF4 a b c (a - b + 1) ((w * x) ^ 2) ((w * y) ^ 2)) U := by
  have hGa : AnalyticOnNhd ℂ (fun w => quadraticGammaRatio (a - b + 1 / 2) *
      regularizedAppellF4 a b c (a - b + 1) ((w * x) ^ 2) ((w * y) ^ 2)) U := by
    intro w hw
    apply analyticAt_const.mul
    apply analyticAt_regularizedAppellF4_comp a b c (a - b + 1) (by fun_prop) (by fun_prop)
    simpa only [norm_pow, Real.sqrt_sq (norm_nonneg _)] using hF w hw
  have hsmall : ∀ᶠ w : ℂ in 𝓝 0,
      ‖w * x‖ ^ 2 + 2 * ‖w * y‖ + ‖w * y‖ ^ 2 < 1 :=
    (show ContinuousAt (fun w : ℂ =>
      ‖w * x‖ ^ 2 + 2 * ‖w * y‖ + ‖w * y‖ ^ 2) 0 by fun_prop).eventually
        (Iio_mem_nhds (by simp))
  have hF2 : ∀ᶠ w : ℂ in 𝓝 0,
      ‖(w * x) ^ 2 / (1 + w * y) ^ 2‖ + ‖4 * (w * y) / (1 + w * y) ^ 2‖ < 1 :=
    (show ContinuousAt (fun w : ℂ =>
      ‖(w * x) ^ 2 / (1 + w * y) ^ 2‖ + ‖4 * (w * y) / (1 + w * y) ^ 2‖) 0 by
        fun_prop (disch := norm_num)).eventually (Iio_mem_nhds (by simp))
  apply (analyticOnNhd_secondMatrix_scale a b c x y hZ).eqOn_of_preconnected_of_eventuallyEq
    hGa hU h0
  filter_upwards [hsmall, hF2] with w hw h2
  exact continued_appellF4SecondMatrix_eq_F4_of_F2_region a b c
    (secondMatrix_domains hw).2 (secondMatrix_domains hw).1 h2

/-- Concrete entry-disk form of the second quadratic matrix identity. The duplication
ratio remains explicit, so no exceptional parameter is discarded. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_second
    (a b c : ℂ) {x y : ℂ} (h : ‖x‖ ^ 2 + 2 * ‖y‖ + ‖y‖ ^ 2 < 1) :
    continuedRegMatrixDirichletAverage (appellF4SecondMatrix x y) (fun z => z ^ (-a))
      (appellF2Parameters b c, pair (a - b + 1 / 2) (a - b + 1 / 2)) =
        quadraticGammaRatio (a - b + 1 / 2) *
          regularizedAppellF4 a b c (a - b + 1) (x ^ 2) (y ^ 2) := by
  have hs (w : ℂ) (hw : w ∈ Metric.closedBall (0 : ℂ) 1) :
      ‖w * x‖ ^ 2 + 2 * ‖w * y‖ + ‖w * y‖ ^ 2 < 1 := by
    have hn : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    have hx : ‖w * x‖ ≤ ‖x‖ := by rw [norm_mul]; nlinarith [norm_nonneg x]
    have hy : ‖w * y‖ ≤ ‖y‖ := by rw [norm_mul]; nlinarith [norm_nonneg y]
    apply lt_of_le_of_lt _ h
    gcongr
  have H := continued_appellF4SecondMatrix_eq_F4_on_scale_domain a b c x y
    (convex_closedBall (0 : ℂ) (1 : ℝ)).isPreconnected (by simp)
    (fun w hw => (secondMatrix_domains (hs w hw)).1)
    (fun w hw => (secondMatrix_domains (hs w hw)).2) (show (1 : ℂ) ∈
      Metric.closedBall (0 : ℂ) 1 by simp)
  simpa only [one_mul] using H

/-- Native normalized form of Carlson (1975), (4.5). Duplication cancels the Gamma
ratio on the native positive-parameter domain. -/
theorem matrixDirichletAverage_eq_appellF4_second (a b c : ℂ)
    (hr : appellF2Parameters b c ∈ mvBetaConvergent) (hβ : 0 < (a - b + 1 / 2).re)
    {x y : ℂ} (h : ‖x‖ ^ 2 + 2 * ‖y‖ + ‖y‖ ^ 2 < 1) :
    matrixDirichletAverage (appellF2Parameters b c)
      (pair (a - b + 1 / 2) (a - b + 1 / 2)) (appellF4SecondMatrix x y)
      (fun z => z ^ (-a)) = appellF4 a b c (a - b + 1) (x ^ 2) (y ^ 2) := by
  have hp : pair (a - b + 1 / 2) (a - b + 1 / 2) ∈ mvBetaConvergent := by
    intro i; fin_cases i <;> exact hβ
  have H := continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_second a b c h
  rw [continuedRegMatrixDirichletAverage_eq_native (f := fun z : ℂ => z ^ (-a))
    isOpen_carlsonRightHalfPlane
    convex_carlsonRightHalfPlane
    (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz))
    (secondMatrix_domains h).1 hr hp] at H
  rw [matrixDirichletAverage, sum_appellF2Parameters, sum_pair, H, appellF4]
  rw [← mul_assoc, mul_assoc (Gamma c), Gamma_mul_quadraticGammaRatio hβ,
    show a - b + 1 / 2 + 1 / 2 = a - b + 1 by ring]

end Carlson.TwoVariable
