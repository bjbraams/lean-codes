/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF4Domains
public import Carlson.TwoVariable.AppellF4Bailey
public import Carlson.TwoVariable.AppellF4Matrix

/-!
# Quadratic transformations of matrix averages

Carlson (1976), equations (2.3) and (2.4), obtained by eliminating F₄ between
its proved matrix reductions, as in the paper's proof on page 296.
Mathlib's analytic identity theorem extends both transformations beyond
their initial series regions. All matrix branches remain explicit. The first
quadratic transformation here is (2.4), and the second is (2.3); these labels
refer to the underlying single-average transformations (1.10) and (1.11).
-/

open Complex Set Dirichlet
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The arithmetic/geometric-mean matrix of the centered parallelogram. -/
def appellQuadraticCenteredMatrix (x y : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![1, 1], ![1 - (x + y) ^ 2, 1 - (x - y) ^ 2]]

/-- The transformed matrix in Carlson (1976), (2.4), before fixing its common center. -/
def appellQuadraticMeanMatrix (x y z w : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![arithmeticMeanSq x w, arithmeticMeanSq y z], ![x * w, y * z]]

/-- The centered form gives exactly the arithmetic/geometric means in (2.4). -/
theorem appellQuadraticMeanMatrix_centered (x y : ℂ) :
    appellQuadraticMeanMatrix (1 - x - y) (1 - x + y) (1 + x - y) (1 + x + y) =
      appellQuadraticCenteredMatrix x y := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [appellQuadraticMeanMatrix, appellQuadraticCenteredMatrix, arithmeticMeanSq] <;> ring

/-- Reversing two rows reverses their parameters in the continued power average. -/
private theorem continued_matrix_reverseRows (t α β γ δ : ℂ)
    {Z : Fin 2 → Fin 2 → ℂ} (hZ : Z ∈ matrixNodeDomain carlsonRightHalfPlane) :
    continuedRegMatrixDirichletAverage (fun i j => Z ((Equiv.swap 0 1) i) j)
        (fun z => z ^ t) (pair β α, pair γ δ) =
      continuedRegMatrixDirichletAverage Z (fun z => z ^ t) (pair α β, pair γ δ) := by
  have hp : pair α β ∘ Equiv.swap (0 : Fin 2) 1 = pair β α := by
    funext i; fin_cases i <;> simp [pair]
  simpa only [hp] using continuedRegMatrixDirichletAverage_perm_rows
    isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane
    (f := fun z : ℂ => z ^ t) (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz))
    hZ (Equiv.swap 0 1) (pair α β) (pair γ δ)

/-- Reversing the equal-denominator matrix puts its constant row first. -/
private theorem reverse_equalMatrix (x y : ℂ) :
    (fun i j => appellF4EqualMatrix x y ((Equiv.swap 0 1) i) j) =
      appellQuadraticCenteredMatrix x y := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [appellF4EqualMatrix, appellQuadraticCenteredMatrix]

/-- Equal-denominator F₄ in the row order used by the 1976 transformations. -/
private theorem centeredMatrix_eq_F4 (a b c : ℂ) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    continuedRegMatrixDirichletAverage (appellQuadraticCenteredMatrix x y)
      (fun z => z ^ (-a)) (pair (c - b) b, pair (c - 1 / 2) (c - 1 / 2)) =
        quadraticGammaRatio (c - 1 / 2) * regularizedAppellF4 a b c c (x ^ 2) (y ^ 2) := by
  rw [← reverse_equalMatrix x y, continued_matrix_reverseRows (-a) b (c - b)
    (c - 1 / 2) (c - 1 / 2) (appellF4EqualMatrix_mem_rightHalfPlane hxy)]
  exact continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_equal a b c hxy

/-- Carlson (1976), (2.4), in centered coordinates on the initial series domain.
The duplication ratio is retained at all exceptional parameters. -/
theorem continuedMatrix_firstQuadratic_centered_of_norm (t μ : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1) :
    continuedRegMatrixDirichletAverage (appellF4BaileyMatrix x y) (fun z => z ^ (2 * t))
      (pair μ μ, pair μ μ) = quadraticGammaRatio μ *
        continuedRegMatrixDirichletAverage (appellQuadraticCenteredMatrix x y)
          (fun z => z ^ t) (pair (μ + t) (1 / 2 - t), pair μ μ) := by
  have hB := continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_bailey
    (-t) (μ + 1 / 2) (μ + 1 / 2) hxy
  have hE := centeredMatrix_eq_F4 (-t) (1 / 2 - t) (μ + 1 / 2) hxy
  rw [show μ + 1 / 2 - 1 / 2 = μ by ring, neg_neg,
    show μ + 1 / 2 - (1 / 2 - t) = μ + t by ring] at hE
  rw [show μ + 1 / 2 - 1 / 2 = μ by ring, show -(2 * -t) = 2 * t by ring,
    show -t + 1 / 2 = 1 / 2 - t by ring] at hB
  rw [hB, hE, mul_assoc]

/-- A polynomial matrix family gives a holomorphic continued power average on its branch domain. -/
private theorem analyticAt_matrix_power_comp (t : ℂ) (r β : Fin 2 → ℂ)
    {Z : ℂ → Fin 2 → Fin 2 → ℂ} {w : ℂ} (ha : AnalyticAt ℂ Z w)
    (hZ : Z w ∈ matrixNodeDomain carlsonRightHalfPlane) :
    AnalyticAt ℂ (fun v => continuedRegMatrixDirichletAverage (Z v)
      (fun z => z ^ t) (r, β)) w := by
  have H := analyticOnNhd_continuedRegMatrixDirichletAverage (f := fun z : ℂ => z ^ t)
    isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane
    (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz)) (r, β, Z w) hZ
  simpa only [Function.comp_def] using H.comp
    (f := fun v => (r, β, Z v)) (analyticAt_const.prod (analyticAt_const.prod ha))

/-- The first centered matrix transformation continues along every verified scaling domain. -/
theorem continuedMatrix_firstQuadratic_centered_on_scale_domain (t μ x y : ℂ)
    {U : Set ℂ} (hU : IsPreconnected U) (h0 : 0 ∈ U)
    (hZ : ∀ w ∈ U, appellF4BaileyMatrix (w * x) (w * y) ∈
      matrixNodeDomain carlsonRightHalfPlane)
    (hW : ∀ w ∈ U, appellQuadraticCenteredMatrix (w * x) (w * y) ∈
      matrixNodeDomain carlsonRightHalfPlane) :
    EqOn (fun w => continuedRegMatrixDirichletAverage
        (appellF4BaileyMatrix (w * x) (w * y)) (fun z => z ^ (2 * t)) (pair μ μ, pair μ μ))
      (fun w => quadraticGammaRatio μ * continuedRegMatrixDirichletAverage
        (appellQuadraticCenteredMatrix (w * x) (w * y)) (fun z => z ^ t)
        (pair (μ + t) (1 / 2 - t), pair μ μ)) U := by
  have hL : AnalyticOnNhd ℂ (fun w => continuedRegMatrixDirichletAverage
      (appellF4BaileyMatrix (w * x) (w * y)) (fun z => z ^ (2 * t)) (pair μ μ, pair μ μ)) U := by
    intro w hw
    apply analyticAt_matrix_power_comp _ _ _
      (Z := fun v => appellF4BaileyMatrix (v * x) (v * y)) _ (hZ w hw)
    apply analyticAt_pi_iff.mpr
    intro i
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp [appellF4BaileyMatrix] <;> fun_prop
  have hR : AnalyticOnNhd ℂ (fun w => quadraticGammaRatio μ *
      continuedRegMatrixDirichletAverage (appellQuadraticCenteredMatrix (w * x) (w * y))
        (fun z => z ^ t) (pair (μ + t) (1 / 2 - t), pair μ μ)) U := by
    intro w hw
    apply analyticAt_const.mul
    apply analyticAt_matrix_power_comp _ _ _
      (Z := fun v => appellQuadraticCenteredMatrix (v * x) (v * y)) _ (hW w hw)
    apply analyticAt_pi_iff.mpr
    intro i
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp [appellQuadraticCenteredMatrix] <;> fun_prop
  apply hL.eqOn_of_preconnected_of_eventuallyEq hR hU h0
  have hs : ∀ᶠ w : ℂ in 𝓝 0, ‖w * x‖ + ‖w * y‖ < 1 :=
    (show ContinuousAt (fun w : ℂ => ‖w * x‖ + ‖w * y‖) 0 by fun_prop).eventually
      (Iio_mem_nhds (by simp))
  filter_upwards [hs] with w hw
  exact continuedMatrix_firstQuadratic_centered_of_norm t μ hw

/-- Both matrices in the first centered transformation preserve their branch domain under
real radial contraction; no Appell-series convergence hypothesis is required. -/
private theorem firstQuadratic_scale_domains {x y : ℂ}
    (hZ : appellF4BaileyMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hW : appellQuadraticCenteredMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    appellF4BaileyMatrix (s * x) (s * y) ∈ matrixNodeDomain carlsonRightHalfPlane ∧
      appellQuadraticCenteredMatrix (s * x) (s * y) ∈
        matrixNodeDomain carlsonRightHalfPlane := by
  have hz (i j : Fin 2) : appellF4BaileyMatrix (s * x) (s * y) i j =
      (1 - (s : ℂ)) * 1 + s * appellF4BaileyMatrix x y i j := by
    fin_cases i <;> fin_cases j <;> simp [appellF4BaileyMatrix] <;> ring
  have hw (i j : Fin 2) : appellQuadraticCenteredMatrix (s * x) (s * y) i j =
      (1 - (s : ℂ) ^ 2) * 1 + (s : ℂ) ^ 2 * appellQuadraticCenteredMatrix x y i j := by
    fin_cases i <;> fin_cases j <;> simp [appellQuadraticCenteredMatrix] <;> ring
  constructor
  · intro i j
    rw [hz]
    simpa only [ofReal_sub, ofReal_one, Complex.real_smul] using
      convex_carlsonRightHalfPlane
        (show (1 : ℂ) ∈ carlsonRightHalfPlane by norm_num [carlsonRightHalfPlane]) (hZ i j)
        (sub_nonneg.mpr hs.2) hs.1 (show 1 - s + s = 1 by ring)
  · intro i j
    rw [hw]
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    simpa only [ofReal_sub, ofReal_one, ofReal_pow, Complex.real_smul] using
      convex_carlsonRightHalfPlane
        (show (1 : ℂ) ∈ carlsonRightHalfPlane by norm_num [carlsonRightHalfPlane]) (hW i j)
        (sub_nonneg.mpr hs2) (sq_nonneg s) (show 1 - s ^ 2 + s ^ 2 = 1 by ring)

/-- **Carlson (1976), (2.4), centered form on the full right-half-plane branch domain.**
No series bound or parameter exclusion is imposed. The row normalization contributes
one duplication ratio, retained even where it vanishes. -/
theorem continuedMatrix_firstQuadratic_centered (t μ : ℂ) {x y : ℂ}
    (hZ : appellF4BaileyMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hW : appellQuadraticCenteredMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane) :
    continuedRegMatrixDirichletAverage (appellF4BaileyMatrix x y) (fun z => z ^ (2 * t))
      (pair μ μ, pair μ μ) = quadraticGammaRatio μ *
        continuedRegMatrixDirichletAverage (appellQuadraticCenteredMatrix x y)
          (fun z => z ^ t) (pair (μ + t) (1 / 2 - t), pair μ μ) := by
  have H := continuedMatrix_firstQuadratic_centered_on_scale_domain t μ x y
    (U := ofReal '' Icc (0 : ℝ) 1)
    (isPreconnected_Icc.image ofReal continuous_ofReal.continuousOn)
    (by exact ⟨0, by simp, by simp⟩)
    (by rintro w ⟨s, hs, rfl⟩; exact (firstQuadratic_scale_domains hZ hW hs).1)
    (by rintro w ⟨s, hs, rfl⟩; exact (firstQuadratic_scale_domains hZ hW hs).2)
    (show (1 : ℂ) ∈ ofReal '' Icc (0 : ℝ) 1 from ⟨1, by simp, by simp⟩)
  simpa only [one_mul] using H

/-- The squared-node matrix in (2.3), with the arithmetic mean of its root nodes fixed at one. -/
def appellQuadraticSquareMatrix (x y : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![(1 + y) ^ 2, (1 - y) ^ 2], ![(1 + y) ^ 2 - x ^ 2, (1 - y) ^ 2 - x ^ 2]]

/-- Reversing the second F₄ matrix yields the row order in (2.3). -/
private theorem reverse_secondMatrix (x y : ℂ) :
    (fun i j => appellF4SecondMatrix x y ((Equiv.swap 0 1) i) j) =
      appellQuadraticSquareMatrix x y := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [appellF4SecondMatrix, appellQuadraticSquareMatrix]

/-- **Carlson (1976), (2.3), centered coordinates.** The substitutions in the article are
`p=1+y`, `q=1-y`, `z=x`. Both matrix averages have the same normalization, so the
regularized transformation has no Gamma prefactor, even at exceptional parameters. -/
theorem continuedMatrix_secondQuadratic_centered (t ν : ℂ) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1)
    (hZ : appellQuadraticSquareMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane) :
    continuedRegMatrixDirichletAverage (appellQuadraticSquareMatrix x y) (fun z => z ^ t)
      (pair (2 * ν + t) (1 / 2 - ν - t), pair ν ν) =
        continuedRegMatrixDirichletAverage (appellQuadraticCenteredMatrix x y) (fun z => z ^ t)
          (pair (2 * ν + t) (1 / 2 - ν - t), pair ν ν) := by
  have hZ' : appellF4SecondMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hZ 1 0
    · exact hZ 1 1
    · exact hZ 0 0
    · exact hZ 0 1
  have hS := continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_second_of_rightHalfPlane
    (-t) (1 / 2 - ν - t) (ν + 1 / 2) hxy hZ'
  have hE := centeredMatrix_eq_F4 (-t) (1 / 2 - ν - t) (ν + 1 / 2) hxy
  have hp : appellF2Parameters (1 / 2 - ν - t) (ν + 1 / 2) =
      pair (1 / 2 - ν - t) (2 * ν + t) := by
    funext i
    fin_cases i
    · rfl
    · change ν + 1 / 2 - (1 / 2 - ν - t) = 2 * ν + t
      ring
  rw [show -t - (1 / 2 - ν - t) + 1 / 2 = ν by ring,
    show -t - (1 / 2 - ν - t) + 1 = ν + 1 / 2 by ring, neg_neg, hp] at hS
  rw [show ν + 1 / 2 - 1 / 2 = ν by ring,
    show ν + 1 / 2 - (1 / 2 - ν - t) = 2 * ν + t by ring, neg_neg] at hE
  rw [← reverse_secondMatrix x y,
    continued_matrix_reverseRows t (1 / 2 - ν - t) (2 * ν + t) ν ν hZ', hS, hE]

/-- Reintroducing the common scale in (2.4), with explicit principal-power branch conditions.
This yields the noncentered quadratic transformation by matrix homogeneity. -/
theorem continuedMatrix_firstQuadratic_scaled (t μ : ℂ) {x y ℓ : ℂ}
    (hℓ : 0 < ℓ.re) (hℓ2 : 0 < (ℓ ^ 2).re)
    (hZ : appellF4BaileyMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hW : appellQuadraticCenteredMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hℓZ : (fun i j => ℓ * appellF4BaileyMatrix x y i j) ∈
      matrixNodeDomain carlsonRightHalfPlane)
    (hℓW : (fun i j => ℓ ^ 2 * appellQuadraticCenteredMatrix x y i j) ∈
      matrixNodeDomain carlsonRightHalfPlane) :
    continuedRegMatrixDirichletAverage (fun i j => ℓ * appellF4BaileyMatrix x y i j)
      (fun z => z ^ (2 * t)) (pair μ μ, pair μ μ) = quadraticGammaRatio μ *
        continuedRegMatrixDirichletAverage
          (fun i j => ℓ ^ 2 * appellQuadraticCenteredMatrix x y i j)
          (fun z => z ^ t) (pair (μ + t) (1 / 2 - t), pair μ μ) := by
  have hL := continuedRegMatrixDirichletAverage_mul_cpow_neg (pair μ μ) (pair μ μ)
    hZ hℓ hℓZ (-(2 * t))
  have hR := continuedRegMatrixDirichletAverage_mul_cpow_neg
    (pair (μ + t) (1 / 2 - t)) (pair μ μ) hW hℓ2 hℓW (-t)
  simp only [neg_neg] at hL hR
  have hℓ0 : ℓ ≠ 0 := fun h => by rw [h] at hℓ; simp at hℓ
  have he : ℓ ^ (2 * t) = (ℓ ^ 2) ^ t := by
    rw [show (2 : ℂ) * t = t + t by ring, cpow_add _ _ hℓ0,
      show ℓ ^ 2 = ℓ * ℓ by ring, mul_cpow_of_re_pos hℓ hℓ]
  rw [hL, hR, continuedMatrix_firstQuadratic_centered t μ hZ hW, he]
  ring

/-- On native parameters, normalization multiplies the continued average by the two Gamma totals. -/
private theorem native_matrix_normalization (t : ℂ) {r β : Fin 2 → ℂ}
    (hr : r ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent) {Z : Fin 2 → Fin 2 → ℂ}
    (hZ : Z ∈ matrixNodeDomain carlsonRightHalfPlane) :
    matrixDirichletAverage r β Z (fun z => z ^ t) =
      Gamma (∑ i, r i) * Gamma (∑ j, β j) *
        continuedRegMatrixDirichletAverage Z (fun z => z ^ t) (r, β) := by
  rw [matrixDirichletAverage, continuedRegMatrixDirichletAverage_eq_native
    (f := fun z : ℂ => z ^ t) isOpen_carlsonRightHalfPlane convex_carlsonRightHalfPlane
    (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz)) hZ hr hβ]

/-- Native normalized version of (2.4) on its full centered branch domain. -/
theorem matrix_firstQuadratic_centered (t μ : ℂ) (hμ : 0 < μ.re)
    (hr : pair (μ + t) (1 / 2 - t) ∈ mvBetaConvergent) {x y : ℂ}
    (hZ : appellF4BaileyMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane)
    (hW : appellQuadraticCenteredMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane) :
    matrixDirichletAverage (pair μ μ) (pair μ μ) (appellF4BaileyMatrix x y)
      (fun z => z ^ (2 * t)) =
        matrixDirichletAverage (pair (μ + t) (1 / 2 - t)) (pair μ μ)
          (appellQuadraticCenteredMatrix x y) (fun z => z ^ t) := by
  have hp : pair μ μ ∈ mvBetaConvergent := by intro i; fin_cases i <;> exact hμ
  rw [native_matrix_normalization (2 * t) hp hp hZ,
    native_matrix_normalization t hr hp hW, continuedMatrix_firstQuadratic_centered t μ hZ hW]
  simp only [sum_pair]
  rw [show μ + t + (1 / 2 - t) = μ + 1 / 2 by ring]
  have hG := Gamma_mul_quadraticGammaRatio hμ
  linear_combination Gamma (μ + μ) *
    continuedRegMatrixDirichletAverage (appellQuadraticCenteredMatrix x y) (fun z => z ^ t)
      (pair (μ + t) (1 / 2 - t), pair μ μ) * hG

/-- Native normalized version of (2.3) on the squared-argument convergence region. -/
theorem matrix_secondQuadratic_centered (t ν : ℂ) (hν : 0 < ν.re)
    (hr : pair (2 * ν + t) (1 / 2 - ν - t) ∈ mvBetaConvergent) {x y : ℂ}
    (hxy : ‖x‖ + ‖y‖ < 1)
    (hZ : appellQuadraticSquareMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane) :
    matrixDirichletAverage (pair (2 * ν + t) (1 / 2 - ν - t)) (pair ν ν)
      (appellQuadraticSquareMatrix x y) (fun z => z ^ t) =
        matrixDirichletAverage (pair (2 * ν + t) (1 / 2 - ν - t)) (pair ν ν)
          (appellQuadraticCenteredMatrix x y) (fun z => z ^ t) := by
  have hp : pair ν ν ∈ mvBetaConvergent := by intro i; fin_cases i <;> exact hν
  have hW : appellQuadraticCenteredMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane := by
    rw [← reverse_equalMatrix]
    exact fun i j => appellF4EqualMatrix_mem_rightHalfPlane hxy ((Equiv.swap 0 1) i) j
  rw [native_matrix_normalization t hr hp hZ, native_matrix_normalization t hr hp hW,
    continuedMatrix_secondQuadratic_centered t ν hxy hZ]

/-- The mean matrix is homogeneous of degree two in all four original nodes. -/
theorem appellQuadraticMeanMatrix_smul (ℓ x y z w : ℂ) :
    appellQuadraticMeanMatrix (ℓ * x) (ℓ * y) (ℓ * z) (ℓ * w) =
      fun i j => ℓ ^ 2 * appellQuadraticMeanMatrix x y z w i j := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [appellQuadraticMeanMatrix, arithmeticMeanSq] <;> ring

/-- **Carlson (1976), (2.3), along verified scaling domains.** This continuation
requires no F₄ convergence bound at the endpoint. Both matrix branches are explicit. -/
theorem continuedMatrix_secondQuadratic_centered_on_scale_domain (t ν x y : ℂ)
    {U : Set ℂ} (hU : IsPreconnected U) (h0 : 0 ∈ U)
    (hZ : ∀ w ∈ U, appellQuadraticSquareMatrix (w * x) (w * y) ∈
      matrixNodeDomain carlsonRightHalfPlane)
    (hW : ∀ w ∈ U, appellQuadraticCenteredMatrix (w * x) (w * y) ∈
      matrixNodeDomain carlsonRightHalfPlane) :
    EqOn (fun w => continuedRegMatrixDirichletAverage
        (appellQuadraticSquareMatrix (w * x) (w * y)) (fun z => z ^ t)
        (pair (2 * ν + t) (1 / 2 - ν - t), pair ν ν))
      (fun w => continuedRegMatrixDirichletAverage
        (appellQuadraticCenteredMatrix (w * x) (w * y)) (fun z => z ^ t)
        (pair (2 * ν + t) (1 / 2 - ν - t), pair ν ν)) U := by
  have hL : AnalyticOnNhd ℂ (fun w => continuedRegMatrixDirichletAverage
      (appellQuadraticSquareMatrix (w * x) (w * y)) (fun z => z ^ t)
      (pair (2 * ν + t) (1 / 2 - ν - t), pair ν ν)) U := by
    intro w hw
    apply analyticAt_matrix_power_comp _ _ _
      (Z := fun v => appellQuadraticSquareMatrix (v * x) (v * y)) _ (hZ w hw)
    apply analyticAt_pi_iff.mpr
    intro i
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp [appellQuadraticSquareMatrix] <;> fun_prop
  have hR : AnalyticOnNhd ℂ (fun w => continuedRegMatrixDirichletAverage
      (appellQuadraticCenteredMatrix (w * x) (w * y)) (fun z => z ^ t)
      (pair (2 * ν + t) (1 / 2 - ν - t), pair ν ν)) U := by
    intro w hw
    apply analyticAt_matrix_power_comp _ _ _
      (Z := fun v => appellQuadraticCenteredMatrix (v * x) (v * y)) _ (hW w hw)
    apply analyticAt_pi_iff.mpr
    intro i
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp [appellQuadraticCenteredMatrix] <;> fun_prop
  apply hL.eqOn_of_preconnected_of_eventuallyEq hR hU h0
  have hc : Continuous (fun w : ℂ => appellQuadraticSquareMatrix (w * x) (w * y)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;> simp [appellQuadraticSquareMatrix] <;> fun_prop
  have hsmall : ∀ᶠ w : ℂ in 𝓝 0, ‖w * x‖ + ‖w * y‖ < 1 :=
    (show ContinuousAt (fun w : ℂ => ‖w * x‖ + ‖w * y‖) 0 by fun_prop).eventually
      (Iio_mem_nhds (by simp))
  have hb := hc.continuousAt.eventually
    ((isOpen_matrixNodeDomain isOpen_carlsonRightHalfPlane).mem_nhds
      (show appellQuadraticSquareMatrix (0 * x) (0 * y) ∈
        matrixNodeDomain carlsonRightHalfPlane by
          intro i j
          fin_cases i <;> fin_cases j <;> norm_num [appellQuadraticSquareMatrix,
            carlsonRightHalfPlane]))
  filter_upwards [hsmall, hb] with w hw hzw
  exact continuedMatrix_secondQuadratic_centered t ν hw hzw

end Carlson.TwoVariable
