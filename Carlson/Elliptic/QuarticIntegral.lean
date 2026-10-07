/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.IntegralExercises
public import Carlson.Elliptic.QuarticReduction
public import Carlson.Elliptic.CompleteK
public import Carlson.Elliptic.ZeroVariable

/-!
# The general elliptic integral of the first kind (Carlson's (9.8-10)–(9.8-13))

Consequences of Theorem 9.8-1 for real integrals whose integrand is the inverse square root of
a product of four linear factors, each positive on the interval of integration, and the case of
Theorem 9.8-1 in which `X` vanishes.

## Main results

* `Carlson.integral_quartic_eq_carlsonR`: (9.8-10), the integral as
  `(x - y) P^{-1/2} R_{-1}(1/2, 1/2, 1/2, 1/2; ·)` with nodes given by ratios of the factors.
* `Carlson.integral_quartic_eq_carlsonRF`: (9.8-12), the integral as `2 R_F(U², V², W²)`.
* `Carlson.quartic_sq_sub_sq`: (9.8-12)–(9.8-13), the differences `V² - U²`, `W² - U²`,
  `V² - W²` as products of `2 × 2` determinants of the coefficients.
* `Carlson.integral_quadratic_mul_quadratic`: Exercise 9.8-3,
  `∫_y^x [(at² + c)(αt² + γ)]^{-1/2} dt = R_F(U², U² + aγ, U² + cα)`.
* `Carlson.integral_quartic_eq_integral_cubic_of_nonneg`: Exercise 9.8-6 for a quartic with
  nonnegative coefficients. As stated by Carlson (any quartic positive on `(0, ∞)`) the exercise
  is false; see the docstring for a counterexample.
* `Carlson.tendsto_carlsonRF_zero_of_tendsto_slit`: `R_F(w, y, z) → (π/2) R_K(y, z)` as `w → 0`
  for `y, z` anywhere in the slit plane.
* `Carlson.carlsonR_quartic_eq_carlsonRK`: Theorem 9.8-1 when `X = 0`,
  `R_{-1}(1/2, 1/2, 1/2, 1/2; A², B², C², D²) = π R_K(Y², Z²)`.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology

@[expose] public noncomputable section

namespace Carlson

/-- `∏ rᵢ^{-1/2} = (r₀ r₁ r₂ r₃)^{-1/2}` for positive reals, as complex numbers. -/
private theorem prod_four_cpow_neg_half {r₀ r₁ r₂ r₃ : ℝ} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) (h₃ : 0 < r₃) :
    (r₀ : ℂ) ^ (-(1 / 2) : ℂ) * (r₁ : ℂ) ^ (-(1 / 2) : ℂ) * (r₂ : ℂ) ^ (-(1 / 2) : ℂ) *
        (r₃ : ℂ) ^ (-(1 / 2) : ℂ) = (((r₀ * r₁ * r₂ * r₃) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [show (-(1 / 2) : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow h₀.le,
    ← ofReal_cpow h₁.le, ← ofReal_cpow h₂.le, ← ofReal_cpow h₃.le, ← ofReal_mul, ← ofReal_mul,
    ← ofReal_mul, Real.mul_rpow (by positivity) h₃.le, Real.mul_rpow (by positivity) h₂.le,
    Real.mul_rpow h₀.le h₁.le]

section Quartic

variable {a b c d α β γ δ x y : ℝ}

/-- **Carlson's (9.8-10)**: for real `y < x` with the four linear factors positive on `[y, x]`,
`∫_y^x [(a + αt)(b + βt)(c + γt)(d + δt)]^{-1/2} dt =
(x - y) P^{-1/2} R_{-1}(1/2, 1/2, 1/2, 1/2; A², B², C², D²)`, where
`P = (a + αy)(b + βy)(c + γy)(d + δy)` and `A² = (a + αx)/(a + αy)` etc. -/
theorem integral_quartic_eq_carlsonR (hxy : y < x)
    (hpos : ∀ t ∈ Icc y x, 0 < a + α * t ∧ 0 < b + β * t ∧ 0 < c + γ * t ∧ 0 < d + δ * t) :
    ((∫ t in Ioo y x,
        ((a + α * t) * (b + β * t) * (c + γ * t) * (d + δ * t)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      (x - y) * (((a + α * y) * (b + β * y) * (c + γ * y) * (d + δ * y)) ^ (-1 / 2 : ℝ) : ℝ) *
        carlsonR (-1) (fun _ => 1 / 2)
          ![(((a + α * x) / (a + α * y) : ℝ) : ℂ), (((b + β * x) / (b + β * y) : ℝ) : ℂ),
            (((c + γ * x) / (c + γ * y) : ℝ) : ℂ), (((d + δ * x) / (d + δ * y) : ℝ) : ℂ)] := by
  set z : Fin 4 → ℂ := ![(a : ℂ), b, c, d]
  set w : Fin 4 → ℂ := ![(α : ℂ), β, γ, δ]
  have hseg : ∀ i, ∀ t ∈ Icc y x, z i + w i * (t : ℂ) ∈ slitPlane := by
    intro i t ht
    obtain ⟨h1, h2, h3, h4⟩ := hpos t ht
    fin_cases i
    · simpa [z, w] using ofReal_mem_slitPlane.mpr h1
    · simpa [z, w] using ofReal_mem_slitPlane.mpr h2
    · simpa [z, w] using ofReal_mem_slitPlane.mpr h3
    · simpa [z, w] using ofReal_mem_slitPlane.mpr h4
  have H := integral_Ioo_real_segment_eq_regCarlsonR (a := 1) (a' := 1)
    (b := fun _ : Fin 4 => (1 / 2 : ℂ)) (z := z) (w := w) (by norm_num) (by norm_num)
    (by simp; norm_num) hxy hseg
  obtain ⟨py1, py2, py3, py4⟩ := hpos y ⟨le_rfl, hxy.le⟩
  obtain ⟨px1, px2, px3, px4⟩ := hpos x ⟨hxy.le, le_rfl⟩
  simp only [show (1 : ℂ) - 1 = 0 by ring, cpow_zero, one_mul, Gamma_one, mul_one,
    show (1 : ℂ) + 1 - 1 = 1 by ring, cpow_one, Fin.prod_univ_four, z, w, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons] at H
  have hnodes : (fun i : Fin 4 => (![(a : ℂ), b, c, d] i + ![(α : ℂ), β, γ, δ] i * x) /
      (![(a : ℂ), b, c, d] i + ![(α : ℂ), β, γ, δ] i * y)) =
      ![(((a + α * x) / (a + α * y) : ℝ) : ℂ), (((b + β * x) / (b + β * y) : ℝ) : ℂ),
        (((c + γ * x) / (c + γ * y) : ℝ) : ℂ), (((d + δ * x) / (d + δ * y) : ℝ) : ℂ)] := by
    funext i; fin_cases i <;> simp
  rw [hnodes] at H
  rw [← integral_complex_ofReal]
  have hint : ∀ t ∈ Ioo y x, ((((a + α * t) * (b + β * t) * (c + γ * t) * (d + δ * t)) ^
      (-1 / 2 : ℝ) : ℝ) : ℂ) = ((a : ℂ) + α * t) ^ (-(1 / 2) : ℂ) * ((b : ℂ) + β * t) ^
        (-(1 / 2) : ℂ) * ((c : ℂ) + γ * t) ^ (-(1 / 2) : ℂ) *
          ((d : ℂ) + δ * t) ^ (-(1 / 2) : ℂ) := by
    intro t ht
    obtain ⟨q1, q2, q3, q4⟩ := hpos t (Ioo_subset_Icc_self ht)
    rw [← prod_four_cpow_neg_half q1 q2 q3 q4]
    push_cast; ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioo hint, H]
  have hP := prod_four_cpow_neg_half py1 py2 py3 py4
  push_cast at hP ⊢
  rw [hP, carlsonR, show (∑ _i : Fin 4, (1 / 2 : ℂ)) = 1 + 1 by simp; norm_num,
    Gamma_add_one _ one_ne_zero, Gamma_one, one_mul,
    show (-1 : ℂ) = -1 by rfl]
  ring_nf

/-- `√(p/q) √(r/s) = √(p r q' s')/√(q r' s q'...)`: the square-root algebra behind (9.8-12),
`√(n₁/d₁) √(n₂/d₂) = √(n₁ n₂ d₃ d₄)/√(d₁ d₂ d₃ d₄)` for positive reals. -/
private theorem sqrt_div_mul_sqrt_div {n₁ n₂ d₁ d₂ d₃ d₄ : ℝ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃) (hd₄ : 0 < d₄) :
    Real.sqrt (n₁ / d₁) * Real.sqrt (n₂ / d₂) =
      Real.sqrt (n₁ * n₂ * d₃ * d₄) / Real.sqrt (d₁ * d₂ * d₃ * d₄) := by
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_div' _ (by positivity)]
  congr 1
  field_simp

/-- **Carlson's (9.8-12)**: for real `y < x` with the four linear factors positive on `[y, x]`,
`∫_y^x [(a + αt)(b + βt)(c + γt)(d + δt)]^{-1/2} dt = 2 R_F(U², V², W²)`, where
`(x - y) U = [(a + αx)(b + βx)(c + γy)(d + δy)]^{1/2} + [(a + αy)(b + βy)(c + γx)(d + δx)]^{1/2}`
and `V`, `W` are given by (9.8-13). -/
theorem integral_quartic_eq_carlsonRF (hxy : y < x)
    (hpos : ∀ t ∈ Icc y x, 0 < a + α * t ∧ 0 < b + β * t ∧ 0 < c + γ * t ∧ 0 < d + δ * t) :
    ((∫ t in Ioo y x,
        ((a + α * t) * (b + β * t) * (c + γ * t) * (d + δ * t)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      2 * carlsonRF
        ((((Real.sqrt ((a + α * x) * (b + β * x) * (c + γ * y) * (d + δ * y)) +
          Real.sqrt ((a + α * y) * (b + β * y) * (c + γ * x) * (d + δ * x))) / (x - y)) ^ 2 : ℝ) :
            ℂ)
        ((((Real.sqrt ((a + α * x) * (b + β * y) * (c + γ * x) * (d + δ * y)) +
          Real.sqrt ((a + α * y) * (b + β * x) * (c + γ * y) * (d + δ * x))) / (x - y)) ^ 2 : ℝ) :
            ℂ)
        ((((Real.sqrt ((a + α * x) * (b + β * y) * (c + γ * y) * (d + δ * x)) +
          Real.sqrt ((a + α * y) * (b + β * x) * (c + γ * x) * (d + δ * y))) / (x - y)) ^ 2 : ℝ) :
            ℂ) := by
  obtain ⟨Da, Db, Dc, Dd⟩ := hpos y ⟨le_rfl, hxy.le⟩
  obtain ⟨Na, Nb, Nc, Nd⟩ := hpos x ⟨hxy.le, le_rfl⟩
  rw [integral_quartic_eq_carlsonR hxy hpos]
  set A := Real.sqrt ((a + α * x) / (a + α * y))
  set B := Real.sqrt ((b + β * x) / (b + β * y))
  set C := Real.sqrt ((c + γ * x) / (c + γ * y))
  set D := Real.sqrt ((d + δ * x) / (d + δ * y))
  have hA : 0 < A := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 < B := Real.sqrt_pos.mpr (by positivity)
  have hC : 0 < C := Real.sqrt_pos.mpr (by positivity)
  have hD : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hnodes : ![(((a + α * x) / (a + α * y) : ℝ) : ℂ), (((b + β * x) / (b + β * y) : ℝ) : ℂ),
      (((c + γ * x) / (c + γ * y) : ℝ) : ℂ), (((d + δ * x) / (d + δ * y) : ℝ) : ℂ)] =
      ![(A : ℂ) ^ 2, (B : ℂ) ^ 2, (C : ℂ) ^ 2, (D : ℂ) ^ 2] := by
    simp only [A, B, C, D, ← ofReal_pow, Real.sq_sqrt (div_pos Na Da).le,
      Real.sq_sqrt (div_pos Nb Db).le, Real.sq_sqrt (div_pos Nc Dc).le,
      Real.sq_sqrt (div_pos Nd Dd).le]
  have re : ∀ r : ℝ, 0 < r → 0 < (r : ℂ).re := fun r hr => by simpa using hr
  have h98 := carlsonR_quartic_eq_carlsonRF (re A hA) (re B hB) (re C hC) (re D hD)
    (by rw [← ofReal_mul, ← ofReal_mul, ← ofReal_add]; exact re _ (by positivity))
    (by rw [← ofReal_mul, ← ofReal_mul, ← ofReal_add]; exact re _ (by positivity))
    (by rw [← ofReal_mul, ← ofReal_mul, ← ofReal_add]; exact re _ (by positivity))
  rw [hnodes, h98]
  -- `AB + CD = λ U` etc. with `λ = (x - y) P^{-1/2}`
  set P := (a + α * y) * (b + β * y) * (c + γ * y) * (d + δ * y)
  have hP : 0 < P := by positivity
  set l := (x - y) / Real.sqrt P
  have hl : 0 < l := div_pos (by linarith) (Real.sqrt_pos.mpr hP)
  have hxy0 : x - y ≠ 0 := by linarith
  have hsP : Real.sqrt P ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  have eX : A * B + C * D = l * ((Real.sqrt ((a + α * x) * (b + β * x) * (c + γ * y) *
      (d + δ * y)) + Real.sqrt ((a + α * y) * (b + β * y) * (c + γ * x) * (d + δ * x))) /
        (x - y)) := by
    simp only [A, B, C, D, l]
    rw [sqrt_div_mul_sqrt_div Na Nb Da Db Dc Dd, sqrt_div_mul_sqrt_div Nc Nd Dc Dd Da Db]
    simp only [P]
    rw [show (c + γ * y) * (d + δ * y) * (a + α * y) * (b + β * y) =
      (a + α * y) * (b + β * y) * (c + γ * y) * (d + δ * y) by ring,
      show (c + γ * x) * (d + δ * x) * (a + α * y) * (b + β * y) =
      (a + α * y) * (b + β * y) * (c + γ * x) * (d + δ * x) by ring]
    field_simp
  have eY : A * C + B * D = l * ((Real.sqrt ((a + α * x) * (b + β * y) * (c + γ * x) *
      (d + δ * y)) + Real.sqrt ((a + α * y) * (b + β * x) * (c + γ * y) * (d + δ * x))) /
        (x - y)) := by
    simp only [A, B, C, D, l]
    rw [sqrt_div_mul_sqrt_div Na Nc Da Dc Db Dd, sqrt_div_mul_sqrt_div Nb Nd Db Dd Da Dc]
    simp only [P]
    rw [show (a + α * x) * (c + γ * x) * (b + β * y) * (d + δ * y) =
      (a + α * x) * (b + β * y) * (c + γ * x) * (d + δ * y) by ring,
      show (b + β * x) * (d + δ * x) * (a + α * y) * (c + γ * y) =
      (a + α * y) * (b + β * x) * (c + γ * y) * (d + δ * x) by ring,
      show (a + α * y) * (c + γ * y) * (b + β * y) * (d + δ * y) =
        (a + α * y) * (b + β * y) * (c + γ * y) * (d + δ * y) by ring,
      show (b + β * y) * (d + δ * y) * (a + α * y) * (c + γ * y) =
        (a + α * y) * (b + β * y) * (c + γ * y) * (d + δ * y) by ring]
    field_simp
  have eZ : A * D + B * C = l * ((Real.sqrt ((a + α * x) * (b + β * y) * (c + γ * y) *
      (d + δ * x)) + Real.sqrt ((a + α * y) * (b + β * x) * (c + γ * x) * (d + δ * y))) /
        (x - y)) := by
    simp only [A, B, C, D, l]
    rw [sqrt_div_mul_sqrt_div Na Nd Da Dd Db Dc, sqrt_div_mul_sqrt_div Nb Nc Db Dc Da Dd]
    simp only [P]
    rw [show (a + α * x) * (d + δ * x) * (b + β * y) * (c + γ * y) =
      (a + α * x) * (b + β * y) * (c + γ * y) * (d + δ * x) by ring,
      show (b + β * x) * (c + γ * x) * (a + α * y) * (d + δ * y) =
      (a + α * y) * (b + β * x) * (c + γ * x) * (d + δ * y) by ring,
      show (a + α * y) * (d + δ * y) * (b + β * y) * (c + γ * y) =
        (a + α * y) * (b + β * y) * (c + γ * y) * (d + δ * y) by ring,
      show (b + β * y) * (c + γ * y) * (a + α * y) * (d + δ * y) =
        (a + α * y) * (b + β * y) * (c + γ * y) * (d + δ * y) by ring]
    field_simp
  have hcast : ∀ r s u v : ℝ, ((r : ℂ) * (s : ℂ) + (u : ℂ) * (v : ℂ)) ^ 2 =
      (((r * s + u * v) ^ 2 : ℝ) : ℂ) := fun r s u v => by push_cast; ring
  rw [hcast, hcast, hcast, eX, eY, eZ, mul_pow l, mul_pow l, mul_pow l, ofReal_mul, ofReal_mul,
    ofReal_mul]
  have sl : ∀ r : ℝ, 0 < r → ((r ^ 2 : ℝ) : ℂ) ∈ slitPlane := fun r hr =>
    ofReal_mem_slitPlane.mpr (by positivity)
  have hdiv : 0 < x - y := by linarith
  rw [carlsonRF_mul_of_pos (by positivity) (sl _ (by positivity)) (sl _ (by positivity))
    (sl _ (by positivity)), ofReal_cpow_neg_half (by positivity), Real.sqrt_sq hl.le,
    show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hP.le, ← Real.sqrt_eq_rpow]
  simp only [l]
  push_cast
  have : (Real.sqrt P : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsP
  have : ((x : ℂ) - y) ≠ 0 := by exact_mod_cast hxy0
  field_simp

/-- **Carlson's (9.8-12), (9.8-13)**: with `U, V, W` as in `integral_quartic_eq_carlsonRF`,
`V² - U² = (aδ - dα)(cβ - bγ)`, `W² - U² = (aγ - cα)(dβ - bδ)` and
`V² - W² = (aβ - bα)(cδ - dγ)`. -/
theorem quartic_sq_sub_sq (hxy : y < x)
    (hpos : ∀ t ∈ Icc y x, 0 < a + α * t ∧ 0 < b + β * t ∧ 0 < c + γ * t ∧ 0 < d + δ * t) :
    let U := (Real.sqrt ((a + α * x) * (b + β * x) * (c + γ * y) * (d + δ * y)) +
      Real.sqrt ((a + α * y) * (b + β * y) * (c + γ * x) * (d + δ * x))) / (x - y)
    let V := (Real.sqrt ((a + α * x) * (b + β * y) * (c + γ * x) * (d + δ * y)) +
      Real.sqrt ((a + α * y) * (b + β * x) * (c + γ * y) * (d + δ * x))) / (x - y)
    let W := (Real.sqrt ((a + α * x) * (b + β * y) * (c + γ * y) * (d + δ * x)) +
      Real.sqrt ((a + α * y) * (b + β * x) * (c + γ * x) * (d + δ * y))) / (x - y)
    V ^ 2 - U ^ 2 = (a * δ - d * α) * (c * β - b * γ) ∧
      W ^ 2 - U ^ 2 = (a * γ - c * α) * (d * β - b * δ) ∧
      V ^ 2 - W ^ 2 = (a * β - b * α) * (c * δ - d * γ) := by
  intro U V W
  obtain ⟨Da, Db, Dc, Dd⟩ := hpos y ⟨le_rfl, hxy.le⟩
  obtain ⟨Na, Nb, Nc, Nd⟩ := hpos x ⟨hxy.le, le_rfl⟩
  set F1 := (a + α * x) * (b + β * x) * (c + γ * y) * (d + δ * y)
  set F2 := (a + α * y) * (b + β * y) * (c + γ * x) * (d + δ * x)
  set F3 := (a + α * x) * (b + β * y) * (c + γ * x) * (d + δ * y)
  set F4 := (a + α * y) * (b + β * x) * (c + γ * y) * (d + δ * x)
  set F5 := (a + α * x) * (b + β * y) * (c + γ * y) * (d + δ * x)
  set F6 := (a + α * y) * (b + β * x) * (c + γ * x) * (d + δ * y)
  have h1 : Real.sqrt F1 ^ 2 = F1 := Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt F2 ^ 2 = F2 := Real.sq_sqrt (by positivity)
  have h3 : Real.sqrt F3 ^ 2 = F3 := Real.sq_sqrt (by positivity)
  have h4 : Real.sqrt F4 ^ 2 = F4 := Real.sq_sqrt (by positivity)
  have h5 : Real.sqrt F5 ^ 2 = F5 := Real.sq_sqrt (by positivity)
  have h6 : Real.sqrt F6 ^ 2 = F6 := Real.sq_sqrt (by positivity)
  have m12 : Real.sqrt F1 * Real.sqrt F2 = Real.sqrt F3 * Real.sqrt F4 := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1; simp only [F1, F2, F3, F4]; ring
  have m56 : Real.sqrt F1 * Real.sqrt F2 = Real.sqrt F5 * Real.sqrt F6 := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1; simp only [F1, F2, F5, F6]; ring
  have hd : (x - y) ≠ 0 := by linarith
  simp only [U, V, W, div_pow]
  refine ⟨?_, ?_, ?_⟩ <;> rw [← sub_div, div_eq_iff (pow_ne_zero 2 hd)]
  · linear_combination h3 + h4 - h1 - h2 - 2 * m12
  · linear_combination h5 + h6 - h1 - h2 - 2 * m56
  · linear_combination h3 + h4 - h5 - h6 + 2 * m56 - 2 * m12

/-- **Exercise 9.8-3**: for real `0 < y < x` with `at² + c`, `αt² + γ` positive on `[y, x]`,
`∫_y^x [(at² + c)(αt² + γ)]^{-1/2} dt = R_F(U², U² + aγ, U² + cα)`, where
`(x² - y²) U = x [(ay² + c)(αy² + γ)]^{1/2} + y [(ax² + c)(αx² + γ)]^{1/2}`. -/
theorem integral_quadratic_mul_quadratic {a c α γ x y : ℝ} (hy : 0 < y) (hxy : y < x)
    (hpos : ∀ t ∈ Icc y x, 0 < a * t ^ 2 + c ∧ 0 < α * t ^ 2 + γ) :
    ((∫ t in Ioo y x, ((a * t ^ 2 + c) * (α * t ^ 2 + γ)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      carlsonRF
        ((((x * Real.sqrt ((a * y ^ 2 + c) * (α * y ^ 2 + γ)) +
          y * Real.sqrt ((a * x ^ 2 + c) * (α * x ^ 2 + γ))) / (x ^ 2 - y ^ 2)) ^ 2 : ℝ) : ℂ)
        ((((x * Real.sqrt ((a * y ^ 2 + c) * (α * y ^ 2 + γ)) +
          y * Real.sqrt ((a * x ^ 2 + c) * (α * x ^ 2 + γ))) / (x ^ 2 - y ^ 2)) ^ 2 + a * γ : ℝ) :
            ℂ)
        ((((x * Real.sqrt ((a * y ^ 2 + c) * (α * y ^ 2 + γ)) +
          y * Real.sqrt ((a * x ^ 2 + c) * (α * x ^ 2 + γ))) / (x ^ 2 - y ^ 2)) ^ 2 + c * α : ℝ) :
            ℂ) := by
  have hy2 : y ^ 2 < x ^ 2 := by nlinarith
  -- positivity of the four linear factors in `s = t²`
  have hpos' : ∀ s ∈ Icc (y ^ 2) (x ^ 2), 0 < 0 + 1 * s ∧ 0 < c + a * s ∧ 0 < γ + α * s ∧
      0 < 1 + 0 * s := by
    intro s hs
    have hs0 : 0 < s := by nlinarith [hs.1]
    have ht : Real.sqrt s ∈ Icc y x := ⟨by rw [← Real.sqrt_sq hy.le]; exact Real.sqrt_le_sqrt hs.1,
      by rw [← Real.sqrt_sq (hy.trans hxy).le]; exact Real.sqrt_le_sqrt hs.2⟩
    obtain ⟨h1, h2⟩ := hpos _ ht
    rw [Real.sq_sqrt hs0.le] at h1 h2
    exact ⟨by linarith, by linarith, by linarith, by norm_num⟩
  have H := integral_quartic_eq_carlsonRF hy2 hpos'
  obtain ⟨-, hWU, hVW⟩ := quartic_sq_sub_sq hy2 hpos'
  -- the substitution `s = t²`
  set G : ℝ → ℂ := fun s => (((1 / 2 : ℝ) * ((0 + 1 * s) * (c + a * s) * (γ + α * s) *
    (1 + 0 * s)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)
  have hsub := integral_Ioo_sq_eq G hy.le hxy
  have hG : ∫ s in Ioo (y ^ 2) (x ^ 2), G s = (1 / 2 : ℂ) * ((∫ s in Ioo (y ^ 2) (x ^ 2),
      ((0 + 1 * s) * (c + a * s) * (γ + α * s) * (1 + 0 * s)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul]
    simp only [G]; push_cast; rfl
  rw [hG, H] at hsub
  rw [← integral_complex_ofReal, show (∫ t in Ioo y x,
      ((((a * t ^ 2 + c) * (α * t ^ 2 + γ)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)) =
      ∫ t in Ioo y x, ((2 * t : ℝ) : ℂ) * G (t ^ 2) from
    setIntegral_congr_fun measurableSet_Ioo fun t ht => by
      have ht0 : 0 < t := hy.trans ht.1
      obtain ⟨h1, h2⟩ := hpos t (Ioo_subset_Icc_self ht)
      simp only [G, zero_add, one_mul, zero_mul, add_zero, mul_one]
      rw [← ofReal_mul]
      congr 1
      rw [show t ^ 2 * (c + a * t ^ 2) * (γ + α * t ^ 2) = t ^ 2 * ((a * t ^ 2 + c) *
        (α * t ^ 2 + γ)) by ring]
      generalize hP : (a * t ^ 2 + c) * (α * t ^ 2 + γ) = P
      have hP0 : 0 < P := hP ▸ mul_pos h1 h2
      rw [Real.mul_rpow (by positivity) hP0.le, show (-1 / 2 : ℝ) = -(1 / 2) by ring,
        Real.rpow_neg (sq_nonneg t), ← Real.sqrt_eq_rpow, Real.sqrt_sq ht0.le]
      field_simp]
  simp only [zero_add, one_mul, zero_mul, add_zero, mul_one, zero_sub] at hsub hWU hVW
  have hsq : ∀ {t : ℝ}, 0 < t → ∀ s : ℝ, Real.sqrt (t ^ 2 * (c + a * s) * (γ + α * s)) =
      t * Real.sqrt ((a * s + c) * (α * s + γ)) := fun ht s => by
    rw [mul_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht.le]; ring_nf
  rw [hsq (hy.trans hxy), hsq hy] at hsub hWU hVW
  set Ub := (x * Real.sqrt ((a * y ^ 2 + c) * (α * y ^ 2 + γ)) +
    y * Real.sqrt ((a * x ^ 2 + c) * (α * x ^ 2 + γ))) / (x ^ 2 - y ^ 2)
  set A := (Real.sqrt (x ^ 2 * (c + a * x ^ 2) * (γ + α * y ^ 2)) +
    Real.sqrt (y ^ 2 * (c + a * y ^ 2) * (γ + α * x ^ 2))) / (x ^ 2 - y ^ 2)
  set B := (Real.sqrt (x ^ 2 * (c + a * y ^ 2) * (γ + α * x ^ 2)) +
    Real.sqrt (y ^ 2 * (c + a * x ^ 2) * (γ + α * y ^ 2))) / (x ^ 2 - y ^ 2)
  rw [show A ^ 2 = Ub ^ 2 + a * γ by linear_combination -hWU,
    show B ^ 2 = Ub ^ 2 + c * α by linear_combination hVW] at hsub
  rw [← hsub]
  obtain ⟨hy1, hy2'⟩ := hpos y ⟨le_rfl, hxy.le⟩
  obtain ⟨hx1, hx2⟩ := hpos x ⟨hxy.le, le_rfl⟩
  have hx0 : 0 < x := hy.trans hxy
  have hU : 0 < Ub := div_pos (by
    have := Real.sqrt_pos.2 (mul_pos hy1 hy2')
    have := Real.sqrt_pos.2 (mul_pos hx1 hx2)
    positivity) (by linarith)
  have hA : 0 < Ub ^ 2 + a * γ := by
    rw [← show A ^ 2 = Ub ^ 2 + a * γ by linear_combination -hWU]
    refine pow_pos (div_pos (add_pos (Real.sqrt_pos.2 ?_) (Real.sqrt_pos.2 ?_)) (by linarith)) 2
    · exact mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
    · exact mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
  have hB : 0 < Ub ^ 2 + c * α := by
    rw [← show B ^ 2 = Ub ^ 2 + c * α by linear_combination hVW]
    refine pow_pos (div_pos (add_pos (Real.sqrt_pos.2 ?_) (Real.sqrt_pos.2 ?_)) (by linarith)) 2
    · exact mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
    · exact mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
  have hs : ∀ {r : ℝ}, 0 < r → (r : ℂ) ∈ slitPlane := fun hr => ofReal_mem_slitPlane.2 hr
  rw [carlsonRF_comm_right (hs hA) (hs (pow_pos hU 2)) (hs hB),
    carlsonRF_comm_left (hs (pow_pos hU 2)) (hs hA) (hs hB)]
  ring

/-- The algebraic identity behind Exercise 9.8-6: with `q² = Q(s)`, `ρ = √a`, `ε = √e`, the
substitution `t = 2ρ²s² + bs + 2ρq - 2ρε` gives `C(t) = [(4ρ²s + b)q + ρQ'(s)]²`. -/
private theorem cubic_eq_sq_of_quartic {ρ ε b c d s q : ℝ}
    (hq : q ^ 2 = ρ ^ 2 * s ^ 4 + b * s ^ 3 + c * s ^ 2 + d * s + ε ^ 2) :
    (2 * ρ ^ 2 * s ^ 2 + b * s + 2 * ρ * q - 2 * ρ * ε) ^ 3 +
        (c + 6 * ρ * ε) * (2 * ρ ^ 2 * s ^ 2 + b * s + 2 * ρ * q - 2 * ρ * ε) ^ 2 +
        (b * d + 4 * c * ρ * ε + 8 * ρ ^ 2 * ε ^ 2) *
          (2 * ρ ^ 2 * s ^ 2 + b * s + 2 * ρ * q - 2 * ρ * ε) + (b * ε + d * ρ) ^ 2 =
      ((4 * ρ ^ 2 * s + b) * q +
        ρ * (4 * ρ ^ 2 * s ^ 3 + 3 * b * s ^ 2 + 2 * c * s + d)) ^ 2 := by
  linear_combination (-b ^ 2 + 4 * b * ρ ^ 2 * s + 4 * c * ρ ^ 2 + 8 * q * ρ ^ 3 +
    8 * ρ ^ 4 * s ^ 2) * hq

/-- **Exercise 9.8-6**, for a quartic with nonnegative coefficients: with
`Q(s) = as⁴ + bs³ + cs² + ds + e` and `C(t) = t³ + ft² + gt + h`, where
`f = c + 6√(ae)`, `g = bd + 4c√(ae) + 8ae`, `h = (b√e + d√a)²`,
`∫₀^∞ Q(s)^{-1/2} ds = ∫₀^∞ C(t)^{-1/2} dt`.

Carlson states this for every `Q` positive on `(0, ∞)`; that is false. For
`Q(s) = s⁴ - 1.9s³ + 2s² - 1.9s + 1` the two sides are `3.3721…` and `1.2574…` (the cubic is
unchanged when `b` and `d` change sign together). Numerically the identity holds exactly when
`b√e + d√a ≥ 0`, which is when the substitution `t = 2as² + bs + 2√a √Q(s) - 2√(ae)` is
increasing. Nonnegative coefficients make it increasing. -/
theorem integral_quartic_eq_integral_cubic_of_nonneg {a b c d e : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    ∫ s in Ioi (0 : ℝ), (a * s ^ 4 + b * s ^ 3 + c * s ^ 2 + d * s + e) ^ (-1 / 2 : ℝ) =
      ∫ t in Ioi (0 : ℝ), (t ^ 3 + (c + 6 * √(a * e)) * t ^ 2 +
        (b * d + 4 * c * √(a * e) + 8 * a * e) * t + (b * √e + d * √a) ^ 2) ^ (-1 / 2 : ℝ) := by
  rw [Real.sqrt_mul ha.le]
  set ρ := √a
  set ε := √e
  have hρ : 0 < ρ := Real.sqrt_pos.2 ha
  have hε : 0 ≤ ε := Real.sqrt_nonneg e
  have hρ2 : ρ ^ 2 = a := Real.sq_sqrt ha.le
  have hε2 : ε ^ 2 = e := Real.sq_sqrt he
  rw [← hρ2, ← hε2]
  set Q : ℝ → ℝ := fun s => ρ ^ 2 * s ^ 4 + b * s ^ 3 + c * s ^ 2 + d * s + ε ^ 2
  set Q' : ℝ → ℝ := fun s => 4 * ρ ^ 2 * s ^ 3 + 3 * b * s ^ 2 + 2 * c * s + d
  have hQpos : ∀ {s : ℝ}, 0 < s → 0 < Q s := fun hs => by simp only [Q]; positivity
  have hQ0 : ∀ {s : ℝ}, 0 ≤ s → 0 ≤ Q s := fun hs => by simp only [Q]; positivity
  set φ : ℝ → ℝ := fun s => 2 * ρ ^ 2 * s ^ 2 + b * s + 2 * ρ * √(Q s) - 2 * ρ * ε
  set w : ℝ → ℝ := fun s => (4 * ρ ^ 2 * s + b) * √(Q s) + ρ * Q' s
  have hwpos : ∀ {s : ℝ}, 0 < s → 0 < w s := fun hs => by
    have := Real.sqrt_pos.2 (hQpos hs)
    simp only [w, Q']; positivity
  have hderiv : ∀ {s : ℝ}, 0 < s → HasDerivAt φ (w s / √(Q s)) s := fun {s} hs => by
    have hq := Real.sqrt_pos.2 (hQpos hs)
    have hQd : HasDerivAt Q (Q' s) s := by
      simp only [Q, Q']
      have := ((((((hasDerivAt_id s).pow 4).const_mul (ρ ^ 2)).add
        (((hasDerivAt_id s).pow 3).const_mul b)).add
        (((hasDerivAt_id s).pow 2).const_mul c)).add ((hasDerivAt_id s).const_mul d)).add_const
        (ε ^ 2)
      convert this using 1 <;> simp; ring
    have := (((((hasDerivAt_id s).pow 2).const_mul (2 * ρ ^ 2)).add
      ((hasDerivAt_id s).const_mul b)).add ((hQd.sqrt (hQpos hs).ne').const_mul (2 * ρ))).sub_const
      (2 * ρ * ε)
    convert this using 1
    · ext x; simp [φ]
    · simp only [w]; field_simp; simp; ring
  have hφ0 : φ 0 = 0 := by simp [φ, Q, Real.sqrt_sq hε]
  have hφcont : Continuous φ := by simp only [φ, Q]; fun_prop
  have hmono : StrictMonoOn φ (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) hφcont.continuousOn fun s hs => ?_
    rw [interior_Ici] at hs
    rw [(hderiv hs).deriv]
    exact div_pos (hwpos hs) (Real.sqrt_pos.2 (hQpos hs))
  have htop : Tendsto φ atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-(2 * ρ * ε))
      (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * ρ ^ 2)))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have h1 := mul_nonneg hρ.le (Real.sqrt_nonneg (Q s))
    have h2 := mul_nonneg hb (zero_le_one.trans hs)
    have h3 : ρ ^ 2 * s ≤ ρ ^ 2 * s ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg ρ)
    simp only [φ, id]
    nlinarith
  have himage : φ '' Ioi 0 = Ioi 0 := by
    apply Subset.antisymm
    · rintro _ ⟨s, hs, rfl⟩
      rw [← hφ0]
      exact hmono self_mem_Ici (mem_Ici_of_Ioi hs) hs
    · have := intermediate_value_Ioi (a := (0 : ℝ)) hφcont.continuousOn htop
      rwa [hφ0] at this
  symm
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun s hs => (hderiv hs).hasDerivWithinAt) (hmono.injOn.mono Ioi_subset_Ici_self), himage]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hq := Real.sqrt_pos.2 (hQpos hs)
  have hw := hwpos hs
  have key : (2 * ρ ^ 2 * s ^ 2 + b * s + 2 * ρ * √(Q s) - 2 * ρ * ε) ^ 3 +
        (c + 6 * (ρ * ε)) * (2 * ρ ^ 2 * s ^ 2 + b * s + 2 * ρ * √(Q s) - 2 * ρ * ε) ^ 2 +
        (b * d + 4 * c * (ρ * ε) + 8 * ρ ^ 2 * ε ^ 2) *
          (2 * ρ ^ 2 * s ^ 2 + b * s + 2 * ρ * √(Q s) - 2 * ρ * ε) + (b * ε + d * ρ) ^ 2 =
      w s ^ 2 := by
    rw [← cubic_eq_sq_of_quartic (Real.sq_sqrt (hQ0 (le_of_lt hs)))]
    ring
  simp only [smul_eq_mul]
  rw [show φ s = 2 * ρ ^ 2 * s ^ 2 + b * s + 2 * ρ * √(Q s) - 2 * ρ * ε from rfl]
  rw [key, abs_of_pos (div_pos hw hq), show (-1 / 2 : ℝ) = -(1 / 2) by norm_num,
    Real.rpow_neg (sq_nonneg _), Real.rpow_neg (hQ0 (le_of_lt hs)), ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow]
  change _ = (√(Q s))⁻¹
  rw [Real.sqrt_sq hw.le]
  field_simp

end Quartic

/-! ### Theorem 9.8-1 with a vanishing `X` -/

open TwoVariable (carlsonRK)

/-- `R_F` is continuous at every point of the slit domain. -/
theorem continuousAt_carlsonRF {p q r : ℂ} (hp : p ∈ slitPlane) (hq : q ∈ slitPlane)
    (hr : r ∈ slitPlane) :
    ContinuousAt (fun w : Fin 3 → ℂ => carlsonRF (w 0) (w 1) (w 2)) ![p, q, r] := by
  have hs : (![p, q, r] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  have := (analyticOnNhd_regCarlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) _ hs).continuousAt
  have hc2 : ContinuousAt (fun w : Fin 3 → ℂ =>
      Gamma (3 / 2) * regCarlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) w) _ :=
    continuousAt_const.mul this
  refine hc2.congr (Filter.Eventually.of_forall fun w => ?_)
  show Gamma (3 / 2) * regCarlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) w =
    carlsonRF (w 0) (w 1) (w 2)
  rw [carlsonRF_eq]
  congr 2
  funext i; fin_cases i <;> rfl

/-- **(8.3-17) on the slit plane**: `R_F(w, y, z) → (π/2) R_K(y, z)` as `w → 0` through the slit
plane and `(y, z)` tends to a point of the slit domain. Unlike
`Carlson.tendsto_carlsonRF_zero_of_tendsto`, `y` and `z` need not have positive real parts; the
proof passes through the duplication theorem. -/
theorem tendsto_carlsonRF_zero_of_tendsto_slit {α : Type*} {l : Filter α} {f g h : α → ℂ}
    {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hf : Tendsto f l (𝓝 0))
    (hg : Tendsto g l (𝓝 y)) (hh : Tendsto h l (𝓝 z)) (hf' : ∀ᶠ a in l, f a ∈ slitPlane) :
    Tendsto (fun a => carlsonRF (f a) (g a) (h a)) l (𝓝 ((π / 2 : ℂ) * carlsonRK y z)) := by
  have hsqrt : ∀ {u : ℂ}, u ∈ slitPlane → ContinuousAt (fun w : ℂ => w ^ (1 / 2 : ℂ)) u :=
    fun {u} hu => continuousAt_cpow_const_of_re_pos
      (by rcases mem_slitPlane_iff.1 hu with h | h; exacts [Or.inl h.le, Or.inr h])
      (by norm_num)
  have h0 : Tendsto (fun a => f a ^ (1 / 2 : ℂ)) l (𝓝 0) := by
    have := (continuousAt_cpow_const_of_re_pos (z := 0) (w := 1 / 2) (Or.inl le_rfl)
      (by norm_num)).tendsto.comp hf
    rwa [zero_cpow (by norm_num)] at this
  have hgs := (hsqrt hy).tendsto.comp hg
  have hhs := (hsqrt hz).tendsto.comp hh
  set L0 := y ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ)
  have hL : Tendsto (fun a => dupLambda (f a) (g a) (h a)) l (𝓝 L0) := by
    have := ((h0.mul hgs).add (h0.mul hhs)).add (hgs.mul hhs)
    simpa [dupLambda, L0] using this
  have hyr := re_cpow_half_pos hy
  have hzr := re_cpow_half_pos hz
  have hcpow : ∀ {u : ℂ}, u ∈ slitPlane → u ^ (1 / 2 : ℂ) * u ^ (1 / 2 : ℂ) = u := fun {u} hu => by
    rw [← cpow_add _ _ (slitPlane_ne_zero hu)]; norm_num
  have m0 : L0 ∈ slitPlane := mul_mem_slitPlane_of_re_pos hyr hzr
  have m1 : y + L0 ∈ slitPlane := by
    rw [show y + L0 = y ^ (1 / 2 : ℂ) * (y ^ (1 / 2 : ℂ) + z ^ (1 / 2 : ℂ)) by
      rw [mul_add, hcpow hy]]
    exact mul_mem_slitPlane_of_re_pos hyr (by rw [add_re]; linarith)
  have m2 : z + L0 ∈ slitPlane := by
    rw [show z + L0 = z ^ (1 / 2 : ℂ) * (z ^ (1 / 2 : ℂ) + y ^ (1 / 2 : ℂ)) by
      rw [mul_add, hcpow hz]; ring]
    exact mul_mem_slitPlane_of_re_pos hzr (by rw [add_re]; linarith)
  have hvec : Tendsto (fun a => (![f a + dupLambda (f a) (g a) (h a),
      g a + dupLambda (f a) (g a) (h a), h a + dupLambda (f a) (g a) (h a)] : Fin 3 → ℂ)) l
      (𝓝 ![L0, y + L0, z + L0]) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · simpa using hf.add hL
    · simpa using hg.add hL
    · simpa using hh.add hL
  have hlim : Tendsto (fun a => 2 * carlsonRF (f a + dupLambda (f a) (g a) (h a))
      (g a + dupLambda (f a) (g a) (h a)) (h a + dupLambda (f a) (g a) (h a))) l
      (𝓝 (2 * carlsonRF L0 (y + L0) (z + L0))) :=
    ((continuousAt_carlsonRF m0 m1 m2).tendsto.comp hvec).const_mul 2
  have hval : 2 * carlsonRF L0 (y + L0) (z + L0) = (π / 2 : ℂ) * carlsonRK y z := by
    rw [carlsonRK_duplication hy hz, carlsonRF_comm_left m1 m0 m2,
      carlsonRF_comm_right m1 m2 m0]
  rw [hval] at hlim
  refine hlim.congr' ?_
  have hgo : ∀ᶠ a in l, g a ∈ slitPlane := hg.eventually (isOpen_slitPlane.mem_nhds hy)
  have hho : ∀ᶠ a in l, h a ∈ slitPlane := hh.eventually (isOpen_slitPlane.mem_nhds hz)
  filter_upwards [hf', hgo, hho] with a ha hb hc
  rw [carlsonRF_duplication ha hb hc]

/-- **Carlson's Theorem 9.8-1 when `X = 0`**: if `A, B, C, D`, `Y = AC + BD` and `Z = AD + BC`
have positive real parts and `X = AB + CD = 0`, then
`R_{-1}(1/2, 1/2, 1/2, 1/2; A², B², C², D²) = 2 R_F(0, Y², Z²) = π R_K(Y², Z²)`. -/
theorem carlsonR_quartic_eq_carlsonRK {A B C D : ℂ} (hA : 0 < A.re) (hB : 0 < B.re)
    (hC : 0 < C.re) (hD : 0 < D.re) (hX : A * B + C * D = 0) (hY : 0 < (A * C + B * D).re)
    (hZ : 0 < (A * D + B * C).re) :
    carlsonR (-1) (fun _ => 1 / 2) ![A ^ 2, B ^ 2, C ^ 2, D ^ 2] =
      π * carlsonRK ((A * C + B * D) ^ 2) ((A * D + B * C) ^ 2) := by
  -- the perturbation `A ↦ A + δ`, `δ > 0`
  have hpert : ∀ δ : ℝ, 0 < δ →
      carlsonR (-1) (fun _ => 1 / 2) ![(A + δ) ^ 2, B ^ 2, C ^ 2, D ^ 2] =
        2 * carlsonRF (((A + δ) * B + C * D) ^ 2) (((A + δ) * C + B * D) ^ 2)
          (((A + δ) * D + B * C) ^ 2) := fun δ hδ =>
    carlsonR_quartic_eq_carlsonRF (by simp; linarith) hB hC hD
      (by rw [show (A + δ) * B + C * D = δ * B by linear_combination hX, re_ofReal_mul]
          positivity)
      (by rw [show (A + δ) * C + B * D = (A * C + B * D) + δ * C by ring, add_re, re_ofReal_mul]
          nlinarith [mul_pos hδ hC])
      (by rw [show (A + δ) * D + B * C = (A * D + B * C) + δ * D by ring, add_re, re_ofReal_mul]
          nlinarith [mul_pos hδ hD])
  have hδ : Tendsto (fun δ : ℝ => (δ : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (continuous_ofReal.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  -- the left side is continuous in `A`
  have hsq : ∀ {u : ℂ}, 0 < u.re → u ^ 2 ∈ slitPlane := fun hu => sq_mem_slitPlane_of_re_pos hu
  have hs : (![A ^ 2, B ^ 2, C ^ 2, D ^ 2] : Fin 4 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    exacts [hsq hA, hsq hB, hsq hC, hsq hD]
  have hLc := (analyticOnNhd_regCarlsonR (-1) (fun _ : Fin 4 => (1 / 2 : ℂ)) _ hs).continuousAt
  have hvec : Tendsto (fun δ : ℝ => (![(A + δ) ^ 2, B ^ 2, C ^ 2, D ^ 2] : Fin 4 → ℂ))
      (𝓝[>] 0) (𝓝 ![A ^ 2, B ^ 2, C ^ 2, D ^ 2]) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · simpa using ((tendsto_const_nhds (x := A)).add hδ).pow 2
    all_goals simp
  have hL := (hLc.tendsto.comp hvec).const_mul (Gamma (∑ _i : Fin 4, (1 / 2 : ℂ)))
  -- the right side
  have hR := tendsto_carlsonRF_zero_of_tendsto_slit (l := 𝓝[>] (0 : ℝ))
    (f := fun δ : ℝ => ((A + δ) * B + C * D) ^ 2)
    (g := fun δ : ℝ => ((A + δ) * C + B * D) ^ 2) (h := fun δ : ℝ => ((A + δ) * D + B * C) ^ 2)
    (hsq hY) (hsq hZ)
    (by
      have := ((((tendsto_const_nhds (x := A)).add hδ).mul (tendsto_const_nhds (x := B))).add
        (tendsto_const_nhds (x := C * D))).pow 2
      simpa [hX] using this)
    (by simpa using ((((tendsto_const_nhds (x := A)).add hδ).mul
        (tendsto_const_nhds (x := C))).add (tendsto_const_nhds (x := B * D))).pow 2)
    (by simpa using ((((tendsto_const_nhds (x := A)).add hδ).mul
        (tendsto_const_nhds (x := D))).add (tendsto_const_nhds (x := B * C))).pow 2)
    (by
      filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      rw [show (A + δ) * B + C * D = δ * B by linear_combination hX]
      exact hsq (by rw [re_ofReal_mul]; positivity))
  have hR2 := hR.const_mul 2
  have huniq := tendsto_nhds_unique (hL.congr' (by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    simp only [Function.comp]
    rw [← carlsonR, hpert δ hδ])) hR2
  rw [← carlsonR] at huniq
  rw [huniq]
  ring

end Carlson
