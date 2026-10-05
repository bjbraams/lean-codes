/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.EllipseCoefficient
public import Carlson.Jacobi.SecondKindLimits
public import Carlson.Jacobi.Chebyshev
public import Carlson.Jacobi.Normalization
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Fourier cosine series as Jacobi series

At `α = β = -1/2` the monic Jacobi polynomials with foci `A ∓ B` satisfy
`pₙ(A + B cos θ) = Bⁿ cos (nθ) / 2ⁿ⁻¹`, and the set `{A + B cos θ : |Im θ| < h}` is the open
elliptic disk with those foci and mean radius `|B| e^h / 2`. The Jacobi expansion of a function
holomorphic there, with its coefficients as Dirichlet averages of derivatives, is therefore a
Fourier cosine series: Carlson's Example 7.7-2, equation (5).

## Main results

* `eval_jacobiOn_affine_monicJacobi`: rescaling of the endpoints.
* `eval_monicJacobi_neg_half_cos`: the monic Chebyshev polynomials.
* `jacobiEllipseRadius_add_mul_cos`: the mean radius of `A + B cos θ`.
* `hasSum_fourier_cosine`: Example 7.7-2, equation (5).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Example 7.7-2.
-/

@[expose] public noncomputable section
open Complex Set Filter Polynomial Dirichlet
open scoped Topology

namespace Carlson.TwoVariable

/-- Carlson's two-node numerator is homogeneous of degree `n` in the node differences. -/
theorem carlsonRPolynomialNumerator₂_mul (n : ℕ) (b₀ b₁ x y c : ℂ) :
    carlsonRPolynomialNumerator₂ n b₀ b₁ (c * x) (c * y) =
      c ^ n * carlsonRPolynomialNumerator₂ n b₀ b₁ x y := by
  simp only [carlsonRPolynomialNumerator₂, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [← Finset.mem_antidiagonal.mp hij, pow_add, mul_pow, mul_pow]
  ring

/-- On the segment with endpoints `A ∓ B`, the monic Jacobi polynomials are rescaled standard
monic Jacobi polynomials: `pₙ(A + B w) = Bⁿ p̂ₙ(w)`. -/
theorem eval_jacobiOn_affine_monicJacobi (α β A B w : ℂ) (n : ℕ)
    (h : (ascPochhammer ℂ n).eval (α + β + n + 1) ≠ 0) :
    (jacobiOn α β (A - B) (A + B) n).eval (A + B * w) = B ^ n * (monicJacobi α β n).eval w := by
  rw [eval_jacobiOn_eq_numerator _ _ _ _ _ _ h, eval_monicJacobi_eq_numerator,
    show A + B * w - (A - B) = B * (w + 1) by ring, show A + B * w - (A + B) = B * (w - 1) by ring,
    carlsonRPolynomialNumerator₂_mul, mul_div_assoc]

/-- The monic Chebyshev polynomial of the first kind: `p̂ₙ(cos θ) = cos (nθ) / 2ⁿ⁻¹` for
`n ≥ 1`, at `α = β = -1/2`. -/
theorem eval_monicJacobi_neg_half_cos (n : ℕ) (hn : n ≠ 0) (θ : ℂ) :
    (monicJacobi (-1 / 2 : ℂ) (-1 / 2) n).eval (cos θ) = cos (n * θ) / 2 ^ (n - 1) := by
  have hP : (ascPochhammer ℂ n).eval ((-1 / 2 : ℂ) + -1 / 2 + n + 1) ≠ 0 := by
    rw [show (-1 / 2 + -1 / 2 + n + 1 : ℂ) = n by ring]
    apply ascPochhammer_eval_ne_zero_of_re_pos
    simp only [natCast_re]; exact_mod_cast Nat.pos_of_ne_zero hn
  have hmon := monic_monicJacobi (-1 / 2 : ℂ) (-1 / 2) n hP
  set c : ℂ := (2 ^ n * n.factorial : ℂ) /
    (ascPochhammer ℂ n).eval ((-1 / 2 : ℂ) + -1 / 2 + n + 1) *
    ((ascPochhammer ℂ n).eval (1 / 2) / n.factorial)
  have he : monicJacobi (-1 / 2 : ℂ) (-1 / 2) n = C c * Chebyshev.T ℂ n := by
    rw [monicJacobi, jacobi_neg_half_eq_chebyshev_T, ← mul_assoc, ← C_mul]
  have hlc : c * 2 ^ (n - 1) = 1 := by
    have h1 := hmon.leadingCoeff
    rw [he, leadingCoeff_mul, leadingCoeff_C, Chebyshev.leadingCoeff_T] at h1
    simpa using h1
  rw [he, eval_mul, eval_C, Chebyshev.T_complex_cos]
  have h2 : (2 : ℂ) ^ (n - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [eq_div_iff h2]
  push_cast
  linear_combination cos (n * θ) * hlc

/-- The points `A + B cos θ` lie on the confocal ellipse with foci `A ∓ B` of mean radius
`|B| e^{|Im θ|} / 2`. -/
theorem jacobiEllipseRadius_add_mul_cos (A B : ℂ) (hB : B ≠ 0) (θ : ℂ) :
    jacobiEllipseRadius (A - B) (A + B) (A + B * cos θ) = ‖B‖ * Real.exp |θ.im| / 2 := by
  set w := B * exp (θ * I) / 2
  have he : ‖exp (θ * I)‖ = Real.exp (-θ.im) := by
    rw [norm_exp]; congr 1; simp
  have hw0 : w ≠ 0 := by simp [w, hB, exp_ne_zero]
  have hJ : jacobiJoukowski (A - B) (A + B) w = A + B * cos θ := by
    simp only [jacobiJoukowski, w, cos]
    have hx : exp (θ * I) ≠ 0 := exp_ne_zero _
    rw [show -θ * I = -(θ * I) by ring, exp_neg]
    field_simp
    ring
  rw [← hJ, jacobiEllipseRadius_jacobiJoukowski_eq_max _ _ _ hw0]
  have hnw : ‖w‖ = ‖B‖ * Real.exp (-θ.im) / 2 := by
    simp only [w, norm_div, norm_mul, he, RCLike.norm_ofNat]
  have hrs : ‖A - B - (A + B)‖ = 2 * ‖B‖ := by
    rw [show A - B - (A + B) = -2 * B by ring, norm_mul, norm_neg, RCLike.norm_ofNat]
  rw [hnw, hrs]
  have hBpos : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have h2 : (2 * ‖B‖) ^ 2 / (16 * (‖B‖ * Real.exp (-θ.im) / 2)) = ‖B‖ * Real.exp θ.im / 2 := by
    rw [Real.exp_neg]
    field_simp
    ring
  rw [h2]
  rcases le_total 0 θ.im with h | h
  · rw [abs_of_nonneg h, max_eq_right]
    gcongr; linarith
  · rw [abs_of_nonpos h, max_eq_left]
    gcongr; linarith

/-- Carlson's Example 7.7-2, equation (5): a function holomorphic on the elliptic disk
`{A + B cos θ : |Im θ| < h}` has the Fourier cosine expansion
`f(A + B cos θ) = F(½, ½; A+B, A−B) + 2 Σₙ Bⁿ/(n! 2ⁿ) F⁽ⁿ⁾(½+n, ½+n; A+B, A−B) cos nθ`,
with the coefficients Dirichlet averages of the derivatives of `f`. -/
theorem hasSum_fourier_cosine (A B : ℂ) (hB : B ≠ 0) {h : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (jacobiEllipseDisk (A - B) (A + B) (‖B‖ * Real.exp h / 2)))
    {θ : ℂ} (hθ : |θ.im| < h) :
    HasSum (fun n : ℕ => (if n = 0 then 1 else 2) * (B ^ n / (n.factorial * 2 ^ n)) *
      carlsonDirichletAverage (pair (1 / 2 + n) (1 / 2 + n)) (pair (A - B) (A + B))
        (iteratedDeriv n f) * cos (n * θ)) (f (A + B * cos θ)) := by
  set τ := ‖B‖ * Real.exp h / 2
  set μx := jacobiEllipseRadius (A - B) (A + B) (A + B * cos θ)
  have hμx : μx = ‖B‖ * Real.exp |θ.im| / 2 := jacobiEllipseRadius_add_mul_cos A B hB θ
  have hBpos : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hμτ : μx < τ := by rw [hμx]; simp only [τ]; gcongr
  have hmin : ‖A - B - (A + B)‖ / 4 ≤ μx := le_jacobiEllipseRadius _ _ _
  set σ := (μx + τ) / 2
  have hσ0 : 0 < σ := by
    have := norm_nonneg (A - B - (A + B)); simp only [σ]; linarith
  have hσ : ‖A - B - (A + B)‖ / 4 < σ := by simp only [σ]; linarith
  have hστ : σ < τ := by simp only [σ]; linarith
  have hxσ : μx < σ := by simp only [σ]; linarith
  have hc : IsGammaRegular ((-1 / 2 : ℂ) + -1 / 2 + 2) := by
    intro k hk
    have := congrArg re hk
    simp at this
    norm_num at this
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have H := hasSum_jacobiContourCoefficient_jacobiEllipseCycle (-1 / 2) (-1 / 2) (A - B) (A + B)
    hc hf hσ0 hσ hστ hxσ
  convert H using 1
  funext n
  have hre : 0 < ((-1 / 2 : ℂ) + n + 1).re := by
    simp only [add_re, natCast_re, one_re, div_re]; norm_num
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [jacobiContourCoefficient_jacobiEllipseCycle_eq_average (-1 / 2) (-1 / 2) (A - B) (A + B) n
    hre hre hf hσ0 hσ hστ]
  have hpair : pair ((-1 / 2 : ℂ) + n + 1) ((-1 / 2 : ℂ) + n + 1) =
      pair (1 / 2 + n) (1 / 2 + n) := by
    congr 1 <;> ring
  rw [hpair]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [jacobiOn_zero]
  · have hP : (ascPochhammer ℂ n).eval ((-1 / 2 : ℂ) + -1 / 2 + n + 1) ≠ 0 := by
      rw [show ((-1 / 2 : ℂ) + -1 / 2 + n + 1) = n by ring]
      apply ascPochhammer_eval_ne_zero_of_re_pos
      simp only [natCast_re]; exact_mod_cast hn
    rw [eval_jacobiOn_affine_monicJacobi _ _ A B (cos θ) n hP,
      eval_monicJacobi_neg_half_cos n hn.ne' θ, ite_eq_right hn.ne']
    have hpow : (2 : ℂ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow]
    have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h2 : (2 : ℂ) ^ (n - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp

end Carlson.TwoVariable
