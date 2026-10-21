/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.RCAsymptotic
public import ToMathlib.Analysis.Polynomial.SlowSingularity
public import Mathlib.Algebra.MvPolynomial.Funext
public import ComplexAnalysis.RealUniqueness

/-!
# Independence of the elementary standard functions in Section 8.5

Carlson's proof of Theorem 8.5-4 uses the independence of `R_C(x,y)` and `x^(-1/2)`
over rational functions in the nodes. The logarithmic singularity of `R_C` at `y = 0`
proves this without assuming the full logarithmic expansion of `R_K`.

We first rule out a polynomial relation at each fixed positive `x`, then specialize
multivariate polynomials to obtain independence with polynomial coefficients in both nodes.
Clearing denominators gives the corresponding rational-coefficient statement.
-/

open Complex Filter Set Polynomial
open scoped Topology

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- The real value of `R_C(x,y)` diverges to infinity at its logarithmic boundary. -/
theorem tendsto_carlsonRC_re_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y : ℝ => (carlsonRC x y).re) (𝓝[>] 0) atTop := by
  have hs : 0 < 2 * Real.sqrt x := by positivity
  have hlog := tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hmain := (tendsto_const_nhds (x := Real.log (4 * x) / (2 * Real.sqrt x))).add_atTop
    (hlog.const_mul_atTop (show 0 < (2 * Real.sqrt x)⁻¹ by positivity))
  have h := (tendsto_carlsonRC_sub_log hx).add_atTop hmain
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  rw [Real.log_div (by positivity) hy.ne']
  dsimp only [Function.comp_def]
  ring

/-- The logarithmic singularity of `R_C(x,y)` is weaker than a pole. -/
theorem tendsto_mul_carlsonRC_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y : ℝ => (y : ℂ) * carlsonRC x y) (𝓝[>] 0) (𝓝 0) := by
  have hy : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hml : Tendsto (fun y : ℝ => y * Real.log y) (𝓝[>] 0) (𝓝 0) := by
    simpa using Real.continuous_mul_log.tendsto 0 |>.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hsmall := ((hy.mul_const (Real.log (4 * x))).sub hml).div_const (2 * Real.sqrt x)
  have herr := hy.mul (tendsto_carlsonRC_sub_log hx)
  have hreal : Tendsto (fun y : ℝ => y * (carlsonRC x y).re) (𝓝[>] 0) (𝓝 0) := by
    have h := herr.add hsmall
    simp only [zero_mul, mul_zero, sub_zero, zero_div, zero_add] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    rw [Real.log_div (by positivity) hy.ne']
    ring
  have h := (continuous_ofReal.tendsto 0).comp hreal
  simp only [ofReal_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  dsimp only [Function.comp_def]
  rw [carlsonRC_eq_euler hx hy, ofReal_re, ofReal_mul]

/-- At a fixed positive first node, `R_C` is not a rational function of its second node.
Only an eventual relation near the boundary is required. -/
theorem eq_zero_of_polynomial_mul_carlsonRC {x : ℝ} (hx : 0 < x) (q r : ℂ[X])
    (hrel : ∀ᶠ y : ℝ in 𝓝[>] 0,
      q.eval (y : ℂ) * carlsonRC x y = r.eval (y : ℂ)) : q = 0 := by
  apply Polynomial.eq_zero_of_slow_singularity ?_ (tendsto_mul_carlsonRC_zero hx) q r hrel
  exact tendsto_atTop_mono (fun y => (le_abs_self _).trans (abs_re_le_norm _))
    (tendsto_carlsonRC_re_zero hx)

/-- Specialize the first node of a bivariate polynomial, retaining the second as `X`. -/
private def polynomialInSecond (x : ℂ) : MvPolynomial (Fin 2) ℂ →+* ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C x, Polynomial.X]

/-- Evaluation commutes with specialization of the first node. -/
private theorem eval_polynomialInSecond (P : MvPolynomial (Fin 2) ℂ) (x y : ℂ) :
    (polynomialInSecond x P).eval y = P.eval (pair x y) := by
  change (Polynomial.evalRingHom y) (MvPolynomial.eval₂Hom _ _ P) = _
  rw [MvPolynomial.map_eval₂Hom]
  change MvPolynomial.eval₂Hom _ _ P = MvPolynomial.eval₂Hom (RingHom.id ℂ) (pair x y) P
  apply MvPolynomial.eval₂Hom_congr
  · ext c; simp
  · funext i; fin_cases i <;> simp [pair]
  · rfl

/-- A bivariate polynomial vanishing on positive real nodes is zero. -/
private theorem eq_zero_of_eval_pair_pos (P : MvPolynomial (Fin 2) ℂ)
    (hP : ∀ x y : ℝ, 0 < x → 0 < y → P.eval (pair x y) = 0) : P = 0 := by
  apply MvPolynomial.funext_set (fun _ => ofReal '' Ioi (0 : ℝ))
    (fun _ => (Set.Ioi_infinite (0 : ℝ)).image ofReal_injective.injOn)
  intro z hz
  obtain ⟨x, hx, hxz⟩ := hz 0 (Set.mem_univ _)
  obtain ⟨y, hy, hyz⟩ := hz 1 (Set.mem_univ _)
  have hzxy : z = pair x y := by
    funext i; fin_cases i <;> simp [pair, ← hxz, ← hyz]
  simpa only [hzxy, map_zero] using hP x y hx hy

/-- **Independence used in Theorem 8.5-4**: `R_C(x,y)` and `x^(-1/2)` are linearly
independent over polynomials in both nodes, hence over rational functions after clearing
denominators. It suffices that the relation hold on positive real nodes. -/
theorem carlsonRC_polynomial_independent (P Q : MvPolynomial (Fin 2) ℂ)
    (hrel : ∀ x y : ℝ, 0 < x → 0 < y →
      P.eval (pair x y) * carlsonRC x y +
        Q.eval (pair x y) * (x : ℂ) ^ (-1 / 2 : ℂ) = 0) : P = 0 ∧ Q = 0 := by
  have hP : P = 0 := by
    apply eq_zero_of_eval_pair_pos
    intro x y hx hy
    have he : polynomialInSecond x P = 0 := by
      apply eq_zero_of_polynomial_mul_carlsonRC hx _
        (-(polynomialInSecond x Q * Polynomial.C ((x : ℂ) ^ (-1 / 2 : ℂ))))
      filter_upwards [self_mem_nhdsWithin] with v (hv : 0 < v)
      rw [eval_neg, eval_mul, eval_C, eval_polynomialInSecond, eval_polynomialInSecond]
      linear_combination hrel x v hx hv
    have := congrArg (Polynomial.eval (y : ℂ)) he
    simpa only [eval_polynomialInSecond, eval_zero] using this
  refine ⟨hP, eq_zero_of_eval_pair_pos Q fun x y hx hy => ?_⟩
  have h := hrel x y hx hy
  rw [hP, map_zero, zero_mul, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_right (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr hx.ne')))

end Carlson.TwoVariable
