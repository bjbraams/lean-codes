/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.PolynomialGrowth
public import Carlson.Jacobi.EndpointBridge
public import Carlson.Jacobi.SecondKindLimits
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import TauCeti.Analysis.SpecialFunctions.Hermite.Orthogonality

/-!
# Hermite polynomials as limits of Jacobi polynomials

Carlson's monic Hermite polynomials `p̃ₙ = 2⁻ⁿ Hₙ` satisfy `p̃ₙ₊₂ = X p̃ₙ₊₁ - (n+1)/2 · p̃ₙ` and
form an Appell sequence. Integration by parts against `e^{-x²}` shows that they are orthogonal
to all polynomials of lower degree. The squared norm `n! 2⁻ⁿ √π` (Theorem 7.10-4) is obtained
from the probabilists' Hermite polynomials `Heₙ` by the scaling `2^{n/2} p̃ₙ(x) = Heₙ(√2 x)`,
using the Gaussian orthogonality in `TauCeti.Analysis.SpecialFunctions.Hermite.Orthogonality`. With
`α = β = t²` and endpoints `∓t`, Carlson's recurrence coefficients for the monic Jacobi
polynomials tend to those of the Hermite recurrence, which gives the limit Theorem 7.10-1.

## Main results

* `monicHermite`: Carlson's monic Hermite polynomials (Definition 7.10-2).
* `derivative_monicHermite_succ`: the Appell property.
* `iteratedDeriv_exp_neg_sq`: the Rodrigues formula (7.10-6).
* `sqrt_two_pow_mul_eval_monicHermite`: the scaling bridge to Mathlib's probabilists' Hermite
  polynomials `Polynomial.hermite`.
* `gaussianFunctional_monicHermite_mul_monicHermite`: Theorem 7.10-4, transported from the
  Gaussian orthogonality of `Polynomial.hermite` proved by the Tau Ceti contributors.
* `tendsto_eval_jacobiOn_monicHermite`: Theorem 7.10-1.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.10.
-/

@[expose] public noncomputable section
open Complex Set Filter Polynomial Finset MeasureTheory
open scoped Topology

namespace Carlson.TwoVariable

/-- Carlson's monic Hermite polynomials (Definition 7.10-2), `p̃ₙ = 2⁻ⁿ Hₙ`, defined by their
three-term recurrence `p̃ₙ₊₂ = X p̃ₙ₊₁ - (n+1)/2 · p̃ₙ`. -/
def monicHermite : ℕ → ℂ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => X * monicHermite (n + 1) - C (((n : ℂ) + 1) / 2) * monicHermite n

/-- The monic Hermite polynomial of degree zero. -/
@[simp] theorem monicHermite_zero : monicHermite 0 = 1 := rfl

/-- The monic Hermite polynomial of degree one. -/
@[simp] theorem monicHermite_one : monicHermite 1 = X := rfl

/-- The recurrence defining the monic Hermite polynomials. -/
theorem monicHermite_add_two (n : ℕ) :
    monicHermite (n + 2) = X * monicHermite (n + 1) - C (((n : ℂ) + 1) / 2) * monicHermite n :=
  rfl

/-- The monic Hermite polynomials form an Appell sequence: `p̃ₙ₊₁' = (n+1) p̃ₙ`. -/
theorem derivative_monicHermite_succ (n : ℕ) :
    derivative (monicHermite (n + 1)) = C ((n : ℂ) + 1) * monicHermite n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp
    · simp [monicHermite_add_two, derivative_mul]; ring
    · rw [monicHermite_add_two, derivative_sub, derivative_mul, derivative_X, one_mul,
        derivative_C_mul, ih (n + 1) (by omega), ih n (by omega)]
      have hH := monicHermite_add_two n
      generalize monicHermite (n + 2) = H at *
      subst hH
      push_cast
      simp only [div_eq_mul_inv, map_add, map_mul, map_natCast, map_one]
      ring

/-- The monic Hermite polynomials have degree at most `n` and leading coefficient one. -/
theorem natDegree_monicHermite_le_and_coeff (n : ℕ) :
    (monicHermite n).natDegree ≤ n ∧ (monicHermite n).coeff n = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp
    · simp
    · obtain ⟨h1, c1⟩ := ih (n + 1) (by omega)
      obtain ⟨h0, -⟩ := ih n (by omega)
      rw [monicHermite_add_two]
      constructor
      · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · exact natDegree_mul_le.trans (by rw [natDegree_X]; omega)
        · exact (natDegree_C_mul_le _ _).trans (by omega)
      · rw [coeff_sub, coeff_X_mul, c1, coeff_C_mul,
          coeff_eq_zero_of_natDegree_lt (by omega : (monicHermite n).natDegree < n + 2)]
        simp

/-- Polynomials are integrable against the Gaussian `e^{-x²}`. -/
theorem integrable_eval_mul_gaussian (p : ℂ[X]) :
    Integrable (fun x : ℝ => p.eval (x : ℂ) * exp (-(x : ℂ) ^ 2)) := by
  conv => arg 1; ext x; rw [p.as_sum_range_C_mul_X_pow]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, sum_mul]
  refine integrable_finsetSum _ (fun k _ => ?_)
  have hk : Integrable (fun x : ℝ => ((x ^ k * Real.exp (-1 * x ^ 2) : ℝ) : ℂ)) := by
    refine Integrable.ofReal ?_
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := (k : ℝ))
      (by linarith [Nat.cast_nonneg (α := ℝ) k])
    simp only [Real.rpow_natCast] at h
    exact h
  refine (hk.const_mul (p.coeff k)).congr (Eventually.of_forall fun x => ?_)
  simp only [ofReal_mul, ofReal_pow, ofReal_exp, ofReal_neg, neg_mul, one_mul]
  ring

/-- Carlson's Gaussian functional `h ↦ ∫ h(x) e^{-x²} dx`. -/
def gaussianFunctional (p : ℂ[X]) : ℂ :=
  ∫ x : ℝ, p.eval (x : ℂ) * exp (-(x : ℂ) ^ 2)

/-- The Gaussian functional is additive for differences. -/
theorem gaussianFunctional_sub (p q : ℂ[X]) :
    gaussianFunctional (p - q) = gaussianFunctional p - gaussianFunctional q := by
  simp only [gaussianFunctional, eval_sub, sub_mul]
  exact integral_sub (integrable_eval_mul_gaussian p) (integrable_eval_mul_gaussian q)

/-- The Gaussian functional is additive. -/
theorem gaussianFunctional_add (p q : ℂ[X]) :
    gaussianFunctional (p + q) = gaussianFunctional p + gaussianFunctional q := by
  simp only [gaussianFunctional, eval_add, add_mul]
  exact integral_add (integrable_eval_mul_gaussian p) (integrable_eval_mul_gaussian q)

/-- The Gaussian functional is homogeneous. -/
theorem gaussianFunctional_C_mul (c : ℂ) (p : ℂ[X]) :
    gaussianFunctional (C c * p) = c * gaussianFunctional p := by
  simp only [gaussianFunctional, eval_mul, eval_C, mul_assoc]
  exact integral_const_mul c _

/-- Integration by parts against the Gaussian: `∫ x h(x) e^{-x²} = ½ ∫ h'(x) e^{-x²}`. -/
theorem gaussianFunctional_X_mul (p : ℂ[X]) :
    gaussianFunctional (X * p) = gaussianFunctional (derivative p) / 2 := by
  have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => p.eval (y : ℂ)) ((derivative p).eval (x : ℂ)) x :=
    fun x => (p.hasDerivAt (x : ℂ)).comp_ofReal
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => exp (-(y : ℂ) ^ 2))
      (-2 * (x : ℂ) * exp (-(x : ℂ) ^ 2)) x := by
    intro x
    have hg : HasDerivAt (fun z : ℂ => -z ^ 2) (-(2 * (x : ℂ))) (x : ℂ) := by
      have := (hasDerivAt_pow 2 (x : ℂ)).fun_neg
      simpa using this
    have h' := hg.cexp.comp_ofReal
    convert h' using 1
    ring
  have hint := integral_mul_deriv_eq_deriv_mul_of_integrable (A := ℂ)
    (u := fun y : ℝ => p.eval (y : ℂ)) (v := fun y : ℝ => exp (-(y : ℂ) ^ 2))
    (u' := fun y : ℝ => (derivative p).eval (y : ℂ))
    (v' := fun y : ℝ => -2 * (y : ℂ) * exp (-(y : ℂ) ^ 2))
    (fun x _ => hu x) (fun x _ => hv x)
    (by
      refine ((integrable_eval_mul_gaussian (X * p)).const_mul (-2)).congr
        (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply, eval_mul, eval_X]; ring)
    (integrable_eval_mul_gaussian _) (integrable_eval_mul_gaussian _)
  have h1 : (∫ x : ℝ, p.eval (x : ℂ) * (-2 * (x : ℂ) * exp (-(x : ℂ) ^ 2))) =
      -2 * gaussianFunctional (X * p) := by
    rw [gaussianFunctional, ← integral_const_mul]
    congr 1; funext x; simp only [eval_mul, eval_X]; ring
  rw [h1] at hint
  unfold gaussianFunctional at hint ⊢
  linear_combination -hint / 2

/-- The monic Hermite polynomials are orthogonal to all polynomials of lower degree. -/
theorem gaussianFunctional_mul_monicHermite_eq_zero (n : ℕ) :
    ∀ q : ℂ[X], q.natDegree < n → gaussianFunctional (q * monicHermite n) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q hq
    rcases n with _ | _ | n
    · omega
    · have hq0 : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
      rw [hq0, monicHermite_one, gaussianFunctional_C_mul, show (X : ℂ[X]) = X * 1 by ring,
        gaussianFunctional_X_mul]
      simp [gaussianFunctional]
    · have hq' : (derivative q).natDegree < n + 1 :=
        (natDegree_derivative_le q).trans_lt (by omega)
      rw [monicHermite_add_two, mul_sub, gaussianFunctional_sub,
        show q * (X * monicHermite (n + 1)) = X * (q * monicHermite (n + 1)) by ring,
        gaussianFunctional_X_mul, derivative_mul, derivative_monicHermite_succ,
        gaussianFunctional_add, ih (n + 1) (by omega) _ hq',
        show q * (C ((n : ℂ) + 1) * monicHermite n) = C ((n : ℂ) + 1) * (q * monicHermite n) by
          ring,
        show q * (C (((n : ℂ) + 1) / 2) * monicHermite n) =
          C (((n : ℂ) + 1) / 2) * (q * monicHermite n) by ring,
        gaussianFunctional_C_mul, gaussianFunctional_C_mul]
      ring

/-- The scaling bridge to the probabilists' Hermite polynomials `Polynomial.hermite`:
`2^{n/2} p̃ₙ(z) = Heₙ(√2 z)`. -/
theorem sqrt_two_pow_mul_eval_monicHermite (n : ℕ) (z : ℂ) :
    (Real.sqrt 2 : ℂ) ^ n * (monicHermite n).eval z =
      aeval ((Real.sqrt 2 : ℂ) * z) (hermite n) := by
  have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [monicHermite]
    | 1, _ => simp [monicHermite]
    | n + 2, ih =>
      rw [monicHermite_add_two, hermite_add_two, map_sub, map_mul, aeval_X, map_nsmul,
        nsmul_eq_mul, ← ih (n + 1) (by omega), ← ih n (by omega)]
      simp only [eval_sub, eval_mul, eval_X, eval_C]
      push_cast
      linear_combination (-((n : ℂ) + 1) * (Real.sqrt 2 : ℂ) ^ n *
        (monicHermite n).eval z / 2) * h2

/-- Carlson's Theorem 7.10-4: the monic Hermite polynomials are orthogonal on the real line with
respect to `e^{-x²}`, with squared norm `n! 2⁻ⁿ √π`. This is the Tau Ceti contributors'
`TauCeti.integral_hermite_mul_hermite_mul_gaussian`, transported by
`sqrt_two_pow_mul_eval_monicHermite` and the substitution `y = √2 x`. -/
theorem gaussianFunctional_monicHermite_mul_monicHermite (m n : ℕ) :
    gaussianFunctional (monicHermite m * monicHermite n) =
      if m = n then (n.factorial : ℂ) / 2 ^ n * (Real.sqrt Real.pi : ℂ) else 0 := by
  set s : ℝ := Real.sqrt 2 with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr two_pos
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt zero_le_two
  set F : ℝ → ℝ := fun y => aeval y (hermite m) * aeval y (hermite n) * Real.exp (-(y ^ 2 / 2))
  have hc (y : ℝ) (p : ℤ[X]) : ((aeval y p : ℝ) : ℂ) = aeval (y : ℂ) p := by
    simpa using (aeval_algebraMap_apply ℂ y p).symm
  have hpt (x : ℝ) : ((F (s * x) : ℝ) : ℂ) = (s : ℂ) ^ (m + n) *
      ((monicHermite m * monicHermite n).eval (x : ℂ) * exp (-(x : ℂ) ^ 2)) := by
    have he : (s * x) ^ 2 / 2 = x ^ 2 := by rw [mul_pow, hs2]; ring
    have hb (k : ℕ) := sqrt_two_pow_mul_eval_monicHermite k (x : ℂ)
    rw [← hs_def] at hb
    simp only [F, he, ofReal_mul, ofReal_exp, hc, ofReal_neg, ofReal_pow, eval_mul, ← hb]
    ring
  have hint : gaussianFunctional (monicHermite m * monicHermite n) * (s : ℂ) ^ (m + n) =
      ((s⁻¹ * ∫ y, F y : ℝ) : ℂ) := by
    rw [← abs_of_pos (inv_pos.mpr hs),
      show |s⁻¹| * ∫ y, F y = |s⁻¹| • ∫ y, F y from rfl, ← Measure.integral_comp_mul_left,
      ← integral_complex_ofReal]
    simp only [hpt, integral_const_mul, gaussianFunctional]
    ring
  rw [TauCeti.integral_hermite_mul_hermite_mul_gaussian] at hint
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  split_ifs at hint ⊢ with hmn
  · subst hmn
    have hsq : (s : ℂ) ^ (m + m) = 2 ^ m := by
      rw [← two_mul, pow_mul, ← ofReal_pow, hs2]; norm_num
    have hpi : Real.sqrt (2 * Real.pi) = s * Real.sqrt Real.pi :=
      Real.sqrt_mul zero_le_two _
    rw [hsq, hpi] at hint
    push_cast at hint
    field_simp at hint ⊢
    linear_combination hint
  · simpa [hs0] using hint

/-- The Jacobi recurrence coefficient `W` for the symmetric Hermite scaling tends to `(n+1)/2`. -/
theorem tendsto_jacobiRecurrenceW_hermite (n : ℕ) :
    Tendsto (fun t : ℝ => jacobiRecurrenceW ((t : ℂ) ^ 2) ((t : ℂ) ^ 2) (-t) t n) atTop
      (𝓝 (((n : ℂ) + 1) / 2)) := by
  have hinv : Tendsto (fun u : ℝ => ((u : ℂ))⁻¹) atTop (𝓝 0) := by
    have h := (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simp only [ofReal_zero] at h
    exact h.congr (fun u => by simp)
  have hA : Tendsto (fun u : ℝ => (2 + (n + 1) * (u : ℂ)⁻¹) / (2 + (2 * n + 1) * (u : ℂ)⁻¹))
      atTop (𝓝 ((2 + (n + 1) * 0) / (2 + (2 * n + 1) * 0))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).div
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)) (by norm_num)
  have hB : Tendsto (fun u : ℝ => 1 / (2 + (2 * n + 3) * (u : ℂ)⁻¹))
      atTop (𝓝 (1 / (2 + (2 * n + 3) * 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)) (by norm_num)
  have hAB := ((hA.mul hB).const_mul ((n : ℂ) + 1)).comp
    (tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num))
  have hlim : Tendsto (fun t : ℝ => ((n : ℂ) + 1) * ((2 + (n + 1) * ((t ^ 2 : ℝ) : ℂ)⁻¹) /
      (2 + (2 * n + 1) * ((t ^ 2 : ℝ) : ℂ)⁻¹) * (1 / (2 + (2 * n + 3) * ((t ^ 2 : ℝ) : ℂ)⁻¹))))
      atTop (𝓝 (((n : ℂ) + 1) / 2)) := by
    have hval : ((n : ℂ) + 1) * ((2 + (n + 1) * 0) / (2 + (2 * n + 1) * 0) *
        (1 / (2 + (2 * n + 3) * 0))) = ((n : ℂ) + 1) / 2 := by ring
    rw [hval] at hAB
    exact hAB
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with t ht
  · simp only [jacobiRecurrenceW]
    have hu : ((t ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (pow_ne_zero 2 ht)
    push_cast at hu ⊢
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
    have h1 : (t : ℂ) ^ 2 + (t : ℂ) ^ 2 + 2 * n + 2 ≠ 0 := by
      have : (0 : ℝ) < t ^ 2 + t ^ 2 + 2 * n + 2 := by positivity
      exact_mod_cast this.ne'
    have h2 : (t : ℂ) ^ 2 + (t : ℂ) ^ 2 + 2 * n + 1 ≠ 0 := by
      have : (0 : ℝ) < t ^ 2 + t ^ 2 + 2 * n + 1 := by positivity
      exact_mod_cast this.ne'
    have h3 : (t : ℂ) ^ 2 + (t : ℂ) ^ 2 + 2 * n + 3 ≠ 0 := by
      have : (0 : ℝ) < t ^ 2 + t ^ 2 + 2 * n + 3 := by positivity
      exact_mod_cast this.ne'
    have e1 : 2 + ((n : ℂ) + 1) * ((t : ℂ) ^ 2)⁻¹ =
        ((t : ℂ) ^ 2 + (t : ℂ) ^ 2 + n + 1) / t ^ 2 := by
      field_simp; ring
    have e2 : 2 + (2 * (n : ℂ) + 1) * ((t : ℂ) ^ 2)⁻¹ =
        ((t : ℂ) ^ 2 + (t : ℂ) ^ 2 + 2 * n + 1) / t ^ 2 := by field_simp; ring
    have e3 : 2 + (2 * (n : ℂ) + 3) * ((t : ℂ) ^ 2)⁻¹ =
        ((t : ℂ) ^ 2 + (t : ℂ) ^ 2 + 2 * n + 3) / t ^ 2 := by field_simp; ring
    have e4 : (t : ℂ) ^ 2 + (t : ℂ) ^ 2 + 2 * n + 2 = 2 * ((t : ℂ) ^ 2 + n + 1) := by ring
    have e5 : (-(t : ℂ) - t) ^ 2 = 4 * (t : ℂ) ^ 2 := by ring
    have hP : (t : ℂ) ^ 2 + n + 1 ≠ 0 := by
      have : (0 : ℝ) < t ^ 2 + n + 1 := by positivity
      exact_mod_cast this.ne'
    rw [e1, e2, e3, e4, e5]
    generalize (t : ℂ) ^ 2 + n + 1 = P at *
    generalize (t : ℂ) ^ 2 + (t : ℂ) ^ 2 + 2 * n + 1 = D1 at *
    generalize (t : ℂ) ^ 2 + (t : ℂ) ^ 2 + 2 * n + 3 = D3 at *
    rw [show (t : ℂ) ^ 2 + (t : ℂ) ^ 2 + n + 1 = (t : ℂ) ^ 2 + n + 1 + (t : ℂ) ^ 2 by ring]
    generalize (t : ℂ) ^ 2 = u at *
    field_simp
    ring

/-- Carlson's Theorem 7.10-1: the monic Hermite polynomial is the limit of the monic Jacobi
polynomials with endpoints `∓t` and parameters `α = β = t²` as `t → ∞`. -/
theorem tendsto_eval_jacobiOn_monicHermite (x : ℂ) (n : ℕ) :
    Tendsto (fun t : ℝ => (jacobiOn ((t : ℂ) ^ 2) ((t : ℂ) ^ 2) (-t) t n).eval x) atTop
      (𝓝 ((monicHermite n).eval x)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [jacobiOn_zero]
    · refine tendsto_const_nhds.congr (fun t => ?_)
      have ht2 : (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) := by push_cast; ring
      have hpos : (0 : ℝ) < t ^ 2 + t ^ 2 + 2 := by positivity
      have hP : (ascPochhammer ℂ 1).eval ((t : ℂ) ^ 2 + (t : ℂ) ^ 2 + (1 : ℕ) + 1) ≠ 0 := by
        simp only [ascPochhammer_one, eval_X, Nat.cast_one, ht2]
        exact_mod_cast (show (t ^ 2 + t ^ 2 + 1 + 1 : ℝ) ≠ 0 by linarith)
      have hne : (ascPochhammer ℂ 1).eval (-(t : ℂ) ^ 2 - (t : ℂ) ^ 2 - 2 * (1 : ℕ)) ≠ 0 := by
        simp only [ascPochhammer_one, eval_X, Nat.cast_one, ht2]
        exact_mod_cast (show (-(t ^ 2) - t ^ 2 - 2 * 1 : ℝ) ≠ 0 by linarith)
      rw [eval_jacobiOn_eq_numerator _ _ _ _ _ _ hP, carlsonRPolynomialNumerator₂,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rw [eq_div_iff hne]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ascPochhammer_one,
        ascPochhammer_zero, eval_X, eval_one, Nat.choose_one_right, Nat.choose_zero_right,
        monicHermite_one, pow_zero, pow_one, Nat.cast_one, Nat.sub_self, Nat.sub_zero]
      ring

    · have hrec : ∀ t : ℝ, (jacobiOn ((t : ℂ) ^ 2) ((t : ℂ) ^ 2) (-t) t (n + 2)).eval x =
          x * (jacobiOn ((t : ℂ) ^ 2) ((t : ℂ) ^ 2) (-t) t (n + 1)).eval x -
            jacobiRecurrenceW ((t : ℂ) ^ 2) ((t : ℂ) ^ 2) (-t) t n *
              (jacobiOn ((t : ℂ) ^ 2) ((t : ℂ) ^ 2) (-t) t n).eval x := by
        intro t
        have hre (m : ℕ) : 0 < ((t : ℂ) ^ 2 + (t : ℂ) ^ 2 + (m : ℂ) + 1).re := by
          rw [show (t : ℂ) ^ 2 + (t : ℂ) ^ 2 + (m : ℂ) + 1 = ((t ^ 2 + t ^ 2 + m + 1 : ℝ) : ℂ) by
            push_cast; ring, ofReal_re]
          positivity
        rw [eval_jacobiOn_three_term _ _ _ _ x n
          (ascPochhammer_eval_ne_zero_of_re_pos (hre n) n)
          (ascPochhammer_eval_ne_zero_of_re_pos (hre (n + 1)) _)
          (ascPochhammer_eval_ne_zero_of_re_pos (hre (n + 2)) _)
          (fun h => by
            have := hre (2 * n)
            rw [show (t : ℂ) ^ 2 + (t : ℂ) ^ 2 + ((2 * n : ℕ) : ℂ) + 1 =
              (t : ℂ) ^ 2 + (t : ℂ) ^ 2 + 2 * n + 1 by push_cast; ring, h] at this
            simp at this)]
        simp only [jacobiRecurrenceV]
        ring_nf
      simp only [hrec, monicHermite_add_two, eval_sub, eval_mul, eval_X, eval_C]
      exact ((tendsto_const_nhds.mul (ih (n + 1) (by omega))).sub
        ((tendsto_jacobiRecurrenceW_hermite n).mul (ih n (by omega))))

/-- Hermite raising: `p̃ₙ₊₁ = X p̃ₙ - p̃ₙ' / 2`. -/
theorem monicHermite_succ_eq (n : ℕ) :
    monicHermite (n + 1) = X * monicHermite n - C (1 / 2 : ℂ) * derivative (monicHermite n) := by
  rcases n with _ | n
  · simp
  · rw [derivative_monicHermite_succ, monicHermite_add_two, ← mul_assoc, ← C_mul]
    congr 3
    ring

/-- Derivative of the complex function `(-2)ʲ e^{-w²} p̃ⱼ(w)`. -/
theorem hasDerivAt_hermiteGaussian (j : ℕ) (w : ℂ) :
    HasDerivAt (fun w : ℂ => (-2 : ℂ) ^ j * cexp (-w ^ 2) * (monicHermite j).eval w)
      ((-2 : ℂ) ^ (j + 1) * cexp (-w ^ 2) * (monicHermite (j + 1)).eval w) w := by
  have he : HasDerivAt (fun x : ℂ => cexp (-x ^ 2)) (cexp (-w ^ 2) * (-(2 * w))) w := by
    simpa using ((hasDerivAt_pow 2 w).neg).cexp
  have hd := (he.const_mul ((-2 : ℂ) ^ j)).fun_mul (Polynomial.hasDerivAt (monicHermite j) w)
  convert hd using 1
  rw [monicHermite_succ_eq]
  simp only [eval_sub, eval_mul, eval_X, eval_C]
  ring

/-- **Rodrigues' formula for Hermite polynomials** (7.10-6): `Dⁿ e^{-x²} = (-2)ⁿ e^{-x²} p̃ₙ(x)`. -/
theorem iteratedDeriv_exp_neg_sq (n : ℕ) :
    iteratedDeriv n (fun x : ℂ => cexp (-x ^ 2)) =
      fun x => (-2 : ℂ) ^ n * cexp (-x ^ 2) * (monicHermite n).eval x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    funext x
    rw [iteratedDeriv_succ, ih, (hasDerivAt_hermiteGaussian n x).deriv]

end Carlson.TwoVariable
