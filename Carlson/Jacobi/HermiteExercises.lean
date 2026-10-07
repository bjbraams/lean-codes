/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Hermite
public import Carlson.Jacobi.GegenbauerRecurrence
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Complex.TaylorSeries
public import Carlson.RPolynomial.Growth
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Hermite polynomials in the standard normalization (Exercises 7.10-1 – 7.10-6)

Carlson's Hermite polynomial is `Hₙ = 2ⁿ p̃ₙ`. The generating function follows from Rodrigues'
formula and the Taylor series of `e^{-w²}`; absolute convergence comes from the comparison
`|p̃ₙ(x)| ≤ |p̃ₙ(i|x|)|`.

## Main results

* `Carlson.TwoVariable.gaussianFunctional_X_pow`: Exercise 7.10-1.
* `Carlson.TwoVariable.gaussianFunctional_affine_pow`: Exercise 7.10-2.
* `Carlson.TwoVariable.hasSum_carlsonHermite_generating`: Exercise 7.10-4.
* `Carlson.TwoVariable.tendsto_gegenbauer_hermite`: Exercise 7.10-5, the Hermite polynomials as
  limits of Gegenbauer polynomials.
* `Carlson.TwoVariable.carlsonHermite_addition`: Exercise 7.10-6.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.10.
-/

open Complex Polynomial Finset Filter
open scoped Topology

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- Carlson's (physicists') Hermite polynomial `Hₙ = 2ⁿ p̃ₙ`. -/
def carlsonHermite (n : ℕ) : ℂ[X] := C (2 ^ n) * monicHermite n

/-- **Exercise 7.10-4**: the generating relation
`e^{2xt - t²} = ∑ₙ tⁿ 2ⁿ/n! p̃ₙ(x) = ∑ₙ tⁿ/n! Hₙ(x)`, for all complex `t, x`. -/
theorem hasSum_carlsonHermite_generating (t x : ℂ) :
    HasSum (fun n : ℕ => t ^ n / n.factorial * (carlsonHermite n).eval x)
      (exp (2 * x * t - t ^ 2)) := by
  have hg : Differentiable ℂ (fun w : ℂ => cexp (-w ^ 2)) := by fun_prop
  have h := Complex.hasSum_taylorSeries_of_entire hg x (x - t)
  have h2 := h.mul_left (cexp (x ^ 2))
  have hval : cexp (x ^ 2) * cexp (-(x - t) ^ 2) = exp (2 * x * t - t ^ 2) := by
    rw [← exp_add]; ring_nf
  rw [hval] at h2
  refine h2.congr_fun fun n => ?_
  rw [iteratedDeriv_exp_neg_sq, carlsonHermite, eval_mul, eval_C]
  simp only [smul_eq_mul, sub_sub_cancel_left]
  have he : cexp (x ^ 2) * cexp (-x ^ 2) = 1 := by rw [← exp_add]; simp
  have hre : cexp (x ^ 2) * ((n.factorial : ℂ)⁻¹ * ((-t) ^ n * ((-2 : ℂ) ^ n * cexp (-x ^ 2) *
      (monicHermite n).eval x))) = ((-t) * (-2)) ^ n * (cexp (x ^ 2) * cexp (-x ^ 2)) *
        (monicHermite n).eval x / n.factorial := by rw [mul_pow]; ring
  rw [hre, he, show (-t) * (-2 : ℂ) = 2 * t by ring, mul_pow]
  ring

/-- On the imaginary axis the monic Hermite polynomials have the form `p̃ₙ(iy) = iⁿ rₙ(y)` with
the nonnegative recurrence `r_{n+2} = y r_{n+1} + (n + 1)/2 rₙ`, so that
`|p̃ₙ(x)| ≤ |p̃ₙ(i|x|)|`. -/
theorem norm_eval_monicHermite_le (n : ℕ) (x : ℂ) :
    ‖(monicHermite n).eval x‖ ≤ ‖(monicHermite n).eval (I * ‖x‖)‖ ∧
      (monicHermite n).eval (I * ‖x‖) = I ^ n * ‖(monicHermite n).eval (I * ‖x‖)‖ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp
    · simp [Complex.norm_real]
    · obtain ⟨h1, e1⟩ := ih (n + 1) (by omega)
      obtain ⟨h0, e0⟩ := ih n (by omega)
      set a1 := ‖(monicHermite (n + 1)).eval (I * ‖x‖)‖
      set a0 := ‖(monicHermite n).eval (I * ‖x‖)‖
      have hval : (monicHermite (n + 2)).eval (I * ‖x‖) =
          I ^ (n + 2) * ((‖x‖ * a1 + ((n : ℝ) + 1) / 2 * a0 : ℝ) : ℂ) := by
        rw [monicHermite_add_two, eval_sub, eval_mul, eval_X, eval_mul, eval_C, e1, e0]
        push_cast
        rw [pow_succ, pow_succ, pow_succ I n]
        ring_nf
        rw [I_sq]; ring
      have hnn : 0 ≤ ‖x‖ * a1 + ((n : ℝ) + 1) / 2 * a0 := by positivity
      have hnorm : ‖(monicHermite (n + 2)).eval (I * ‖x‖)‖ = ‖x‖ * a1 + ((n : ℝ) + 1) / 2 * a0 := by
        rw [hval, norm_mul, norm_pow, norm_I, one_pow, one_mul, Complex.norm_real,
          Real.norm_of_nonneg hnn]
      refine ⟨?_, by rw [hnorm, hval]⟩
      rw [hnorm, monicHermite_add_two, eval_sub, eval_mul, eval_X, eval_mul, eval_C]
      calc ‖x * (monicHermite (n + 1)).eval x - ((n : ℂ) + 1) / 2 * (monicHermite n).eval x‖
          ≤ ‖x‖ * ‖(monicHermite (n + 1)).eval x‖ +
            ‖((n : ℂ) + 1) / 2‖ * ‖(monicHermite n).eval x‖ := by
            refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
        _ ≤ ‖x‖ * a1 + ((n : ℝ) + 1) / 2 * a0 := by
            have hn : ‖((n : ℂ) + 1) / 2‖ = ((n : ℝ) + 1) / 2 := by
              rw [show ((n : ℂ) + 1) / 2 = (((n : ℝ) + 1) / 2 : ℝ) by push_cast; ring,
                Complex.norm_real, Real.norm_of_nonneg (by positivity)]
            rw [hn]
            gcongr

/-- The Hermite generating series converges absolutely. -/
theorem summable_norm_carlsonHermite (t x : ℂ) :
    Summable fun n : ℕ => ‖t ^ n / n.factorial * (carlsonHermite n).eval x‖ := by
  have h := hasSum_carlsonHermite_generating (-I * ‖t‖) (I * ‖x‖)
  have hterm : ∀ n : ℕ, (-I * ‖t‖) ^ n / n.factorial * (carlsonHermite n).eval (I * ‖x‖) =
      ((‖t‖ ^ n / n.factorial * 2 ^ n * ‖(monicHermite n).eval (I * ‖x‖)‖ : ℝ) : ℂ) := fun n => by
    rw [carlsonHermite, eval_mul, eval_C]
    conv_lhs => rw [(norm_eval_monicHermite_le n x).2]
    rw [mul_pow, neg_pow I]
    push_cast
    have : ((-1 : ℂ) ^ n * I ^ n) * I ^ n = 1 := by
      rw [mul_assoc, ← mul_pow, I_mul_I, ← mul_pow]; norm_num
    linear_combination (‖t‖ ^ n / n.factorial * 2 ^ n * ‖(monicHermite n).eval (I * ‖x‖)‖ : ℂ) *
      this
  have hreal : Summable fun n : ℕ => ‖t‖ ^ n / n.factorial * 2 ^ n *
      ‖(monicHermite n).eval (I * ‖x‖)‖ := by
    have := (h.congr_fun fun n => (hterm n).symm).summable
    exact Complex.summable_ofReal.mp this
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hreal
  rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, carlsonHermite, eval_mul, eval_C,
    norm_mul, norm_pow, Complex.norm_ofNat]
  have := (norm_eval_monicHermite_le n x).1
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- **Exercise 7.10-6** (addition theorem):
`Hₙ(x cos θ + y sin θ) = ∑ₘ (n choose m) cosᵐ θ sin^{n-m} θ Hₘ(x) H_{n-m}(y)`. -/
theorem carlsonHermite_addition (n : ℕ) (x y θ : ℂ) :
    (carlsonHermite n).eval (x * cos θ + y * sin θ) = ∑ m ∈ range (n + 1),
      (n.choose m : ℂ) * cos θ ^ m * sin θ ^ (n - m) * (carlsonHermite m).eval x *
        (carlsonHermite (n - m)).eval y := by
  set a : ℕ → ℂ := fun k => (carlsonHermite k).eval (x * cos θ + y * sin θ) / k.factorial
  set b : ℕ → ℂ := fun k => ∑ m ∈ range (k + 1), (cos θ ^ m * (carlsonHermite m).eval x /
    m.factorial) * (sin θ ^ (k - m) * (carlsonHermite (k - m)).eval y / (k - m).factorial)
  have hab : a = b := by
    refine coeff_eq_of_hasSum_pow one_pos (F := fun t => exp (2 * (x * cos θ + y * sin θ) * t -
      t ^ 2)) (fun t _ => ?_) (fun t _ => ?_)
    · refine (hasSum_carlsonHermite_generating t _).congr_fun fun k => ?_
      simp only [a]; ring
    · have h := hasSum_sum_range_mul_of_summable_norm (summable_norm_carlsonHermite
        (t * cos θ) x) (summable_norm_carlsonHermite (t * sin θ) y)
      rw [(hasSum_carlsonHermite_generating _ _).tsum_eq,
        (hasSum_carlsonHermite_generating _ _).tsum_eq, ← exp_add] at h
      have hexp : 2 * x * (t * cos θ) - (t * cos θ) ^ 2 + (2 * y * (t * sin θ) - (t * sin θ) ^ 2) =
          2 * (x * cos θ + y * sin θ) * t - t ^ 2 := by
        linear_combination (-t ^ 2) * sin_sq_add_cos_sq θ
      rw [hexp] at h
      refine h.congr_fun fun k => ?_
      simp only [b]
      rw [Finset.sum_mul]
      refine sum_congr rfl fun m hm => ?_
      have hmk : m ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hm)
      have htk : t ^ k = t ^ m * t ^ (k - m) := by rw [← pow_add, Nat.add_sub_cancel' hmk]
      rw [htk, mul_pow, mul_pow]
      ring
  have h := congrFun hab n
  simp only [a, b] at h
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [div_eq_iff hf, sum_mul] at h
  rw [h]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [Nat.cast_choose ℂ hmn]
  have h1 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((n - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - m).factorial_ne_zero
  field_simp

/-- The Gaussian functional of `1` is `√π`. -/
theorem gaussianFunctional_one : gaussianFunctional 1 = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
  have h := integral_gaussian_complex (b := 1) (by simp)
  simp only [neg_mul, one_mul, div_one] at h
  rw [gaussianFunctional]
  simpa using h

/-- **Exercise 7.10-1**: the moments of the normal distribution with density `π^{-1/2} e^{-x²}`.
The odd moments vanish and `∫ x^{2n} e^{-x²} dx = (1/2)ₙ √π`. -/
theorem gaussianFunctional_X_pow (n : ℕ) :
    gaussianFunctional (X ^ (2 * n)) =
        (ascPochhammer ℂ n).eval (1 / 2) * (Real.pi : ℂ) ^ (1 / 2 : ℂ) ∧
      gaussianFunctional (X ^ (2 * n + 1)) = 0 := by
  induction n with
  | zero =>
    refine ⟨by simp [gaussianFunctional_one], ?_⟩
    have h := gaussianFunctional_X_mul 1
    have h0 : gaussianFunctional 0 = 0 := by
      rw [show (0 : ℂ[X]) = C 0 * 1 by simp, gaussianFunctional_C_mul, zero_mul]
    simp only [mul_one, derivative_one, h0, zero_div] at h
    simpa using h
  | succ n ih =>
    obtain ⟨he, ho⟩ := ih
    have hstep : ∀ k : ℕ, gaussianFunctional (X ^ (k + 2)) =
        ((k : ℂ) + 1) / 2 * gaussianFunctional (X ^ k) := fun k => by
      rw [show X ^ (k + 2) = X * X ^ (k + 1) by ring, gaussianFunctional_X_mul,
        derivative_X_pow, show k + 1 - 1 = k by omega, gaussianFunctional_C_mul]
      push_cast; ring
    refine ⟨?_, ?_⟩
    · rw [show 2 * (n + 1) = 2 * n + 2 by ring, hstep, he, ascPochhammer_succ_eval]
      push_cast; ring
    · rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, hstep, ho, mul_zero]

/-- **Exercise 7.10-2**: the monic Hermite polynomial is the Gaussian average of `zⁿ` over the
line through `x` parallel to the imaginary axis:
`√π p̃ₙ(x) = ∫ (x + it)ⁿ e^{-t²} dt`. -/
theorem gaussianFunctional_affine_pow (x : ℂ) (n : ℕ) :
    gaussianFunctional ((C x + C I * X) ^ n) =
      (Real.pi : ℂ) ^ (1 / 2 : ℂ) * (monicHermite n).eval x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [gaussianFunctional_one]
    · have h := gaussianFunctional_X_mul (C I)
      rw [derivative_C, show (0 : ℂ[X]) = C 0 * 1 by simp, gaussianFunctional_C_mul, zero_mul,
        zero_div] at h
      have hadd : gaussianFunctional (C x + C I * X) = gaussianFunctional (C x * 1) +
          gaussianFunctional (X * C I) := by
        rw [← gaussianFunctional_add]; congr 1; ring
      rw [pow_one, hadd, h, gaussianFunctional_C_mul, gaussianFunctional_one]
      simp; ring
    · -- the recurrence, by integration by parts
      set q : ℂ[X] := (C x + C I * X) ^ (n + 1)
      have hsplit : (C x + C I * X) ^ (n + 2) = C x * q + C I * (X * q) := by
        simp only [q]; ring
      have hder : derivative q = C (((n : ℂ) + 1) * I) * (C x + C I * X) ^ n := by
        simp only [q]
        rw [derivative_pow, derivative_add, derivative_C, zero_add, derivative_C_mul_X,
          Nat.add_sub_cancel, C_mul]
        push_cast
        ring
      rw [hsplit, gaussianFunctional_add, gaussianFunctional_C_mul, gaussianFunctional_C_mul,
        gaussianFunctional_X_mul, hder, gaussianFunctional_C_mul, ih (n + 1) (by omega),
        ih n (by omega), monicHermite_add_two, eval_sub, eval_mul, eval_X, eval_mul, eval_C]
      ring_nf
      rw [I_sq]; ring

/-- `C₁^ν(z) = 2νz`. -/
theorem eval_gegenbauer_one_deg (ν z : ℂ) : (gegenbauer ν 1).eval z = 2 * ν * z := by
  simp [gegenbauer, shiftedGegenbauer, Finset.Nat.antidiagonal_succ]
  ring

/-- **Exercise 7.10-5**, with `ν = s²`: `Hₙ(x) = n! lim_{s→∞} s⁻ⁿ Cₙ^{s²}(x/s)`. -/
theorem tendsto_gegenbauer_sq_hermite (x : ℂ) (n : ℕ) :
    Tendsto (fun s : ℝ => ((s : ℂ) ^ n)⁻¹ * (gegenbauer ((s : ℂ) ^ 2) n).eval (x / s)) atTop
      (𝓝 ((carlsonHermite n).eval x / n.factorial)) := by
  have hinv : Tendsto (fun s : ℝ => ((s : ℂ) ^ 2)⁻¹) atTop (𝓝 0) := by
    have h := (continuous_ofReal.tendsto 0).comp
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)))
    simp only [ofReal_zero] at h
    exact h.congr fun s => by simp
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [carlsonHermite]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with s hs
      have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
      rw [eval_gegenbauer_one_deg]
      simp [carlsonHermite]
      field_simp
    · have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have hA : Tendsto (fun s : ℝ => (2 * (1 + (n + 1) * ((s : ℂ) ^ 2)⁻¹) * x *
          (((s : ℂ) ^ (n + 1))⁻¹ * (gegenbauer ((s : ℂ) ^ 2) (n + 1)).eval (x / s)) -
          (2 + n * ((s : ℂ) ^ 2)⁻¹) *
          (((s : ℂ) ^ n)⁻¹ * (gegenbauer ((s : ℂ) ^ 2) n).eval (x / s))) / ((n : ℂ) + 2))
          atTop (𝓝 ((2 * (1 + (n + 1) * 0) * x * ((carlsonHermite (n + 1)).eval x /
            (n + 1).factorial) - (2 + n * 0) * ((carlsonHermite n).eval x / n.factorial)) /
              ((n : ℂ) + 2))) :=
        ((((tendsto_const_nhds.mul (tendsto_const_nhds.add
          (tendsto_const_nhds.mul hinv))).mul tendsto_const_nhds).mul h1).sub
          ((tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).mul h0)).div_const _
      convert hA.congr' ?_ using 2
      · simp only [carlsonHermite, monicHermite_add_two, eval_mul, eval_C, eval_sub, eval_X,
          Nat.factorial_succ]
        push_cast
        have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
        have hn2 : (n : ℂ) + 2 ≠ 0 := by
          have : (0 : ℝ) < n + 2 := by positivity
          exact_mod_cast this.ne'
        rw [mul_zero, add_zero, mul_zero, add_zero, eq_div_iff hn2]
        rw [show (n : ℂ) + 1 + 1 = n + 2 by ring]
        have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
        field_simp
        ring
      · filter_upwards [eventually_ne_atTop 0] with s hs
        have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
        have hrec := gegenbauer_three_term ((s : ℂ) ^ 2) (x / s) n
        have hn2 : (n : ℂ) + 2 ≠ 0 := by
          have : (0 : ℝ) < n + 2 := by positivity
          exact_mod_cast this.ne'
        rw [div_eq_iff hn2]
        field_simp at hrec ⊢
        linear_combination (-(s : ℂ) ^ 2 * (s : ℂ) ^ (n * 2)) * hrec

/-- **Exercise 7.10-5**: `Hₙ(x) = n! lim_{ν→∞} ν^{-n/2} Cₙ^ν(x ν^{-1/2})`, along real `ν → ∞`. -/
theorem tendsto_gegenbauer_hermite (x : ℂ) (n : ℕ) :
    Tendsto (fun ν : ℝ => (n.factorial : ℂ) * ((Real.sqrt ν : ℂ) ^ n)⁻¹ *
      (gegenbauer (ν : ℂ) n).eval (x / Real.sqrt ν)) atTop (𝓝 ((carlsonHermite n).eval x)) := by
  have h := ((tendsto_gegenbauer_sq_hermite x n).comp Real.tendsto_sqrt_atTop).const_mul
    (n.factorial : ℂ)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [mul_div_cancel₀ _ hf] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with ν hν
  simp only [Function.comp_apply]
  rw [show ((Real.sqrt ν : ℝ) : ℂ) ^ 2 = (ν : ℂ) by rw [← ofReal_pow, Real.sq_sqrt hν],
    mul_assoc]

end Carlson.TwoVariable
