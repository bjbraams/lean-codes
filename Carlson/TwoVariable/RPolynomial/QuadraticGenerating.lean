/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.GeneratingIdentities
public import Carlson.TwoVariable.Quadratic.Polynomial

/-!
# Generating functions of `(at² + 2bt + c)^(-ν)` (Exercises 6.6-4 and 6.10-6)

Factor `at² + 2bt + c = c (1 - t z₁)(1 - t z₂)` with `c z_{1,2} = -b ± s`, `s² = b² - ac`. The
generating relation (6.6-1) for two nodes and equal parameters `ν` then expands
`(at² + 2bt + c)^(-ν)` in powers of `t`. The branch bookkeeping is the splitting
`(c w)^(-ν) = c^(-ν) w^(-ν)`, valid for `c` in the slit plane and `w` near `1`; hence the
statements hold for all `t` in a neighbourhood of `0`. The second quadratic transformation of
§6.10 turns the coefficients into R-polynomials with parameters `1/2 - ν - n`.

## Main results

* `Carlson.TwoVariable.eventually_hasSum_quadratic_generating`: Exercise 6.6-4.
* `Carlson.TwoVariable.eventually_hasSum_quadratic_generating_second`: Exercise 6.10-6.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§6.6, 6.10.
-/

open Complex Finset Filter
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- A complex number in the slit plane has `|arg| < π`. -/
theorem abs_arg_lt_pi_of_mem_slitPlane {c : ℂ} (hc : c ∈ slitPlane) : |arg c| < Real.pi := by
  have h1 := neg_pi_lt_arg c
  have h2 := arg_le_pi c
  have h3 := (mem_slitPlane_iff_arg.mp hc).1
  rw [abs_lt]; exact ⟨h1, lt_of_le_of_ne h2 h3⟩

/-- `(c w)^μ = c^μ w^μ` if `arg c + arg w` lies in `(-π, π)`. -/
theorem mul_cpow_of_abs_arg_add_lt {c w : ℂ} (hc : c ≠ 0) (hw : w ≠ 0)
    (h : |arg c| + |arg w| < Real.pi) (μ : ℂ) : (c * w) ^ μ = c ^ μ * w ^ μ := by
  have hlog : log (c * w) = log c + log w := (log_mul_eq_add_log_iff hc hw).mpr
    ⟨by linarith [neg_abs_le (arg c), neg_abs_le (arg w)],
      by linarith [le_abs_self (arg c), le_abs_self (arg w)]⟩
  rw [cpow_def_of_ne_zero (mul_ne_zero hc hw), cpow_def_of_ne_zero hc, cpow_def_of_ne_zero hw,
    hlog, add_mul, exp_add]

/-- **Exercise 6.6-4**: if `c` lies in the slit plane and `s² = b² - ac`, then for all `t` near
`0`, `(at² + 2bt + c)^(-ν) = ∑ₙ tⁿ (2ν)ₙ Rₙ(ν, ν; -b + s, -b - s)/(c^(ν+n) n!)`, written with the
numerator `Nₙ = (2ν)ₙ Rₙ`. -/
theorem eventually_hasSum_quadratic_generating (ν a b c s : ℂ) (hc : c ∈ slitPlane)
    (hs : s ^ 2 = b ^ 2 - a * c) :
    ∀ᶠ t in 𝓝 (0 : ℂ), HasSum (fun n : ℕ => c ^ (-ν) * (t ^ n *
        carlsonRPolynomialNumerator₂ n ν ν (-b + s) (-b - s) / (c ^ n * (n.factorial : ℂ))))
      ((a * t ^ 2 + 2 * b * t + c) ^ (-ν)) := by
  have hc0 : c ≠ 0 := slitPlane_ne_zero hc
  set z₁ := (-b + s) / c
  set z₂ := (-b - s) / c
  set P : ℂ → ℂ := fun t => (1 - t * z₁) * (1 - t * z₂)
  have hP : ∀ t, a * t ^ 2 + 2 * b * t + c = c * P t := fun t => by
    simp only [P, z₁, z₂]; field_simp; linear_combination (t ^ 2) * hs
  have hargc := abs_arg_lt_pi_of_mem_slitPlane hc
  have hPc : ContinuousAt P 0 := by simp only [P]; fun_prop
  have hP0 : P 0 = 1 := by simp [P]
  have harg : Tendsto (fun t => arg (P t)) (𝓝 0) (𝓝 0) := by
    have := (continuousAt_arg (by rw [hP0]; exact one_mem_slitPlane)).tendsto.comp hPc.tendsto
    simpa [hP0, Function.comp_def] using this
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℂ), |arg (P t)| < Real.pi - |arg c| := by
    have := harg.abs
    simp only [abs_zero] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  have hsmall : ∀ z : ℂ, ∀ᶠ t in 𝓝 (0 : ℂ), ‖t * z‖ < 1 := fun z => by
    have : Tendsto (fun t : ℂ => t * z) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun t : ℂ => t * z := by fun_prop
      simpa using hc.tendsto (0 : ℂ)
    exact (this.norm).eventually (gt_mem_nhds (by simp))
  filter_upwards [hev1, hsmall z₁, hsmall z₂] with t ht h1 h2
  have hre : ∀ w : ℂ, ‖w‖ < 1 → 0 < (1 - w).re := fun w hw => by
    have := (abs_re_le_norm w).trans_lt hw
    simp only [sub_re, one_re]; linarith [le_abs_self w.re]
  have hr1 := hre _ h1
  have hr2 := hre _ h2
  have hP0' : P t ≠ 0 := mul_ne_zero (fun h => by simp [h] at hr1) (fun h => by simp [h] at hr2)
  have h := hasSum_carlsonRPolynomialNumerator_div_factorial (pair ν ν) (pair z₁ z₂) t
    (fun i => by fin_cases i <;> [exact h1; exact h2])
  have hk : carlsonRGeneratingKernel (pair ν ν) (pair z₁ z₂) t = (P t) ^ (-ν) := by
    simp only [carlsonRGeneratingKernel, Fin.prod_univ_two, pair_zero, pair_one, P]
    rw [cpow_neg, mul_cpow_of_re_pos hr1 hr2]; field_simp
  rw [hk] at h
  rw [hP, mul_cpow_of_abs_arg_add_lt hc0 hP0' (by linarith) (-ν)]
  refine (h.mul_left (c ^ (-ν))).congr_fun fun n => ?_
  rw [carlsonRPolynomialNumerator_pair, show z₁ = c⁻¹ * (-b + s) by simp [z₁, div_eq_inv_mul],
    show z₂ = c⁻¹ * (-b - s) by simp [z₂, div_eq_inv_mul], carlsonRPolynomialNumerator₂_smul,
    inv_pow]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **Exercise 6.10-6**: the quadratic transformation of the expansion of Exercise 6.6-4. If
`2b = -(x² + y²)` and `ac = x²y²`, then near `t = 0` the coefficients of `(at² + 2bt + c)^(-ν)`
are given by R-polynomials with parameters `1/2 - ν - n` and nodes `(x ± y)²`, provided the
factors `(1 - 2ν - 2n)ₙ` do not vanish. -/
theorem eventually_hasSum_quadratic_generating_second (ν a b c x y : ℂ) (hc : c ∈ slitPlane)
    (hb : 2 * b = -(x ^ 2 + y ^ 2)) (hac : a * c = x ^ 2 * y ^ 2)
    (hν : ∀ n : ℕ, (ascPochhammer ℂ n).eval (1 - 2 * ν - 2 * n) ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℂ), HasSum (fun n : ℕ => c ^ (-ν) * (t ^ n * (ascPochhammer ℂ n).eval ν *
        carlsonRPolynomialNumerator₂ n (1 / 2 - ν - n) (1 / 2 - ν - n) ((x + y) ^ 2)
          ((x - y) ^ 2) / ((ascPochhammer ℂ n).eval (1 - 2 * ν - 2 * n) * c ^ n *
            (n.factorial : ℂ))))
      ((a * t ^ 2 + 2 * b * t + c) ^ (-ν)) := by
  have hs : ((x ^ 2 - y ^ 2) / 2) ^ 2 = b ^ 2 - a * c := by
    rw [hac, show b = -(x ^ 2 + y ^ 2) / 2 by linear_combination hb / 2]; ring
  filter_upwards [eventually_hasSum_quadratic_generating ν a b c _ hc hs] with t ht
  refine ht.congr_fun fun n => ?_
  have hx : -b + (x ^ 2 - y ^ 2) / 2 = x ^ 2 := by linear_combination -hb / 2
  have hy : -b - (x ^ 2 - y ^ 2) / 2 = y ^ 2 := by linear_combination -hb / 2
  have hq := carlsonRPolynomialNumerator₂_secondQuadratic n ν x y
  rw [hx, hy]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hcn : c ^ n ≠ 0 := pow_ne_zero _ (slitPlane_ne_zero hc)
  have hp := hν n
  rw [mul_assoc (t ^ n), ← hq]
  generalize (ascPochhammer ℂ n).eval (1 - 2 * ν - 2 * n) = p at hp ⊢
  field_simp

end Carlson.TwoVariable
