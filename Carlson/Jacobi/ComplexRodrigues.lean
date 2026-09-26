/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Raising
public import Carlson.Jacobi.Weight
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Complex Jacobi weights and Rodrigues' formula

The weight `z^α (1-z)^β` uses principal complex powers. Its derivative identities
hold where both `z` and `1-z` lie in the slit plane, with arbitrary complex
parameters. In particular the whole open real unit interval is allowed.
The Rodrigues identity is multiplied by the weight and factorial, so it needs
no parameter nonvanishing assumptions and includes degree drops.

## Main results

* `hasDerivAt_complexJacobiWeight_succ`: the complex Pearson identity.
* `hasDerivAt_complexJacobiWeight_mul_shiftedJacobi`: the weighted raising identity.
* `iteratedDeriv_complexJacobiWeight`: Rodrigues' formula for complex parameters.
* `intervalIntegrable_complexJacobiWeight`: integrability for real parts greater than `-1`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Formula 7.8-1.
-/

@[expose] public noncomputable section
namespace Polynomial
open Complex MeasureTheory Set

/-- The shifted Jacobi weight with complex exponents and principal complex powers. -/
def complexJacobiWeight (α β z : ℂ) : ℂ := z ^ α * (1 - z) ^ β

/-- Raising both exponents multiplies the complex weight by `z(1-z)`. -/
theorem complexJacobiWeight_succ (α β : ℂ) {z : ℂ} (hz : z ≠ 0) (hz1 : 1 - z ≠ 0) :
    complexJacobiWeight (α + 1) (β + 1) z = z * (1 - z) * complexJacobiWeight α β z := by
  simp only [complexJacobiWeight, cpow_add _ _ hz, cpow_add _ _ hz1, cpow_one]
  ring

/-- Pearson's derivative identity on the common principal-branch domain. -/
theorem hasDerivAt_complexJacobiWeight_succ (α β : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) (hz1 : 1 - z ∈ slitPlane) :
    HasDerivAt (complexJacobiWeight (α + 1) (β + 1))
      ((α + 1 - (α + β + 2) * z) * complexJacobiWeight α β z) z := by
  have h1 := (hasDerivAt_id z).cpow_const (c := α + 1) hz
  have h2 := ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).cpow_const
    (c := β + 1) hz1
  convert h1.mul h2 using 1
  · rfl
  · simp only [Pi.sub_apply, id_eq, add_sub_cancel_right, mul_one, zero_sub, mul_neg,
    complexJacobiWeight, cpow_add _ _ (slitPlane_ne_zero hz),
    cpow_add _ _ (slitPlane_ne_zero hz1), cpow_one]
    ring

/-- Differentiation of the complex weight times a shifted Jacobi polynomial
raises the index and lowers both weight exponents. -/
theorem hasDerivAt_complexJacobiWeight_mul_shiftedJacobi (α β : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) (hz1 : 1 - z ∈ slitPlane) :
    HasDerivAt (fun w => complexJacobiWeight (α + 1) (β + 1) w *
      (shiftedJacobi (α + 1) (β + 1) n).eval w)
      ((n + 1 : ℂ) * (complexJacobiWeight α β z * (shiftedJacobi α β (n + 1)).eval z)) z := by
  have he := congrArg (eval z) (shiftedJacobi_raising α β n)
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one] at he
  convert (hasDerivAt_complexJacobiWeight_succ α β hz hz1).mul
    ((shiftedJacobi (α + 1) (β + 1) n).hasDerivAt z) using 1
  rw [complexJacobiWeight_succ α β (slitPlane_ne_zero hz) (slitPlane_ne_zero hz1)]
  linear_combination -complexJacobiWeight α β z * he

/-- Rodrigues' formula on the common principal-branch domain, for all complex
Jacobi parameters, including exceptional values. -/
theorem iteratedDeriv_complexJacobiWeight (α β : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) (hz1 : 1 - z ∈ slitPlane) :
    iteratedDeriv n (complexJacobiWeight (α + n) (β + n)) z =
      n.factorial * (complexJacobiWeight α β z * (shiftedJacobi α β n).eval z) := by
  induction n generalizing α β z with
  | zero => simp [complexJacobiWeight]
  | succ n ih =>
    have he : iteratedDeriv n (complexJacobiWeight (α + (n + 1)) (β + (n + 1)))
        =ᶠ[nhds z] (fun w => n.factorial * (complexJacobiWeight (α + 1) (β + 1) w *
          (shiftedJacobi (α + 1) (β + 1) n).eval w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz,
        (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
          (isOpen_slitPlane.mem_nhds hz1)] with w hw hw1
      simpa only [add_assoc, add_comm (1 : ℂ) (n : ℂ)] using ih (α + 1) (β + 1) hw hw1
    rw [iteratedDeriv_succ, Nat.cast_add, Nat.cast_one, he.deriv_eq]
    rw [((hasDerivAt_complexJacobiWeight_mul_shiftedJacobi α β n hz hz1).const_mul
      (n.factorial : ℂ)).deriv, Nat.factorial_succ]
    push_cast
    ring

/-- The complex Jacobi weight is integrable when both real parts exceed `-1`. -/
theorem intervalIntegrable_complexJacobiWeight {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) :
    IntervalIntegrable (fun t : ℝ => complexJacobiWeight α β t) volume 0 1 := by
  simpa only [complexJacobiWeight, add_sub_cancel_right] using
    betaIntegral_convergent (u := α + 1) (v := β + 1)
      (by simpa using (show 0 < α.re + 1 by linarith))
      (by simpa using (show 0 < β.re + 1 by linarith))

/-- The raised complex weight is continuous on the real line, including the endpoints. -/
theorem continuous_complexJacobiWeight_succ {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) :
    Continuous (fun t : ℝ => complexJacobiWeight (α + 1) (β + 1) t) := by
  have ha : 0 < (α + 1).re := by simpa using (show 0 < α.re + 1 by linarith)
  have hb : 0 < (β + 1).re := by simpa using (show 0 < β.re + 1 by linarith)
  simpa only [complexJacobiWeight, Function.comp_def, Pi.mul_apply, Pi.sub_apply, id_eq, ofReal_sub, ofReal_one] using
    (continuous_ofReal_cpow_const ha).fun_mul
      ((continuous_ofReal_cpow_const hb).comp
        ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).sub continuous_id))

/-- Positive real part of the left exponent makes the raised weight vanish at zero. -/
@[simp] theorem complexJacobiWeight_succ_zero {α β : ℂ} (hα : -1 < α.re) :
    complexJacobiWeight (α + 1) (β + 1) 0 = 0 := by
  have ha : α + 1 ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  simp [complexJacobiWeight, zero_cpow ha]

/-- Positive real part of the right exponent makes the raised weight vanish at one. -/
@[simp] theorem complexJacobiWeight_succ_one {α β : ℂ} (hβ : -1 < β.re) :
    complexJacobiWeight (α + 1) (β + 1) 1 = 0 := by
  have hb : β + 1 ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  simp [complexJacobiWeight, zero_cpow hb]

end Polynomial
