/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# A slowly divergent function is not rational

A complex-valued function on the positive real axis whose norm tends to infinity at zero,
but for which `x f(x)` tends to zero, cannot satisfy a polynomial relation `q f = r`
with nonzero `q`. The proof cancels common factors of `X` from the relation.
This applies, in particular, to logarithmic boundary singularities.
-/

open Complex Filter Set
open scoped Topology

@[expose] public section

namespace Polynomial

/-- A singularity that diverges more slowly than a simple pole cannot be rational.
The relation need only hold eventually on the positive side of zero. -/
theorem eq_zero_of_slow_singularity {f : ℝ → ℂ}
    (hnorm : Tendsto (fun x => ‖f x‖) (𝓝[>] 0) atTop)
    (h₀ : Tendsto (fun x : ℝ => (x : ℂ) * f x) (𝓝[>] 0) (𝓝 0))
    (q r : ℂ[X])
    (hrel : ∀ᶠ x : ℝ in 𝓝[>] 0, q.eval (x : ℂ) * f x = r.eval (x : ℂ)) :
    q = 0 := by
  induction hn : q.natDegree using Nat.strong_induction_on generalizing q r with
  | h n ih =>
    by_cases hq : q = 0
    · exact hq
    have hq₀ : q.coeff 0 = 0 := by
      by_contra hq₀
      have hqLim : Tendsto (fun x : ℝ => q.eval (x : ℂ)) (𝓝[>] 0)
          (𝓝 (q.coeff 0)) := by
        simpa only [Function.comp_def, ofReal_zero, coeff_zero_eq_eval_zero] using (q.continuous.comp continuous_ofReal).tendsto (0 : ℝ) |>.mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      have hrLim : Tendsto (fun x : ℝ => r.eval (x : ℂ)) (𝓝[>] 0)
          (𝓝 (r.coeff 0)) := by
        simpa only [Function.comp_def, ofReal_zero, coeff_zero_eq_eval_zero] using (r.continuous.comp continuous_ofReal).tendsto (0 : ℝ) |>.mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      have hf : Tendsto f (𝓝[>] 0) (𝓝 (r.coeff 0 / q.coeff 0)) := by
        apply (hrLim.div hqLim hq₀).congr'
        filter_upwards [hrel, hqLim.eventually_ne hq₀] with x hx hqx
        exact ((eq_div_iff hqx).mpr (by simpa [mul_comm] using hx)).symm
      exact not_tendsto_nhds_of_tendsto_atTop hnorm _ hf.norm
    have hqX : X * q.divX = q := by simpa [hq₀] using X_mul_divX_add q
    have hr₀ : r.coeff 0 = 0 := by
      have hlim := ((q.divX.continuous.comp continuous_ofReal).tendsto (0 : ℝ) |>.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).mul h₀
      have hrLim : Tendsto (fun x : ℝ => r.eval (x : ℂ)) (𝓝[>] 0)
          (𝓝 (r.coeff 0)) := by
        simpa only [Function.comp_def, ofReal_zero, coeff_zero_eq_eval_zero] using (r.continuous.comp continuous_ofReal).tendsto (0 : ℝ) |>.mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      have hzero : Tendsto (fun x : ℝ => r.eval (x : ℂ)) (𝓝[>] 0) (𝓝 0) := by
        simp only [mul_zero] at hlim
        apply hlim.congr'
        filter_upwards [hrel] with x hx
        change q.divX.eval (x : ℂ) * ((x : ℂ) * f x) = r.eval (x : ℂ)
        calc
          _ = (X * q.divX).eval (x : ℂ) * f x := by simp only [eval_mul, eval_X]; ring
          _ = _ := by rw [hqX, hx]
      exact tendsto_nhds_unique hrLim hzero
    have hrX : X * r.divX = r := by simpa [hr₀] using X_mul_divX_add r
    have hdeg : q.divX.natDegree < n := by
      rw [natDegree_divX_eq_natDegree_tsub_one, ← hn]
      have : q.natDegree ≠ 0 := by
        intro he
        exact hq (by rw [eq_C_of_natDegree_eq_zero he, hq₀, C_0])
      omega
    have hdiv : q.divX = 0 := by
      refine ih _ hdeg q.divX r.divX ?_ rfl
      filter_upwards [hrel, self_mem_nhdsWithin] with x hx (hx₀ : 0 < x)
      rw [← hqX, ← hrX, eval_mul, eval_mul, eval_X] at hx
      exact (mul_left_cancel₀ (ofReal_ne_zero.mpr hx₀.ne'))
        (by simpa [mul_assoc] using hx)
    rw [← hqX, hdiv, mul_zero]

end Polynomial
