/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.ContourRepresentation

/-!
# Carlson's fractional integral

Carlson's Section 5.5 extends the `n`-fold repeated integral `Iⁿ f(x) = (x-a)ⁿ F(1, n; x, a)/n!`
to non-integral order by (5.5-14), `I^ν f(x) = (x - a)^ν F(1, ν; x, a)/Γ(1 + ν)`, and identifies
it with the Riemann–Liouville fractional integral (5.5-15). Here the average divided by
`Γ(1 + ν)` is the regularized two-node average, and the identification follows from the Euler
integral of the two-node average by the substitution `t = a + (x - a) u`.

## Main results

* `Carlson.TwoVariable.carlsonFractionalIntegral`: the fractional integral (5.5-14).
* `Carlson.TwoVariable.carlsonFractionalIntegral_eq_integral`: the Riemann–Liouville form
  (5.5-15).

## Implementation notes

The analytic continuation of `I^ν f` in `ν` and the values `I^{-n} f = f⁽ⁿ⁾` (5.5-16), which
Carlson defers to Section 6.3 and Exercise 6.3-3, are in
`Carlson.TwoVariable.FractionalContinuation`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.5.
-/

open Dirichlet
open Complex MeasureTheory Set Filter
open scoped Topology
@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- Carlson's fractional integral (5.5-14), `I^ν f(x) = (x - a)^ν F(1, ν; x, a)/Γ(1 + ν)`,
written with the regularized average. -/
def carlsonFractionalIntegral (ν a x : ℂ) (f : ℂ → ℂ) : ℂ :=
  (x - a) ^ ν * regCarlsonDirichletAverage (pair 1 ν) (pair x a) f

/-- **The Riemann–Liouville form (5.5-15)**: for real `a < x`,
`I^ν f(x) = Γ(ν)⁻¹ ∫ₐˣ f(t) (x - t)^{ν-1} dt`. Carlson assumes `re ν > 0`, where both integrals
converge absolutely for continuous `f`; as an identity of Bochner integrals it holds for every
`ν`. -/
theorem carlsonFractionalIntegral_eq_integral (ν : ℂ) {a x : ℝ} (hax : a < x)
    (f : ℂ → ℂ) :
    carlsonFractionalIntegral ν a x f =
      (Gamma ν)⁻¹ * ∫ t in a..x, f t * ((x - t : ℝ) : ℂ) ^ (ν - 1) := by
  have hd : 0 < x - a := by linarith
  have hdc : ((x : ℂ) - a) = ((x - a : ℝ) : ℂ) := by push_cast; ring
  set G : ℝ → ℂ := fun t => (((x - t) / (x - a) : ℝ) : ℂ) ^ (ν - 1) * f t
  have h1 : ∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ ((1 : ℂ) - 1) * (1 - (u : ℂ)) ^ (ν - 1) *
      f ((u : ℂ) * x + (1 - (u : ℂ)) * a) = ∫ u in (0 : ℝ)..1, G (a + (x - a) * u) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    simp only [G, sub_self, cpow_zero, one_mul]
    congr 1
    · congr 1
      rw [show (x - (a + (x - a) * u)) / (x - a) = 1 - u by field_simp; ring]
      push_cast; ring
    · congr 1; push_cast; ring
  have h2 := intervalIntegral.integral_comp_add_mul (f := G) (a := 0) (b := 1) hd.ne' a
  simp only [mul_zero, add_zero, mul_one, show a + (x - a) = x by ring] at h2
  have h3 : ∫ t in a..x, G t = ((((x - a : ℝ) : ℂ)) ^ (ν - 1))⁻¹ *
      ∫ t in a..x, f t * ((x - t : ℝ) : ℂ) ^ (ν - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hax.le] at ht
    simp only [G]
    have hxt : 0 ≤ x - t := by linarith [ht.2]
    rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hxt (inv_nonneg.mpr hd.le),
      ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hd.le]; exact Real.pi_ne_zero.symm)]
    ring
  unfold carlsonFractionalIntegral
  rw [regCarlsonDirichletAverage_pair_eq, regEulerIntegral, Gamma_one, one_mul, h1, h2, h3, hdc]
  have hne : ((x - a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpow : ((x - a : ℝ) : ℂ) ^ ν = ((x - a : ℝ) : ℂ) * ((x - a : ℝ) : ℂ) ^ (ν - 1) := by
    rw [cpow_sub _ _ hne, cpow_one]; field_simp
  have hpow0 : ((x - a : ℝ) : ℂ) ^ (ν - 1) ≠ 0 := (cpow_ne_zero_iff).mpr (Or.inl hne)
  rw [hpow]
  simp only [Complex.real_smul, ofReal_inv]
  field_simp

end Carlson.TwoVariable
