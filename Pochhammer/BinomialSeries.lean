/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.Analysis.Analytic.Binomial

/-!
# Binomial series for the ascending Pochhammer symbol

The generating function \(\sum_n (a)_n t^n / n! = (1-t)^{-a}\) for \(\|t\| < 1\), written in
Mathlib's `ascPochhammer` and `Ring.multichoose` language. The algebraic identification of
\((a)_n / n!\) with `Ring.multichoose a n` holds in any field of characteristic zero; the
analytic series results are complex. The complex binomial series itself is imported from
`TauCeti.Analysis.Analytic.Binomial`, by the Tau Ceti contributors.

## Main results

* `ascPochhammer_eval_div_factorial`: Ascending Pochhammer symbols divided by factorials
  are the binomial-ring multichoose coefficients in a field of characteristic zero.
* `Complex.hasSum_ascPochhammer_mul_pow_div_factorial`: The binomial series \(\sum (a)_n t^n /
  n! = (1-t)^{-a}\) inside the unit disk.
* `Complex.summable_norm_ascPochhammer_mul_pow_div_factorial`: The binomial series of
  `hasSum_ascPochhammer_mul_pow_div_factorial` is absolutely summable inside the unit disk.

## References

* `Mathlib.Analysis.Analytic.Binomial`: formal background used by this module.
* `Mathlib.RingTheory.Binomial`: formal background used by this module.
* `Mathlib.RingTheory.Polynomial.Pochhammer`: formal background used by this module.
* `TauCeti.Analysis.Analytic.Binomial`: the complex binomial series in multichoose form.
-/

open scoped Topology

public noncomputable section

section Algebraic

variable {K : Type*} [Field K] [CharZero K]

/-- Ascending Pochhammer symbols divided by factorials are the binomial-ring multichoose
coefficients, in any field of characteristic zero. -/
theorem ascPochhammer_eval_div_factorial (a : K) (n : ℕ) :
    (ascPochhammer K n).eval a / (n.factorial : K) = Ring.multichoose a n := by
  refine Eq.symm ((eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).2 ?_)
  rw [mul_comm]
  simpa [Polynomial.ascPochhammer_smeval_cast,
    Polynomial.ascPochhammer_smeval_eq_eval] using
      (Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n)

end Algebraic

namespace Complex

/-- The binomial series \(\sum (a)_n t^n / n! = (1-t)^{-a}\) inside the unit disk.

The series is `TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one`, by the
Tau Ceti contributors, rewritten in Pochhammer form. -/
theorem hasSum_ascPochhammer_mul_pow_div_factorial (a t : ℂ) (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ ↦
      (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * t ^ n)
      (1 / (1 - t) ^ a) := by
  simpa only [ascPochhammer_eval_div_factorial] using
    TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one (r := a) ht

/-- The binomial series of `hasSum_ascPochhammer_mul_pow_div_factorial` is absolutely
summable inside the unit disk. -/
theorem summable_norm_ascPochhammer_mul_pow_div_factorial (a t : ℂ) (ht : ‖t‖ < 1) :
    Summable fun n : ℕ =>
      ‖(ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * t ^ n‖ := by
  have hp := Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a
  have htball : t ∈ Metric.eball (0 : ℂ) 1 := by
    simp only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    exact_mod_cast ht
  have hx : t ∈ Metric.eball (0 : ℂ)
      (FormalMultilinearSeries.ofScalars ℂ
        fun n ↦ Ring.choose (a + n - 1) n).radius :=
    (Metric.eball_subset_eball hp.r_le) htball
  have hnorm :=
    (FormalMultilinearSeries.ofScalars ℂ
      fun n ↦ Ring.choose (a + n - 1) n).summable_norm_apply hx
  refine hnorm.congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [← Ring.multichoose_eq, ← ascPochhammer_eval_div_factorial]

end Complex

end
