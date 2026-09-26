/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Aggregation
public import Carlson.RPolynomial.Generating
public import Carlson.RPolynomial.TaylorContinuation

/-!
# Deleting zero Dirichlet parameters

In the polynomial formula, a zero parameter kills every term involving its node.
Combining this with equal-node aggregation deletes that coordinate altogether.
The exponential series and the continued Taylor series inherit the same property.
This proves Corollary 6.3-2 for holomorphic averages on disks; the general R-function
specialization is in `Carlson.R.ZeroParameter`. The deletion statements use a
nonempty remaining index type, the usual special-function setting.

## Main results

* `Carlson.carlsonRPolynomialNumerator_update_of_param_zero`: A zero parameter makes the
  polynomial numerator independent of its node.
* `Carlson.regCarlsonSSeries_update_of_param_zero`: The entire regularized `S` function does not
  depend on a zero-parameter node.
* `Carlson.regCarlsonRPolynomial_option_zero`: Deleting a zero parameter from a regularized `R`
  polynomial. `Option ι` distinguishes the deleted coordinate from the nonempty set of remaining
  coordinates.
* `Carlson.regCarlsonSSeries_option_zero`: Deleting a zero parameter from the entire regularized
  `S` function.
* `Dirichlet.IsRegCarlsonContinuation.option_zero`: Zero parameters may be deleted from any
  continued holomorphic average on a disk (Carlson, Corollary 6.3-2), including exceptional
  values of the total parameter in the regularized normalization.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex Finset Polynomial
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- A zero parameter makes the polynomial numerator independent of its node. -/
theorem carlsonRPolynomialNumerator_update_of_param_zero (n : ℕ)
    {b : ι → ℂ} (z : ι → ℂ) (i : ι) (hbi : b i = 0) (w : ℂ) :
    carlsonRPolynomialNumerator n b (Function.update z i w) =
      carlsonRPolynomialNumerator n b z := by
  simp only [carlsonRPolynomialNumerator_eq_sum_piAntidiag, carlsonGeneratingCoeff]
  apply sum_congr rfl
  intro m _
  by_cases hmi : m i = 0
  · congr 2
    apply prod_congr rfl
    intro j _
    by_cases hji : j = i <;> simp [hji, hmi]
  · have hp : ∏ j, (ascPochhammer ℂ (m j)).eval (b j) = 0 := by
      apply prod_eq_zero (mem_univ i)
      simp [hbi, hmi]
    simp [hp]

open scoped Classical in
/-- Regularized `R` polynomials do not depend on nodes with zero parameter. -/
theorem regCarlsonRPolynomial_update_of_param_zero (n : ℕ) {b : ι → ℂ}
    (z : ι → ℂ) (i : ι) (hbi : b i = 0) (w : ℂ) :
    regCarlsonRPolynomial n b (Function.update z i w) = regCarlsonRPolynomial n b z := by
  simp only [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
    carlsonRPolynomialNumerator_update_of_param_zero n z i hbi w]

open scoped Classical in
/-- The entire regularized `S` function does not depend on a zero-parameter node. -/
theorem regCarlsonSSeries_update_of_param_zero {b : ι → ℂ}
    (z : ι → ℂ) (i : ι) (hbi : b i = 0) (w : ℂ) :
    regCarlsonSSeries (Function.update z i w) b = regCarlsonSSeries z b := by
  simp only [regCarlsonSSeries_eq_tsum_regCarlsonRPolynomial,
    regCarlsonRPolynomial_update_of_param_zero _ z i hbi w]

/-- Aggregating an extra coordinate with zero parameter into an existing coordinate leaves the
remaining parameter vector unchanged. -/
private lemma aggregate_option_zero (k : ι) {b : Option ι → ℂ} (hb : b none = 0) :
    stdSimplexAggregate (fun o => o.elim k id) b = b ∘ some := by
  classical
  ext j
  simp only [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply,
    Finset.sum_filter, Fintype.sum_option, Option.elim_none, Option.elim_some, id_eq,
    hb, ite_self, zero_add, Function.comp_apply]
  exact Fintype.sum_ite_eq' j (fun a => b (some a))

/-- Deleting a zero parameter from a regularized `R` polynomial. `Option ι`
distinguishes the deleted coordinate from the nonempty set of remaining coordinates. -/
theorem regCarlsonRPolynomial_option_zero [Nonempty ι] (n : ℕ)
    {b : Option ι → ℂ} (hb : b none = 0) (z : Option ι → ℂ) :
    regCarlsonRPolynomial n b z = regCarlsonRPolynomial n (b ∘ some) (z ∘ some) := by
  let : DecidableEq (Option ι) := Classical.decEq _
  let k : ι := Classical.arbitrary ι
  let q : Option ι → ι := fun o => o.elim k id
  have hq : Function.Surjective q := fun i => ⟨some i, rfl⟩
  have hz : Function.update z none (z (some k)) = (z ∘ some) ∘ q := by
    ext o
    cases o <;> simp [q]
  have hupdate := regCarlsonRPolynomial_update_of_param_zero n z none hb (z (some k))
  have hagg := regCarlsonRPolynomial_aggregate hq n (z ∘ some) b
  have hnodes := congrArg (fun w : Option ι → ℂ => regCarlsonRPolynomial n b w) hz
  have hparams := congrArg (fun c : ι → ℂ => regCarlsonRPolynomial n c (z ∘ some))
    (aggregate_option_zero k hb)
  exact hupdate.symm.trans (hnodes.trans (hagg.trans hparams))

/-- Deleting a zero parameter from the entire regularized `S` function. -/
theorem regCarlsonSSeries_option_zero [Nonempty ι]
    {b : Option ι → ℂ} (hb : b none = 0) (z : Option ι → ℂ) :
    regCarlsonSSeries z b = regCarlsonSSeries (z ∘ some) (b ∘ some) := by
  simp only [regCarlsonSSeries_eq_tsum_regCarlsonRPolynomial,
      regCarlsonRPolynomial_option_zero _ hb z]

/-- Zero parameters may be deleted from any continued holomorphic average on a
disk (Carlson, Corollary 6.3-2), including exceptional values of the total parameter
in the regularized normalization. -/
theorem _root_.Dirichlet.IsRegCarlsonContinuation.option_zero [Nonempty ι]
    {A : ℂ} {R : ℝ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball A R))
    {z : Option ι → ℂ} (hz : ‖fun i => z i - A‖ < R)
    {G : (Option ι → ℂ) → ℂ} {H : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f z G) (hH : IsRegCarlsonContinuation f (z ∘ some) H)
    {b : Option ι → ℂ} (hb : b none = 0) : G b = H (b ∘ some) := by
  have hz' : ‖fun i : ι => z (some i) - A‖ < R := by
    refine lt_of_le_of_lt ?_ hz
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      (fun i => norm_le_pi_norm (fun j => z j - A) (some i))
  rw [hG.eq_taylor hf hz, hH.eq_taylor hf hz']
  unfold regCarlsonTaylorSeries
  apply tsum_congr
  intro n
  rw [regCarlsonRPolynomial_option_zero n hb]
  rfl

end Carlson
end
