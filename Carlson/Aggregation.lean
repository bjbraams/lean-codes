/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Aggregation
public import Carlson.R.Continuation
public import Carlson.S
public import Carlson.R.Explicit

/-!
# Equal-node aggregation for Carlson functions

These specializations of the general continuation theorem impose no restrictions
on the Dirichlet parameters. The `R` function retains its right-half-plane node
domain; the polynomial and `S` statements allow arbitrary complex nodes.

## Main results

* `Carlson.regCarlsonR_aggregate`: Equal-node aggregation for the entire regularized `R`
  function.
* `Carlson.regCarlsonR_aggregate_of_slit`: the same on all slit-plane nodes.
* `Carlson.regCarlsonR_comp_perm`: permutation symmetry on all slit-plane nodes.
* `Carlson.regCarlsonRPolynomial_aggregate`: Equal-node aggregation for regularized `R`
  polynomials at every complex parameter.
* `Carlson.regCarlsonSSeries_aggregate`: Equal-node aggregation for the entire regularized `S`
  function.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex Set
@[expose] public noncomputable section
namespace Carlson
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Equal-node aggregation for the entire regularized `R` function. -/
theorem regCarlsonR_aggregate {q : ι → κ} (hq : Function.Surjective q)
    (t : ℂ) {z : κ → ℂ} (hz : z ∈ carlsonRVariableDomain) (b : ι → ℂ) :
    regCarlsonR t b (z ∘ q) =
      regCarlsonR t (stdSimplexAggregate q b) z := by
  exact IsRegCarlsonContinuation.aggregate hq
    (isRegCarlsonRContinuation_regCarlsonR t (fun i => hz (q i)))
    (isRegCarlsonRContinuation_regCarlsonR t hz)
    ((continuous_carlsonAffineForm z).continuousOn.cpow_const
      (fun _ hu => carlsonAffineForm_mem_slitPlane hz hu)) b

/-- Equal-node aggregation for regularized `R` polynomials at every complex parameter. -/
theorem regCarlsonRPolynomial_aggregate {q : ι → κ} (hq : Function.Surjective q)
    (n : ℕ) (z : κ → ℂ) (b : ι → ℂ) :
    regCarlsonRPolynomial n b (z ∘ q) = regCarlsonRPolynomial n (stdSimplexAggregate q b) z := by
  have h (w : ι → ℂ) : IsRegCarlsonContinuation (fun x => x ^ n) w (regCarlsonRPolynomial n · w) :=
    ⟨analyticOnNhd_regCarlsonRPolynomial n w,
        fun _ hb => (regCarlsonDirichletAverage_pow n w hb).symm⟩
  have h' : IsRegCarlsonContinuation (fun x => x ^ n) z (regCarlsonRPolynomial n · z) :=
    ⟨analyticOnNhd_regCarlsonRPolynomial n z,
        fun _ hb => (regCarlsonDirichletAverage_pow n z hb).symm⟩
  exact (h (z ∘ q)).aggregate hq h'
    ((continuous_carlsonAffineForm z).pow n).continuousOn b

/-- Equal-node aggregation for the entire regularized `S` function. -/
theorem regCarlsonSSeries_aggregate {q : ι → κ} (hq : Function.Surjective q)
    (z : κ → ℂ) (b : ι → ℂ) :
    regCarlsonSSeries (z ∘ q) b = regCarlsonSSeries z (stdSimplexAggregate q b) := by
  exact IsRegCarlsonContinuation.aggregate hq
    (isRegCarlsonSContinuation_series (z ∘ q)) (isRegCarlsonSContinuation_series z)
    (Complex.continuous_exp.comp (continuous_carlsonAffineForm z)).continuousOn b

/-- Equal-node aggregation for the regularized `R` function on all slit-plane nodes. -/
theorem regCarlsonR_aggregate_of_slit {q : ι → κ}
    (hq : Function.Surjective q) (t : ℂ) {z : κ → ℂ} (hz : z ∈ carlsonRSlitDomain) (b : ι → ℂ) :
    regCarlsonR t b (z ∘ q) = regCarlsonR t (stdSimplexAggregate q b) z := by
  have hcomp : AnalyticOnNhd ℂ (fun w : κ → ℂ => regCarlsonR t b (w ∘ q)) carlsonRSlitDomain :=
    fun w hw => analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pi_iff.mpr fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : κ => ℂ)
        (q i)).analyticAt w) (fun i => hw (q i))
  exact eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hcomp
    (analyticOnNhd_regCarlsonR t _) (fun w hw => regCarlsonR_aggregate hq t hw b) hz

/-- **Permutation symmetry** of the regularized `R` function on all slit-plane nodes: permuting the
nodes is the same as permuting the parameters inversely. -/
theorem regCarlsonR_comp_perm (σ : Equiv.Perm ι) (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) (b : ι → ℂ) :
    regCarlsonR t b (z ∘ σ) = regCarlsonR t (b ∘ σ.symm) z := by
  classical
  rw [regCarlsonR_aggregate_of_slit σ.surjective t hz b]
  congr 1
  funext k
  rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
  have : (Finset.univ.filter fun x => σ x = k) = {σ.symm k} := by
    ext j; simp [Equiv.eq_symm_apply]
  rw [this, Finset.sum_singleton]
  rfl

end Carlson
end
