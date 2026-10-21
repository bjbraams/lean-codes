/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SlitDeriv
public import Dirichlet.Polynomial

/-!
# Arbitrary mixed node derivatives of R

Carlson's node differentiation formula (1977, §5.9) holds for an arbitrary list
of coordinates, with repeated indices included, at all complex parameters on
the full product slit domain. Its coefficient is the falling factorial of the
exponent times the multivariate rising factorial of the parameter vector.
-/

open Complex Dirichlet Filter Set SeveralComplexVariables
open scoped Topology Classical

@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- Adding a differentiation coordinate increments its rising-factorial coefficient. -/
private theorem mvPochhammer_count_cons (b : ι → ℂ) (i : ι) (is : List ι) :
    mvPochhammer b (fun j => (i :: is).count j) =
      mvPochhammer b (fun j => is.count j) * (b i + is.count i) := by
  classical
  have h (j : ι) :
      (ascPochhammer ℂ ((i :: is).count j)).eval (b j) =
        (ascPochhammer ℂ (is.count j)).eval (b j) *
          (if j = i then b i + is.count i else 1) := by
    by_cases hj : j = i
    · subst j
      simp [ascPochhammer_succ_eval, mul_comm]
    · simp [hj, Ne.symm hj]
  unfold mvPochhammer
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp

omit [Fintype ι] in
/-- Raising a parameter after a list of differentiations adds one to that coordinate's count. -/
private theorem addDirichletUnit_count (b : ι → ℂ) (i : ι) (is : List ι) :
    addDirichletUnit (fun j => b j + is.count j) i =
      fun j => b j + (i :: is).count j := by
  funext j
  by_cases hj : j = i
  · subst j; simp [addDirichletUnit, Nat.cast_add, add_assoc]
  · simp [addDirichletUnit, hj, Ne.symm hj]

/-- **Carlson §5.9, arbitrary order.** Every mixed node derivative is a shifted R-function,
with falling-factorial and multivariate Pochhammer coefficients. This division-free identity
includes zero and negative parameters, repeated coordinates, and coincident slit-plane nodes. -/
theorem iteratedPartialDeriv_regCarlsonR (is : List ι) (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    iteratedPartialDeriv is (regCarlsonR t b) z =
      (descPochhammer ℂ is.length).eval t * mvPochhammer b (fun i => is.count i) *
        regCarlsonR (t - is.length) (fun i => b i + is.count i) z := by
  induction is generalizing z with
  | nil => simp [iteratedPartialDeriv, mvPochhammer]
  | cons i is ih =>
    have he : iteratedPartialDeriv is (regCarlsonR t b) =ᶠ[𝓝 z]
        (fun w => (descPochhammer ℂ is.length).eval t * mvPochhammer b (fun j => is.count j) *
          regCarlsonR (t - is.length) (fun j => b j + is.count j) w) := by
      filter_upwards [isOpen_carlsonRSlitDomain.mem_nhds hz] with w hw
      exact ih hw
    rw [iteratedPartialDeriv, partialDeriv_congr he,
      partialDeriv_const_mul _ ((analyticOnNhd_regCarlsonR _ _ z hz).differentiableAt) i]
    change _ * carlsonPartialDeriv i (regCarlsonR (t - is.length)
      (fun j => b j + is.count j)) z = _
    rw [carlsonPartialDeriv_regCarlsonR _ _ hz,
      List.length_cons, descPochhammer_succ_eval, mvPochhammer_count_cons,
      addDirichletUnit_count]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show t - (is.length : ℂ) - 1 = t - ((is.length : ℂ) + 1) by ring]
    ring

end Carlson
