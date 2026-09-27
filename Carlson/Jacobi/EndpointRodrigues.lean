/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.EndpointBridge

/-!
# Rodrigues' formula at arbitrary complex endpoints

Carlson's Formula 7.8-1 expresses the monic Jacobi polynomial with foci `r, s` through
the `n`-th derivative of `(x-r)^(β+n) (x-s)^(α+n)`. The proof applies the Leibniz rule to
the two principal powers and identifies the result with Carlson's two-node numerator.
The formula holds wherever `x - r` and `x - s` lie in the slit plane.

## Main results

* `iteratedDeriv_sub_cpow`: iterated derivatives of a shifted principal power.
* `iteratedDeriv_sub_cpow_mul_sub_cpow`: Formula 7.8-1.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Formula 7.8-1.
-/

public section

open Complex Set Filter Polynomial Finset
open scoped Topology

namespace Carlson.TwoVariable

/-- Iterated derivatives of a shifted principal power. -/
theorem iteratedDeriv_sub_cpow (c A : ℂ) (i : ℕ) {x : ℂ} (hx : x - c ∈ slitPlane) :
    iteratedDeriv i (fun w => (w - c) ^ A) x =
      (descPochhammer ℂ i).eval A * (x - c) ^ (A - i) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    have hU : {w : ℂ | w - c ∈ slitPlane} ∈ 𝓝 x :=
      (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
        (isOpen_slitPlane.mem_nhds hx)
    have he : iteratedDeriv i (fun w => (w - c) ^ A) =ᶠ[𝓝 x]
        fun w => (descPochhammer ℂ i).eval A * (w - c) ^ (A - i) := by
      filter_upwards [hU] with w hw using ih hw
    have hd := (((hasDerivAt_id x).sub_const c).cpow_const (c := A - i) hx).const_mul
      ((descPochhammer ℂ i).eval A)
    simp only [id] at hd
    rw [iteratedDeriv_succ, he.deriv_eq, hd.deriv, descPochhammer_succ_eval]
    push_cast
    ring_nf

/-- Shifted principal powers are smooth on the slit plane. -/
theorem contDiffAt_sub_cpow (c A : ℂ) (n : WithTop ℕ∞) {x : ℂ} (hx : x - c ∈ slitPlane) :
    ContDiffAt ℂ n (fun w => (w - c) ^ A) x :=
  ((analyticAt_id.sub analyticAt_const).cpow analyticAt_const hx).contDiffAt

/-- **Formula 7.8-1** (Rodrigues' formula) at arbitrary complex endpoints, on the principal
branch: `(1+α+β+n)ₙ (x-r)^β (x-s)^α pₙ(x) = Dⁿ[(x-r)^(β+n) (x-s)^(α+n)]`. -/
theorem iteratedDeriv_sub_cpow_mul_sub_cpow (α β r s : ℂ) (n : ℕ) {x : ℂ}
    (hr : x - r ∈ slitPlane) (hs : x - s ∈ slitPlane)
    (h : (ascPochhammer ℂ n).eval (α + β + n + 1) ≠ 0) :
    iteratedDeriv n (fun w => (w - r) ^ (β + n) * (w - s) ^ (α + n)) x =
      (ascPochhammer ℂ n).eval (α + β + n + 1) *
        ((x - r) ^ β * (x - s) ^ α * (jacobiOn α β r s n).eval x) := by
  have hr0 : x - r ≠ 0 := slitPlane_ne_zero hr
  have hs0 : x - s ≠ 0 := slitPlane_ne_zero hs
  have hQ : (ascPochhammer ℂ n).eval (-α - β - 2 * n) =
      (-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval (α + β + n + 1) := by
    rw [show -α - β - 2 * n = 1 - (α + β + n + 1) - n by ring]
    exact ascPochhammer_eval_reflect _ _
  rw [iteratedDeriv_fun_mul (contDiffAt_sub_cpow r _ _ hr) (contDiffAt_sub_cpow s _ _ hs),
    eval_jacobiOn_eq_numerator α β r s x n h, carlsonRPolynomialNumerator₂,
    ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => (Nat.choose n k : ℂ) * (ascPochhammer ℂ k).eval (-α - n) *
        (ascPochhammer ℂ i).eval (-β - n) * (x - r) ^ k * (x - s) ^ i),
    hQ]
  simp only [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [iteratedDeriv_sub_cpow r _ i hr, iteratedDeriv_sub_cpow s _ (n - i) hs,
    Nat.choose_symm hin,
    show β + n - i = β + ((n - i : ℕ) : ℂ) by push_cast [hin]; ring,
    show α + n - ((n - i : ℕ) : ℂ) = α + (i : ℂ) by push_cast [hin]; ring,
    cpow_add _ _ hr0, cpow_add _ _ hs0, cpow_natCast, cpow_natCast,
    show -α - (n : ℂ) = -(α + n) by ring, show -β - (n : ℂ) = -(β + n) by ring,
    ascPochhammer_eval_neg_eq_descPochhammer, ascPochhammer_eval_neg_eq_descPochhammer]
  have hsign : (-1 : ℂ) ^ (n - i) * (-1) ^ i = (-1) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hin]
  field_simp
  rw [← hsign]
  ring

end Carlson.TwoVariable
