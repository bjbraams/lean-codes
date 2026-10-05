/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Carlson.TwoVariable.ParameterSymmetry
public import Carlson.L.Continuation

/-!
# Exponent derivatives with moving Dirichlet parameters

Differentiating the quadratic transformations in the exponent also moves the Dirichlet
parameters, keeping their sum fixed. This module isolates that calculus for the two-variable
regularized R-function: the chain rule splits the derivative into an L-term and a
sum-preserving parameter derivative, and the parameter-transfer identity of Carlson (1987),
(2.12), identifies the latter with a transformed L-term. At exponent zero the correction
vanishes. The equal-parameter applications, Carlson (1987), (6.4), (6.5) and (6.8), are in
`TwoVariable.EqualParameterSlit`.

## Main results

* `Carlson.TwoVariable.deriv_regCarlsonR_exponent_transfer`: the chain rule for the exponent and a
  sum-preserving parameter transfer, on slit-plane nodes.
* `Carlson.TwoVariable.regRParameterTransfer_eq_L`, `regRParameterTransfer_eq_neg_L`: Carlson
  (1987), (2.12), normalized at the first or the last node.
* `Carlson.TwoVariable.regRParameterTransfer_zero`: at degree zero a sum-preserving parameter
  derivative vanishes.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
* B. C. Carlson, *Dirichlet averages of x^t log x*, SIAM J. Math. Anal. 18 (1987), 550–565.
-/

open Dirichlet
open Complex Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The missing term when the exponent and the Dirichlet parameters both vary.
The parameter sum `u + v` stays fixed along this derivative. -/
def regRParameterTransfer (t u v x y : ℂ) : ℂ :=
  deriv (fun s => regCarlsonR t (pair (u + s) (v - s)) (pair x y)) 0

/-- Carlson (1987), (2.12), normalized at the first node. The ratio may lie outside
the right half-plane, so the transformed L-function uses its slit continuation. -/
theorem regRParameterTransfer_eq_L (t u v x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    regRParameterTransfer t u v x y =
      x ^ t * regCarlsonL (-v) (pair (u + v + t) (-t)) (pair 1 (y / x)) := by
  have hs : pair 1 (y / x) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · simp [pair]
    · exact div_mem_slitPlane_of_re_pos (hz 1) (hz 0)
  have heq : (fun s => regCarlsonR t (pair (u + s) (v - s)) (pair x y)) =
      (fun s => x ^ t * regCarlsonR (s - v) (pair (u + v + t) (-t)) (pair 1 (y / x))) := by
    funext s
    have h := regCarlsonR_parameterInterchange t (u + s) (v - s) (hz 0) (hz 1)
    simp only [pair_zero, pair_one] at h
    rw [show u + s + (v - s) + t = u + v + t by ring,
      show -(v - s) = s - v by ring] at h
    exact h
  have h := ((hasDerivAt_regCarlsonR_L (-v) (pair (u + v + t) (-t)) hs).comp_of_eq 0
    ((hasDerivAt_id 0).sub_const v) (by simp)).const_mul (x ^ t)
  rw [regRParameterTransfer, heq]
  simpa using h.deriv

/-- Carlson (1987), second form of (2.12), normalized at the last node. -/
theorem regRParameterTransfer_eq_neg_L (t u v x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    regRParameterTransfer t u v x y =
      -(y ^ t * regCarlsonL (-u) (pair (-t) (u + v + t)) (pair (x / y) 1)) := by
  have hs : pair (x / y) 1 ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact div_mem_slitPlane_of_re_pos (hz 0) (hz 1)
    · simp [pair]
  have heq : (fun s => regCarlsonR t (pair (u + s) (v - s)) (pair x y)) =
      (fun s => y ^ t * regCarlsonR (-u - s) (pair (-t) (u + v + t)) (pair (x / y) 1)) := by
    funext s
    have h := regCarlsonR_parameterInterchange_last t (u + s) (v - s) (hz 0) (hz 1)
    simp only [pair_zero, pair_one] at h
    rw [show u + s + (v - s) + t = u + v + t by ring,
      show -(u + s) = -u - s by ring] at h
    exact h
  have h := ((hasDerivAt_regCarlsonR_L (-u) (pair (-t) (u + v + t)) hs).comp_of_eq 0
    ((hasDerivAt_const 0 (-u)).sub (hasDerivAt_id 0)) (by simp)).const_mul (y ^ t)
  rw [regRParameterTransfer, heq]
  simpa using h.deriv

/-- Chain rule for the exponent and a sum-preserving parameter transfer. -/
theorem deriv_regCarlsonR_exponent_transfer (t u v x y : ℂ)
    (hz : pair x y ∈ carlsonRSlitDomain) :
    deriv (fun s => regCarlsonR s (pair (u + s) (v - s)) (pair x y)) t =
      regCarlsonL t (pair (u + t) (v - t)) (pair x y) +
        regRParameterTransfer t (u + t) (v - t) x y := by
  have ha : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      regCarlsonR p.1 (pair (u + p.2) (v - p.2)) (pair x y)) (t, t) := by
    refine analyticAt_regCarlsonR_comp analyticAt_fst ?_ analyticAt_const
      hz
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i
    · exact analyticAt_const.add analyticAt_snd
    · exact analyticAt_const.sub analyticAt_snd
  have h₁ := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t t)) rfl
  have h₂ := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq t
    ((hasDerivAt_const t t).prodMk (hasDerivAt_id t)) rfl
  have h := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq t
    ((hasDerivAt_id t).prodMk (hasDerivAt_id t)) rfl
  simp only [Function.comp_def, id_eq] at h h₁ h₂
  have hsplit : ((1, 1) : ℂ × ℂ) = (1, 0) + (0, 1) := by simp
  rw [h.deriv, hsplit, map_add, ← h₁.deriv, ← h₂.deriv]
  congr 1
  let g : ℂ → ℂ := fun s => regCarlsonR t (pair (u + s) (v - s)) (pair x y)
  have hg : DifferentiableAt ℂ g t := by
    apply AnalyticAt.differentiableAt
    refine analyticAt_regCarlsonR_comp analyticAt_const ?_ analyticAt_const
      hz
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i
    · exact analyticAt_const.add analyticAt_id
    · exact analyticAt_const.sub analyticAt_id
  have h := hg.hasDerivAt.comp_of_eq 0
    ((hasDerivAt_const 0 t).add (hasDerivAt_id 0)) (by simp)
  simpa [regRParameterTransfer, g, Function.comp_def, add_assoc, sub_sub] using h.deriv.symm

/-- At degree zero a sum-preserving parameter derivative vanishes. -/
theorem regRParameterTransfer_zero (u v x y : ℂ)
    (hz : pair x y ∈ carlsonRSlitDomain) :
    regRParameterTransfer 0 u v x y = 0 := by
  have heq : (fun s => regCarlsonR 0 (pair (u + s) (v - s)) (pair x y)) =
      (fun _ : ℂ => (Gamma (u + v))⁻¹) := by
    funext s
    rw [show (0 : ℂ) = (0 : ℕ) by norm_num,
      regCarlsonR_natCast _ _ hz]
    simp only [regCarlsonRPolynomial_zero, sum_pair]
    congr 2
    ring
  unfold regRParameterTransfer
  rw [heq, deriv_const]

end Carlson.TwoVariable
