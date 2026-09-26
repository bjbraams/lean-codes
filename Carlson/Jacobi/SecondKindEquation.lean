/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Pearson
public import Carlson.Jacobi.SecondKind
public import Dirichlet.Average.ResolventDeriv

/-!
# The adjoint Jacobi differential equation

Pearson's identity for the continued two-node average gives a three-term
relation between consecutive integer resolvents. Differentiation converts this
relation into the differential equation for Carlson's adjoint second-kind Jacobi
function. The quadratic coefficient is `(x-r)(x-s)`; the equation is valid off
the endpoint segment, including coincident endpoints and exceptional parameters.

## Main results

* `continuedRegCarlsonResolvent_pearson`: the two-node relation between three
  consecutive resolvent orders at arbitrary complex parameters.
* `hasDerivAt_jacobiSecondKind`: differentiation raises the index and lowers both
  Jacobi parameters.
* `jacobiSecondKind_differential_equation`: the adjoint Jacobi equation on the
  entire complement of the endpoint segment.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Chapter 7 (Jacobi polynomials and associated functions).
-/

public noncomputable section
namespace Carlson.TwoVariable
open Dirichlet Set Complex

/-- Differentiation in the argument of the scalar resolvent kernel has a positive
coefficient, in contrast to differentiation in its exterior point. -/
private theorem hasDerivAt_resolvent_arg (m : ℕ) {x w : ℂ} (hw : x ≠ w) :
    HasDerivAt (fun v : ℂ => (x - v) ^ (-(m + 1 : ℤ)))
      (((m : ℂ) + 1) * (x - w) ^ (-((m + 1 : ℕ) + 1 : ℤ))) w := by
  have h := (hasDerivAt_zpow (-(m + 1 : ℤ)) (x - w) (Or.inl (sub_ne_zero.mpr hw))).comp w
    ((hasDerivAt_const w x).sub (hasDerivAt_id w))
  have he : -(m + 1 : ℤ) - 1 = -((m + 1 : ℕ) + 1 : ℤ) := by omega
  simpa only [Function.comp_def, he, Int.cast_neg, Int.cast_add, Int.cast_natCast,
    Int.cast_one, zero_sub, mul_neg, mul_one, neg_mul, neg_neg] using h

/-- Pearson's relation between three consecutive regularized resolvent orders.
No nonvanishing or positivity conditions are imposed on the beta parameters. -/
theorem continuedRegCarlsonResolvent_pearson (a b r s : ℂ) (n : ℕ) {x : ℂ}
    (hx : x ∉ segment ℝ r s) :
    ((n : ℂ) + 2) * ((x - r) * (x - s)) *
        continuedRegCarlsonResolvent (n + 2) (pair a b) (pair r s) x +
      ((a + b - 2 * ((n : ℂ) + 2)) * x + ((n : ℂ) + 2) * (r + s) - a * r - b * s) *
        continuedRegCarlsonResolvent (n + 1) (pair a b) (pair r s) x +
      ((n : ℂ) + 2 - a - b) * continuedRegCarlsonResolvent n (pair a b) (pair r s) x = 0 := by
  let k := fun (m : ℕ) (w : ℂ) => (x - w) ^ (-(m + 1 : ℤ))
  let R := fun m c => continuedRegCarlsonResolvent m c (pair r s) x
  have hdom : (x, pair r s) ∈ carlsonResolventDomain :=
    mem_carlsonResolventDomain_of_not_mem_convexHull (by rwa [convexHull_range_pair])
  have hK (m : ℕ) : IsRegCarlsonContinuation (k m) (pair r s) (R m) :=
    isRegCarlsonContinuation_continuedRegCarlsonResolvent m hdom
  have hne {w : ℂ} (hw : w ∈ segment ℝ r s) : x ≠ w := fun h => hx (h ▸ hw)
  have hka (m : ℕ) : AnalyticOnNhd ℂ (k m) (segment ℝ r s) :=
    fun w hw => (analyticAt_const.sub analyticAt_id).zpow (sub_ne_zero.mpr (hne hw))
  have hmem {u : Fin 2 → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) :
      carlsonAffineForm (pair r s) u ∈ segment ℝ r s := by
    rw [← convexHull_range_pair]
    exact carlsonAffineForm_mem_convexHull _ hu
  have hkc (m : ℕ) := (hka m).continuousOn.comp
    (continuous_carlsonAffineForm (pair r s)).continuousOn (fun _ hu => hmem hu)
  have hk (m : ℕ) {w : ℂ} (hw : w ∈ segment ℝ r s) : (x - w) * k (m + 1) w = k m w := by
    dsimp only [k]
    nth_rw 1 [← zpow_one (x - w)]
    rw [← zpow_add₀ (sub_ne_zero.mpr (hne hw))]
    congr 1
  have hd {w : ℂ} (hw : w ∈ segment ℝ r s) :
      deriv (k (n + 1)) w = ((n : ℂ) + 2) * k (n + 2) w := by
    convert (hasDerivAt_resolvent_arg (n + 1) (hne hw)).deriv using 1
    simp only [Nat.cast_add, Nat.cast_one, k]
    congr 1
    ring
  have hD : IsRegCarlsonContinuation (deriv (k (n + 1))) (pair r s)
      (fun c => ((n : ℂ) + 2) * R (n + 2) c) :=
    (IsRegDirichletContinuation.smul (hK (n + 2)) ((n : ℂ) + 2)).congr
      (fun _ hu => (hd (hmem hu)).symm)
  have hW := (IsRegDirichletContinuation.smul (hK (n + 1)) x).add
    (IsRegDirichletContinuation.smul (hK n) (-1))
    (continuousOn_const.mul (hkc (n + 1))) (continuousOn_const.mul (hkc n))
  have hW' : IsRegCarlsonContinuation (fun w => w * k (n + 1) w) (pair r s)
      (fun c => x * R (n + 1) c + -1 * R n c) := hW.congr (by
    intro u hu
    linear_combination hk n (hmem hu))
  have hA := (((IsRegDirichletContinuation.smul (hK (n + 2)) ((x - r) * (x - s))).add
    (IsRegDirichletContinuation.smul (hK (n + 1)) (-(2 * x - r - s)))
    (continuousOn_const.mul (hkc (n + 2))) (continuousOn_const.mul (hkc (n + 1)))).add
      (hK n) ((continuousOn_const.mul (hkc (n + 2))).add
        (continuousOn_const.mul (hkc (n + 1)))) (hkc n)).smul ((n : ℂ) + 2)
  have hA' : IsRegCarlsonContinuation
      (fun w => (w - r) * (w - s) * deriv (k (n + 1)) w) (pair r s)
      (fun c => ((n : ℂ) + 2) * (((x - r) * (x - s)) * R (n + 2) c +
        -(2 * x - r - s) * R (n + 1) c + R n c)) := hA.congr (by
    intro u hu
    dsimp only
    rw [hd (hmem hu)]
    linear_combination ((n : ℂ) + 2) * (x + carlsonAffineForm (pair r s) u - r - s) *
      hk (n + 1) (hmem hu) - ((n : ℂ) + 2) * hk n (hmem hu))
  have h := carlsonAverage_pearson (hka (n + 1)) (hK (n + 1)) hD hA' hW' a b
  dsimp only [R] at h
  linear_combination h

/-- Differentiating Carlson's adjoint second-kind function raises its index and
lowers both Jacobi parameters, preserving the Dirichlet parameters and normalization. -/
theorem hasDerivAt_jacobiSecondKind (α β r s : ℂ) (n : ℕ) {x : ℂ}
    (hx : x ∉ segment ℝ r s) :
    HasDerivAt (jacobiSecondKind α β r s n)
      (-((n : ℂ) + 1) * jacobiSecondKind (α - 1) (β - 1) r s (n + 1) x) x := by
  have h := (hasDerivAt_continuedRegCarlsonResolvent n
    (pair (α + n + 1) (β + n + 1)) (pair r s)
    (by rwa [convexHull_range_pair])).const_mul (Gamma (α + n + 1 + (β + n + 1)))
  have he (c : ℂ) : c - 1 + ((n + 1 : ℕ) : ℂ) + 1 = c + n + 1 := by push_cast; ring
  unfold jacobiSecondKind
  rw [he, he]
  convert h using 1
  ring

/-- Carlson's adjoint second-kind function satisfies the formal adjoint of the
Jacobi polynomial equation. All complex parameters and coincident endpoints are
allowed; the evaluation point must lie outside the endpoint segment. At Gamma
poles this assertion concerns the totalized normalization in the definition. -/
theorem jacobiSecondKind_differential_equation (α β r s : ℂ) (n : ℕ) {x : ℂ}
    (hx : x ∉ segment ℝ r s) :
    (x - r) * (x - s) * deriv (deriv (jacobiSecondKind α β r s n)) x +
      ((2 - α - β) * x + (α - 1) * r + (β - 1) * s) *
        deriv (jacobiSecondKind α β r s n) x -
      ((n : ℂ) + 1) * ((n : ℂ) + α + β) * jacobiSecondKind α β r s n x = 0 := by
  have hx' : x ∉ convexHull ℝ (range (pair r s)) := by rwa [convexHull_range_pair]
  have h := continuedRegCarlsonResolvent_pearson (α + n + 1) (β + n + 1) r s n hx
  unfold jacobiSecondKind
  simp only [deriv_const_mul_field']
  rw [deriv_continuedRegCarlsonResolvent n _ _ hx',
    deriv_deriv_continuedRegCarlsonResolvent n _ _ hx']
  linear_combination Gamma (α + n + 1 + (β + n + 1)) * ((n : ℂ) + 1) * h

end Carlson.TwoVariable
