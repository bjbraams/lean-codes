/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.ResolventContinuation
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Differentiation of the continued Carlson resolvent

Differentiation in the exterior evaluation point raises the integer kernel order.
The identity holds for all complex Dirichlet parameters, including Gamma poles,
because the regularized resolvent is entire in those parameters. Joint analyticity
and uniqueness extend the native integral identity to this full parameter range.

## Main results

* `hasDerivAt_continuedRegCarlsonResolvent`: the derivative at any point outside
  the convex hull of the nodes, with no parameter restrictions.
* `deriv_continuedRegCarlsonResolvent`: the corresponding derivative evaluation.
* `deriv_deriv_continuedRegCarlsonResolvent`: the second derivative in terms of
  the resolvent two orders higher.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §§5.11 and 7.1.
-/

public noncomputable section
namespace Dirichlet
open Complex Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

/-- Differentiation in the exterior point raises the continued regularized
resolvent order, at arbitrary complex Dirichlet parameters. -/
theorem hasDerivAt_continuedRegCarlsonResolvent (n : ℕ) (b z : ι → ℂ)
    {x : ℂ} (hx : x ∉ convexHull ℝ (range z)) :
    HasDerivAt (continuedRegCarlsonResolvent n b z)
      (-((n : ℂ) + 1) * continuedRegCarlsonResolvent (n + 1) b z x) x := by
  let H : ((ι → ℂ) × ℂ) → ℂ := fun p => continuedRegCarlsonResolvent n p.1 z p.2
  have hH (c : ι → ℂ) : AnalyticAt ℂ H (c, x) :=
    (analyticOnNhd_continuedRegCarlsonResolvent n (c, x, z)
      ⟨mem_univ _, mem_carlsonResolventDomain_of_not_mem_convexHull hx⟩).comp_of_eq
      (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const)) rfl
  have hd (c : ι → ℂ) : HasDerivAt (continuedRegCarlsonResolvent n c z)
      (fderiv ℂ H (c, x) (0, 1)) x :=
    (hH c).differentiableAt.hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x c).prodMk (hasDerivAt_id x))
  have ha : AnalyticOnNhd ℂ (fun c => fderiv ℂ H (c, x) (0, 1)) univ := by
    intro c _
    have hm : AnalyticAt ℂ (fun d : ι → ℂ => (d, x)) c :=
      analyticAt_id.prod analyticAt_const
    exact ((ContinuousLinearMap.apply ℂ ℂ (0, 1)).analyticAt _).comp_of_eq
      ((hH c).fderiv.comp_of_eq hm rfl) rfl
  have hr : AnalyticOnNhd ℂ (fun c => -((n : ℂ) + 1) *
      continuedRegCarlsonResolvent (n + 1) c z x) univ :=
    analyticOnNhd_const.mul
      (isRegCarlsonContinuation_continuedRegCarlsonResolvent (n + 1)
        (mem_carlsonResolventDomain_of_not_mem_convexHull hx)).analyticOnNhd
  have he := analyticOnNhd_eq_of_eqOn_mvBetaConvergent ha hr (by
    intro c hc
    have hn := hasDerivAt_regCarlsonResolvent n hc z hx
    have heq : continuedRegCarlsonResolvent n c z =ᶠ[𝓝 x] regCarlsonResolvent n c z := by
      filter_upwards [((finite_range z).isCompact_convexHull ℝ).isClosed.isOpen_compl.mem_nhds hx]
        with y hy
      exact continuedRegCarlsonResolvent_eq_native n hc
        (mem_carlsonResolventDomain_of_not_mem_convexHull hy)
    dsimp only
    rw [continuedRegCarlsonResolvent_eq_native (n + 1) hc
      (mem_carlsonResolventDomain_of_not_mem_convexHull hx)]
    exact (hd c).unique (hn.congr_of_eventuallyEq heq))
  simpa only [congrFun he b] using hd b

/-- Evaluation of the derivative of the continued regularized resolvent outside
the convex hull of its nodes. -/
theorem deriv_continuedRegCarlsonResolvent (n : ℕ) (b z : ι → ℂ)
    {x : ℂ} (hx : x ∉ convexHull ℝ (range z)) :
    deriv (continuedRegCarlsonResolvent n b z) x =
      -((n : ℂ) + 1) * continuedRegCarlsonResolvent (n + 1) b z x :=
  (hasDerivAt_continuedRegCarlsonResolvent n b z hx).deriv

/-- The second exterior derivative of the continued regularized resolvent,
without restrictions on its Dirichlet parameters. -/
theorem deriv_deriv_continuedRegCarlsonResolvent (n : ℕ) (b z : ι → ℂ)
    {x : ℂ} (hx : x ∉ convexHull ℝ (range z)) :
    deriv (deriv (continuedRegCarlsonResolvent n b z)) x =
      ((n : ℂ) + 1) * ((n : ℂ) + 2) * continuedRegCarlsonResolvent (n + 2) b z x := by
  have he : deriv (continuedRegCarlsonResolvent n b z) =ᶠ[𝓝 x]
      (fun y => -((n : ℂ) + 1) * continuedRegCarlsonResolvent (n + 1) b z y) := by
    filter_upwards [((finite_range z).isCompact_convexHull ℝ).isClosed.isOpen_compl.mem_nhds hx]
      with y hy
    exact deriv_continuedRegCarlsonResolvent n b z hy
  rw [he.deriv_eq]
  rw [((hasDerivAt_continuedRegCarlsonResolvent (n + 1) b z hx).const_mul
    (-((n : ℂ) + 1))).deriv]
  push_cast
  ring

end Dirichlet
