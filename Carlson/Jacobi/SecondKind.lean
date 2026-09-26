/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.FiniteExpansion
public import Carlson.Normalization.Basic
public import Dirichlet.Average.CauchyContinuation

/-!
# Carlson's Jacobi functions of the second kind

Carlson's adjoint second-kind function is the continued average of the integer
Cauchy kernel of order `n+1`, with beta parameters `α+n+1, β+n+1`. It is
holomorphic outside the segment joining the endpoints, without choosing a
logarithmic branch. Its ordinary normalization uses Gamma of the total parameter.
Assertions identifying its normalized values exclude poles of that factor.

## Main results

* `analyticOnNhd_jacobiSecondKind`: holomorphy on the complement of the segment.
* `analyticAt_jacobiSecondKind_comp`: joint analytic dependence on all five variables.
* `jacobiSecondKind_eq_native`: agreement with the native integer-kernel average.
* `jacobiSecondKind_self`: the coincident-endpoint Cauchy kernel.
* `circleIntegral_jacobiSecondKind_mul_polynomial`: contour extraction of the
  finite Jacobi coefficient on any circle enclosing both endpoints.
* `circleIntegral_jacobiOn_mul_jacobiSecondKind`: circle biorthogonality at all
  admissible complex parameter pairs.

These are Carlson's adjoint functions, not the conventional Jacobi `Q` functions
without a weight factor. Their differentiation rule and adjoint differential equation
are proved in `Carlson.Jacobi.SecondKindEquation`; boundary jumps and asymptotics
remain further work.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Definition 7.1-1 and §7.2.
-/

@[expose] public noncomputable section

namespace Polynomial
/-- Iterated analytic derivatives of a polynomial agree with its iterated
algebraic derivatives over any nontrivially normed field. -/
theorem iteratedDeriv_eval {K : Type*} [NontriviallyNormedField K] (p : K[X]) (n : ℕ) :
    iteratedDeriv n (fun x => p.eval x) = fun x => (derivative^[n] p).eval x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    simp only [Polynomial.deriv, Function.iterate_succ_apply']
end Polynomial

namespace Carlson.TwoVariable
open Polynomial Dirichlet Complex Set
open scoped Interval

/-- Carlson's adjoint Jacobi function of the second kind. Values on the endpoint
segment are unspecified; at total-parameter Gamma poles the normalization is totalized. -/
def jacobiSecondKind (α β r s : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  Gamma (α + n + 1 + (β + n + 1)) *
    continuedRegCarlsonResolvent n (pair (α + n + 1) (β + n + 1)) (pair r s) x

/-- The two-node convex hull is the segment between the nodes. -/
theorem convexHull_range_pair (r s : ℂ) : convexHull ℝ (range (pair r s)) = segment ℝ r s := by
  have h : range (pair r s) = {r, s} := by
    ext x
    simp [pair, or_comm]
  rw [h, convexHull_pair]

/-- The Jacobi function of the second kind is holomorphic off the endpoint segment. -/
theorem analyticOnNhd_jacobiSecondKind (α β r s : ℂ) (n : ℕ) :
    AnalyticOnNhd ℂ (jacobiSecondKind α β r s n) (segment ℝ r s)ᶜ := by
  intro x hx
  have hdom : (x, pair r s) ∈ carlsonResolventDomain :=
    mem_carlsonResolventDomain_of_not_mem_convexHull (by rwa [convexHull_range_pair])
  have hmap : AnalyticAt ℂ
      (fun y : ℂ => (pair (α + n + 1) (β + n + 1), y, pair r s)) x :=
    analyticAt_const.prod (analyticAt_id.prod analyticAt_const)
  exact analyticAt_const.mul
    ((analyticOnNhd_continuedRegCarlsonResolvent n
      (pair (α + n + 1) (β + n + 1), x, pair r s) ⟨mem_univ _, hdom⟩).comp_of_eq hmap rfl)

/-- The second-kind function is jointly analytic under analytic variation of
both Jacobi parameters, both endpoints and the exterior evaluation point. -/
theorem analyticAt_jacobiSecondKind_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {α β r s x : E → ℂ} {p : E} (n : ℕ)
    (hα : AnalyticAt ℂ α p) (hβ : AnalyticAt ℂ β p)
    (hr : AnalyticAt ℂ r p) (hs : AnalyticAt ℂ s p) (hx : AnalyticAt ℂ x p)
    (hc : IsCarlsonGammaRegular (α p + β p + 2))
    (hz : x p ∉ segment ℝ (r p) (s p)) :
    AnalyticAt ℂ (fun q => jacobiSecondKind (α q) (β q) (r q) (s q) n (x q)) p := by
  have hb : AnalyticAt ℂ (fun q => pair (α q + n + 1) (β q + n + 1)) p := by
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i
    · exact (hα.add analyticAt_const).add analyticAt_const
    · exact (hβ.add analyticAt_const).add analyticAt_const
  have hnodes : AnalyticAt ℂ (fun q => pair (r q) (s q)) p := by
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i
    · exact hr
    · exact hs
  have hdom : (x p, pair (r p) (s p)) ∈ carlsonResolventDomain :=
    mem_carlsonResolventDomain_of_not_mem_convexHull (by rwa [convexHull_range_pair])
  exact analyticAt_Gamma_mul_comp
    (((hα.add analyticAt_const).add analyticAt_const).add
      ((hβ.add analyticAt_const).add analyticAt_const))
    ((analyticOnNhd_continuedRegCarlsonResolvent n _ ⟨mem_univ _, hdom⟩).comp_of_eq
      (hb.prod (hx.prod hnodes)) rfl)
    (jacobiTotalParameter_shift hc n)

/-- On the convergence region the second-kind function is the native Dirichlet
average of the integer Cauchy kernel. -/
theorem jacobiSecondKind_eq_native (α β r s x : ℂ) (n : ℕ)
    (hb : pair (α + n + 1) (β + n + 1) ∈ mvBetaConvergent)
    (hx : x ∉ segment ℝ r s) :
    jacobiSecondKind α β r s n x =
      carlsonDirichletAverage (pair (α + n + 1) (β + n + 1)) (pair r s)
        (fun w => (x - w) ^ (-(n + 1 : ℤ))) := by
  have hdom : (x, pair r s) ∈ carlsonResolventDomain :=
    mem_carlsonResolventDomain_of_not_mem_convexHull (by rwa [convexHull_range_pair])
  rw [jacobiSecondKind, continuedRegCarlsonResolvent_eq_native n hb hdom,
    regCarlsonResolvent, carlsonDirichletAverage, sum_pair]

/-- Coincident endpoints recover the integer Cauchy kernels used in Taylor's formula. -/
theorem jacobiSecondKind_self (α β s x : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) (n : ℕ) (hx : x ≠ s) :
    jacobiSecondKind α β s s n x = (x - s) ^ (-(n + 1 : ℤ)) := by
  have hz : pair s s = fun _ => s := by ext i; fin_cases i <;> rfl
  rw [jacobiSecondKind, hz, continuedRegCarlsonResolvent_const_nodes n _ hx, sum_pair]
  exact mul_div_cancel₀ _ (Gamma_ne_zero (jacobiTotalParameter_shift hc n))

/-- The contour coefficient of a holomorphic function is its continued derivative
average divided by the factorial. The continuation may be constructed independently. -/
theorem circleIntegral_jacobiSecondKind_mul (α β r s : ℂ) (n : ℕ)
    {f : ℂ → ℂ} {G : (Fin 2 → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation (iteratedDeriv n f) (pair r s) G)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hf : DiffContOnCl ℂ f (Metric.ball c R))
    (hz : range (pair r s) ⊆ Metric.ball c R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∮ x in C(c, R), jacobiSecondKind α β r s n x * f x) =
        Gamma (α + n + 1 + (β + n + 1)) *
          G (pair (α + n + 1) (β + n + 1)) / (n.factorial : ℂ) := by
  rw [hG.eq_circleIntegral hR hf hz]
  simp only [jacobiSecondKind, mul_assoc, circleIntegral.integral_const_mul]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- Integrating a polynomial against the adjoint second-kind function extracts
its continued derivative-average coefficient. The circle must enclose both nodes. -/
theorem circleIntegral_jacobiSecondKind_mul_polynomial (α β r s : ℂ) (n : ℕ) (p : ℂ[X])
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hz : range (pair r s) ⊆ Metric.ball c R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∮ x in C(c, R), jacobiSecondKind α β r s n x * p.eval x) =
        carlsonJacobiCoefficient α β r s n p := by
  have hcont := isRegCarlsonContinuation_polynomial (derivative^[n] p) (pair r s)
  rw [← iteratedDeriv_eval] at hcont
  have he := circleIntegral_jacobiSecondKind_mul α β r s n hcont hR
    (show DiffContOnCl ℂ (fun x => p.eval x) (Metric.ball c R) from
      ⟨p.differentiableOn, p.continuous.continuousOn⟩) hz
  simpa only [carlsonJacobiCoefficient_apply, carlsonPolynomialAverage,
    LinearMap.smul_apply, smul_eq_mul, sum_pair] using he

/-- Carlson's Jacobi polynomials and adjoint second-kind functions are
biorthogonal on every positively oriented circle enclosing the endpoint segment. -/
theorem circleIntegral_jacobiOn_mul_jacobiSecondKind (α β r s : ℂ)
    (hc : IsCarlsonGammaRegular (α + β + 2)) (m n : ℕ)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hz : range (pair r s) ⊆ Metric.ball c R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∮ x in C(c, R), (jacobiOn α β r s m).eval x * jacobiSecondKind α β r s n x) =
        if m = n then 1 else 0 := by
  simp_rw [mul_comm ((jacobiOn α β r s m).eval _)]
  rw [circleIntegral_jacobiSecondKind_mul_polynomial α β r s n _ hR hz,
    carlsonJacobiCoefficient_apply_jacobiOn α β r s hc]

end Carlson.TwoVariable
