/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.CarlsonDirichletAverage.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Averages of Cauchy's integral formula

This file develops the foundational part of [Carl77, Section 5.11].  We use Mathlib's circle
integral formulation of Cauchy's theorem.  Carlson works more generally with positively
oriented rectifiable Jordan curves.

The first results establish that the integer resolvent kernel is single-valued and analytic
away from the convex hull of the Carlson variables.  The final theorem below averages
Cauchy's formula before interchanging the circle and simplex integrals.  That interchange,
which gives Carlson's Representation 5.11-2 verbatim, requires a separate product-integrability
estimate and Fubini theorem.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.11,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory Metric
open scoped Classical

@[expose] public noncomputable section CarlsonCauchyAverage

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The integer Cauchy kernel occurring in Carlson's Theorem 5.11-1 and
Representation 5.11-2. -/
def carlsonCauchyKernel (n : ℕ) (z : ι → ℂ) (u : ι → ℝ) (s : ℂ) : ℂ :=
  (s - carlsonAffineForm z u) ^ (-(n + 1 : ℤ))

/-- The native regularized average of Carlson's integer Cauchy kernel. -/
def regCarlsonResolvent (n : ℕ) (b z : ι → ℂ) (s : ℂ) : ℂ :=
  regCarlsonDirichletAverage b z (fun w ↦ (s - w) ^ (-(n + 1 : ℤ)))

/-- The regularized resolvent is the Dirichlet integral of the corresponding pointwise
Cauchy kernel. -/
theorem regCarlsonResolvent_eq_regDirichletIntegral
    (n : ℕ) (b z : ι → ℂ) (s : ℂ) :
    regCarlsonResolvent n b z s =
      regDirichletIntegral b (fun u ↦ carlsonCauchyKernel n z u s) := by
  rfl

/-- The denominator of Carlson's Cauchy kernel does not vanish when `s` lies outside the
convex hull of the Carlson variables. -/
theorem sub_carlsonAffineForm_ne_zero_of_mem_compl_convexHull
    (z : ι → ℂ) {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι)
    {s : ℂ} (hs : s ∈ (convexHull ℝ (Set.range z))ᶜ) :
    s - carlsonAffineForm z u ≠ 0 :=
  sub_carlsonAffineForm_ne_zero hs hu

/-- For a fixed simplex point, Carlson's integer Cauchy kernel is analytic in `s` outside
the convex hull of the variables.  Integer powers make this statement branch-independent. -/
theorem analyticOnNhd_carlsonCauchyKernel (n : ℕ) (z : ι → ℂ)
    {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι) :
    AnalyticOnNhd ℂ (carlsonCauchyKernel n z u)
      ((convexHull ℝ (Set.range z))ᶜ) := by
  intro s hs
  unfold carlsonCauchyKernel
  exact (analyticAt_id.sub analyticAt_const).zpow
    (sub_carlsonAffineForm_ne_zero_of_mem_compl_convexHull z hu hs)

/-- The first Cauchy kernel is the usual reciprocal kernel. -/
@[simp] theorem carlsonCauchyKernel_zero (z : ι → ℂ) (u : ι → ℝ) (s : ℂ) :
    carlsonCauchyKernel 0 z u s = (s - carlsonAffineForm z u)⁻¹ := by
  simp [carlsonCauchyKernel]

/-- Cauchy's integral formula at a Carlson affine combination contained in a circle. -/
theorem two_pi_I_inv_mul_circleIntegral_carlsonCauchyKernel_zero
    {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f (ball c R))
    (z : ι → ℂ) {u : ι → ℝ} (hu : carlsonAffineForm z u ∈ ball c R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∮ s in C(c, R), carlsonCauchyKernel 0 z u s * f s) =
      f (carlsonAffineForm z u) := by
  simpa [carlsonCauchyKernel, smul_eq_mul] using
    hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hu

/-- Circle form of the first step in Carlson's Representation 5.11-2: average Cauchy's
formula over the simplex, before applying Fubini to interchange the two integrals. -/
theorem regCarlsonDirichletAverage_eq_average_circleIntegral
    {b : ι → ℂ} (z : ι → ℂ) {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball c R))
    (hz : ∀ u, u ∈ stdSimplex ℝ ι → carlsonAffineForm z u ∈ ball c R) :
    regCarlsonDirichletAverage b z f =
      (2 * (Real.pi : ℂ) * I)⁻¹ * regDirichletIntegral b
        (fun u ↦ ∮ s in C(c, R), carlsonCauchyKernel 0 z u s * f s) := by
  unfold regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (isClosed_stdSimplex ℝ ι).measurableSet
  intro u hu
  dsimp only
  have hcauchy := two_pi_I_inv_mul_circleIntegral_carlsonCauchyKernel_zero
    hf z (hz u hu)
  rw [← hcauchy]
  ring

/-- The circle-contour expression on the right side of Carlson's Representation 5.11-2,
specialized to the zeroth derivative. -/
def regCarlsonCauchyRepresentation
    (b z : ι → ℂ) (c : ℂ) (R : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ∮ s in C(c, R), regCarlsonResolvent 0 b z s * f s

end DirichletTransform

end CarlsonCauchyAverage
