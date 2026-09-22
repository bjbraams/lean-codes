/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Average.Basic
public import Dirichlet.Transform.Laws

/-!
# Associated Dirichlet-average identities

Carlson's relation 5.6-1(4): a Dirichlet average is the sum of the averages with one parameter
raised by one, in regularized form and in Carlson's original weighted normalization.

## Main results

* `Dirichlet.regCarlsonDirichletAverage_eq_sum_addDirichletUnit`.
* `Dirichlet.carlsonDirichletAverage_eq_sum_addDirichletUnit`.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]

/-- Regularized form of Carlson's relation 5.6-1(4): an average is the sum of its
one-coordinate positive parameter shifts. -/
theorem regCarlsonDirichletAverage_eq_sum_addDirichletUnit
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : ι → ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn (fun u : ι → ℝ ↦ f (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regCarlsonDirichletAverage b z f =
      ∑ i, b i * regCarlsonDirichletAverage (addDirichletUnit b i) z f :=
  regDirichletIntegral_eq_sum_addDirichletUnit hb _ hf

/-- Carlson's relation 5.6-1(4) in its original normalization: an average is the weighted
sum of its positive unit shifts, with weights `b i / ∑ j, b j`. -/
theorem carlsonDirichletAverage_eq_sum_addDirichletUnit [Nonempty ι]
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : ι → ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn (fun u : ι → ℝ ↦ f (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    carlsonDirichletAverage b z f =
      ∑ i, (b i / ∑ j, b j) * carlsonDirichletAverage (addDirichletUnit b i) z f := by
  let c : ℂ := ∑ i, b i
  have hcpos : 0 < c.re := by
    simpa [c] using Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty
  have hc : c ≠ 0 := ne_zero_of_re_pos hcpos
  have hsum (i : ι) : ∑ j, addDirichletUnit b i j = c + 1 := sum_addDirichletUnit b i
  unfold carlsonDirichletAverage
  rw [regCarlsonDirichletAverage_eq_sum_addDirichletUnit hb z f hf]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsum, Gamma_add_one c hc]
  change Gamma c * (b i * regCarlsonDirichletAverage (addDirichletUnit b i) z f) =
    (b i / c) * (c * Gamma c * regCarlsonDirichletAverage (addDirichletUnit b i) z f)
  field_simp [hc]

end Dirichlet
