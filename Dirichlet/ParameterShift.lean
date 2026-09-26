/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Complex

/-!
# Unit shifts of Dirichlet parameters and their integral identities

Raising one Dirichlet parameter by one multiplies the regularized density by the corresponding
simplex coordinate. This is the integral form of the parameter-shift relations underlying
Carlson's associated functions.

## Main definitions

* `Dirichlet.addDirichletUnit`: the parameter vector with coordinate `i` raised by one.

## Main results

* `Dirichlet.mul_regDirichletDensity_addDirichletUnit`: the density identity.
* `Dirichlet.mul_regDirichletIntegral_addDirichletUnit`: the integral identity.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The Dirichlet parameter vector obtained by increasing coordinate `i` by one. -/
def addDirichletUnit (b : ι → ℂ) (i : ι) : ι → ℂ :=
  Function.update b i (b i + 1)

/-- A unit parameter shift increases the total parameter by one. -/
@[simp] theorem sum_addDirichletUnit (b : ι → ℂ) (i : ι) :
    ∑ j, addDirichletUnit b i j = (∑ j, b j) + 1 := by
  classical
  unfold addDirichletUnit
  rw [Fintype.sum_eq_add_sum_subtype_ne (Function.update b i (b i + 1)) i,
    Fintype.sum_eq_add_sum_subtype_ne b i]
  simp [add_assoc, add_comm, add_left_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Function.update_of_ne j.property _ _

omit [Fintype ι] in
/-- Unit parameter shifts in two coordinates commute. -/
theorem addDirichletUnit_comm (b : ι → ℂ) (i j : ι) :
    addDirichletUnit (addDirichletUnit b i) j = addDirichletUnit (addDirichletUnit b j) i := by
  classical
  unfold addDirichletUnit
  by_cases hij : i = j
  · subst hij
    simp [Function.update_idem]
  · rw [Function.update_of_ne (Ne.symm hij), Function.update_of_ne hij,
      Function.update_comm hij]

omit [Fintype ι] in
open scoped Classical in
/-- The coordinates of a unit parameter shift. -/
theorem addDirichletUnit_apply (b : ι → ℂ) (i j : ι) :
    addDirichletUnit b i j = b j + if j = i then 1 else 0 := by
  unfold addDirichletUnit
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

omit [Fintype ι] in
/-- A positive unit shift preserves the native convergence region. -/
theorem addDirichletUnit_mem_mvBetaConvergent {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) :
    addDirichletUnit b i ∈ mvBetaConvergent := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [addDirichletUnit] using add_pos_of_pos_of_nonneg (hb i) (by norm_num : 0 ≤ (1 : ℝ))
  · simpa [addDirichletUnit, hji] using hb j

/-- Increasing one Dirichlet parameter by one multiplies the regularized density by the
corresponding simplex coordinate, up to the factor `b i`. -/
theorem mul_regDirichletDensity_addDirichletUnit {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) (u : ι → ℝ) :
    b i * regDirichletDensity (addDirichletUnit b i) u =
      (u i : ℂ) * regDirichletDensity b u := by
  classical
  classical
  by_cases hu : u ∈ stdSimplexInterior
  · rw [regDirichletDensity, Set.indicator_of_mem hu]
    rw [regDirichletDensity, Set.indicator_of_mem hu]
    have hbi : b i ≠ 0 := ne_zero_of_re_pos (hb i)
    have hui : (u i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu.2 i).ne'
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun j ↦ (u j : ℂ) ^ (addDirichletUnit b i j - 1) /
        Gamma (addDirichletUnit b i j))]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun j ↦ (u j : ℂ) ^ (b j - 1) / Gamma (b j))]
    have hoff :
        ∏ j ∈ Finset.univ \ {i},
            (u j : ℂ) ^ (addDirichletUnit b i j - 1) /
              Gamma (addDirichletUnit b i j) =
          ∏ j ∈ Finset.univ \ {i}, (u j : ℂ) ^ (b j - 1) / Gamma (b j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        simp at hj
      simp [addDirichletUnit, hji]
    rw [hoff]
    simp only [addDirichletUnit, Function.update_self]
    rw [Gamma_add_one (b i) hbi]
    rw [show (u i : ℂ) ^ (b i + 1 - 1) = (u i : ℂ) ^ b i by ring_nf]
    rw [cpow_sub _ _ hui, cpow_one]
    field_simp
  · simp [regDirichletDensity, hu]

/-- Integral form of the regularized one-coordinate parameter-shift identity. -/
theorem mul_regDirichletIntegral_addDirichletUnit {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) (f : (ι → ℝ) → ℂ) :
    b i * regDirichletIntegral (addDirichletUnit b i) f =
      regDirichletIntegral b (fun u ↦ (u i : ℂ) * f u) := by
  unfold regDirichletIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  intro u _
  dsimp only
  rw [← mul_assoc, mul_regDirichletDensity_addDirichletUnit hb]
  ring

end Dirichlet
