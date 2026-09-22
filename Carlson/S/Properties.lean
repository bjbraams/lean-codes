/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.S.Series

/-!
# Permutation, translation, and special values of S

Functional identities for the native and continued S-functions: symmetry under simultaneous
permutation of parameters and nodes, the exponential translation law
`S(b, z + a) = exp a * S(b, z)`, and the value at the zero node vector.

## Main results

* `Carlson.regCarlsonSIntegral_perm`, `Carlson.regCarlsonSIntegral_add_const`,
  `Carlson.regCarlsonSIntegral_zero`: identities for the native integral.
* `Carlson.regCarlsonSSeries_add_const`: the translation law for the continued function.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- Simultaneous permutation of the Dirichlet parameters and variables leaves the native
regularized `S` integral unchanged. -/
theorem regCarlsonSIntegral_perm (b z : ι → ℂ) (σ : Equiv.Perm ι) :
    regCarlsonSIntegral (b ∘ σ) (z ∘ σ) = regCarlsonSIntegral b z :=
  regCarlsonDirichletAverage_perm b z exp σ

/-- Translating every variable by `a` multiplies the native regularized `S` integral by
`exp a`.  This is Carlson's exponential translation identity. -/
theorem regCarlsonSIntegral_add_const (b z : ι → ℂ) (a : ℂ) :
    regCarlsonSIntegral b (fun i ↦ z i + a) = exp a * regCarlsonSIntegral b z := by
  unfold regCarlsonSIntegral
  rw [show (fun i ↦ z i + a) = (fun i ↦ 1 * z i + a) by funext i; simp]
  rw [← regCarlsonDirichletAverage_comp_affine b z exp 1 a]
  unfold regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [one_mul, exp_add]
  ring

/-- Translation of all variables for Carlson's analytically continued `S` function.  This
global identity follows from the native integral identity and uniqueness of continuation in
the Dirichlet parameters. -/
theorem regCarlsonSSeries_add_const (z b : ι → ℂ) (a : ℂ) :
    regCarlsonSSeries (fun i => z i + a) b = exp a * regCarlsonSSeries z b := by
  let z' : ι → ℂ := fun i => z i + a
  have hleft : IsRegCarlsonSContinuation z' (regCarlsonSSeries z') :=
    isRegCarlsonSContinuation_series z'
  suffices hright : IsRegCarlsonSContinuation z'
      (fun b => exp a * regCarlsonSSeries z b) from congrFun (hleft.eq hright) b
  refine ⟨?_, ?_⟩
  · intro b hb
    exact analyticAt_const.mul
      (analyticOnNhd_regCarlsonSSeries z b (Set.mem_univ b))
  · intro b hb
    dsimp only
    rw [regCarlsonSSeries_eq_regCarlsonSIntegral z hb]
    exact (regCarlsonSIntegral_add_const b z a).symm

/-- At the zero variable vector, the native regularized `S` integral is the reciprocal Gamma
factor on the ordinary convergence domain. -/
theorem regCarlsonSIntegral_zero {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonSIntegral b (fun _ ↦ 0) = 1 / Gamma (∑ i, b i) := by
  simpa [regCarlsonSIntegral] using
    (regCarlsonDirichletAverage_const exp 0 hb)

end Carlson
