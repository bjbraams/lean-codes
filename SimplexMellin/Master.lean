/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.Bridge
public import ToMathlib.Analysis.SpecialFunctions.RamanujanMaster

/-!
# A master theorem with simplex structure

Combining Ramanujan's master theorem (`Complex.ramanujan_master_theorem`) with the Mellin bridge
(`Dirichlet.mvMellin_radial_mul_eq`) gives a several-variable master theorem for functions of the
form `F(x) = Φ(∑ x) g(x / ∑ x)` on the positive orthant, with `Φ` the function of the
one-variable theorem and `g` a kernel on the simplex:

* near the origin, `F(x) = ∑ φ(k) (-(∑ x))^k g(x / ∑ x)`;
* `∫_{ℝ₊^ι} x^(b-1) F(x) dx = π / sin (π ∑ b) · φ(-∑ b) · ∏ Γ(b i) · T_b[g]` for `Re b i > 0`,
  `Re ∑ b < δ`.

For `g = 1` the transform `T_b[1] = 1 / Γ(∑ b)` gives the Mellin transform of a function of
`∑ x` alone.

## Main results

* `Dirichlet.ramanujanFunction_sum_mul_hasSum`: the series near the origin.
* `Dirichlet.mvMellin_ramanujanFunction_radial`: the several-variable Mellin transform.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Real

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- **The series near the origin.** For `x` in the positive orthant with `∑ x < e^(-P)`,
`Φ(∑ x) g(x / ∑ x) = ∑ φ(k) (-(∑ x))^k g(x / ∑ x)`. -/
theorem ramanujanFunction_sum_mul_hasSum {φ : ℂ → ℂ} {δ C P A : ℝ}
    (h : Complex.RamanujanClass φ δ C P A) (g : (ι → ℝ) → ℂ) {x : ι → ℝ}
    (hx : 0 < ∑ i, x i) (hxP : ∑ i, x i < Real.exp (-P)) :
    HasSum (fun k : ℕ => φ k * (-((∑ i, x i : ℝ) : ℂ)) ^ k * g ((∑ i, x i)⁻¹ • x))
      (Complex.ramanujanFunction φ δ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x)) :=
  ((Complex.ramanujan_master_theorem h).1 _ hx hxP).mul_right _

/-- **A master theorem with simplex structure.** For `Re b i > 0` and `Re ∑ b < δ`,
`∫_{ℝ₊^ι} x^(b-1) Φ(∑ x) g(x / ∑ x) dx = π / sin (π ∑ b) · φ(-∑ b) · ∏ Γ(b i) · T_b[g]`. -/
theorem mvMellin_ramanujanFunction_radial [Nonempty ι] {φ : ℂ → ℂ} {δ C P A : ℝ}
    (h : Complex.RamanujanClass φ δ C P A) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hbδ : (∑ i, b i).re < δ) {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    mvMellin (fun x => Complex.ramanujanFunction φ δ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x)) b =
      π / sin (π * ∑ i, b i) * φ (-∑ i, b i) *
        ((∏ i, Gamma (b i)) * regDirichletIntegral b g) := by
  have hc0 : 0 < δ / 2 := by linarith [h.delta_pos]
  have hcδ : δ / 2 < δ := by linarith [h.delta_pos]
  have hB0 : 0 < (∑ i, b i).re := by
    rw [re_sum]
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact Finset.sum_pos (fun j _ => hb j) ⟨i, Finset.mem_univ i⟩
  have hcont : ContinuousOn (Complex.ramanujanFunction φ δ) (Ioi 0) :=
    h.continuousOn_mellinInv hc0 hcδ
  rw [mvMellin_radial_mul_eq hb hg hcont, ((Complex.ramanujan_master_theorem h).2 _ hB0 hbδ).2]

end Dirichlet
