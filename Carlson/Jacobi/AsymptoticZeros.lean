/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Chebyshev
public import Carlson.Jacobi.Normalization
public import Pochhammer.Estimates
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Zeros and the ratio interpretation of polynomial asymptotics

Carlson's Theorem 7.4-2, p. 198, states a two-saddle approximation on
`V = {(x,y) : xy ≠ 0, x² ≠ y²}` and defines uniform asymptotics by convergence
of the quotient to one. Taken as an unextended pointwise quotient on all of
`V`, this needs a qualification at zeros. At `α = β = -1/2`, `x = 1`, `y = I`,
the polynomial vanishes in every odd degree. No quotient by any sequence can
then converge to one with Lean's totalized division. In ordinary division it
is either zero or undefined along that subsequence.

These results concern the literal quotient. They do not refute a formulation
using removable extensions, or a two-saddle expansion with an additive error
controlled by the sum of the magnitudes of the two saddle contributions.
-/

@[expose] public noncomputable section
open Filter Polynomial Complex
open scoped Topology

namespace Carlson.TwoVariable

/-- Every odd-degree monic Chebyshev specialization vanishes at the midpoint. -/
theorem eval_monicJacobi_neg_half_odd_zero (k : ℕ) :
    (monicJacobi (-1 / 2 : ℂ) (-1 / 2) (2 * k + 1)).eval 0 = 0 := by
  simp [monicJacobi, jacobi_neg_half_eq_chebyshev_T]

/-- At the midpoint, no unextended relative approximation to the full monic
Chebyshev sequence can have quotient tending to one. -/
theorem not_tendsto_monicJacobi_neg_half_zero_div (g : ℕ → ℂ) :
    ¬ Tendsto (fun n : ℕ => (monicJacobi (-1 / 2 : ℂ) (-1 / 2) n).eval 0 / g n)
      atTop (𝓝 1) := by
  intro h
  have hn : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => by dsimp; omega) tendsto_id
  have hh := h.comp hn
  simp only [Function.comp_def, eval_monicJacobi_neg_half_odd_zero, zero_div] at hh
  have he : (0 : ℂ) = 1 := tendsto_nhds_unique tendsto_const_nhds hh
  exact zero_ne_one he

/-- The polynomial normalization at the counterexample has no singular degrees;
the obstruction comes from polynomial zeros, not parameter poles. -/
theorem chebyshev_midpoint_pochhammer_ne_zero (n : ℕ) :
    (ascPochhammer ℂ n).eval (1 - 2 * (n : ℂ)) ≠ 0 := by
  by_cases hn : n = 0
  · subst n; simp
  rw [show 1 - 2 * (n : ℂ) = 1 - (n : ℂ) - n by ring, ascPochhammer_eval_reflect]
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  apply ascPochhammer_eval_ne_zero_of_re_pos
  simp only [natCast_re]
  exact_mod_cast Nat.pos_of_ne_zero hn

/-- The obstruction expressed in Carlson's rational polynomial normalization at
nodes `1` and `-1`, corresponding to the admissible square roots `1` and `I`. -/
theorem not_tendsto_carlsonRPolynomial_chebyshev_midpoint_div (g : ℕ → ℂ) :
    ¬ Tendsto (fun n : ℕ =>
      (carlsonRPolynomialNumerator₂ n (1 / 2 - n) (1 / 2 - n) 1 (-1) /
        (ascPochhammer ℂ n).eval (1 - 2 * (n : ℂ))) / g n) atTop (𝓝 1) := by
  have he (n : ℕ) : (monicJacobi (-1 / 2 : ℂ) (-1 / 2) n).eval 0 =
      carlsonRPolynomialNumerator₂ n (1 / 2 - n) (1 / 2 - n) 1 (-1) /
        (ascPochhammer ℂ n).eval (1 - 2 * (n : ℂ)) := by
    convert eval_monicJacobi_eq_numerator (-1 / 2) (-1 / 2) 0 n using 1
    norm_num
  simpa only [he] using not_tendsto_monicJacobi_neg_half_zero_div g

/-- The point `(1,I)` lies in Carlson's polynomial asymptotic domain, but the
literal ratio to a sum of two saddle terms cannot converge to one there,
regardless of the two constants. -/
theorem carlson_polynomial_two_saddle_ratio_counterexample :
    (1 : ℂ) * I ≠ 0 ∧ (1 : ℂ) ^ 2 ≠ I ^ 2 ∧ ∀ C₁ C₂ : ℂ,
      ¬ Tendsto (fun n : ℕ =>
        (carlsonRPolynomialNumerator₂ n (1 / 2 - n) (1 / 2 - n) 1 (-1) /
          (ascPochhammer ℂ n).eval (1 - 2 * (n : ℂ))) /
          (C₁ * ((1 + I) / 2) ^ (2 * n) + C₂ * ((1 - I) / 2) ^ (2 * n))) atTop (𝓝 1) := by
  refine ⟨by simp, by norm_num, fun C₁ C₂ => ?_⟩
  exact not_tendsto_carlsonRPolynomial_chebyshev_midpoint_div _

end Carlson.TwoVariable
