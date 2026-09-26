/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.Quadratic
public import Carlson.R.JointParameter
public import Carlson.R.Explicit

/-!
# Quadratic transformations on the full Dirichlet parameter domain

The regularized transformations are entire identities in `(t, β)`. The entire Gamma ratio
below, rather than a quotient evaluated at Gamma poles, implements Legendre duplication.
Node domains are unchanged from the native transformation theorems.
`EqualParameter` supplies the canonical ordinary continuation, retaining the removable
values at nonpositive integral `β` where the entire ratio here vanishes.

## Main results

* `Carlson.TwoVariable.analyticOnNhd_quadraticGammaRatio`: Legendre's duplication ratio is
  entire.
* `Carlson.TwoVariable.Gamma_mul_quadraticGammaRatio`: Duplication converts the native
  normalization into the equal-parameter normalization.
* `Carlson.TwoVariable.regCarlsonR_pair_firstQuadratic`: First quadratic transformation, entire
  in both parameters, including exceptional Gamma parameters. There are no convergence or
  non-pole hypotheses.
* `Carlson.TwoVariable.regCarlsonR_pair_secondQuadratic`: Second quadratic transformation,
  entire in both parameters.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Complex ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- Entire extension of `Γ(β + 1/2) / Γ(2β)`. The formula remains meaningful at Gamma poles. -/
def quadraticGammaRatio (β : ℂ) : ℂ :=
  (2 : ℂ) ^ (1 - 2 * β) * (Real.sqrt Real.pi : ℂ) * (Gamma β)⁻¹

/-- Legendre's duplication ratio is entire. -/
theorem analyticOnNhd_quadraticGammaRatio : AnalyticOnNhd ℂ quadraticGammaRatio univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  have he : Differentiable ℂ (fun β : ℂ => 1 - 2 * β) :=
    (differentiable_const (1 : ℂ)).sub ((differentiable_const (2 : ℂ)).mul differentiable_id)
  have hp : Differentiable ℂ (fun β : ℂ => (2 : ℂ) ^ (1 - 2 * β)) :=
    fun β => (he β).const_cpow (Or.inl two_ne_zero)
  exact ((hp.mul_const (Real.sqrt Real.pi : ℂ)).mul differentiable_one_div_Gamma).differentiableOn

/-- Duplication converts the native normalization into the equal-parameter normalization. -/
theorem Gamma_mul_quadraticGammaRatio {β : ℂ} (hβ : 0 < β.re) :
    Gamma (β + β) * quadraticGammaRatio β = Gamma (β + 1 / 2) := by
  have hG := Gamma_ne_zero_of_re_pos hβ
  apply (mul_right_cancel₀ hG)
  dsimp [quadraticGammaRatio]
  rw [show β + β = 2 * β by ring]
  have H := Gamma_mul_Gamma_add_half β
  calc
    _ = Gamma (2 * β) * (2 : ℂ) ^ (1 - 2 * β) * (Real.sqrt Real.pi : ℂ) := by
      field_simp
    _ = _ := by linear_combination -H

/-- Permanence of functional relations in the two complex parameters. -/
private theorem quadratic_parameter_identity
    (l : ℂ → ℂ) (r : ℂ → ℂ → Fin 2 → ℂ)
    (hl : AnalyticOnNhd ℂ l univ)
    (hr : AnalyticOnNhd ℂ (fun p : Fin 2 → ℂ => r (p 0) (p 1)) univ)
    (hseed : r 0 (1 / 4) ∈ mvBetaConvergent)
    (hsum : ∀ t β, ∑ i, r t β i = β + 1 / 2)
    (z Z : Fin 2 → ℂ) (hz : z ∈ carlsonRVariableDomain) (hZ : Z ∈ carlsonRVariableDomain)
    (hnative : ∀ t β, pair β β ∈ mvBetaConvergent → r t β ∈ mvBetaConvergent →
      carlsonRIntegral (l t) (pair β β) z = carlsonRIntegral t (r t β) Z)
    (t β : ℂ) :
    regCarlsonR (l t) (pair β β) z =
      quadraticGammaRatio β * regCarlsonR t (r t β) Z := by
  let L : (Fin 2 → ℂ) → ℂ := fun p => regCarlsonR (l (p 0)) (pair (p 1) (p 1)) z
  let R : (Fin 2 → ℂ) → ℂ := fun p => quadraticGammaRatio (p 1) *
    regCarlsonR (p 0) (r (p 0) (p 1)) Z
  have hleft : AnalyticOnNhd ℂ L univ := by
    intro p _
    refine analyticAt_regCarlsonR_comp
      ((hl _ (mem_univ _)).comp (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 0))
      (analyticAt_pi_iff.mpr fun i => ?_) analyticAt_const
      (carlsonRVariableDomain_subset_slitDomain hz)
    fin_cases i <;> exact (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 1)
  have hright : AnalyticOnNhd ℂ R univ := by
    intro p _
    apply AnalyticAt.mul
    · exact (analyticOnNhd_quadraticGammaRatio _ (mem_univ _)).comp
        (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 1)
    · exact analyticAt_regCarlsonR_comp (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 0)
        (hr p (mem_univ _)) analyticAt_const (carlsonRVariableDomain_subset_slitDomain hZ)
  let o := pair (0 : ℂ) (1 / 4)
  have hbc : ContinuousAt (fun p : Fin 2 → ℂ => pair (p 1) (p 1)) o := by
    apply continuousAt_pi.mpr
    intro i; fin_cases i <;> exact (continuous_apply 1).continuousAt
  have hbl := hbc.tendsto.eventually (isOpen_mvBetaConvergent.mem_nhds (by
    intro i; fin_cases i <;> norm_num [o, pair]))
  have hbr := (hr o (mem_univ _)).continuousAt.tendsto.eventually
    (isOpen_mvBetaConvergent.mem_nhds hseed)
  apply congrFun (hleft.eq_of_eventuallyEq hright (z₀ := o) ?_) (pair t β)
  filter_upwards [hbl, hbr] with p hbp hrp
  dsimp [L, R]
  rw [regCarlsonR_eq_regCarlsonRIntegral _ hbp hz, regCarlsonR_eq_regCarlsonRIntegral _ hrp hZ]
  have hβ : 0 < (p 1).re := hbp 0
  have htotal : 0 < (p 1 + p 1).re := by simpa using add_pos hβ hβ
  apply mul_left_cancel₀ (Gamma_ne_zero_of_re_pos htotal)
  rw [← mul_assoc, Gamma_mul_quadraticGammaRatio hβ]
  have H := hnative (p 0) (p 1) hbp hrp
  simpa only [carlsonRIntegral, sum_pair, hsum] using H

/-- First quadratic transformation, entire in both parameters, including exceptional
Gamma parameters. There are no convergence or non-pole hypotheses. -/
theorem regCarlsonR_pair_firstQuadratic (t β x y : ℂ) (hz : FirstQuadraticDomain x y) :
    regCarlsonR (2 * t) (pair β β) (pair x y) =
      quadraticGammaRatio β * regCarlsonR t (pair (β + t) (1 / 2 - t)) (pair (arithmeticMeanSq x y)
          (geometricMeanSq x y)) := by
  apply quadratic_parameter_identity (fun t => 2 * t) (fun t β => pair (β + t) (1 / 2 - t))
  · exact analyticOnNhd_const.mul analyticOnNhd_id
  · intro p _
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p))
        1).add (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 0)
    · exact analyticAt_const.sub (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 0)
  · intro i; fin_cases i <;> norm_num [pair]
  · intro t β; simp only [sum_pair]; ring
  · exact hz.1
  · exact hz.2
  · exact fun t β hb hr => rIntegral_firstQuadratic t β x y hb hr hz

/-- Second quadratic transformation, entire in both parameters. -/
theorem regCarlsonR_pair_secondQuadratic (t β x y : ℂ) (hz : SecondQuadraticDomain x y) :
    regCarlsonR t (pair β β) (pair (x ^ 2) (y ^ 2)) =
      quadraticGammaRatio β * regCarlsonR t (pair (2 * β + t) (1 / 2 - β - t)) (pair
          (arithmeticMeanSq x y) (geometricMeanSq x y)) := by
  apply quadratic_parameter_identity id (fun t β => pair (2 * β + t) (1 / 2 - β - t))
  · exact analyticOnNhd_id
  · intro p _
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact (analyticAt_const.mul (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 1)).add
        (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 0)
    · exact (analyticAt_const.sub (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 1)).sub
        (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 0)
  · intro i; fin_cases i <;> norm_num [pair]
  · intro t β; simp only [sum_pair]; ring
  · exact hz.1
  · exact hz.2
  · exact fun t β hb hr => rIntegral_secondQuadratic t β x y hb hr hz

end Carlson.TwoVariable
end
