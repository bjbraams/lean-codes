/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.QuadraticSlit
public import Carlson.TwoVariable.GaussHypergeometric
public import Carlson.TwoVariable.ParameterSymmetry
public import Carlson.TwoVariable.R.ElementaryValues
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# The quadratic transformation of `₂F₁` (Exercise 6.10-1)

For real `z < 0` choose `x, y > 0` with `xy = 1` and `((x + y)/2)² = 1 - z`. The second
quadratic transformation (6.10-1 in the text) and the first one (6.9) applied to
`R_{-2α}(α + β, α + β; x², y²)` give
`R_{-2α}(α - β + ½, 2β; 1, 1 - z) = R_{-α}(α + ½, β; 1, (1 - 2z)²)`. The identity theorem extends
this to `re z < 1/2`, and density removes the exclusion of poles of `Γ(α + β)`. By (8.3-7) this
is Carlson's `₂F₁(2α, 2β; α + β + ½; z) = ₂F₁(α, β; α + β + ½; 4z(1 - z))`.

## Main results

* `Carlson.TwoVariable.regCarlsonR_quadratic_gauss`: the R-function form, for all `α, β` and
  `re z < 1/2`.
* `Carlson.TwoVariable.regularizedGaussHGFun_quadratic`: the regularized `₂F₁` form.
* `Carlson.TwoVariable.ordinaryHypergeometric_quadratic`: Exercise 6.10-1.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.10.
-/

open Complex Filter Set
open scoped Topology

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- The quadratic transformation in R-function form at real `z < 0`, when `α + β` is not a
nonpositive integer. -/
theorem regCarlsonR_quadratic_gauss_of_neg (α β : ℂ) (hαβ : ∀ m : ℕ, α + β ≠ -m) {z : ℝ}
    (hz : z < 0) :
    regCarlsonR (-2 * α) (pair (α - β + 1 / 2) (2 * β)) (pair 1 (1 - z)) =
      regCarlsonR (-α) (pair (α + 1 / 2) β) (pair 1 ((1 - 2 * z) ^ 2)) := by
  set s := Real.sqrt (1 - z)
  set r := Real.sqrt (-z)
  have hs2 : s ^ 2 = 1 - z := Real.sq_sqrt (by linarith)
  have hr2 : r ^ 2 = -z := Real.sq_sqrt (by linarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrs : r < s := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  set x : ℂ := ((s + r : ℝ) : ℂ)
  set y : ℂ := ((s - r : ℝ) : ℂ)
  have hx : 0 < x.re := by simp only [x, ofReal_re]; linarith
  have hy : 0 < y.re := by simp only [y, ofReal_re]; linarith
  have hx2 : 0 < (x ^ 2).re := by
    rw [show x ^ 2 = (((s + r) ^ 2 : ℝ) : ℂ) by push_cast [x]; ring, ofReal_re]; positivity
  have hy2 : 0 < (y ^ 2).re := by
    rw [show y ^ 2 = (((s - r) ^ 2 : ℝ) : ℂ) by push_cast [y]; ring, ofReal_re]
    exact pow_pos (by linarith) 2
  have hsec := regRSlit_secondQuadratic (-2 * α) (α + β) x y hx hy
  have hfir := regRSlit_firstQuadratic (-α) (α + β) (x ^ 2) (y ^ 2) hx2 hy2
  have hs2c : (s : ℂ) ^ 2 = 1 - z := by exact_mod_cast hs2
  have hr2c : (r : ℂ) ^ 2 = -z := by exact_mod_cast hr2
  have hAM : arithmeticMeanSq x y = 1 - z := by
    simp only [arithmeticMeanSq, x, y]; push_cast; linear_combination hs2c
  have hGM : geometricMeanSq x y = 1 := by
    simp only [geometricMeanSq, x, y]; push_cast; linear_combination hs2c - hr2c
  have hAM2 : arithmeticMeanSq (x ^ 2) (y ^ 2) = (1 - 2 * z) ^ 2 := by
    simp only [arithmeticMeanSq, x, y]; push_cast
    congr 1; linear_combination hs2c + hr2c
  have hGM2 : geometricMeanSq (x ^ 2) (y ^ 2) = 1 := by
    simp only [geometricMeanSq, x, y]; push_cast
    linear_combination (((s : ℂ) ^ 2 - r ^ 2) + 1) * (hs2c - hr2c)
  rw [hAM, hGM, show 2 * (α + β) + -2 * α = 2 * β by ring,
    show 1 / 2 - (α + β) - -2 * α = α - β + 1 / 2 by ring] at hsec
  rw [hAM2, hGM2, show 2 * -α = -2 * α by ring, show α + β + -α = β by ring,
    show 1 / 2 - -α = α + 1 / 2 by ring] at hfir
  have hq : quadraticGammaRatio (α + β) ≠ 0 := by
    unfold quadraticGammaRatio
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (inv_ne_zero (Gamma_ne_zero hαβ))
    · rw [cpow_def_of_ne_zero two_ne_zero]; exact exp_ne_zero _
    · exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h1 : (1 - (z : ℂ)) ∈ slitPlane := by
    rw [show (1 : ℂ) - z = ((1 - z : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.mpr (by linarith)
  have h2 : ((1 - 2 * (z : ℂ)) ^ 2) ∈ slitPlane := by
    rw [show ((1 : ℂ) - 2 * z) ^ 2 = (((1 - 2 * z) ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.mpr (by nlinarith)
  rw [← regCarlsonR_pair_swap _ _ _ one_mem_slitPlane h1,
    ← regCarlsonR_pair_swap _ _ _ one_mem_slitPlane h2]
  exact mul_left_cancel₀ hq (hsec.symm.trans hfir)

/-- Membership facts for the nodes of the quadratic transformation when `re z < 1/2`. -/
theorem quadratic_gauss_mem_slitPlane {z : ℂ} (hz : z.re < 1 / 2) :
    1 - z ∈ slitPlane ∧ (1 - 2 * z) ^ 2 ∈ slitPlane := by
  have h1 : 0 < (1 - 2 * z).re := by simp; linarith
  refine ⟨Or.inl (by simp; linarith), ?_⟩
  rw [sq]; exact mul_mem_slitPlane_of_re_pos h1 h1

/-- The R-function form of the quadratic transformation is analytic in `z` on `re z < 1/2`. -/
theorem analyticAt_quadratic_gauss_sides (α β : ℂ) {z : ℂ} (hz : z.re < 1 / 2) :
    AnalyticAt ℂ (fun w => regCarlsonR (-2 * α) (pair (α - β + 1 / 2) (2 * β)) (pair 1 (1 - w)))
        z ∧
      AnalyticAt ℂ (fun w => regCarlsonR (-α) (pair (α + 1 / 2) β) (pair 1 ((1 - 2 * w) ^ 2)))
        z := by
  obtain ⟨h1, h2⟩ := quadratic_gauss_mem_slitPlane hz
  constructor
  · refine analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pi_iff.mpr fun i => ?_) fun i => ?_ <;> fin_cases i
    · exact analyticAt_const
    · exact analyticAt_const.sub analyticAt_id
    · exact one_mem_slitPlane
    · exact h1
  · refine analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pi_iff.mpr fun i => ?_) fun i => ?_ <;> fin_cases i
    · exact analyticAt_const
    · exact ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).pow 2)
    · exact one_mem_slitPlane
    · exact h2

/-- The quadratic transformation in R-function form for `re z < 1/2`, when `α + β` is not a
nonpositive integer. -/
theorem regCarlsonR_quadratic_gauss_of_ne (α β : ℂ) (hαβ : ∀ m : ℕ, α + β ≠ -m) {z : ℂ}
    (hz : z.re < 1 / 2) :
    regCarlsonR (-2 * α) (pair (α - β + 1 / 2) (2 * β)) (pair 1 (1 - z)) =
      regCarlsonR (-α) (pair (α + 1 / 2) β) (pair 1 ((1 - 2 * z) ^ 2)) := by
  set U : Set ℂ := Complex.reLm ⁻¹' Set.Iio (1 / 2)
  have hUmem : ∀ w : ℂ, w ∈ U ↔ w.re < 1 / 2 := fun w => by simp [U]
  have hUc : Convex ℝ U := (convex_Iio _).is_linear_preimage Complex.reLm.isLinear
  have hF : AnalyticOnNhd ℂ
      (fun w => regCarlsonR (-2 * α) (pair (α - β + 1 / 2) (2 * β)) (pair 1 (1 - w))) U :=
    fun w hw => (analyticAt_quadratic_gauss_sides α β ((hUmem w).mp hw)).1
  have hG : AnalyticOnNhd ℂ
      (fun w => regCarlsonR (-α) (pair (α + 1 / 2) β) (pair 1 ((1 - 2 * w) ^ 2))) U :=
    fun w hw => (analyticAt_quadratic_gauss_sides α β ((hUmem w).mp hw)).2
  have h0 : (-1 : ℂ) ∈ U := (hUmem _).mpr (by norm_num)
  have hfreq : ∃ᶠ w in 𝓝[≠] (-1 : ℂ),
      regCarlsonR (-2 * α) (pair (α - β + 1 / 2) (2 * β)) (pair 1 (1 - w)) =
        regCarlsonR (-α) (pair (α + 1 / 2) β) (pair 1 ((1 - 2 * w) ^ 2)) := by
    have ht : Tendsto (fun n : ℕ => ((-1 + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝[≠] (-1)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have := (continuous_ofReal.tendsto (-1 + 0)).comp
          ((tendsto_const_nhds (x := (-1 : ℝ))).add (tendsto_one_div_add_atTop_nhds_zero_nat
            |>.comp (tendsto_add_atTop_nat 1)))
        simp only [add_zero, ofReal_neg, ofReal_one] at this
        refine this.congr fun n => ?_
        simp; ring_nf
      · exact Eventually.of_forall fun n => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h
          have h' : (-1 + 1 / ((n : ℝ) + 2)) = -1 := by exact_mod_cast h
          have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
          linarith
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    have hneg : -1 + 1 / ((n : ℝ) + 2) < 0 := by
      have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) two_pos]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
    exact regCarlsonR_quadratic_gauss_of_neg α β hαβ hneg
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hUc.isPreconnected h0 hfreq
    ((hUmem z).mpr hz)

/-- **The quadratic transformation of Exercise 6.10-1** in R-function form, for all complex
`α, β` and `re z < 1/2`: `R_{-2α}(α - β + ½, 2β; 1, 1 - z) = R_{-α}(α + ½, β; 1, (1 - 2z)²)`,
regularized by `Γ(α + β + ½)`. -/
theorem regCarlsonR_quadratic_gauss (α β : ℂ) {z : ℂ} (hz : z.re < 1 / 2) :
    regCarlsonR (-2 * α) (pair (α - β + 1 / 2) (2 * β)) (pair 1 (1 - z)) =
      regCarlsonR (-α) (pair (α + 1 / 2) β) (pair 1 ((1 - 2 * z) ^ 2)) := by
  obtain ⟨h1, h2⟩ := quadratic_gauss_mem_slitPlane hz
  set f : ℂ → ℂ := fun β => regCarlsonR (-2 * α) (pair (α - β + 1 / 2) (2 * β)) (pair 1 (1 - z))
  set g : ℂ → ℂ := fun β => regCarlsonR (-α) (pair (α + 1 / 2) β) (pair 1 ((1 - 2 * z) ^ 2))
  have hslit1 : pair (1 : ℂ) (1 - z) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact one_mem_slitPlane
    · exact h1
  have hslit2 : pair (1 : ℂ) ((1 - 2 * z) ^ 2) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact one_mem_slitPlane
    · exact h2
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun β =>
    (analyticAt_regCarlsonR_comp analyticAt_const (analyticAt_pi_iff.mpr fun i => by
      fin_cases i
      · exact (analyticAt_const.sub analyticAt_id).add analyticAt_const
      · exact analyticAt_const.mul analyticAt_id) analyticAt_const hslit1).continuousAt
  have hg : Continuous g := continuous_iff_continuousAt.mpr fun β =>
    (analyticAt_regCarlsonR_comp analyticAt_const (analyticAt_pi_iff.mpr fun i => by
      fin_cases i
      · exact analyticAt_const
      · exact analyticAt_id) analyticAt_const hslit2).continuousAt
  have hdense : Dense (Set.range fun m : ℕ => -(m : ℂ) - α)ᶜ :=
    (Set.countable_range _).dense_compl ℂ
  have heq : Set.EqOn f g (Set.range fun m : ℕ => -(m : ℂ) - α)ᶜ := by
    intro β hβ
    refine regCarlsonR_quadratic_gauss_of_ne α β (fun m hm => hβ ⟨m, ?_⟩) hz
    linear_combination -hm
  exact congrFun (hf.ext_on hdense hg heq) β

/-- **Exercise 6.10-1** with Mathlib's regularized Gauss function: for `re z < 1/2`, `‖z‖ < 1`
and `‖4z(1 - z)‖ < 1`, `₂F₁(2α, 2β; α + β + ½; z)/Γ(α + β + ½) =
₂F₁(α, β; α + β + ½; 4z(1 - z))/Γ(α + β + ½)`. -/
theorem regularizedGaussHGFun_quadratic (α β : ℂ) {z : ℂ} (hz : z.re < 1 / 2) (h1 : ‖z‖ < 1)
    (h2 : ‖4 * z * (1 - z)‖ < 1) :
    regularizedGaussHGFun (2 * α) (2 * β) (α + β + 1 / 2) z =
      regularizedGaussHGFun α β (α + β + 1 / 2) (4 * z * (1 - z)) := by
  have hL := regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun (2 * α) (2 * β) (α + β + 1 / 2) h1
  have hR := regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun α β (α + β + 1 / 2) h2
  rw [← hL, ← hR, show 1 - 4 * z * (1 - z) = (1 - 2 * z) ^ 2 by ring,
    show α + β + 1 / 2 - 2 * β = α - β + 1 / 2 by ring, show α + β + 1 / 2 - β = α + 1 / 2 by ring,
    show -(2 * α) = -2 * α by ring]
  exact regCarlsonR_quadratic_gauss α β hz

/-- **Exercise 6.10-1**: if `α + β + ½` is not a nonpositive integer, `re z < 1/2`, `‖z‖ < 1`
and `‖4z(1 - z)‖ < 1`, then `₂F₁(2α, 2β; α + β + ½; z) = ₂F₁(α, β; α + β + ½; 4z(1 - z))`. The
regularized form `regularizedGaussHGFun_quadratic` holds for all parameters, and the R-function
form `regCarlsonR_quadratic_gauss` on the whole half-plane `re z < 1/2`. -/
theorem ordinaryHypergeometric_quadratic (α β : ℂ) (hc : ∀ k : ℕ, α + β + 1 / 2 ≠ -k) {z : ℂ}
    (hz : z.re < 1 / 2) (h1 : ‖z‖ < 1) (h2 : ‖4 * z * (1 - z)‖ < 1) :
    ordinaryHypergeometric (2 * α) (2 * β) (α + β + 1 / 2) z =
      ordinaryHypergeometric α β (α + β + 1 / 2) (4 * z * (1 - z)) := by
  have h := regularizedGaussHGFun_quadratic α β hz h1 h2
  rw [← ordinaryHypergeometric_div_Gamma_eq hc, ← ordinaryHypergeometric_div_Gamma_eq hc] at h
  exact (div_left_inj' (Gamma_ne_zero hc)).mp h

end Carlson.TwoVariable
