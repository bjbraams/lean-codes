/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.GaussHypergeometric
public import Pochhammer.Gamma
public import Carlson.TwoVariable.QuadraticHybrid
public import Carlson.R.SmallVariableContinuation
public import Carlson.R.EulerTransform
public import Carlson.R.Homogeneity
public import Carlson.TwoVariable.ParameterSymmetry

/-!
# Gauss-summation exercises of Carlson's Chapter 8

Values of two-variable R-functions at special nodes, obtained from Gauss's theorem (8.3-4)
and the quadratic and Euler transformations, and the resulting Kummer-type evaluations of
`₂F₁` (Carlson's Exercises 8.3-1 to 8.3-5).

## Main results

* `Carlson.TwoVariable.regCarlsonR_two_mul_pair_half_one`: Exercise 8.3-1.
* `Carlson.TwoVariable.regCarlsonR_pair_one_two`: Exercise 8.3-2.
* `Carlson.TwoVariable.regCarlsonR_kummer`: Exercise 8.3-3 (Kummer's theorem at `-1`).
* `Carlson.TwoVariable.ordinaryHypergeometric_kummer_half`: Exercise 8.3-4
  (`₂F₁(2a, 1 - 2a; 2c; 1/2)`).
* `Carlson.TwoVariable.hasSum_beta_series`: Exercise 8.3-5 (a series for the beta function).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.3.
-/

open Complex Polynomial Filter Dirichlet
open scoped Topology

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- **Exercise 8.3-5**: for `x` not a nonpositive integer and `re y > 0`,
`B(x, y) = ∑ₙ (1 - y)ₙ/((x + n) n!)`, with `B(x, y) = Γ(x) Γ(y)/Γ(x + y)`. -/
theorem hasSum_beta_series {x y : ℂ} (hx : IsGammaRegular x) (hy : 0 < y.re) :
    HasSum (fun n : ℕ => (ascPochhammer ℂ n).eval (1 - y) / ((x + n) * n.factorial))
      (Gamma x * Gamma y / Gamma (x + y)) := by
  have hγ : ∀ k : ℕ, x + 1 ≠ -k := fun k h => hx (k + 1) (by push_cast; linear_combination h)
  have h := hasSum_gaussCoeff (α := 1 - y) (β := x) hγ
    (by simp only [sub_re, add_re]; simp; linarith)
  rw [show x + 1 - (1 - y) - x = y by ring, show x + 1 - (1 - y) = x + y by ring,
    show x + 1 - x = 1 by ring, Complex.Gamma_one, inv_one, mul_one] at h
  have hG := Gamma_ne_zero hx
  have h2 := h.mul_left (Gamma x)
  rw [show Gamma x * Gamma y / Gamma (x + y) = Gamma x * (Gamma y * (Gamma (x + y))⁻¹) by ring]
  refine h2.congr_fun fun n => ?_
  have hxn : x + n ≠ 0 := fun h0 => hx n (by linear_combination h0)
  have hP := hx.ascPochhammer_ne_zero n
  rw [gaussCoeff, show x + 1 + (n : ℂ) = x + (n + 1 : ℕ) by push_cast; ring,
    Complex.Gamma_add_nat_eq_ascPochhammer_mul hx, ascPochhammer_succ_eval]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **Exercise 8.3-1**, regularized: for all complex `t, β`,
`R̃_{2t}(2β, 1/2 - β - t; 1/2, 1) = Γ(1/2)/(Γ(1/2 + β) Γ(1/2 - t))`, where
`R̃ = R/Γ(1/2 + β - t)`. Carlson's form
`R_{2t}(2β, 1/2 - β - t; 1/2, 1) = π^{1/2} Γ(1/2 + β - t)/(Γ(1/2 + β) Γ(1/2 - t))` follows on
multiplying by `Γ(1/2 + β - t)`. -/
theorem regCarlsonR_two_mul_pair_half_one (t β : ℂ) :
    regCarlsonR (2 * t) (pair (2 * β) (1 / 2 - β - t)) (pair (1 / 2) 1) =
      Gamma (1 / 2) * ((Gamma (1 / 2 + β))⁻¹ * (Gamma (1 / 2 - t))⁻¹) := by
  set x : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hx0 : ∀ n, 0 < x n := fun n => by simp only [x]; positivity
  have hxlim : Tendsto x atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hxc : Tendsto (fun n => ((x n : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (continuous_ofReal.tendsto 0).comp hxlim
    rwa [ofReal_zero] at this
  -- the left side of the hybrid transformation tends to the small-variable limit
  have hL := tendsto_regCarlsonR_update_zero_const (ι := Fin 2) 0 (a := -t) (a' := β + 1 / 2)
    (b := pair β (1 / 2 - t)) (w₀ := 1) (by simp; ring) (by simp) (by simp)
    ⟨1, by decide⟩ (w := fun n => ((x n : ℝ) : ℂ) ^ 2)
    (fun n => by rw [← ofReal_pow, ofReal_re]; exact pow_pos (hx0 n) 2)
    (by simpa using hxc.pow 2)
  -- the right side tends to its value at `x = 0` by continuity in the nodes
  have hcont : ContinuousAt (fun q : ℂ => regCarlsonR (2 * t) (pair (2 * β) (1 / 2 - t - β))
      (pair ((q + 1) / 2) 1)) 0 := by
    refine (analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const ?_ ?_).continuousAt
    · apply analyticAt_pi_iff.mpr
      intro i; fin_cases i
      · exact (analyticAt_id.add analyticAt_const).div_const
      · exact analyticAt_const
    · intro i; fin_cases i <;> simp [pair, mem_slitPlane_iff]
  have hR := hcont.tendsto.comp hxc
  have heq : ∀ n, regCarlsonR (-(-t)) (pair β (1 / 2 - t))
      (Function.update (fun _ => (1 : ℂ)) 0 (((x n : ℝ) : ℂ) ^ 2)) =
      (fun q : ℂ => regCarlsonR (2 * t) (pair (2 * β) (1 / 2 - t - β))
        (pair ((q + 1) / 2) 1)) ((x n : ℝ) : ℂ) := by
    intro n
    have h := regR_hybridQuadratic t β ((x n : ℝ) : ℂ) 1 (by simpa using hx0 n) (by simp)
    rw [one_pow] at h
    have hu : Function.update (fun _ => (1 : ℂ)) 0 (((x n : ℝ) : ℂ) ^ 2) =
        pair (((x n : ℝ) : ℂ) ^ 2) 1 := by
      funext i; fin_cases i <;> simp [pair]
    rw [neg_neg, hu, h]
  simp only [heq] at hL
  have hu := tendsto_nhds_unique hR hL
  have hp0 : pair β (1 / 2 - t) 0 = β := rfl
  simp only [zero_add, hp0] at hu
  rw [show (1 / 2 : ℂ) - β - t = 1 / 2 - t - β by ring, hu]
  rw [one_cpow, one_mul, show β + 1 / 2 - β = 1 / 2 by ring,
    show -t + (β + 1 / 2) - β = 1 / 2 - t by ring, add_comm β]

/-- Positive real nodes lie in the slit domain. -/
private theorem pair_mem_slitDomain_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    pair (x : ℂ) y ∈ carlsonRSlitDomain := by
  intro i; fin_cases i
  · exact ofReal_mem_slitPlane.mpr hx
  · exact ofReal_mem_slitPlane.mpr hy

/-- **Exercise 8.3-2**, regularized: for all complex `α, β`,
`R̃_{-α}(1 - α, 2β; 1, 2) = 2^{-2β} Γ(1/2)/(Γ(1/2 + β) Γ(1 - α + β))`, where
`R̃ = R/Γ(1 - α + 2β)`. -/
theorem regCarlsonR_pair_one_two (α β : ℂ) :
    regCarlsonR (-α) (pair (1 - α) (2 * β)) (pair 1 2) =
      (2 : ℂ) ^ (-(2 * β)) * (Gamma (1 / 2) * ((Gamma (1 / 2 + β))⁻¹ *
        (Gamma (1 - α + β))⁻¹)) := by
  have hz : pair (1 : ℂ) 2 ∈ carlsonRSlitDomain := by
    simpa using pair_mem_slitDomain_of_pos (x := 1) (y := 2) one_pos two_pos
  rw [regCarlsonR_euler _ _ hz, Fin.prod_univ_two, sum_pair]
  have hinv : (fun i => (pair (1 : ℂ) 2 i)⁻¹) = pair (1 : ℂ) (1 / 2) := by
    funext i; fin_cases i <;> simp [pair]
  rw [hinv, regCarlsonR_pair_swap _ _ _ (by rw [mem_slitPlane_iff]; norm_num)
    (by rw [mem_slitPlane_iff]; norm_num)]
  have h := regCarlsonR_two_mul_pair_half_one (α - β - 1 / 2) β
  rw [show 2 * (α - β - 1 / 2) = -(1 - α + 2 * β) - -α by ring,
    show 1 / 2 - β - (α - β - 1 / 2) = 1 - α by ring,
    show 1 / 2 - (α - β - 1 / 2) = 1 - α + β by ring] at h
  rw [h]
  simp [pair]

/-- **Kummer's theorem** (Exercise 8.3-3), regularized: with `₂F₁(a, b; 1 + a - b; -1)`
represented by `R_{-a}(b, 1 + a - 2b; 2, 1)` (Carlson's 8.3-7; it is the value of the `₂F₁`
function whether or not the series converges),
`R̃_{-a}(b, 1 + a - 2b; 2, 1) = 2^{-a} Γ(1/2)/(Γ(1 + a/2 - b) Γ(1/2 + a/2))`, where
`R̃ = R/Γ(1 + a - b)`. -/
theorem regCarlsonR_kummer (a b : ℂ) :
    regCarlsonR (-a) (pair b (1 + a - 2 * b)) (pair 2 1) =
      (2 : ℂ) ^ (-a) * (Gamma (1 / 2) * ((Gamma (1 + a / 2 - b))⁻¹ *
        (Gamma (1 / 2 + a / 2))⁻¹)) := by
  rw [← regCarlsonR_pair_swap _ _ _ (by rw [mem_slitPlane_iff]; norm_num)
    (by rw [mem_slitPlane_iff]; norm_num)]
  have hs : pair (1 : ℂ) 2 = fun i => ((2 : ℝ) : ℂ) * pair (1 / 2) 1 i := by
    funext i; fin_cases i <;> simp [pair]
  rw [hs, regCarlsonR_smul_of_pos _ _ two_pos
    (by simpa using pair_mem_slitDomain_of_pos (x := 1 / 2) (y := 1) (by norm_num) one_pos)]
  have h := regCarlsonR_two_mul_pair_half_one (-a / 2) ((1 + a) / 2 - b)
  rw [show 2 * (-a / 2) = -a by ring, show 2 * ((1 + a) / 2 - b) = 1 + a - 2 * b by ring,
    show 1 / 2 - ((1 + a) / 2 - b) - -a / 2 = b by ring,
    show 1 / 2 + ((1 + a) / 2 - b) = 1 + a / 2 - b by ring,
    show 1 / 2 - -a / 2 = 1 / 2 + a / 2 by ring] at h
  rw [h]
  push_cast
  ring

/-- **Exercise 8.3-4** (Kummer), regularized R-form: `R̃_{-2a}(2c - 1 + 2a, 1 - 2a; 1, 1/2) =
2^{1-2c} Γ(1/2)/(Γ(c + a) Γ(c - a + 1/2))`, where `R̃ = R/Γ(2c)`; by Carlson's (8.3-7) the left
side is the regularized `₂F₁(2a, 1 - 2a; 2c; 1/2)`. -/
theorem regCarlsonR_kummer_half (a c : ℂ) :
    regCarlsonR (-(2 * a)) (pair (2 * c - (1 - 2 * a)) (1 - 2 * a)) (pair 1 (1 - 1 / 2)) =
      (2 : ℂ) ^ (1 - 2 * c) * (Gamma (1 / 2) * ((Gamma (c + a))⁻¹ *
        (Gamma (c - a + 1 / 2))⁻¹)) := by
  have hz : pair (1 : ℂ) (1 - 1 / 2) ∈ carlsonRSlitDomain := by
    rw [show (1 : ℂ) - 1 / 2 = ((1 / 2 : ℝ) : ℂ) by push_cast; norm_num]
    simpa using pair_mem_slitDomain_of_pos (x := 1) (y := 1 / 2) one_pos (by norm_num)
  rw [regCarlsonR_euler _ _ hz, Fin.prod_univ_two, sum_pair]
  have hinv : (fun i => (pair (1 : ℂ) (1 - 1 / 2) i)⁻¹) =
      fun i => ((2 : ℝ) : ℂ) * pair (1 / 2) 1 i := by
    funext i; fin_cases i <;> norm_num [pair]
  rw [hinv, regCarlsonR_smul_of_pos _ _ two_pos
    (by simpa using pair_mem_slitDomain_of_pos (x := 1 / 2) (y := 1) (by norm_num) one_pos)]
  have h := regCarlsonR_two_mul_pair_half_one (a - c) (c - 1 / 2 + a)
  rw [show 2 * (a - c) = -(2 * c - (1 - 2 * a) + (1 - 2 * a)) - -(2 * a) by ring,
    show 2 * (c - 1 / 2 + a) = 2 * c - (1 - 2 * a) by ring,
    show 1 / 2 - (c - 1 / 2 + a) - (a - c) = 1 - 2 * a by ring,
    show 1 / 2 + (c - 1 / 2 + a) = c + a by ring,
    show 1 / 2 - (a - c) = c - a + 1 / 2 by ring] at h
  rw [h]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hhalf : (1 - 1 / 2 : ℂ) ^ (-(1 - 2 * a)) = (2 : ℂ) ^ (1 - 2 * a) := by
    rw [show (1 - 1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num, inv_cpow _ _ (by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, arg_ofReal_of_nonneg (by norm_num)]
      exact Real.pi_pos.ne), cpow_neg, inv_inv]
  simp only [pair, Matrix.cons_val_zero, Matrix.cons_val_one, one_cpow, one_mul]
  rw [hhalf]
  push_cast
  rw [← mul_assoc, ← cpow_add _ _ h2]
  congr 2
  ring

/-- **Exercise 8.3-4** (Kummer): if `2c` is not a nonpositive integer,
`₂F₁(2a, 1 - 2a; 2c; 1/2) = Γ(c) Γ(c + 1/2)/(Γ(c + a) Γ(c - a + 1/2))`. -/
theorem ordinaryHypergeometric_kummer_half (a c : ℂ) (hc : ∀ k : ℕ, 2 * c ≠ -k) :
    ordinaryHypergeometric (2 * a) (1 - 2 * a) (2 * c) (1 / 2 : ℂ) =
      Gamma c * Gamma (c + 1 / 2) * ((Gamma (c + a))⁻¹ * (Gamma (c - a + 1 / 2))⁻¹) := by
  have hreg := regCarlsonR_pair_one_sub_eq_regularizedGaussHGFun (2 * a) (1 - 2 * a) (2 * c)
    (x := 1 / 2) (by norm_num)
  rw [regCarlsonR_kummer_half] at hreg
  have hdiv := ordinaryHypergeometric_div_Gamma_eq (a := 2 * a) (b := 1 - 2 * a)
    (z := (1 / 2 : ℂ)) hc
  rw [← hreg] at hdiv
  have hG : Gamma (2 * c) ≠ 0 := Gamma_ne_zero hc
  rw [div_eq_iff hG] at hdiv
  rw [hdiv, Gamma_mul_Gamma_add_half, Complex.Gamma_one_half_eq,
    show (Real.pi : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) by
      rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf]
  ring

end Carlson.TwoVariable
