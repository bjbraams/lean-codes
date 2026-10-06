/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.SharpEstimates
public import Carlson.RPolynomial.Concentration
public import Carlson.RPolynomial.GeneratingIdentities
public import Carlson.RPolynomial.TaylorContinuation
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# R-polynomials and averages with small parameters (Exercises 6.2-6, 6.2-8, 6.3-4)

## Main results

* `Carlson.isLittleO_regCarlsonRPolynomial_sub`: Exercise 6.2-6,
  `Rₙ(b, z)/Γ(c) = ∑ bᵢ zᵢⁿ + o(‖b‖)` as `b → 0`.
* `Carlson.norm_carlsonRPolynomial_smul_le`: Exercise 6.2-8,
  `‖Rₙ(c w, z)‖ ≤ (½ ‖w‖)ₙ/|(-½)ₙ| ‖z‖ⁿ` for `0 < ‖c‖ ≤ 1/2`.
* `Carlson.tendsto_gamma_mul_regCarlsonContinuation_smul`: Exercise 6.3-4,
  `F(c w, z) → ∑ wᵢ f(zᵢ)` as `c → 0`, by dominated convergence with the bound of 6.2-8.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§6.2–6.3.
-/

open Complex Finset Filter Asymptotics
open scoped Topology
@[expose] public noncomputable section
namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- `(x)ₙ ≥ 0` for real `x ≥ 0`. -/
theorem ascPochhammer_eval_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ (ascPochhammer ℝ n).eval x := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval]; positivity

/-- The Pochhammer comparison behind Exercise 6.2-8: for `0 < ‖c‖ ≤ 1/2` and `W ≥ 0`,
`(‖c‖ W)ₙ |(-1/2)ₙ| ≤ ‖(c)ₙ‖ (W/2)ₙ`. -/
theorem ascPochhammer_norm_mul_le {c : ℂ} (hc : ‖c‖ ≤ 1 / 2) {W : ℝ} (hW : 0 ≤ W) (n : ℕ) :
    (ascPochhammer ℝ n).eval (‖c‖ * W) * |(ascPochhammer ℝ n).eval (-1 / 2)| ≤
      ‖(ascPochhammer ℂ n).eval c‖ * (ascPochhammer ℝ n).eval (W / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : 0 ≤ (ascPochhammer ℝ n).eval (‖c‖ * W) :=
      ascPochhammer_eval_nonneg_of_nonneg (by positivity) n
    have h1 : 0 ≤ (ascPochhammer ℝ n).eval (W / 2) :=
      ascPochhammer_eval_nonneg_of_nonneg (by positivity) n
    simp only [ascPochhammer_succ_eval, norm_mul, abs_mul]
    have hstep : (‖c‖ * W + n) * |(-1 / 2 : ℝ) + n| ≤ ‖c + n‖ * (W / 2 + n) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp; nlinarith [norm_nonneg c]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have habs : |(-1 / 2 : ℝ) + n| = n - 1 / 2 := by
          rw [abs_of_nonneg (by linarith)]; ring
        have hcn : (n : ℝ) - 1 / 2 ≤ ‖c + n‖ := by
          have := norm_sub_norm_le (n : ℂ) (-c)
          rw [norm_neg, Complex.norm_natCast, sub_neg_eq_add, add_comm] at this
          linarith
        rw [habs]
        have hcW : ‖c‖ * W ≤ W / 2 := by nlinarith [norm_nonneg c]
        calc (‖c‖ * W + n) * (n - 1 / 2) ≤ (W / 2 + n) * ‖c + n‖ :=
              mul_le_mul (by linarith) hcn (by linarith) (by positivity)
          _ = _ := by ring
    calc (ascPochhammer ℝ n).eval (‖c‖ * W) * (‖c‖ * W + n) *
          (|(ascPochhammer ℝ n).eval (-1 / 2)| * |(-1 / 2 : ℝ) + n|)
        = ((ascPochhammer ℝ n).eval (‖c‖ * W) * |(ascPochhammer ℝ n).eval (-1 / 2)|) *
          ((‖c‖ * W + n) * |(-1 / 2 : ℝ) + n|) := by ring
      _ ≤ (‖(ascPochhammer ℂ n).eval c‖ * (ascPochhammer ℝ n).eval (W / 2)) *
          (‖c + n‖ * (W / 2 + n)) :=
        mul_le_mul ih hstep (by positivity) (by positivity)
      _ = _ := by ring

/-- **Exercise 6.2-8**: if `∑ wᵢ = 1`, `0 < ‖c‖ ≤ 1/2` and `‖zᵢ‖ ≤ r`, then
`‖Rₙ(c w, z)‖ ≤ (½ ‖w‖)ₙ/|(-½)ₙ| rⁿ`, with `‖w‖ = ∑ ‖wᵢ‖` and `Rₙ(c w, z) = Nₙ(c w, z)/(c)ₙ`. -/
theorem norm_carlsonRPolynomial_smul_le {w z : ι → ℂ} {c : ℂ} (hc0 : c ≠ 0)
    (hc : ‖c‖ ≤ 1 / 2) {r : ℝ} (hr : 0 ≤ r) (hz : ∀ i, ‖z i‖ ≤ r) (n : ℕ) :
    ‖carlsonRPolynomialNumerator n (fun i => c * w i) z / (ascPochhammer ℂ n).eval c‖ ≤
      (ascPochhammer ℝ n).eval ((∑ i, ‖w i‖) / 2) / |(ascPochhammer ℝ n).eval (-1 / 2)| *
        r ^ n := by
  have hP : (ascPochhammer ℂ n).eval c ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨k, -, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact hc0 (by simpa using hk.symm)
    · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      have := congrArg norm hk
      rw [Complex.norm_natCast, norm_neg] at this
      linarith
  have hQ : (ascPochhammer ℝ n).eval (-1 / 2 : ℝ) ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨k, -, hk⟩
    have : (2 * k : ℝ) = 1 := by linarith
    have : (2 * k : ℕ) = 1 := by exact_mod_cast this
    omega
  have hN := norm_carlsonRPolynomialNumerator_le_pochhammer n (fun i => c * w i) z
    (B := fun i => ‖c‖ * ‖w i‖) (fun i => by rw [norm_mul]) hr hz
  rw [← mul_sum] at hN
  have hcmp := ascPochhammer_norm_mul_le hc (W := ∑ i, ‖w i‖)
    (sum_nonneg fun i _ => norm_nonneg (w i)) n
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hP)]
  have habs : 0 < |(ascPochhammer ℝ n).eval (-1 / 2 : ℝ)| := abs_pos.mpr hQ
  calc ‖carlsonRPolynomialNumerator n (fun i => c * w i) z‖
      ≤ (ascPochhammer ℝ n).eval (‖c‖ * ∑ i, ‖w i‖) * r ^ n := hN
    _ ≤ (‖(ascPochhammer ℂ n).eval c‖ * (ascPochhammer ℝ n).eval ((∑ i, ‖w i‖) / 2) /
          |(ascPochhammer ℝ n).eval (-1 / 2)|) * r ^ n := by
        gcongr
        rw [le_div_iff₀ habs]; exact hcmp
    _ = _ := by ring

/-- With all parameters zero, the numerators vanish in positive degree. -/
theorem carlsonRPolynomialNumerator_zero_params (n : ℕ) (z : ι → ℂ) :
    carlsonRPolynomialNumerator n (0 : ι → ℂ) z = if n = 0 then 1 else 0 := by
  rcases n with _ | n
  · simp
  · rw [carlsonRPolynomialNumerator_succ_eq_sum]; simp

/-- With parameter one at node `i` and zero elsewhere, `Nₙ(eᵢ; z) = n! zᵢⁿ`. -/
theorem carlsonRPolynomialNumerator_addDirichletUnit_zero (n : ℕ) (z : ι → ℂ) (i : ι) :
    carlsonRPolynomialNumerator n (Dirichlet.addDirichletUnit 0 i) z =
      n.factorial * z i ^ n := by
  have h := carlsonRPolynomialNumerator_addDirichletUnit n 0 z i
  rw [sum_eq_single 0 (fun m _ hm => by simp [carlsonRPolynomialNumerator_zero_params, hm])
    (by simp)] at h
  simp only [carlsonRPolynomialNumerator_zero_params, ite_true, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul, Nat.sub_zero] at h
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [div_eq_iff hf] at h
  rw [h]; ring

/-- **Exercise 6.2-6**: as `b → 0`, `Rₙ(b, z)/Γ(c) = ∑ bᵢ zᵢⁿ + o(‖b‖)` for `n ≥ 1`. -/
theorem isLittleO_regCarlsonRPolynomial_sub (n : ℕ) (z : ι → ℂ) :
    (fun b : ι → ℂ => regCarlsonRPolynomial (n + 1) b z - ∑ i, b i * z i ^ (n + 1)) =o[𝓝 0]
      fun b => ‖b‖ := by
  classical
  have hrepr : ∀ b : ι → ℂ, regCarlsonRPolynomial (n + 1) b z - ∑ i, b i * z i ^ (n + 1) =
      ∑ i, b i * (z i * (carlsonRPolynomialNumerator n (Dirichlet.addDirichletUnit b i) z *
        (Gamma ((∑ j, b j) + (n + 1 : ℕ)))⁻¹ - z i ^ n)) := fun b => by
    rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
      carlsonRPolynomialNumerator_succ_eq_sum, sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by push_cast; ring
  simp_rw [hrepr]
  refine IsLittleO.fun_sum fun i _ => ?_
  have hO : (fun b : ι → ℂ => b i) =O[𝓝 0] fun b => ‖b‖ :=
    isBigO_of_le _ fun b => by simpa using norm_le_pi_norm b i
  have hcont : Continuous fun b : ι → ℂ =>
      carlsonRPolynomialNumerator n (Dirichlet.addDirichletUnit b i) z := by
    have hj := (analyticOnNhd_carlsonRPolynomialNumerator_joint (ι := ι) n).continuousOn
    have hmap : Continuous fun b : ι → ℂ => (Dirichlet.addDirichletUnit b i, z) := by
      refine Continuous.prodMk ?_ continuous_const
      simp only [Dirichlet.addDirichletUnit]
      exact continuous_id.update i ((continuous_apply i).add continuous_const)
    exact ContinuousOn.comp_continuous (g := fun p : (ι → ℂ) × (ι → ℂ) =>
      carlsonRPolynomialNumerator n p.1 p.2) (f := fun b : ι → ℂ =>
        (Dirichlet.addDirichletUnit b i, z)) hj hmap fun _ => Set.mem_univ _
  have hG : Continuous fun b : ι → ℂ => (Gamma ((∑ j, b j) + (n + 1 : ℕ)))⁻¹ :=
    differentiable_one_div_Gamma.continuous.comp
      ((continuous_finsetSum _ fun j _ => continuous_apply j).add continuous_const)
  have hlim : Tendsto (fun b : ι → ℂ => z i * (carlsonRPolynomialNumerator n
      (Dirichlet.addDirichletUnit b i) z * (Gamma ((∑ j, b j) + (n + 1 : ℕ)))⁻¹ - z i ^ n))
      (𝓝 0) (𝓝 0) := by
    have := ((continuous_const (y := z i)).mul ((hcont.mul hG).sub
      (continuous_const (y := z i ^ n)))).tendsto (0 : ι → ℂ)
    convert this using 2
    show (0 : ℂ) = z i * (carlsonRPolynomialNumerator n (Dirichlet.addDirichletUnit 0 i) z *
      (Gamma ((∑ j, (0 : ι → ℂ) j) + (n + 1 : ℕ)))⁻¹ - z i ^ n)
    simp only [Pi.zero_apply, sum_const_zero, zero_add,
      carlsonRPolynomialNumerator_addDirichletUnit_zero]
    rw [show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring, Complex.Gamma_nat_eq_factorial]
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    field_simp
    ring
  have := hO.mul_isLittleO ((isLittleO_one_iff ℝ).mpr hlim)
  simpa using this

/-- The majorant `(W/2)ₙ/|(-1/2)ₙ| sⁿ` of Exercise 6.2-8 is summable for `0 < s < 1`. -/
theorem summable_ascPochhammer_div_mul_pow {W s : ℝ} (hW : 0 < W) (hs0 : 0 < s) (hs1 : s < 1) :
    Summable fun n : ℕ => (ascPochhammer ℝ n).eval (W / 2) /
      |(ascPochhammer ℝ n).eval (-1 / 2)| * s ^ n := by
  have hQ : ∀ n : ℕ, (ascPochhammer ℝ n).eval (-1 / 2 : ℝ) ≠ 0 := fun n => by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨k, -, hk⟩
    have : (2 * k : ℝ) = 1 := by linarith
    have : (2 * k : ℕ) = 1 := by exact_mod_cast this
    omega
  have hP : ∀ n : ℕ, 0 < (ascPochhammer ℝ n).eval (W / 2) := fun n =>
    ascPochhammer_pos n _ (by positivity)
  refine summable_of_ratio_test_tendsto_lt_one hs1
    (Eventually.of_forall fun n => by have := hP n; have := abs_pos.mpr (hQ n); positivity) ?_
  have hev : ∀ᶠ n : ℕ in atTop, ‖(ascPochhammer ℝ (n + 1)).eval (W / 2) /
      |(ascPochhammer ℝ (n + 1)).eval (-1 / 2)| * s ^ (n + 1)‖ /
      ‖(ascPochhammer ℝ n).eval (W / 2) / |(ascPochhammer ℝ n).eval (-1 / 2)| * s ^ n‖ =
      s * (1 + (W / 2 + 1 / 2) / ((n : ℝ) - 1 / 2)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos := hP n
    have hpos' := hP (n + 1)
    have habs := abs_pos.mpr (hQ n)
    have habs' := abs_pos.mpr (hQ (n + 1))
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      ascPochhammer_succ_eval, ascPochhammer_succ_eval, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ -1 / 2 + n by linarith)]
    have h2 : (0 : ℝ) < -1 / 2 + n := by linarith
    generalize (ascPochhammer ℝ n).eval (W / 2) = p at *
    generalize |(ascPochhammer ℝ n).eval (-1 / 2 : ℝ)| = qq at *
    rw [show (n : ℝ) - 1 / 2 = -1 / 2 + n by ring]
    have h4 : (-1 + (n : ℝ) * 2) ≠ 0 := (by linarith : (0 : ℝ) < -1 + n * 2).ne'
    field_simp
    linear_combination (s * s ^ n) * mul_inv_cancel₀ h4
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have hlim : Tendsto (fun n : ℕ => (W / 2 + 1 / 2) / ((n : ℝ) - 1 / 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  simpa using (tendsto_const_nhds (x := s)).mul ((tendsto_const_nhds (x := (1 : ℝ))).add hlim)

/-- **Exercise 6.3-4**: if `f` is holomorphic on a disk containing the nodes, `∑ wᵢ = 1`, and
`G` is the continued regularized average, then `F(c w, z) = Γ(c) G(c w) → ∑ wᵢ f(zᵢ)` as
`c → 0`. -/
theorem tendsto_gamma_mul_regCarlsonContinuation_smul {A : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball A R)) {z : ι → ℂ} (hz : ‖fun i => z i - A‖ < R)
    {w : ι → ℂ} (hw : ∑ i, w i = 1) {G : (ι → ℂ) → ℂ}
    (hG : Dirichlet.IsRegCarlsonContinuation f z G) :
    Tendsto (fun c : ℂ => Gamma c * G (fun i => c * w i)) (𝓝[≠] 0)
      (𝓝 (∑ i, w i * f (z i))) := by
  classical
  set y : ι → ℂ := fun i => z i - A
  set r : ℝ := ‖y‖
  have hyr : ∀ i, ‖y i‖ ≤ r := fun i => norm_le_pi_norm y i
  set W : ℝ := ∑ i, ‖w i‖
  have hW : 0 < W := by
    have := norm_sum_le univ w
    rw [hw, norm_one] at this; linarith
  obtain ⟨C, q, hC, hq, hqr, ha⟩ := Complex.exists_taylor_geometric_bound hf (norm_nonneg y) hz
  set s : ℝ := (q * r + 1) / 2
  have hs0 : 0 < s := by
    have h : 0 ≤ q * r := mul_nonneg hq (norm_nonneg _)
    simp only [s]; linarith
  have hs1 : s < 1 := by simp only [s]; linarith
  have hqrs : q * r ≤ s := by simp only [s]; linarith
  set a : ℕ → ℂ := fun n => iteratedDeriv n f A / n.factorial
  set D : ℕ → ℝ := fun n => (ascPochhammer ℝ n).eval (W / 2) /
    |(ascPochhammer ℝ n).eval (-1 / 2)|
  set F : ℂ → ℕ → ℂ := fun c n => a n * (carlsonRPolynomialNumerator n (fun i => c * w i) y /
    (ascPochhammer ℂ n).eval c)
  have hsum := summable_ascPochhammer_div_mul_pow hW hs0 hs1
  have hlimit : Tendsto (fun c => ∑' n, F c n) (𝓝[≠] 0)
      (𝓝 (∑' n, a n * ∑ i, w i * y i ^ n)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => C * (D n * s ^ n))
      (hsum.mul_left C) (fun n => (tendsto_carlsonRPolynomial_concentration_zero n w y hw
        |>.const_mul (a n))) ?_
    have hsmall : ∀ᶠ c : ℂ in 𝓝[≠] 0, c ≠ 0 ∧ ‖c‖ ≤ 1 / 2 := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.closedBall_mem_nhds 0
        (by norm_num : (0 : ℝ) < 1 / 2))] with c hc hc'
      exact ⟨hc, by simpa using hc'⟩
    filter_upwards [hsmall] with c ⟨hc0, hc⟩ n
    have hR := norm_carlsonRPolynomial_smul_le (w := w) hc0 hc (norm_nonneg y) hyr n
    have hD : 0 ≤ D n := by
      have := ascPochhammer_eval_nonneg_of_nonneg (x := W / 2) (by positivity) n
      positivity
    rw [norm_mul]
    calc ‖a n‖ * ‖carlsonRPolynomialNumerator n (fun i => c * w i) y /
          (ascPochhammer ℂ n).eval c‖ ≤ (C * q ^ n) * (D n * r ^ n) :=
        mul_le_mul (ha n) hR (norm_nonneg _) (by positivity)
      _ = C * (D n * (q * r) ^ n) := by ring
      _ ≤ C * (D n * s ^ n) := by gcongr
  -- identify the limit
  have hval : ∑' n, a n * ∑ i, w i * y i ^ n = ∑ i, w i * f (z i) := by
    have hT : ∀ i, HasSum (fun n => a n * y i ^ n) (f (z i)) := fun i => by
      have hmem : z i ∈ Metric.ball A R := by
        rw [Metric.mem_ball, dist_eq_norm]; exact (hyr i).trans_lt hz
      have := Complex.hasSum_taylorSeries_on_ball (hf.differentiableOn) hmem
      refine this.congr_fun fun n => ?_
      simp only [a, y, smul_eq_mul]; ring
    have hT' : HasSum (fun n => a n * ∑ i, w i * y i ^ n) (∑ i, w i * f (z i)) := by
      have := hasSum_sum (s := univ) fun i _ => (hT i).mul_left (w i)
      refine this.congr_fun fun n => ?_
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    exact hT'.tsum_eq
  rw [← hval]
  refine hlimit.congr' ?_
  -- `Γ(c) G(c w)` is the tsum of `F c`
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.closedBall_mem_nhds 0
    (by norm_num : (0 : ℝ) < 1 / 2))] with c (hc0 : c ≠ 0) hc'
  have hc : ‖c‖ ≤ 1 / 2 := by simpa using hc'
  have hreg : IsGammaRegular c := fun k hk => by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact hc0 (by simpa using hk)
    · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      have := congrArg norm hk
      rw [norm_neg, Complex.norm_natCast] at this
      linarith
  have hs := hG.hasSum_taylor hf hz (fun i => c * w i)
  have hcw : ∑ i, c * w i = c := by rw [← mul_sum, hw, mul_one]
  rw [← hs.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [F, a]
  rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, hcw,
    Complex.Gamma_add_nat_eq_ascPochhammer_mul hreg]
  have hP := hreg.ascPochhammer_ne_zero n
  have hG0 := Gamma_ne_zero hreg
  field_simp
  rfl

end Carlson
