/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.BilateralGenerating
public import SeveralComplexVariables.LocallyUniform
public import SeveralComplexVariables.Analyticity

/-!
# Continuation of the bilateral generating relation

Carlson proves Generating Relation 6.11-1 in the Euler strip `re a > 0`, `re (c - a) > 0`
(`Carlson.hasSum_bilateral_generating`) and removes these conditions by analytic continuation.
This module carries out the continuation. Both sides, divided by `Γ(c)`, are holomorphic in the
parameters `(a, b) ∈ ℂ × ℂ^ι`. For the series this follows from a majorant built from Carlson's
estimate 6.2-7(24) for the numerators and from `‖Γ(w + m)⁻¹‖ ≤ ‖Γ(w)⁻¹‖/m!` for `Re w ≥ 1`
(`norm_inv_Gamma_add_nat_le`), with the several-variable Weierstrass theorem. The two sides agree
on the strip, hence everywhere.

## Main results

* `Carlson.hasSum_bilateral_generating_of_nonempty`: Generating Relation 6.11-1 for all complex
  `a` and `b`.
* `Carlson.hasSum_meixner_continued`: Meixner's formula (Corollary 6.11-2) for all complex
  `a, β, c`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.11.
-/

open Dirichlet
open Complex Set Filter MeasureTheory
open scoped Topology
@[expose] public noncomputable section

namespace Carlson
open TwoVariable

/-- `‖Γ(w + m)⁻¹‖ ≤ ‖Γ(w)⁻¹‖ / m!` for `Re w ≥ 1`. -/
theorem norm_inv_Gamma_add_nat_le {w : ℂ} (hw : 1 ≤ w.re) (m : ℕ) :
    ‖(Gamma (w + m))⁻¹‖ ≤ ‖(Gamma w)⁻¹‖ / m.factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hne : w + m ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hge : (m : ℝ) + 1 ≤ ‖w + m‖ := by
      have := re_le_norm (w + m); simp at this; linarith
    rw [show w + ((m + 1 : ℕ) : ℂ) = (w + m) + 1 by push_cast; ring, Gamma_add_one _ hne,
      mul_inv, norm_mul, norm_inv, Nat.factorial_succ, Nat.cast_mul]
    have hpos : (0 : ℝ) < m + 1 := by positivity
    calc ‖w + m‖⁻¹ * ‖(Gamma (w + m))⁻¹‖ ≤ ((m : ℝ) + 1)⁻¹ * (‖(Gamma w)⁻¹‖ / m.factorial) :=
          mul_le_mul (inv_anti₀ hpos hge) ih (norm_nonneg _) (by positivity)
      _ = _ := by push_cast; field_simp

/-- Real Pochhammer symbols are nonnegative and monotone in a nonnegative argument. -/
theorem ascPochhammer_real_eval_nonneg_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) :
    0 ≤ (ascPochhammer ℝ n).eval s ∧ (ascPochhammer ℝ n).eval s ≤ (ascPochhammer ℝ n).eval t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    exact ⟨mul_nonneg ih.1 (by positivity),
      mul_le_mul ih.2 (by linarith) (by positivity) (ih.1.trans ih.2)⟩


/-- Summability of the majorant `∑ (A)_{m+N} q^{m+N}/(m+N)! · (B)_{m+N}/m!` for `0 ≤ q < 1`. -/
theorem summable_ascPochhammer_mul_ascPochhammer {A B q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hq0 : 0 ≤ q) (hq : q < 1) (N : ℕ) :
    Summable (fun m : ℕ => (ascPochhammer ℝ (m + N)).eval A * q ^ (m + N) / (m + N).factorial *
      ((ascPochhammer ℝ (m + N)).eval B / m.factorial)) := by
  set s := Real.sqrt q
  have hs0 : 0 ≤ s := Real.sqrt_nonneg q
  have hs1 : s < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt hq0 hq
  have hss : s * s = q := Real.mul_self_sqrt hq0
  have hA' := summable_ascPochhammer_real_mul_pow_div_factorial A hs0 hs1
  have hAnn : ∀ n : ℕ, 0 ≤ (ascPochhammer ℝ n).eval A / n.factorial * s ^ n := fun n =>
    mul_nonneg (div_nonneg (ascPochhammer_real_eval_nonneg_le hA le_rfl n).1 (by positivity))
      (by positivity)
  set M := ∑' n, (ascPochhammer ℝ n).eval A / n.factorial * s ^ n
  have hM : ∀ n, (ascPochhammer ℝ n).eval A / n.factorial * s ^ n ≤ M := fun n =>
    hA'.le_tsum n fun j _ => hAnn j
  have hB' := summable_ascPochhammer_real_mul_pow_div_factorial (B + N) hs0 hs1
  have hPN : ∀ m : ℕ, (ascPochhammer ℝ (m + N)).eval B =
      (ascPochhammer ℝ N).eval B * (ascPochhammer ℝ m).eval (B + N) := by
    intro m
    rw [add_comm m N, ← ascPochhammer_mul, Polynomial.eval_mul, Polynomial.eval_comp]
    simp
  have hBN : 0 ≤ (ascPochhammer ℝ N).eval B := (ascPochhammer_real_eval_nonneg_le hB le_rfl N).1
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    ((hB'.mul_left (M * (ascPochhammer ℝ N).eval B * s ^ N)))
  · exact mul_nonneg (div_nonneg (mul_nonneg (ascPochhammer_real_eval_nonneg_le hA le_rfl _).1
      (pow_nonneg hq0 _)) (by positivity))
      (div_nonneg (ascPochhammer_real_eval_nonneg_le hB le_rfl _).1 (by positivity))
  · have hq' : q ^ (m + N) = s ^ (m + N) * s ^ (m + N) := by rw [← mul_pow, hss]
    have h1 : (ascPochhammer ℝ (m + N)).eval A * q ^ (m + N) / (m + N).factorial ≤
        M * s ^ (m + N) := by
      rw [hq', show (ascPochhammer ℝ (m + N)).eval A * (s ^ (m + N) * s ^ (m + N)) /
        (m + N).factorial = (ascPochhammer ℝ (m + N)).eval A / (m + N).factorial *
          s ^ (m + N) * s ^ (m + N) by ring]
      exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
    have h2 : 0 ≤ (ascPochhammer ℝ (m + N)).eval B / m.factorial :=
      div_nonneg (ascPochhammer_real_eval_nonneg_le hB le_rfl _).1 (by positivity)
    calc (ascPochhammer ℝ (m + N)).eval A * q ^ (m + N) / (m + N).factorial *
          ((ascPochhammer ℝ (m + N)).eval B / m.factorial)
        ≤ M * s ^ (m + N) * ((ascPochhammer ℝ (m + N)).eval B / m.factorial) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = M * (ascPochhammer ℝ N).eval B * s ^ N *
          ((ascPochhammer ℝ m).eval (B + N) / m.factorial * s ^ m) := by
          rw [hPN, pow_add]; ring

variable {ι : Type*} [Fintype ι]

/-- **Generating Relation 6.11-1 for all parameters.** For any number `k ≥ 1` of nodes, all
complex `a` and all complex Dirichlet parameters `b`, `c = ∑ bᵢ`, and `‖x zᵢ‖, ‖y zᵢ‖ < 1`:
`∏ (1 - y zᵢ)^(-bᵢ) R_{-a}(b; (1 - x z)/(1 - y z)) = ∑ (c)ₙ/n! Rₙ(a, c - a; x, y) Rₙ(b, z)`,
in regularized form (both sides divided by `Γ(c)`). Carlson's continuation from the Euler strip:
both sides are holomorphic in `(a, b)`, the series by a majorant built from Carlson's estimate
6.2-7(24) and `‖Γ(w + m)⁻¹‖ ≤ ‖Γ(w)⁻¹‖/m!` (`Re w ≥ 1`), and they agree on the strip
(`hasSum_bilateral_generating`). -/
theorem hasSum_bilateral_generating_of_nonempty [Nonempty ι] (a : ℂ) (b z : ι → ℂ) (x y : ℂ)
    (hx : ∀ i, ‖x * z i‖ < 1) (hy : ∀ i, ‖y * z i‖ < 1) :
    HasSum (fun n : ℕ => carlsonRPolynomialNumerator₂ n a (∑ i, b i - a) x y *
        regCarlsonRPolynomial n b z / n.factorial)
      ((∏ i, (1 - y * z i) ^ (-b i)) *
        regCarlsonR (-a) b (fun i => (1 - x * z i) / (1 - y * z i))) := by
  classical
  -- radii
  set ρ : ℝ := max ‖x‖ ‖y‖
  set r : ℝ := ((Finset.univ.sup fun i => ‖z i‖₊ : NNReal) : ℝ)
  have hr0 : 0 ≤ r := NNReal.coe_nonneg _
  have hzr : ∀ i, ‖z i‖ ≤ r := fun i => by
    have := Finset.le_sup (f := fun i => ‖z i‖₊) (Finset.mem_univ i)
    exact_mod_cast this
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg _)
  have hρr : ρ * r < 1 := by
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun i => ‖z i‖₊)
    have hrj : r = ‖z j‖ := by simp only [r, hj, coe_nnnorm]
    rw [hrj]
    rcases le_total ‖x‖ ‖y‖ with h | h
    · rw [show ρ = ‖y‖ from max_eq_right h, ← norm_mul]; exact hy j
    · rw [show ρ = ‖x‖ from max_eq_left h, ← norm_mul]; exact hx j
  -- the joint parameter space
  let aP : (Option ι → ℂ) → ℂ := fun p => p none
  let bP : (Option ι → ℂ) → ι → ℂ := fun p i => p (some i)
  let T : ℕ → (Option ι → ℂ) → ℂ := fun n p =>
    carlsonRPolynomialNumerator₂ n (aP p) (∑ i, bP p i - aP p) x y *
      regCarlsonRPolynomial n (bP p) z / n.factorial
  let w : ι → ℂ := fun i => (1 - x * z i) / (1 - y * z i)
  let L : (Option ι → ℂ) → ℂ := fun p =>
    (∏ i, (1 - y * z i) ^ (-bP p i)) * regCarlsonR (-aP p) (bP p) w
  have hre : ∀ i, 0 < (1 - y * z i).re := fun i => by
    have := hy i; have h1 := Complex.re_le_norm (y * z i)
    simp only [sub_re, one_re]; linarith
  have hw : w ∈ carlsonRSlitDomain := by
    intro i
    refine div_mem_slitPlane_of_re_pos ?_ (hre i)
    have := hx i; have h1 := Complex.re_le_norm (x * z i)
    simp only [sub_re, one_re]; linarith
  have hproj : ∀ o : Option ι, AnalyticOnNhd ℂ (fun p : Option ι → ℂ => p o) univ := fun o p _ =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option ι => ℂ) o).analyticAt p
  -- holomorphy of the left side
  have hL : AnalyticOnNhd ℂ L univ := by
    refine AnalyticOnNhd.mul (fun p _ => ?_) ?_
    · refine Finset.analyticAt_fun_prod _ fun i _ => ?_
      exact analyticAt_const.cpow ((hproj (some i) p (mem_univ _)).neg)
        (mem_slitPlane_iff.mpr (Or.inl (hre i)))
    · exact analyticOnNhd_regCarlsonR_comp isOpen_univ (fun p _ => (hproj none p trivial).neg)
        (fun p _ => analyticAt_pi_iff.mpr fun i => hproj (some i) p trivial)
        analyticOnNhd_const (fun _ _ => hw)
  -- holomorphy of the terms
  have hT : ∀ n, AnalyticOnNhd ℂ (T n) univ := by
    intro n p _
    have hN : AnalyticAt ℂ (fun p : Option ι → ℂ =>
        carlsonRPolynomialNumerator₂ n (aP p) (∑ i, bP p i - aP p) x y) p := by
      unfold carlsonRPolynomialNumerator₂
      refine Finset.analyticAt_fun_sum _ fun ij _ => ?_
      refine ((analyticAt_const.mul ?_).mul ?_).mul analyticAt_const |>.mul analyticAt_const
      · exact ((Polynomial.differentiable _).analyticAt _).comp (hproj none p trivial)
      · exact ((Polynomial.differentiable _).analyticAt _).comp
          ((Finset.analyticAt_fun_sum _ fun i _ => hproj (some i) p trivial).sub
            (hproj none p trivial))
    have hR : AnalyticAt ℂ (fun p : Option ι → ℂ => regCarlsonRPolynomial n (bP p) z) p :=
      analyticAt_regCarlsonRPolynomial_comp (x := p) (b := bP)
        (z := fun _ : Option ι → ℂ => z) (fun i => hproj (some i) p trivial)
        (fun _ => analyticAt_const) n
    exact (hN.mul hR).div_const
  -- a summable majorant on every unit ball
  have hbound : ∀ p₀ : Option ι → ℂ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, ∀ p ∈ Metric.ball p₀ 1, ‖T n p‖ ≤ u n := by
    intro p₀
    set R := ‖p₀‖ + 1
    set k : ℝ := (Fintype.card ι : ℝ)
    set B : ℝ := k * R
    set A : ℝ := R + (B + R)
    have hR0 : 0 ≤ R := by positivity
    have hB0 : 0 ≤ B := by positivity
    have hA0 : 0 ≤ A := by positivity
    have hpR : ∀ p ∈ Metric.closedBall p₀ 1, ‖p‖ ≤ R := fun p hp => by
      have := norm_le_of_mem_closedBall hp; simp only [R]; linarith
    have hbB : ∀ p ∈ Metric.closedBall p₀ 1, ∑ i, ‖bP p i‖ ≤ B := by
      intro p hp
      calc ∑ i, ‖bP p i‖ ≤ ∑ _i : ι, R :=
            Finset.sum_le_sum fun i _ => (norm_le_pi_norm p (some i)).trans (hpR p hp)
        _ = B := by simp [B, k]
    have hcB : ∀ p ∈ Metric.closedBall p₀ 1, ‖∑ i, bP p i‖ ≤ B := fun p hp =>
      (norm_sum_le _ _).trans (hbB p hp)
    have hNa : ∀ n, ∀ p ∈ Metric.closedBall p₀ 1,
        ‖carlsonRPolynomialNumerator₂ n (aP p) (∑ i, bP p i - aP p) x y‖ ≤
          (ascPochhammer ℝ n).eval A * ρ ^ n := by
      intro n p hp
      rw [← carlsonRPolynomialNumerator_pair]
      refine (norm_carlsonRPolynomialNumerator_le_sum_norm n _ _ hρ0 fun i => ?_).trans ?_
      · fin_cases i
        · exact le_max_left _ _
        · exact le_max_right _ _
      · refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hρ0 _)
        refine (ascPochhammer_real_eval_nonneg_le (by positivity) ?_ n).2
        simp only [Fin.sum_univ_two, pair_zero, pair_one]
        have h1 : ‖aP p‖ ≤ R := (norm_le_pi_norm p none).trans (hpR p hp)
        have h2 : ‖∑ i, bP p i - aP p‖ ≤ B + R :=
          (norm_sub_le _ _).trans (add_le_add (hcB p hp) h1)
        simp only [A]; linarith
    have hNb : ∀ n, ∀ p ∈ Metric.closedBall p₀ 1,
        ‖carlsonRPolynomialNumerator n (bP p) z‖ ≤ (ascPochhammer ℝ n).eval B * r ^ n :=
      fun n p hp => (norm_carlsonRPolynomialNumerator_le_sum_norm n _ z hr0 hzr).trans
        (mul_le_mul_of_nonneg_right ((ascPochhammer_real_eval_nonneg_le
          (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hbB p hp) n).2) (pow_nonneg hr0 _))
    -- the reciprocal Gamma factor
    set N₀ : ℕ := ⌈B⌉₊ + 1
    have hN₀ : B + 1 ≤ N₀ := by
      simp only [N₀]; push_cast; linarith [Nat.le_ceil B]
    have hcompact : IsCompact (Metric.closedBall p₀ (1 : ℝ)) := isCompact_closedBall _ _
    obtain ⟨G, hG⟩ := hcompact.exists_bound_of_continuousOn (f := fun p : Option ι → ℂ =>
      (Gamma (∑ i, bP p i + N₀))⁻¹) (by
        refine Continuous.continuousOn ?_
        have h1 : Continuous fun w : ℂ => (Gamma w)⁻¹ := by
          simpa [one_div] using differentiable_one_div_Gamma.continuous
        exact h1.comp (by fun_prop))
    have hGam : ∀ n, N₀ ≤ n → ∀ p ∈ Metric.closedBall p₀ 1,
        ‖(Gamma (∑ i, bP p i + n))⁻¹‖ ≤ G / (n - N₀).factorial := by
      intro n hn p hp
      have hre1 : 1 ≤ (∑ i, bP p i + N₀).re := by
        have := (Complex.abs_re_le_norm (∑ i, bP p i)).trans (hcB p hp)
        simp only [add_re, natCast_re]
        linarith [neg_abs_le (∑ i, bP p i).re]
      have := norm_inv_Gamma_add_nat_le hre1 (n - N₀)
      rw [show ∑ i, bP p i + (N₀ : ℂ) + ((n - N₀ : ℕ) : ℂ) = ∑ i, bP p i + n by
        push_cast [hn]; ring] at this
      exact this.trans (div_le_div_of_nonneg_right (hG p hp) (by positivity))
    -- small degrees
    have hsmall : ∀ n : ℕ, ∃ M, ∀ p ∈ Metric.closedBall p₀ 1, ‖T n p‖ ≤ M := fun n =>
      hcompact.exists_bound_of_continuousOn (fun p _ => (hT n p trivial).continuousAt
        |>.continuousWithinAt)
    choose M hM using hsmall
    let u : ℕ → ℝ := fun n => if n < N₀ then M n else
      (ascPochhammer ℝ n).eval A * (ρ * r) ^ n / n.factorial *
        ((ascPochhammer ℝ n).eval B * G / (n - N₀).factorial)
    refine ⟨u, ?_, fun n p hp => ?_⟩
    · rw [← summable_nat_add_iff N₀]
      have hsum := (summable_ascPochhammer_mul_ascPochhammer hA0 hB0
        (mul_nonneg hρ0 hr0) hρr N₀).mul_right G
      refine hsum.congr fun m => ?_
      simp only [u, show ¬ (m + N₀ < N₀) by omega, ite_false, Nat.add_sub_cancel]
      ring
    · have hp' := Metric.ball_subset_closedBall hp
      by_cases hn : n < N₀
      · simp only [u, hn, ite_true]; exact hM n p hp'
      · simp only [u, hn, ite_false]
        push Not at hn
        have hR := regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma n (bP p) z
        simp only [T]
        rw [hR, norm_div, norm_mul, norm_mul, Complex.norm_natCast]
        have e1 := hNa n p hp'
        have e2 := hNb n p hp'
        have e3 := hGam n hn p hp'
        have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG p hp')
        calc ‖carlsonRPolynomialNumerator₂ n (aP p) (∑ i, bP p i - aP p) x y‖ *
              (‖carlsonRPolynomialNumerator n (bP p) z‖ *
                ‖(Gamma (∑ i, bP p i + n))⁻¹‖) / n.factorial
            ≤ (ascPochhammer ℝ n).eval A * ρ ^ n *
                ((ascPochhammer ℝ n).eval B * r ^ n * (G / (n - N₀).factorial)) /
                  n.factorial := by
              have hA' := (ascPochhammer_real_eval_nonneg_le hA0 le_rfl n).1
              have hB' := (ascPochhammer_real_eval_nonneg_le hB0 le_rfl n).1
              gcongr
          _ = _ := by rw [mul_pow]; ring
  -- holomorphy of the sum
  have hF : AnalyticOnNhd ℂ (fun p => ∑' n, T n p) univ := by
    intro p₀ _
    obtain ⟨u, hu, hle⟩ := hbound p₀
    have hlim := (tendstoUniformlyOn_tsum hu fun n p hp => hle n p hp).tendstoLocallyUniformlyOn
    have hA := hlim.analyticOnNhd_of_finiteDimensional
      (Eventually.of_forall fun t => fun p _ =>
        Finset.analyticAt_fun_sum _ fun n _ => hT n p trivial) Metric.isOpen_ball
    exact hA p₀ (Metric.mem_ball_self one_pos)
  -- agreement on the Euler strip
  set S : Set (Option ι → ℂ) := {p | 0 < (aP p).re ∧ 0 < (∑ i, bP p i - aP p).re}
  have hSo : IsOpen S := by
    rw [show S = {p | 0 < (aP p).re} ∩ {p | 0 < (∑ i, bP p i - aP p).re} from rfl]
    refine (isOpen_lt continuous_const ?_).inter (isOpen_lt continuous_const ?_)
    · exact continuous_re.comp (continuous_apply none)
    · exact continuous_re.comp ((continuous_finsetSum _ fun i _ => continuous_apply (some i)).sub
        (continuous_apply none))
  set p₁ : Option ι → ℂ := fun o => Option.elim o 1 fun _ => 2
  have hp₁ : p₁ ∈ S := by
    have hk : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    refine ⟨by simp [p₁, aP], ?_⟩
    simp only [p₁, aP, bP, Option.elim, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      sub_re, mul_re, natCast_re, re_ofNat, natCast_im, im_ofNat, mul_zero, sub_zero, one_re]
    linarith
  have hEq : ∀ p ∈ S, L p = ∑' n, T n p := fun p hp =>
    (hasSum_bilateral_generating (aP p) (bP p) z x y hp.1 hp.2 hx hy).tsum_eq.symm
  have hall := hL.eqOn_of_preconnected_of_eventuallyEq hF isPreconnected_univ (mem_univ p₁)
    (Filter.eventually_of_mem (hSo.mem_nhds hp₁) hEq)
  -- conclusion
  set p : Option ι → ℂ := fun o => Option.elim o a b
  obtain ⟨u, hu, hle⟩ := hbound p
  have hsum : Summable fun n => T n p :=
    Summable.of_norm_bounded hu fun n => hle n p (Metric.mem_ball_self one_pos)
  have h := hall (mem_univ p)
  have := hsum.hasSum
  rw [show (∑' n, T n p) = L p from h.symm] at this
  exact this

/-- **Meixner's formula** (Corollary 6.11-2) for all complex `a, β, c`, in regularized form, for
`‖xX‖, ‖xY‖, ‖yX‖, ‖yY‖ < 1`. -/
theorem hasSum_meixner_continued (a β c x y X Y : ℂ)
    (hxX : ‖x * X‖ < 1) (hxY : ‖x * Y‖ < 1) (hyX : ‖y * X‖ < 1) (hyY : ‖y * Y‖ < 1) :
    HasSum (fun n : ℕ => carlsonRPolynomialNumerator₂ n a (c - a) x y *
        regRPolynomial n β (c - β) X Y / n.factorial)
      ((1 - y * X) ^ (a - β) * (1 - y * Y) ^ (a + β - c) *
        regCarlsonR (-a) (pair β (c - β))
          (pair ((1 - x * X) * (1 - y * Y)) ((1 - x * Y) * (1 - y * X)))) := by
  have hsum : ∑ i, pair β (c - β) i = c := by simp [pair, Fin.sum_univ_two]
  have h := hasSum_bilateral_generating_of_nonempty a (pair β (c - β)) (pair X Y) x y
    (fun i => by fin_cases i; exacts [hxX, hxY]) (fun i => by fin_cases i; exacts [hyX, hyY])
  rw [hsum] at h
  set A₀ := 1 - y * X
  set A₁ := 1 - y * Y
  have hA₀ : 0 < A₀.re := Complex.re_one_sub_pos hyX
  have hA₁ : 0 < A₁.re := Complex.re_one_sub_pos hyY
  have hP₀ : 0 < (1 - x * X).re := Complex.re_one_sub_pos hxX
  have hP₁ : 0 < (1 - x * Y).re := Complex.re_one_sub_pos hxY
  have hA₀0 : A₀ ≠ 0 := fun h => by simp [h] at hA₀
  have hA₁0 : A₁ ≠ 0 := fun h => by simp [h] at hA₁
  set μ := A₀ * A₁
  set w : Fin 2 → ℂ := fun i => (1 - x * pair X Y i) / (1 - y * pair X Y i)
  have hw : w ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact div_mem_slitPlane_of_re_pos hP₀ hA₀
    · exact div_mem_slitPlane_of_re_pos hP₁ hA₁
  have hμ : μ ∈ slitPlane := mul_mem_slitPlane_of_re_pos hA₀ hA₁
  have hargA₀ : |arg A₀| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA₀)
  have hargA₁ : |arg A₁| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA₁)
  have hargP₀ : |arg (1 - x * X)| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hP₀)
  have hargP₁ : |arg (1 - x * Y)| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hP₁)
  have hargμ : arg μ = arg A₀ + arg A₁ := by
    refine arg_mul hA₀0 hA₁0 ⟨?_, ?_⟩ <;>
      linarith [abs_lt.mp hargA₀, abs_lt.mp hargA₁, Real.pi_pos]
  have hharg : ∀ i, arg μ + arg (w i) ∈ Set.Ioo (-Real.pi) Real.pi := by
    intro i; fin_cases i
    · change arg μ + arg ((1 - x * X) / A₀) ∈ _
      rw [arg_div_of_re_pos hP₀ hA₀, hargμ]
      constructor <;> linarith [abs_lt.mp hargA₁, abs_lt.mp hargP₀, Real.pi_pos]
    · change arg μ + arg ((1 - x * Y) / A₁) ∈ _
      rw [arg_div_of_re_pos hP₁ hA₁, hargμ]
      constructor <;> linarith [abs_lt.mp hargA₀, abs_lt.mp hargP₁, Real.pi_pos]
  have hhom := regCarlsonR_mul_of_arg_add (-a) (pair β (c - β)) hw hμ hharg
  have hnodes : (fun i => μ * w i) =
      pair ((1 - x * X) * (1 - y * Y)) ((1 - x * Y) * (1 - y * X)) := by
    funext i; fin_cases i
    · change μ * ((1 - x * X) / A₀) = (1 - x * X) * A₁
      simp only [μ]; field_simp
    · change μ * ((1 - x * Y) / A₁) = (1 - x * Y) * A₀
      simp only [μ]; field_simp
  rw [hnodes] at hhom
  have hμ0 : μ ≠ 0 := mul_ne_zero hA₀0 hA₁0
  have hR : regCarlsonR (-a) (pair β (c - β)) w = μ ^ a *
      regCarlsonR (-a) (pair β (c - β))
        (pair ((1 - x * X) * (1 - y * Y)) ((1 - x * Y) * (1 - y * X))) := by
    rw [hhom, ← mul_assoc, ← cpow_add _ _ hμ0, add_neg_cancel, cpow_zero, one_mul]
  have hpre : (∏ i, (1 - y * pair X Y i) ^ (-pair β (c - β) i)) * μ ^ a =
      A₀ ^ (a - β) * A₁ ^ (a + β - c) := by
    rw [Fin.prod_univ_two, mul_cpow_of_re_pos hA₀ hA₁]
    simp only [pair_zero, pair_one]
    rw [show a - β = -β + a by ring, show a + β - c = -(c - β) + a by ring,
      cpow_add _ _ hA₀0, cpow_add _ _ hA₁0]
    ring
  change HasSum _ ((∏ i, (1 - y * pair X Y i) ^ (-pair β (c - β) i)) *
    regCarlsonR (-a) (pair β (c - β)) w) at h
  rw [hR, ← mul_assoc, hpre] at h
  exact h

end Carlson
