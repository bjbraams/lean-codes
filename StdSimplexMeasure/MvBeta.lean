/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

import Mathlib.MeasureTheory.Integral.Pi
import StdSimplexMeasure.PiSnoc
import StdSimplexMeasure.ProdSlices

/-!
# The multivariate complex Beta function

## Main definitions and results

* `Complex.mvBeta`: the multivariate complex Beta function.
* `Complex.mvBetaConvergent`: the domain on which the usual simplex integral converges.
* `Complex.mvBeta_perm`: invariance under permutation of the parameters.
* `Complex.mvBeta_addNat_of_ne_neg_nat`: the translation identity away from Gamma poles.
* `Complex.mvBeta_addNat`: its specialization to the domain of absolute convergence.
* `Complex.mvBetaIntegral_eq_mvBeta`: the solid-simplex integral in DLMF 5.14.2.
* `Complex.mvBetaIntegralOne_eq_mvBeta`: the specialization in DLMF 5.14.1.

## References

* [NIST Digital Library of Mathematical Functions, §5.14](https://dlmf.nist.gov/5.14)
-/

open Fintype

public noncomputable section MvBeta

namespace Complex

variable {ι : Type*} [Fintype ι]

/-- The multivariate Beta function. -/
def mvBeta (b : ι → ℂ) : ℂ :=
    (∏ i, Gamma (b i)) / Gamma (∑ i, b i)

/-- The domain on which the usual simplex integral representation of `mvBeta` converges
absolutely. -/
def mvBetaConvergent : Set (ι → ℂ) :=
  {b | ∀ i, 0 < (b i).re}

/-- The sum of parameters in `mvBetaConvergent` has positive real part. -/
theorem sum_re_pos_of_mem_mvBetaConvergent [Nonempty ι] {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) : 0 < (∑ i, b i).re := by
  simpa using Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty

/-- The multivariate Beta function does not vanish on its convergence domain. -/
theorem mvBeta_ne_zero [Nonempty ι] {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    mvBeta b ≠ 0 := by
  apply div_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Gamma_ne_zero_of_re_pos (hb i)
  · exact Gamma_ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hb)

omit [Fintype ι] in
/-- Adding nonnegative integers coordinatewise preserves `mvBetaConvergent`. -/
theorem addNat_mem_mvBetaConvergent {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (m : ι → ℕ) : (fun i ↦ b i + (m i : ℂ)) ∈ mvBetaConvergent := by
  intro i
  norm_num
  exact add_pos_of_pos_of_nonneg (hb i) (Nat.cast_nonneg _)

omit [Fintype ι] in
/-- Simultaneously permuting the parameters preserves the convergence domain. -/
theorem comp_perm_mem_mvBetaConvergent {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent)
    (σ : Equiv.Perm ι) : b ∘ σ ∈ mvBetaConvergent :=
  fun i ↦ hb (σ i)

/-- `mvBeta` is symmetric in its arguments. -/
theorem mvBeta_perm (b : ι → ℂ) (σ : Equiv.Perm ι) :
    mvBeta (b ∘ σ) = mvBeta b := by
  change (∏ i, Gamma (b (σ i))) / Gamma (∑ i, b (σ i)) =
    (∏ i, Gamma (b i)) / Gamma (∑ i, b i)
  have hp : (∏ i, Gamma (b (σ i))) = ∏ i, Gamma (b i) :=
    Equiv.prod_comp σ (fun i => Gamma (b i))
  have hs : (∑ i, b (σ i)) = ∑ i, b i :=
    Equiv.sum_comp σ b
  rw [hp, hs]

/-- On a singleton index type, `mvBeta` equals one throughout its convergence domain. -/
theorem mvBeta_eq_one_of_unique [Unique ι] {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    mvBeta b = 1 := by
  have hG : Gamma (b default) ≠ 0 := Gamma_ne_zero_of_re_pos (hb default)
  simp [mvBeta, hG]

/-- The natural-shift recurrence for reciprocal Gamma, valid at every complex argument. This is
the pole-free counterpart of expressing an ascending Pochhammer symbol as a quotient of Gamma
functions. -/
theorem one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat (z : ℂ) (n : ℕ) :
    (Gamma z)⁻¹ = (ascPochhammer ℂ n).eval z * (Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ih, one_div_Gamma_eq_self_mul_one_div_Gamma_add_one]
      simp only [Nat.cast_succ, ascPochhammer_succ_right, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]
      ring_nf

/-- Positive integer translates of `mvBeta`, assuming only that the coordinate parameters avoid
the poles of the Gamma function. This hypothesis is substantially weaker than
membership in `mvBetaConvergent`.

Some pole-avoidance hypothesis is necessary: because Mathlib totalizes `Gamma` to be zero at its
poles, the displayed identity is not valid for arbitrary complex parameters. -/
theorem mvBeta_addNat_of_ne_neg_nat {b : ι → ℂ}
    (hb : ∀ i (k : ℕ), b i ≠ -(k : ℂ))
    (m : ι → ℕ) :
    mvBeta (fun i : ι => b i + (m i : ℂ)) * (ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) =
    mvBeta b * ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [mvBeta]
  | inr hι =>
      let _ := hι
      have hcoord (i : ι) :
          Gamma (b i + (m i : ℂ)) =
            (ascPochhammer ℂ (m i)).eval (b i) * Gamma (b i) := by
        apply (div_eq_iff (Gamma_ne_zero (hb i))).mp
        exact Gamma_add_nat_div_Gamma_eq (b i) (hb i)
      have hsum_add :
          ∑ i, (b i + (m i : ℂ)) = (∑ i, b i) + (∑ i, m i : ℕ) := by
        simp [Finset.sum_add_distrib]
      have hprod :
          ∏ i, Gamma (b i + (m i : ℂ)) =
            (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * ∏ i, Gamma (b i) := by
        simp_rw [hcoord, Finset.prod_mul_distrib]
      have hrec := one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat
        (∑ i, b i) (∑ i, m i)
      simp only [mvBeta, hsum_add, hprod, div_eq_mul_inv]
      calc
        ((∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * ∏ i, Gamma (b i)) *
              (Gamma ((∑ i, b i) + (∑ i, m i : ℕ)))⁻¹ *
              (ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) =
            (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * (∏ i, Gamma (b i)) *
              ((ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) *
                (Gamma ((∑ i, b i) + (∑ i, m i : ℕ)))⁻¹) := by ring
        _ = (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) * (∏ i, Gamma (b i)) *
              (Gamma (∑ i, b i))⁻¹ := by rw [← hrec]
        _ = (∏ i, Gamma (b i)) * (Gamma (∑ i, b i))⁻¹ *
              ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by ring

/-- Positive integer translates of `mvBeta` on its absolutely convergent domain. -/
theorem mvBeta_addNat {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (m : ι → ℕ) :
    mvBeta (fun i : ι => b i + (m i : ℂ)) * (ascPochhammer ℂ (∑ i, m i)).eval (∑ i, b i) =
    mvBeta b * ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [mvBeta]
  | inr hι =>
      let _ := hι
      apply mvBeta_addNat_of_ne_neg_nat (m := m)
      intro i k hik
      have hi : 0 < (b i).re := hb i
      rw [hik] at hi
      norm_num at hi
      linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]

section SolidSimplexIntegral

open MeasureTheory MeasurableEquiv

/-- The solid standard `n`-simplex used in the DLMF multivariate Beta integrals. -/
def mvBetaSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- The solid standard simplex is a measurable set. -/
theorem measurableSet_mvBetaSimplex (n : ℕ) : MeasurableSet (mvBetaSimplex n) := by
  apply IsClosed.measurableSet
  apply IsClosed.inter
  · change IsClosed ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} : Set (Fin n → ℝ))
    rw [show {x : Fin n → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} by ext x; simp]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const

/-- Splitting off the last coordinate identifies a solid-simplex section with an interval
whose upper endpoint is the remaining slack coordinate. -/
private theorem snoc_mem_mvBetaSimplex_iff {n : ℕ} (y : Fin n → ℝ) (t : ℝ) :
    Fin.snoc y t ∈ mvBetaSimplex (n + 1) ↔
      (∀ i, 0 ≤ y i) ∧ 0 ≤ t ∧ t ≤ 1 - ∑ i, y i := by
  simp only [mvBetaSimplex, Set.mem_ofPred_eq, Fin.forall_fin_succ', Fin.snoc_last,
    Fin.snoc_castSucc, Fin.sum_univ_castSucc]
  constructor
  · rintro ⟨⟨hy, ht⟩, hsum⟩
    exact ⟨hy, ht, by linarith⟩
  · rintro ⟨hy, ht, hsum⟩
    exact ⟨⟨hy, ht⟩, by linarith⟩

/-- The solid-coordinate multivariate Beta integral. The parameter `b₀` belongs to the slack
coordinate `1 - ∑ i, x i`, while `b i` belongs to `x i`. This is the integral on the left-hand
side of DLMF 5.14.2. -/
def mvBetaIntegral {n : ℕ} (b₀ : ℂ) (b : Fin n → ℂ) : ℂ :=
  ∫ x in mvBetaSimplex n,
    ((1 - ∑ i, x i : ℝ) : ℂ) ^ (b₀ - 1) * ∏ i, (x i : ℂ) ^ (b i - 1)

/-- The solid-coordinate integral in DLMF 5.14.1, in which the slack coordinate has exponent
zero. -/
def mvBetaIntegralOne {n : ℕ} (b : Fin n → ℂ) : ℂ :=
  ∫ x in mvBetaSimplex n, ∏ i, (x i : ℂ) ^ (b i - 1)

/-- The zero-dimensional solid-coordinate integral has the expected value. -/
private theorem mvBetaIntegral_zero {b₀ : ℂ} (hb₀ : 0 < b₀.re) :
    mvBetaIntegral (n := 0) b₀ Fin.elim0 = mvBeta (Fin.cons b₀ Fin.elim0) := by
  have hG : Gamma b₀ ≠ 0 := Gamma_ne_zero_of_re_pos hb₀
  simp [mvBetaIntegral, mvBetaSimplex, mvBeta, hG, measureReal_def]
  rw [volume_pi]
  simp

/-- Raising a real number to a fixed complex power is measurable. -/
private theorem measurable_ofReal_cpow (c : ℂ) :
    Measurable fun x : ℝ => (x : ℂ) ^ c :=
  measurable_of_continuousOn_compl_singleton (0 : ℝ) fun x hx =>
    (continuousAt_ofReal_cpow_const x c (Or.inr hx)).continuousWithinAt

/-- The solid-simplex Dirichlet monomial is measurable. -/
private theorem measurable_mvBetaIntegrand {n : ℕ} (b₀ : ℂ) (b : Fin n → ℂ) :
    Measurable fun x : Fin n → ℝ =>
      ((1 - ∑ i, x i : ℝ) : ℂ) ^ (b₀ - 1) * ∏ i, (x i : ℂ) ^ (b i - 1) := by
  refine ((measurable_ofReal_cpow (b₀ - 1)).comp ?_).mul ?_
  · exact measurable_const.sub (Finset.univ.measurable_sum fun i _ => measurable_pi_apply i)
  · exact Finset.univ.measurable_prod fun i _ =>
      (measurable_ofReal_cpow (b i - 1)).comp (measurable_pi_apply i)

/-- Interior points of the solid simplex have strictly positive coordinates and slack. -/
private theorem interior_mvBetaSimplex_subset (n : ℕ) :
    interior (mvBetaSimplex n) ⊆ {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  intro x hx
  have hxmem : x ∈ mvBetaSimplex n := interior_subset hx
  obtain ⟨ε, εpos, hε⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  refine ⟨fun i => ?_, ?_⟩
  · by_contra hi
    have hi0 : x i = 0 := le_antisymm (not_lt.mp hi) (hxmem.1 i)
    let y : Fin n → ℝ := x - (ε / 2) • Pi.single i (1 : ℝ)
    have hydist : dist y x < ε := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Pi.norm_single]
      simp [abs_of_pos εpos]
      linarith
    have : y ∈ mvBetaSimplex n := hε hydist
    have hyi : y i < 0 := by
      simp [y, hi0]
      linarith [εpos]
    exact hyi.not_ge (this.1 i)
  · by_contra hs
    have hs1 : ∑ i, x i = 1 := le_antisymm hxmem.2 (not_lt.mp hs)
    cases n with
    | zero => simp at hs1
    | succ n =>
        let y : Fin (n + 1) → ℝ := x + (ε / 2) • Pi.single (0 : Fin (n + 1)) (1 : ℝ)
        have hydist : dist y x < ε := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Pi.norm_single]
          simp [abs_of_pos εpos]
          linarith
        have hymem : y ∈ mvBetaSimplex n.succ := hε hydist
        have hsum : ∑ i, y i = 1 + ε / 2 := by
          simp [y, Finset.sum_add_distrib, Pi.smul_apply, hs1]
          rw [← Finset.mul_sum, Finset.sum_eq_single (0 : Fin (n + 1))]
          · simp
          · intro i _ hi
            simp [Pi.single_eq_of_ne hi]
          · simp
        have hnot : ¬ ∑ i, y i ≤ 1 := by
          rw [hsum]
          linarith [εpos]
        exact hnot hymem.2

/-- The scaled Beta integrand is interval-integrable on `[0, a]`. -/
private theorem intervalIntegrable_scaled_beta {u v : ℂ}
    (hu : 0 < u.re) (hv : 0 < v.re) {a : ℝ} (ha : 0 ≤ a) :
    IntervalIntegrable
      (fun x : ℝ => (x : ℂ) ^ (u - 1) * ((a : ℂ) - x) ^ (v - 1)) volume 0 a := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    simp
  have hf := betaIntegral_convergent hu hv
  have hcomp := hf.comp_mul_left (c := a⁻¹) (by finiteness) (by finiteness)
  have hz : (0 : ℝ) / a⁻¹ = 0 := by simp
  have hone : (1 : ℝ) / a⁻¹ = a := by field_simp [hpos.ne']
  have hI : IntervalIntegrable
      (fun x : ℝ => ((a⁻¹ * x : ℝ) : ℂ) ^ (u - 1) * (1 - ((a⁻¹ * x : ℝ) : ℂ)) ^ (v - 1))
      volume 0 a := by
    simpa [hz, hone] using hcomp
  have hpow : IntervalIntegrable
      (fun x : ℝ => (a : ℂ) ^ (u - 1 + (v - 1)) *
        (((a⁻¹ * x : ℝ) : ℂ) ^ (u - 1) * (1 - ((a⁻¹ * x : ℝ) : ℂ)) ^ (v - 1)))
      volume 0 a :=
    hI.const_mul _
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha] at hpow ⊢
  refine hpow.congr_fun (fun x hx => ?_) measurableSet_Ioc
  have hx0 : 0 < x := hx.1
  have hxa : x ≤ a := hx.2
  have hx' : 0 ≤ a⁻¹ * x := by positivity
  have hx'' : a⁻¹ * x ≤ 1 := by
    rw [mul_comm, ← div_eq_mul_inv, div_le_one hpos]
    exact hxa
  have hane : 0 ≤ a := ha
  have h1 : (x : ℂ) ^ (u - 1) = (a : ℂ) ^ (u - 1) * ((a⁻¹ * x : ℝ) : ℂ) ^ (u - 1) := by
    have hxeq : (x : ℝ) = a * (a⁻¹ * x) := by field_simp [hpos.ne']
    calc
      (x : ℂ) ^ (u - 1) = ((a * (a⁻¹ * x) : ℝ) : ℂ) ^ (u - 1) := by rw [← hxeq]
      _ = (a : ℂ) ^ (u - 1) * ((a⁻¹ * x : ℝ) : ℂ) ^ (u - 1) := by
          rw [ofReal_mul, mul_cpow_ofReal_nonneg hane hx']
  have h2 : ((a : ℂ) - x) ^ (v - 1) =
      (a : ℂ) ^ (v - 1) * (1 - ((a⁻¹ * x : ℝ) : ℂ)) ^ (v - 1) := by
    have hunit : 0 ≤ 1 - a⁻¹ * x := sub_nonneg.mpr hx''
    have hmul : (a - x : ℝ) = a * (1 - a⁻¹ * x) := by field_simp [hpos.ne']
    calc
      ((a : ℂ) - x) ^ (v - 1) = ((a - x : ℝ) : ℂ) ^ (v - 1) := by simp
      _ = ((a * (1 - a⁻¹ * x) : ℝ) : ℂ) ^ (v - 1) := by rw [hmul]
      _ = (a : ℂ) ^ (v - 1) * ((1 - a⁻¹ * x : ℝ) : ℂ) ^ (v - 1) := by
          rw [ofReal_mul, mul_cpow_ofReal_nonneg hane hunit]
      _ = (a : ℂ) ^ (v - 1) * (1 - ((a⁻¹ * x : ℝ) : ℂ)) ^ (v - 1) := by simp
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
  rw [h1, h2, mul_mul_mul_comm, ← mul_assoc, ← cpow_add _ _ ha0]
  ring

/-- Scaling identity for the L¹ norm of the Beta kernel. -/
private theorem integral_norm_scaled_beta {u v : ℂ}
    (_hu : 0 < u.re) (_hv : 0 < v.re) {a : ℝ} (ha : 0 < a) :
    ∫ t in (0 : ℝ)..a, ‖(t : ℂ) ^ (u - 1) * ((a : ℂ) - t) ^ (v - 1)‖ =
      a ^ (u.re + v.re - 1) *
        ∫ t in (0 : ℝ)..1, ‖(t : ℂ) ^ (u - 1) * (1 - (t : ℂ)) ^ (v - 1)‖ := by
  have hchg :=
    intervalIntegral.smul_integral_comp_mul_left
      (f := fun t : ℝ => ‖(t : ℂ) ^ (u - 1) * ((a : ℂ) - t) ^ (v - 1)‖)
      (a := 0) (b := 1) a
  -- `a • ∫ t in 0..1, f (a * t) = ∫ t in 0..a, f t`
  simp only [mul_zero, mul_one] at hchg
  rw [← hchg, smul_eq_mul]
  simp_rw [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  rw [← integral_const_mul, ← integral_const_mul]
  rw [setIntegral_congr_set (μ := volume) Ioo_ae_eq_Ioc.symm,
    setIntegral_congr_set (μ := volume) Ioo_ae_eq_Ioc.symm]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have hpos : 0 < a * t := mul_pos ha ht0
  have hpos' : 0 < a * (1 - t) := mul_pos ha (sub_pos.mpr ht1)
  have h1 : ‖((a * t : ℝ) : ℂ) ^ (u - 1)‖ = a ^ (u.re - 1) * t ^ (u.re - 1) := by
    rw [norm_cpow_eq_rpow_re_of_pos hpos, Real.mul_rpow ha.le ht0.le, sub_re, one_re]
  have h2 : ‖((a : ℂ) - (a * t : ℝ)) ^ (v - 1)‖ = a ^ (v.re - 1) * (1 - t) ^ (v.re - 1) := by
    have : (a : ℂ) - (a * t : ℝ) = ((a * (1 - t) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, norm_cpow_eq_rpow_re_of_pos hpos', Real.mul_rpow ha.le (sub_nonneg.mpr ht1.le),
      sub_re, one_re]
  have h3 : ‖(t : ℂ) ^ (u - 1) * (1 - (t : ℂ)) ^ (v - 1)‖ =
      t ^ (u.re - 1) * (1 - t) ^ (v.re - 1) := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re,
      show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by simp,
      norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr ht1), sub_re, one_re]
  have hrpow : a * a ^ (u.re - 1) * a ^ (v.re - 1) = a ^ (u.re + v.re - 1) := by
    have h1 : a * a ^ (u.re - 1) = a ^ u.re := by
      rw [mul_comm, ← Real.rpow_add_one ha.ne', sub_add_cancel]
    rw [h1, ← Real.rpow_add ha]
    ring_nf
  rw [norm_mul, h1, h2, h3]
  calc
    a * (a ^ (u.re - 1) * t ^ (u.re - 1) * (a ^ (v.re - 1) * (1 - t) ^ (v.re - 1))) =
        (a * a ^ (u.re - 1) * a ^ (v.re - 1)) *
          (t ^ (u.re - 1) * (1 - t) ^ (v.re - 1)) := by ring
    _ = a ^ (u.re + v.re - 1) * (t ^ (u.re - 1) * (1 - t) ^ (v.re - 1)) := by
        rw [hrpow]

/-- Combining the last coordinate against the slack parameter recovers `mvBeta`. -/
private theorem mvBeta_cons_mul_betaIntegral {n : ℕ} {b₀ : ℂ} {b : Fin (n + 1) → ℂ}
    (hb₀ : 0 < b₀.re) (hb : ∀ i, 0 < (b i).re) :
    mvBeta (Fin.cons (b₀ + b (Fin.last n)) (fun i => b (Fin.castSucc i))) *
      betaIntegral (b (Fin.last n)) b₀ =
    mvBeta (Fin.cons b₀ b) := by
  have hbl : 0 < (b (Fin.last n)).re := hb _
  have hsum : 0 < (b₀ + b (Fin.last n)).re := by
    rw [add_re]
    exact add_pos hb₀ hbl
  have hΓ : Gamma (b₀ + b (Fin.last n)) ≠ 0 := Gamma_ne_zero_of_re_pos hsum
  have hβ := betaIntegral_eq_Gamma_mul_div (b (Fin.last n)) b₀ hbl hb₀
  simp only [mvBeta, hβ]
  rw [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]
  rw [Fin.prod_univ_castSucc (fun i => Gamma (b i)), Fin.sum_univ_castSucc b]
  have hcomm : b₀ + b (Fin.last n) = b (Fin.last n) + b₀ := add_comm _ _
  have hadd : b₀ + b (Fin.last n) + ∑ i : Fin n, b (Fin.castSucc i) =
      b₀ + (∑ i : Fin n, b (Fin.castSucc i) + b (Fin.last n)) := by ac_rfl
  have hΓ' : Gamma (b (Fin.last n) + b₀) ≠ 0 := by rwa [add_comm] at hΓ
  rw [hadd, hcomm]
  field_simp [hΓ', Gamma_ne_zero_of_re_pos hb₀, Gamma_ne_zero_of_re_pos hbl]

/-- The hyperplane `∑ x i = 1` is a null set. -/
private theorem volume_setOf_sum_eq_one (n : ℕ) :
    volume {x : Fin n → ℝ | ∑ i, x i = 1} = 0 := by
  induction n with
  | zero =>
      simp
  | succ n _ =>
      have hmeas : MeasurableSet {x : Fin (n + 1) → ℝ | ∑ i, x i = 1} :=
        (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i)
          continuous_const).measurableSet
      have hmp := measurePreserving_piFinSnoc n ℝ
      have hpre : piFinSnoc n ℝ ⁻¹' {x | ∑ i, x i = 1} =
          {p : (Fin n → ℝ) × ℝ | p.2 + ∑ i, p.1 i = 1} := by
        ext p
        simp [Fin.sum_univ_castSucc, add_comm]
      have hpre_meas : MeasurableSet {p : (Fin n → ℝ) × ℝ | p.2 + ∑ i, p.1 i = 1} :=
        (isClosed_eq
          (continuous_snd.add
            ((continuous_finsetSum _ fun i _ => continuous_apply i).comp continuous_fst))
          continuous_const).measurableSet
      rw [← hmp.map_eq, Measure.map_apply hmp.measurable hmeas, hpre, Measure.volume_eq_prod]
      refine (Measure.measure_prod_null hpre_meas).2 ?_
      refine Filter.Eventually.of_forall fun y => ?_
      have : Prod.mk y ⁻¹' {p : (Fin n → ℝ) × ℝ | p.2 + ∑ i, p.1 i = 1} =
          {1 - ∑ i, y i} := by
        ext t
        simp [eq_sub_iff_add_eq]
      simp [this]

/-- A coordinate hyperplane is a null set. -/
private theorem volume_setOf_eval_eq_zero {n : ℕ} (i : Fin n) :
    volume {x : Fin n → ℝ | x i = 0} = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i
      have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i
      have hpre : {x : Fin (n + 1) → ℝ | x i = 0} =
          e ⁻¹' ({(0 : ℝ)} ×ˢ (Set.univ : Set (Fin n → ℝ))) := by
        ext x
        simp [e, MeasurableEquiv.piFinSuccAbove_apply]
      have hmeas : MeasurableSet ({(0 : ℝ)} ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
        MeasurableSet.prod (measurableSet_singleton (0 : ℝ)) MeasurableSet.univ
      rw [hpre, ← Measure.map_apply e.measurable hmeas, hmp.map_eq, Measure.volume_eq_prod,
        Measure.prod_prod, Real.volume_singleton, zero_mul]

private theorem piFinSnoc_preimage_mvBetaSimplex (n : ℕ) :
    piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1) =
      {p : (Fin n → ℝ) × ℝ |
        p.1 ∈ mvBetaSimplex n ∧ p.2 ∈ Set.Icc 0 (1 - ∑ i, p.1 i)} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, piFinSnoc_apply]
  rw [snoc_mem_mvBetaSimplex_iff]
  simp only [mvBetaSimplex, Set.mem_Icc, Set.mem_ofPred_eq]
  constructor
  · intro ⟨hy, ht, hsum⟩
    refine ⟨⟨hy, ?_⟩, ht, hsum⟩
    linarith
  · intro ⟨⟨hy, _hys⟩, ht, hsum⟩
    exact ⟨hy, ht, hsum⟩

/-- Integrability of the solid-simplex Dirichlet monomial, together with DLMF 5.14.2. -/
private theorem mvBetaIntegral_eq_mvBeta_aux {n : ℕ} {b₀ : ℂ} {b : Fin n → ℂ}
    (hb₀ : 0 < b₀.re) (hb : ∀ i, 0 < (b i).re) :
    IntegrableOn (fun x : Fin n → ℝ =>
        ((1 - ∑ i, x i : ℝ) : ℂ) ^ (b₀ - 1) * ∏ i, (x i : ℂ) ^ (b i - 1))
      (mvBetaSimplex n) ∧
    mvBetaIntegral b₀ b = mvBeta (Fin.cons b₀ b) := by
  induction n generalizing b₀ with
  | zero =>
      refine ⟨?_, mvBetaIntegral_zero hb₀⟩
      have hfun :
          (fun x : Fin 0 → ℝ =>
              ((1 - ∑ i, x i : ℝ) : ℂ) ^ (b₀ - 1) * ∏ i, (x i : ℂ) ^ (b i - 1)) =
            fun _ => 1 := by
        funext x
        simp
      rw [hfun]
      refine (integrableOn_const_iff).2 (Or.inr ?_)
      simp [mvBetaSimplex]
  | succ n ih =>
      have hb' : ∀ i : Fin n, 0 < (b i.castSucc).re := fun i => hb _
      have hbl : 0 < (b (Fin.last n)).re := hb _
      have hb₀' : 0 < (b₀ + b (Fin.last n)).re := by
        rw [add_re]
        exact add_pos hb₀ hbl
      have ih' := ih hb₀' hb'
      set f : (Fin (n + 1) → ℝ) → ℂ := fun x =>
        ((1 - ∑ i, x i : ℝ) : ℂ) ^ (b₀ - 1) * ∏ i, (x i : ℂ) ^ (b i - 1)
      set f' : (Fin n → ℝ) → ℂ := fun y =>
        ((1 - ∑ i, y i : ℝ) : ℂ) ^ (b₀ + b (Fin.last n) - 1) *
          ∏ i, (y i : ℂ) ^ (b i.castSucc - 1)
      have hfmeas : Measurable f := measurable_mvBetaIntegrand b₀ b
      have hmp := measurePreserving_piFinSnoc n ℝ
      have hme := (piFinSnoc n ℝ).measurableEmbedding
      have hR := piFinSnoc_preimage_mvBetaSimplex n
      have hRmeas : MeasurableSet (piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1)) :=
        hmp.measurable (measurableSet_mvBetaSimplex _)
      have hf_comp : ∀ y t,
          f (piFinSnoc n ℝ (y, t)) =
            ((1 - ∑ i, y i - t : ℝ) : ℂ) ^ (b₀ - 1) *
              ((t : ℂ) ^ (b (Fin.last n) - 1) *
                ∏ i, (y i : ℂ) ^ (b i.castSucc - 1)) := by
        intro y t
        simp [f, piFinSnoc_apply, Fin.sum_univ_castSucc, Fin.prod_univ_castSucc]
        ring
      have hslice (y : Fin n → ℝ) :
          Integrable fun t : ℝ =>
            (piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1)).indicator (f ∘ piFinSnoc n ℝ) (y, t) := by
        by_cases hy : y ∈ mvBetaSimplex n
        · have hs : 0 ≤ 1 - ∑ i, y i := sub_nonneg.mpr hy.2
          have hβint := intervalIntegrable_scaled_beta hbl hb₀ hs
          have hIcc : IntegrableOn
              (fun t : ℝ => (t : ℂ) ^ (b (Fin.last n) - 1) *
                ((1 - ∑ i, y i - t : ℝ) : ℂ) ^ (b₀ - 1))
              (Set.Icc 0 (1 - ∑ i, y i)) :=
            (intervalIntegrable_iff_integrableOn_Icc_of_le hs).mp (by
              convert hβint using 1
              ext t
              simp)
          have hmul : IntegrableOn
              (fun t : ℝ => (∏ i, (y i : ℂ) ^ (b i.castSucc - 1)) *
                ((t : ℂ) ^ (b (Fin.last n) - 1) *
                  ((1 - ∑ i, y i - t : ℝ) : ℂ) ^ (b₀ - 1)))
              (Set.Icc 0 (1 - ∑ i, y i)) :=
            hIcc.const_mul _
          have hfun : (fun t : ℝ =>
              (piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1)).indicator (f ∘ piFinSnoc n ℝ) (y, t)) =
              (Set.Icc 0 (1 - ∑ i, y i)).indicator (fun t =>
                (∏ i, (y i : ℂ) ^ (b i.castSucc - 1)) *
                  ((t : ℂ) ^ (b (Fin.last n) - 1) *
                    ((1 - ∑ i, y i - t : ℝ) : ℂ) ^ (b₀ - 1))) := by
            funext t
            by_cases ht : t ∈ Set.Icc 0 (1 - ∑ i, y i)
            · have hmem : (y, t) ∈ piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1) := by
                rw [hR]; exact ⟨hy, ht⟩
              rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ht]
              simp only [Function.comp_apply, hf_comp]
              ring
            · have hnmem : (y, t) ∉ piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1) := by
                rw [hR]; exact fun h => ht h.2
              simp [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem ht]
          rw [hfun]
          exact (integrable_indicator_iff measurableSet_Icc).mpr hmul
        · have h0 : ∀ t, (piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1)).indicator (f ∘ piFinSnoc n ℝ) (y, t) = 0 := by
            intro t
            apply Set.indicator_of_notMem
            rw [hR]
            exact fun h => hy h.1
          simp [h0]
      have hfR : IntegrableOn (f ∘ piFinSnoc n ℝ)
          (piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1)) volume := by
        rw [Measure.volume_eq_prod]
        have hASM : AEStronglyMeasurable
            ((piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1)).indicator (f ∘ piFinSnoc n ℝ))
            (volume.prod volume) :=
          (hfmeas.comp hmp.measurable).aestronglyMeasurable.indicator hRmeas
        refine (integrable_indicator_iff hRmeas).1 ?_
        rw [integrable_prod_iff hASM]
        refine ⟨Filter.Eventually.of_forall hslice, ?_⟩
        -- The inner-norm integral is controlled by the inductive integrand.
        let C : ℝ :=
          ∫ t in (0 : ℝ)..1, ‖(t : ℂ) ^ (b (Fin.last n) - 1) * (1 - (t : ℂ)) ^ (b₀ - 1)‖
        have hbound : Integrable fun y : Fin n → ℝ =>
            ∫ t : ℝ, ‖(piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1)).indicator
              (f ∘ piFinSnoc n ℝ) (y, t)‖ := by
          have hf'n : IntegrableOn (fun y => ‖f' y‖) (mvBetaSimplex n) := ih'.1.norm
          have hsum0 : ∀ᵐ (y : Fin n → ℝ), ∑ i, y i ≠ (1 : ℝ) := by
            simpa [ae_iff] using volume_setOf_sum_eq_one n
          have hcoord0 : ∀ᵐ (y : Fin n → ℝ), ∀ i : Fin n, y i ≠ 0 := by
            have h := measure_iUnion_null fun i : Fin n => volume_setOf_eval_eq_zero i
            rw [ae_iff]
            convert h
            ext y
            simp
          have hEq :
              (fun y => ∫ t, ‖(piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1)).indicator
                  (f ∘ piFinSnoc n ℝ) (y, t)‖) =ᵐ[volume]
                (mvBetaSimplex n).indicator (fun y => C * ‖f' y‖) := by
            filter_upwards [hsum0, hcoord0] with y hsum hcoord
            by_cases hy : y ∈ mvBetaSimplex n
            · have hs : 0 < 1 - ∑ i, y i :=
                lt_of_le_of_ne (sub_nonneg.mpr hy.2) (fun h => hsum (by linarith [h]))
              have hscale := integral_norm_scaled_beta hbl hb₀ hs
              have hs0 : 0 ≤ 1 - ∑ i, y i := le_of_lt hs
              have hfun : (fun t =>
                  ‖(piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1)).indicator
                    (f ∘ piFinSnoc n ℝ) (y, t)‖) =
                  (Set.Icc 0 (1 - ∑ i, y i)).indicator (fun t =>
                    ‖∏ i, (y i : ℂ) ^ (b i.castSucc - 1)‖ *
                      ‖(t : ℂ) ^ (b (Fin.last n) - 1) *
                        ((1 - ∑ i, y i - t : ℝ) : ℂ) ^ (b₀ - 1)‖) := by
                funext t
                by_cases ht : t ∈ Set.Icc 0 (1 - ∑ i, y i)
                · have hmem : (y, t) ∈ piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1) := by
                    rw [hR]; exact ⟨hy, ht⟩
                  rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ht]
                  simp only [Function.comp_apply, hf_comp, norm_mul]
                  ring
                · have hnmem : (y, t) ∉ piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1) := by
                    rw [hR]; exact fun h => ht h.2
                  simp [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem ht]
              have hI :
                  ∫ t, ‖(piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1)).indicator
                      (f ∘ piFinSnoc n ℝ) (y, t)‖ =
                    ‖∏ i, (y i : ℂ) ^ (b i.castSucc - 1)‖ *
                      ∫ t in (0 : ℝ)..(1 - ∑ i, y i),
                        ‖(t : ℂ) ^ (b (Fin.last n) - 1) *
                          (((1 - ∑ i, y i : ℝ) : ℂ) - t) ^ (b₀ - 1)‖ := by
                rw [hfun, integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le hs0,
                  ← integral_const_mul, integral_Icc_eq_integral_Ioc]
                apply setIntegral_congr_fun measurableSet_Ioc
                intro t _
                simp only [ofReal_sub]
              have hf'eq : ‖f' y‖ =
                  (1 - ∑ i, y i : ℝ) ^ ((b₀ + b (Fin.last n)).re - 1) *
                    ‖∏ i, (y i : ℂ) ^ (b i.castSucc - 1)‖ := by
                simp only [f', norm_mul]
                rw [norm_cpow_eq_rpow_re_of_pos hs, sub_re, add_re, one_re]
              rw [hI, hscale, Set.indicator_of_mem hy, hf'eq]
              simp only [C, add_re]
              ring
            · have h0 : ∀ t,
                  (piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1)).indicator
                    (f ∘ piFinSnoc n ℝ) (y, t) = 0 := by
                intro t
                apply Set.indicator_of_notMem
                rw [hR]
                exact fun h => hy h.1
              simp [h0, Set.indicator_of_notMem hy, integral_zero]
          exact (integrable_congr hEq).mpr
            ((integrable_indicator_iff (measurableSet_mvBetaSimplex n)).mpr (hf'n.const_mul C))
        exact hbound
      have hfΔ : IntegrableOn f (mvBetaSimplex (n + 1)) :=
        (hmp.integrableOn_comp_preimage hme).1 hfR
      refine ⟨hfΔ, ?_⟩
      have hFubini :=
        (hmp.setIntegral_preimage_emb hme f (mvBetaSimplex (n + 1))).symm
      have hprod :
          ∫ p in piFinSnoc n ℝ ⁻¹' mvBetaSimplex (n + 1), f (piFinSnoc n ℝ p) =
            ∫ y in mvBetaSimplex n, ∫ t in Set.Icc 0 (1 - ∑ i, y i),
              f (piFinSnoc n ℝ (y, t)) := by
        rw [hR]
        exact setIntegral_prod_Icc_slice_volume (measurableSet_mvBetaSimplex n)
          (measurable_const : Measurable (fun _ : Fin n → ℝ => (0 : ℝ)))
          (measurable_const.sub
            (Finset.univ.measurable_sum fun i _ => measurable_pi_apply i))
          (fun p => f (piFinSnoc n ℝ p)) (hR ▸ hfR)
      have hinter (y : Fin n → ℝ) (_hy : y ∈ mvBetaSimplex n)
          (hs : 0 < 1 - ∑ i, y i) :
          ∫ t in Set.Icc 0 (1 - ∑ i, y i), f (piFinSnoc n ℝ (y, t)) =
            (∏ i, (y i : ℂ) ^ (b i.castSucc - 1)) *
              ((1 - ∑ i, y i : ℝ) : ℂ) ^ (b₀ + b (Fin.last n) - 1) *
                betaIntegral (b (Fin.last n)) b₀ := by
        have hs0 : 0 ≤ 1 - ∑ i, y i := le_of_lt hs
        have hmul (t : ℝ) :
            f (piFinSnoc n ℝ (y, t)) =
              (∏ i, (y i : ℂ) ^ (b i.castSucc - 1)) *
                ((t : ℂ) ^ (b (Fin.last n) - 1) *
                  (((1 - ∑ i, y i : ℝ) : ℂ) - t) ^ (b₀ - 1)) := by
          rw [hf_comp]
          push_cast
          ring
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs0]
        simp_rw [hmul]
        rw [intervalIntegral.integral_const_mul, betaIntegral_scaled (b (Fin.last n)) b₀ hs]
        ring_nf
      simp only [mvBetaIntegral]
      rw [hFubini, hprod]
      have houter :
          ∫ y in mvBetaSimplex n, ∫ t in Set.Icc 0 (1 - ∑ i, y i),
              f (piFinSnoc n ℝ (y, t)) =
            betaIntegral (b (Fin.last n)) b₀ * ∫ y in mvBetaSimplex n, f' y := by
        have hnull : ∀ᵐ (y : Fin n → ℝ), ∑ i, y i ≠ (1 : ℝ) := by
          simpa [ae_iff] using volume_setOf_sum_eq_one n
        rw [← integral_const_mul]
        refine setIntegral_congr_ae (measurableSet_mvBetaSimplex n) ?_
        filter_upwards [hnull] with y hy
        intro hymem
        by_cases hs : 0 < 1 - ∑ i, y i
        · rw [hinter y hymem hs]
          simp [f']
          ring_nf
        · have hs0 : 1 - ∑ i, y i = 0 :=
            le_antisymm (not_lt.mp hs) (sub_nonneg.mpr hymem.2)
          exact (hy (sub_eq_zero.mp hs0).symm).elim
      rw [houter, ← mvBetaIntegral, ih'.2, mul_comm]
      exact mvBeta_cons_mul_betaIntegral hb₀ hb

/-- DLMF 5.14.2: the solid-coordinate Dirichlet integral equals the multivariate Beta function.
The slack parameter is placed first in `Fin.cons`; parameter symmetry identifies this convention
with the DLMF convention, where it is displayed last. -/
theorem mvBetaIntegral_eq_mvBeta {n : ℕ} {b₀ : ℂ} {b : Fin n → ℂ}
    (hb₀ : 0 < b₀.re) (hb : ∀ i, 0 < (b i).re) :
    mvBetaIntegral b₀ b = mvBeta (Fin.cons b₀ b) :=
  (mvBetaIntegral_eq_mvBeta_aux hb₀ hb).2

/-- DLMF 5.14.1: the solid-simplex integral without a slack-coordinate factor equals the
multivariate Beta function with slack parameter one. -/
theorem mvBetaIntegralOne_eq_mvBeta {n : ℕ} {b : Fin n → ℂ} (hb : ∀ i, 0 < (b i).re) :
    mvBetaIntegralOne b = mvBeta (Fin.cons 1 b) := by
  simpa [mvBetaIntegralOne, mvBetaIntegral] using
    (mvBetaIntegral_eq_mvBeta (b₀ := (1 : ℂ)) (b := b) (by norm_num) hb)

end SolidSimplexIntegral

end Complex

end MvBeta
