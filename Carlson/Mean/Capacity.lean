/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Real
public import Carlson.R.SingleIntegral.PositiveRay
public import ToMathlib.Analysis.Convex.ElementarySymmetricMean
public import ToMathlib.Analysis.Integral.StrictMono
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Carlson's capacity inequality in arbitrary finite dimension

Theorem 3 of Carlson (1966) follows by comparing the positive-ray kernel with
the derivative of a negative power of the arithmetic mean of the square roots.
Maclaurin's inequality supplies the strict pointwise comparison.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology Real
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The real positive-ray kernel for half-integral Dirichlet parameters. -/
def capacityKernel (x : ι → ℝ) (t : ℝ) : ℝ := (∏ i, √(t + x i))⁻¹

/-- The arithmetic mean of the square roots along a translated positive ray. -/
def capacityRootMean (x : ι → ℝ) (t : ℝ) : ℝ :=
  (∑ i, √(t + x i)) / Fintype.card ι

/-- The mean of square roots is positive when all translated nodes are positive. -/
theorem capacityRootMean_pos {x : ι → ℝ} {t : ℝ} (hx : ∀ i, 0 < t + x i) :
    0 < capacityRootMean x t := by
  exact div_pos (Finset.sum_pos (fun i _ => Real.sqrt_pos.mpr (hx i)) Finset.univ_nonempty)
    (by exact_mod_cast (Fintype.card_pos (α := ι)))

omit [Nonempty ι] in
/-- Derivative of the arithmetic mean of the square roots. -/
theorem hasDerivAt_capacityRootMean {x : ι → ℝ} {t : ℝ} (hx : ∀ i, 0 < t + x i) :
    HasDerivAt (capacityRootMean x)
      ((∑ i, (√(t + x i))⁻¹) / (2 * Fintype.card ι)) t := by
  have hd := (HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    ((hasDerivAt_id t).add_const (x i)).sqrt (hx i).ne')).div_const (Fintype.card ι : ℝ)
  convert hd using 1
  · rfl
  · simp only [id_eq, one_div, mul_inv_rev]
    rw [← Finset.sum_mul]
    ring

/-- A negative power of the root mean has a nonnegative derivative after negation. -/
theorem hasDerivAt_neg_capacityRootMean_rpow {x : ι → ℝ} {t : ℝ}
    (hx : ∀ i, 0 < t + x i) (k : ℝ) :
    HasDerivAt (fun u => -(capacityRootMean x u) ^ (-k))
      (k * (capacityRootMean x t) ^ (-k - 1) *
        ((∑ i, (√(t + x i))⁻¹) / (2 * Fintype.card ι))) t := by
  have hd := (Real.hasDerivAt_rpow_const (x := capacityRootMean x t)
    (p := -k) (Or.inl (capacityRootMean_pos hx).ne')).comp t
      (hasDerivAt_capacityRootMean hx)
  convert hd.neg using 1 <;> first | rfl | ring

/-- The arithmetic mean of square roots tends to infinity along the positive ray. -/
theorem tendsto_capacityRootMean_atTop (x : ι → ℝ) :
    Tendsto (capacityRootMean x) atTop atTop := by
  have hterm i : Tendsto (fun t : ℝ => √(t + x i)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right atTop (x i) tendsto_id)
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
  have ht := (hterm (Classical.arbitrary ι)).atTop_div_const hN
  apply tendsto_atTop_mono _ ht
  intro t
  apply div_le_div_of_nonneg_right _ hN.le
  exact Finset.single_le_sum (fun i _ => Real.sqrt_nonneg (t + x i))
    (Finset.mem_univ (Classical.arbitrary ι))

omit [Nonempty ι] in
/-- A shifted integrable power dominates the capacity kernel on the positive ray. -/
private theorem capacityKernel_le_rpow {x : ι → ℝ} {m t : ℝ}
    (hm : 0 < m) (hx : ∀ i, m ≤ x i) (ht : 0 ≤ t) :
    capacityKernel x t ≤ (t + m) ^ (-(Fintype.card ι : ℝ) / 2) := by
  have htm : 0 < t + m := add_pos_of_nonneg_of_pos ht hm
  have he : ((√(t + m))⁻¹) ^ Fintype.card ι =
      (t + m) ^ (-(Fintype.card ι : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg htm.le,
      ← Real.rpow_natCast, ← Real.rpow_mul htm.le]
    congr 1
    ring
  rw [← he, capacityKernel, ← Finset.prod_inv_distrib]
  calc
    _ ≤ ∏ _i : ι, (√(t + m))⁻¹ := by
      apply Finset.prod_le_prod₀ (fun i _ => by positivity)
      intro i _
      exact inv_anti₀ (Real.sqrt_pos.mpr htm) (Real.sqrt_le_sqrt (by linarith [hx i]))
    _ = _ := by simp

/-- A power below minus one is integrable after a positive shift. -/
private theorem integrableOn_shifted_negative_power {m c : ℝ} (hm : 0 < m) (hc : 1 < c) :
    IntegrableOn (fun t : ℝ => (t + m) ^ (-c)) (Ioi 0) := by
  let g : ℝ → ℝ := fun t => -(t + m) ^ (-(c - 1)) / (c - 1)
  have hd (t : ℝ) (ht : t ∈ Ici 0) : HasDerivAt g ((t + m) ^ (-c)) t := by
    have hp : 0 < t + m := add_pos_of_nonneg_of_pos ht hm
    have h := (((Real.hasDerivAt_rpow_const (x := t + m) (p := -(c - 1))
      (Or.inl hp.ne')).comp t ((hasDerivAt_id t).add_const m)).neg).div_const (c - 1)
    have he : -(c - 1) - 1 = -c := by ring
    convert h using 1 <;> first | rfl | (rw [he]; field_simp)
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hc)).comp
      (tendsto_atTop_add_const_right atTop m tendsto_id)
    simpa [g] using h.neg.div_const (c - 1)
  exact integrableOn_Ioi_deriv_of_nonneg' hd
    (fun t ht => Real.rpow_nonneg (add_nonneg (show 0 ≤ t from ht.le) hm.le) _) hlim

/-- Absolute integrability of the capacity kernel for positive nodes in dimension at least three. -/
theorem integrableOn_capacityKernel {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (hn : 3 ≤ Fintype.card ι) : IntegrableOn (capacityKernel x) (Ioi 0) := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  have hcont : ContinuousOn (capacityKernel x) (Ioi 0) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.inv₀
    · fun_prop
    · exact (Finset.prod_pos (fun i _ =>
        Real.sqrt_pos.mpr (add_pos (show 0 < t from ht) (hx i)))).ne'
  have h := integrableOn_shifted_negative_power (hx i)
    (show 1 < (Fintype.card ι : ℝ) / 2 by
      have hnR : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
      linarith)
  apply h.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold capacityKernel; positivity)]
  simpa only [neg_div] using
    capacityKernel_le_rpow (hx i) (fun j => hmin j (Finset.mem_univ j)) ht.le

/-- Maclaurin's strict inequality compares the derivative kernel with the capacity kernel. -/
private theorem capacity_derivative_lt {x : ι → ℝ} (hn : 3 ≤ Fintype.card ι)
    (hne : ∃ i j, x i ≠ x j) {t : ℝ} (hx : ∀ i, 0 < t + x i) :
    ((Fintype.card ι : ℝ) - 2) * capacityRootMean x t ^
        (-((Fintype.card ι : ℝ) - 2) - 1) *
      ((∑ i, (√(t + x i))⁻¹) / (2 * Fintype.card ι)) <
        ((Fintype.card ι : ℝ) / 2 - 1) * capacityKernel x t := by
  classical
  let N : ℝ := Fintype.card ι
  let m := capacityRootMean x t
  let P := ∏ i, √(t + x i)
  let Q := ∑ i, (√(t + x i))⁻¹
  have hnR : (3 : ℝ) ≤ N := by
    change (3 : ℝ) ≤ Fintype.card ι
    exact_mod_cast hn
  have hN : 0 < N := by linarith
  have hm : 0 < m := capacityRootMean_pos hx
  have hP : 0 < P := Finset.prod_pos (fun i _ => Real.sqrt_pos.mpr (hx i))
  have hd : 0 < m ^ (Fintype.card ι - 1) := pow_pos hm _
  have hne' : ∃ i j, √(t + x i) ≠ √(t + x j) := by
    obtain ⟨i, j, hij⟩ := hne
    refine ⟨i, j, fun h => hij ?_⟩
    have he := (Real.sqrt_inj (hx i).le (hx j).le).mp h
    linarith
  have hMac := Real.prod_mul_sum_inv_lt_arithmetic_pow
    (fun i => Real.sqrt_pos.mpr (hx i)) hn hne'
  change P * Q < N * m ^ (Fintype.card ι - 1) at hMac
  have hexp : -((Fintype.card ι : ℝ) - 2) - 1 = -((Fintype.card ι - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one]
    ring
  rw [hexp, Real.rpow_neg (capacityRootMean_pos hx).le, Real.rpow_natCast]
  change (N - 2) * (m ^ (Fintype.card ι - 1))⁻¹ * (Q / (2 * N)) <
    (N / 2 - 1) * P⁻¹
  have heL : (N - 2) * (m ^ (Fintype.card ι - 1))⁻¹ * (Q / (2 * N)) =
      ((N - 2) * Q) / (2 * N * m ^ (Fintype.card ι - 1)) := by ring
  have heR : (N / 2 - 1) * P⁻¹ = (N - 2) / (2 * P) := by ring
  rw [heL, heR, div_lt_div_iff₀ (by positivity) (by positivity)]
  have h := mul_lt_mul_of_pos_left hMac (show 0 < 2 * (N - 2) by linarith)
  convert h using 1 <;> ring

/-- **Carlson (1966), Theorem 3, integral form.** The capacity kernel strictly
bounds the reciprocal root mean for positive nonconstant nodes in every dimension at least three. -/
theorem capacity_integral_lower_bound {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (hn : 3 ≤ Fintype.card ι) (hne : ∃ i j, x i ≠ x j) :
    capacityRootMean x 0 ^ (-((Fintype.card ι : ℝ) - 2)) <
      ((Fintype.card ι : ℝ) / 2 - 1) * ∫ t in Ioi 0, capacityKernel x t := by
  let k : ℝ := (Fintype.card ι : ℝ) - 2
  let g : ℝ → ℝ := fun t => -(capacityRootMean x t) ^ (-k)
  let q : ℝ → ℝ := fun t => k * capacityRootMean x t ^ (-k - 1) *
    ((∑ i, (√(t + x i))⁻¹) / (2 * Fintype.card ι))
  have hk : 0 < k := by
    have hnR : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
    dsimp [k]
    linarith
  have hd (t : ℝ) (ht : t ∈ Ici 0) : HasDerivAt g (q t) t :=
    hasDerivAt_neg_capacityRootMean_rpow (fun i => add_pos_of_nonneg_of_pos ht (hx i)) k
  have hq (t : ℝ) (_ht : t ∈ Ioi 0) : 0 ≤ q t := by
    have hm := capacityRootMean_pos (fun i => add_pos (show 0 < t from _ht) (hx i))
    exact mul_nonneg (mul_nonneg hk.le (Real.rpow_nonneg hm.le _))
      (div_nonneg (Finset.sum_nonneg (fun i _ => by positivity)) (by positivity))
  have hlim : Tendsto g atTop (𝓝 0) := by
    simpa only [g, Function.comp_def, Pi.neg_apply, neg_zero] using
      ((tendsto_rpow_neg_atTop hk).comp (tendsto_capacityRootMean_atTop x)).neg
  have hint := integrableOn_Ioi_deriv_of_nonneg' hd hq hlim
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hd hq hlim
  have : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨by
    intro hzero
    have h := Measure.restrict_eq_zero.mp hzero
    simp at h⟩
  have hcmp : (∫ t in Ioi 0, q t) <
      ∫ t in Ioi 0, ((Fintype.card ι : ℝ) / 2 - 1) * capacityKernel x t := by
    apply integral_lt_integral_of_ae_lt hint ((integrableOn_capacityKernel hx hn).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact capacity_derivative_lt hn hne (fun i => add_pos (show 0 < t from ht) (hx i))
  rw [integral_const_mul] at hcmp
  simpa only [he, g, zero_sub, neg_neg] using hcmp

/-- The capacity kernel gives the half-integral Carlson R-average. -/
theorem capacity_integral_eq_carlsonRReal {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (hn : 3 ≤ Fintype.card ι) :
    ((Fintype.card ι : ℝ) / 2 - 1) * ∫ t in Ioi 0, capacityKernel x t =
      carlsonRReal (1 - (Fintype.card ι : ℝ) / 2) (fun _ => 1 / 2) x := by
  let C : ℂ := (Fintype.card ι : ℂ) / 2
  have hC : 0 < (C - 1).re := by
    have hnR : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
    dsimp [C]
    simp only [Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  have hsum : (1 : ℂ) + (C - 1) = ∑ _i : ι, (1 / 2 : ℂ) := by simp [C]; ring
  have hz : (fun i => (x i : ℂ)) ∈ carlsonRSlitDomain :=
    fun i => Complex.ofReal_mem_slitPlane.mpr (hx i)
  have hrep := carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR
    (a := 1) (a' := C - 1) (b := fun _ : ι => (1 / 2 : ℂ))
    (by norm_num) hC hsum hz
  have he : ((∫ t in Ioi 0, capacityKernel x t : ℝ) : ℂ) =
      carlsonRPositiveRayIntegral 1 (fun _ : ι => (1 / 2 : ℂ)) (fun i => (x i : ℂ)) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [sub_self, Complex.cpow_zero, one_mul]
    rw [capacityKernel, Complex.ofReal_inv, Complex.ofReal_prod]
    have hfactor (i : ι) : ((√(t + x i) : ℝ) : ℂ) =
        ((x i : ℂ) + (t : ℂ)) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow]
      have hp : 0 ≤ t + x i := (add_pos (show 0 < t from ht) (hx i)).le
      have hh := Complex.ofReal_cpow (y := (1 / 2 : ℝ)) hp
      rw [show (x i : ℂ) + (t : ℂ) = ((t + x i : ℝ) : ℂ) by push_cast; ring]
      simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hh
    simp_rw [hfactor, Complex.cpow_neg]
    rw [← Finset.prod_inv_distrib]
  have hgamma : (C - 1) * Complex.Gamma (C - 1) = Complex.Gamma C := by
    simpa using (Complex.Gamma_add_one (C - 1) (by
      intro h; rw [h] at hC; simp at hC)).symm
  have hidentity : (C - 1) * ((∫ t in Ioi 0, capacityKernel x t : ℝ) : ℂ) =
      carlsonR (1 - C) (fun _ : ι => (1 / 2 : ℂ)) (fun i => (x i : ℂ)) := by
    rw [he, hrep, Complex.Gamma_one]
    unfold carlsonR
    rw [show ∑ _i : ι, (1 / 2 : ℂ) = C by simp [C, div_eq_mul_inv],
      show -(C - 1) = 1 - C by ring]
    rw [one_mul, ← mul_assoc, hgamma]
  apply Complex.ofReal_injective
  have hr := ofReal_carlsonRReal (1 - (Fintype.card ι : ℝ) / 2)
    (b := fun _ : ι => (1 / 2 : ℝ)) (x := x) (by intro i; norm_num) hx
  rw [Complex.ofReal_mul, hr]
  convert hidentity using 1 <;> simp [C]

/-- **Carlson (1966), Theorem 3.** The strict capacity bound for positive
nonconstant nodes in arbitrary finite dimension at least three. -/
theorem carlsonRReal_capacity_lower_bound {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (hn : 3 ≤ Fintype.card ι) (hne : ∃ i j, x i ≠ x j) :
    ((Fintype.card ι : ℝ) / (∑ i, √(x i))) ^ (Fintype.card ι - 2) <
      carlsonRReal (1 - (Fintype.card ι : ℝ) / 2) (fun _ => 1 / 2) x := by
  have h := capacity_integral_lower_bound hx hn hne
  rw [capacity_integral_eq_carlsonRReal hx hn] at h
  have hexp : -((Fintype.card ι : ℝ) - 2) = -((Fintype.card ι - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ Fintype.card ι), Nat.cast_ofNat]
  rw [hexp, Real.rpow_neg (capacityRootMean_pos (by simpa using hx)).le,
    Real.rpow_natCast, ← inv_pow] at h
  simpa only [capacityRootMean, zero_add, inv_div] using h

/-- **Carlson (1966), Theorem 3 at nonnegative nodes.** The positive-ray integral
is interpreted in the extended nonnegative reals, so divergent boundary integrals
are included without assigning a finite value to the slit-domain R-function. -/
theorem capacity_lintegral_lower_bound {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hn : 3 ≤ Fintype.card ι) (hne : ∃ i j, x i ≠ x j) :
    ENNReal.ofReal (capacityRootMean x 0 ^ (-((Fintype.card ι : ℝ) - 2))) <
      ∫⁻ t in Ioi 0, ENNReal.ofReal
        (((Fintype.card ι : ℝ) / 2 - 1) * capacityKernel x t) := by
  let k : ℝ := (Fintype.card ι : ℝ) - 2
  let g : ℝ → ℝ := fun t => -(capacityRootMean x t) ^ (-k)
  let q : ℝ → ℝ := fun t => k * capacityRootMean x t ^ (-k - 1) *
    ((∑ i, (√(t + x i))⁻¹) / (2 * Fintype.card ι))
  have hk : 0 < k := by
    have hnR : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
    dsimp [k]
    linarith
  have hp : ∃ i, 0 < x i := by
    by_contra h
    push Not at h
    obtain ⟨i, j, hij⟩ := hne
    exact hij ((le_antisymm (h i) (hx i)).trans (le_antisymm (h j) (hx j)).symm)
  have hm0 : 0 < capacityRootMean x 0 := by
    obtain ⟨i, hi⟩ := hp
    apply div_pos _ (by exact_mod_cast (Fintype.card_pos (α := ι)))
    simpa only [zero_add] using (Real.sqrt_pos.mpr hi).trans_le
      (Finset.single_le_sum (fun j _ => Real.sqrt_nonneg (x j)) (Finset.mem_univ i))
  have hm : ContinuousAt (capacityRootMean x) 0 := by
    unfold capacityRootMean
    fun_prop
  have hg : ContinuousWithinAt g (Ici 0) 0 :=
    (hm.rpow_const (Or.inl hm0.ne')).neg.continuousWithinAt
  have hd (t : ℝ) (ht : t ∈ Ioi 0) : HasDerivAt g (q t) t :=
    hasDerivAt_neg_capacityRootMean_rpow (fun i => add_pos_of_pos_of_nonneg ht (hx i)) k
  have hq (t : ℝ) (ht : t ∈ Ioi 0) : 0 ≤ q t := by
    have hmt := capacityRootMean_pos (fun i => add_pos_of_pos_of_nonneg ht (hx i))
    exact mul_nonneg (mul_nonneg hk.le (Real.rpow_nonneg hmt.le _))
      (div_nonneg (Finset.sum_nonneg (fun i _ => by positivity)) (by positivity))
  have hlim : Tendsto g atTop (𝓝 0) := by
    simpa only [g, Function.comp_def, Pi.neg_apply, neg_zero] using
      ((tendsto_rpow_neg_atTop hk).comp (tendsto_capacityRootMean_atTop x)).neg
  have hint := integrableOn_Ioi_deriv_of_nonneg hg hd hq hlim
  have he := integral_Ioi_of_hasDerivAt_of_nonneg hg hd hq hlim
  have hNN : 0 ≤ᵐ[volume.restrict (Ioi 0)] q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hq t ht
  have heN := ofReal_integral_eq_lintegral_ofReal hint hNN
  rw [he] at heN
  simp only [g, zero_sub, neg_neg] at heN
  rw [heN]
  apply lintegral_strict_mono
    (show volume.restrict (Ioi (0 : ℝ)) ≠ 0 from fun h => by
      have he := Measure.restrict_eq_zero.mp h
      simp at he)
  · have hm : Measurable (fun t : ℝ => ENNReal.ofReal
        (((Fintype.card ι : ℝ) / 2 - 1) * capacityKernel x t)) := by
      unfold capacityKernel
      fun_prop
    exact hm.aemeasurable
  · rw [← heN]
    exact ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hh := capacity_derivative_lt hn hne
      (fun i => add_pos_of_pos_of_nonneg (show 0 < t from ht) (hx i))
    exact (ENNReal.ofReal_lt_ofReal_iff ((hq t ht).trans_lt hh)).mpr hh

end Carlson
