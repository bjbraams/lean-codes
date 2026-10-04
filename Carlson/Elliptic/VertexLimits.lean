/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.SchwarzChristoffel
public import ToMathlib.Analysis.Integral.ProdAbsRPow

/-!
# Boundary values of the Schwarz–Christoffel map (Carlson §8.2)

For real nodes `xᵢ`, exponents `0 < bᵢ < 1` and `a > 0` with `a + 1 = ∑ bᵢ`, the
Schwarz–Christoffel map `w(z) = R_{-a}(b; z - x)` of Theorem 8.2-1 is given on the upper
half-plane by `w(z) = a ∫_z^∞ ∏ (t - xᵢ)^{-bᵢ} dt` (8.2-2). This module extends `w` to the closed
upper half-plane by the same integral along the horizontal ray,
`scMap a b x z = a ∫_{re z}^∞ ∏ (σ + i im z - xᵢ)^{-bᵢ} dσ`, and proves:

* the extension is continuous on the closed upper half-plane: the dominating function
  `∏ |σ - xᵢ|^{-bᵢ}` is integrable because `bᵢ < 1` and `∑ bᵢ > 1`;
* hence `w(z)` has a limit as `z → t` from the upper half-plane for every real `t`, and in
  particular at the nodes: these are the vertices `w(xᵢ)` of Theorem 8.2-1, with Carlson's
  remark that each `w(xᵢ)` is finite because `bᵢ < 1`;
* `w(z) → 0` as `z → ∞` in the closed upper half-plane, by homogeneity of `R`;
* the polygon closes: `∫_{-∞}^{∞} ∏ (σ - xᵢ)^{-bᵢ} dσ = 0` with upper-edge phases.

## Main results

* `Carlson.scMap`: the map on the closed upper half-plane.
* `Carlson.scMap_eq_carlsonR`: it agrees with `R_{-a}(b; z - x)` on the upper half-plane.
* `Carlson.continuousOn_scMap`: continuity on the closed upper half-plane.
* `Carlson.tendsto_carlsonR_sub_nhdsWithin`: the boundary limits, including the vertices.
* `Carlson.tendsto_scMap_cobounded`: `w(∞) = 0`.
* `Carlson.integral_scIntegrand_eq_zero`: closure of the polygon.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.2.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology
@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- The hypotheses of Carlson's Theorem 8.2-1 on the parameters of a Schwarz–Christoffel map:
distinct real nodes `xᵢ`, exponents `0 < bᵢ < 1`, and `a > 0` with `a + 1 = ∑ bᵢ`. -/
structure SchwarzChristoffelParams (a : ℝ) (b x : ι → ℝ) : Prop where
  injective : Function.Injective x
  pos : ∀ i, 0 < b i
  lt_one : ∀ i, b i < 1
  a_pos : 0 < a
  sum_eq : a + 1 = ∑ i, b i

namespace SchwarzChristoffelParams

variable {a : ℝ} {b x : ι → ℝ}

theorem one_lt_sum (h : SchwarzChristoffelParams a b x) : 1 < ∑ i, b i := by
  linarith [h.sum_eq, h.a_pos]

end SchwarzChristoffelParams

/-- The Schwarz–Christoffel integrand `∏ (ζ - xᵢ)^{-bᵢ}` with principal powers. On the real axis
it gives the upper-edge values. -/
def scIntegrand (b x : ι → ℝ) (ζ : ℂ) : ℂ := ∏ i, (ζ - x i) ^ (-(b i : ℂ))

/-- The dominating function `∏ |σ - xᵢ|^{-bᵢ}` of the Schwarz–Christoffel integrand. -/
def scDensity (b x : ι → ℝ) (σ : ℝ) : ℝ := ∏ i, |σ - x i| ^ (-b i)

/-- **The Schwarz–Christoffel map on the closed upper half-plane**:
`w(z) = a ∫_{re z}^∞ ∏ (σ + i im z - xᵢ)^{-bᵢ} dσ`, the integral (8.2-2) along the horizontal ray
from `z`. -/
def scMap (a : ℝ) (b x : ι → ℝ) (z : ℂ) : ℂ :=
  a * ∫ σ in Ioi z.re, scIntegrand b x (σ + z.im * I)

/-- The closed upper half-plane. -/
def closedUpperHalfPlane : Set ℂ := {z | 0 ≤ z.im}

theorem isClosed_closedUpperHalfPlane : IsClosed closedUpperHalfPlane :=
  isClosed_le continuous_const continuous_im

variable {a : ℝ} {b x : ι → ℝ}

theorem integrable_scDensity (h : SchwarzChristoffelParams a b x) : Integrable (scDensity b x) :=
  integrable_prod_abs_sub_rpow_neg h.injective h.lt_one h.one_lt_sum

theorem scDensity_nonneg (σ : ℝ) : 0 ≤ scDensity b x σ :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

/-- Off the nodes, the integrand on a horizontal line in the closed upper half-plane is
dominated by `∏ |σ - xᵢ|^{-bᵢ}`. -/
theorem norm_scIntegrand_le (hb : ∀ i, 0 < b i) {σ v : ℝ} (hσ : ∀ i, σ ≠ x i) :
    ‖scIntegrand b x (σ + v * I)‖ ≤ scDensity b x σ := by
  rw [scIntegrand, norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
  rw [show -(b i : ℂ) = ((-b i : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
  have hre : |σ - x i| ≤ ‖(σ : ℂ) + v * I - x i‖ := by
    have := abs_re_le_norm ((σ : ℂ) + v * I - x i)
    simpa using this
  have hpos : 0 < |σ - x i| := abs_pos.mpr (sub_ne_zero.mpr (hσ i))
  exact Real.rpow_le_rpow_of_nonpos hpos hre (by linarith [hb i])

theorem measurable_scIntegrand_line (b x : ι → ℝ) (v : ℝ) :
    Measurable fun σ : ℝ => scIntegrand b x (σ + v * I) := by
  unfold scIntegrand
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (((Complex.measurable_ofReal.add_const _).sub_const _)).pow_const _

/-- Almost every real number is not a node. -/
theorem ae_ne_nodes (x : ι → ℝ) : ∀ᵐ σ : ℝ, ∀ i, σ ≠ x i := by
  have h := (Set.finite_range x).countable.ae_notMem (volume : Measure ℝ)
  filter_upwards [h] with σ hσ i hi
  exact hσ ⟨i, hi.symm⟩

/-- The integrand is integrable along every horizontal line in the closed upper half-plane. -/
theorem integrable_scIntegrand_line (h : SchwarzChristoffelParams a b x) (v : ℝ) :
    Integrable fun σ : ℝ => scIntegrand b x (σ + v * I) := by
  refine (integrable_scDensity h).mono' (measurable_scIntegrand_line b x v).aestronglyMeasurable ?_
  filter_upwards [ae_ne_nodes x] with σ hσ
  exact norm_scIntegrand_le h.pos hσ

/-- Translation of an integral over a half-line, for vector-valued functions. -/
theorem integral_Ioi_zero_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E)
    (c : ℝ) : ∫ s in Ioi (0 : ℝ), g (s + c) = ∫ σ in Ioi c, g σ := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (f := fun s => s + c) (f' := fun _ => 1)
    (fun s _ => ((hasDerivAt_id s).add_const c).hasDerivWithinAt) (add_left_injective c).injOn g
  rw [image_add_const_Ioi, zero_add] at h
  simpa using h.symm

/-- On the upper half-plane the extended map is Carlson's `w(z) = R_{-a}(b; z - x)`. -/
theorem scMap_eq_carlsonR (h : SchwarzChristoffelParams a b x) {z : ℂ} (hz : 0 < z.im) :
    scMap a b x z = carlsonR (-(a : ℂ)) (fun i => (b i : ℂ)) (fun i => z - x i) := by
  have hsum : (a : ℂ) + 1 = ∑ i, (b i : ℂ) := by exact_mod_cast h.sum_eq
  have hs : ∀ i, z - (x i : ℂ) ∈ slitPlane := fun i =>
    Or.inr (by simp [hz.ne'])
  rw [carlsonR_sub_eq_integral (a := (a : ℂ)) (by simpa using h.a_pos) (fun i => (b i : ℂ))
    (fun i => (x i : ℂ)) hsum hs, scMap]
  congr 1
  rw [← integral_Ioi_zero_add]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [scIntegrand]
  congr 1
  funext i
  congr 1
  refine Complex.ext ?_ ?_ <;> simp [add_comm]

/-- Principal powers are continuous from the closed upper half-plane at every nonzero point. -/
theorem continuousWithinAt_cpow_const_closedUpperHalfPlane (w : ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    ContinuousWithinAt (fun ζ : ℂ => ζ ^ w) closedUpperHalfPlane ζ := by
  by_cases hs : ζ ∈ slitPlane
  · exact (continuousAt_cpow_const hs).continuousWithinAt
  · have hre : ζ.re < 0 := by
      rw [mem_slitPlane_iff] at hs
      push Not at hs
      exact lt_of_le_of_ne hs.1 fun h => hζ (Complex.ext (by simp [h]) (by simp [hs.2]))
    have him : ζ.im = 0 := by
      rw [mem_slitPlane_iff] at hs
      push Not at hs
      exact hs.2
    have hexp : ContinuousWithinAt (fun ζ : ℂ => exp (log ζ * w)) closedUpperHalfPlane ζ :=
      continuous_exp.continuousAt.comp_continuousWithinAt
        ((continuousWithinAt_log_of_re_neg_of_im_zero hre him).mul continuousWithinAt_const)
    refine hexp.congr_of_eventuallyEq ?_ (cpow_def_of_ne_zero hζ w)
    filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds hζ)] with η hη
    exact cpow_def_of_ne_zero hη w

/-- **Continuity up to the boundary**: the Schwarz–Christoffel map extends continuously to the
closed upper half-plane. -/
theorem continuousOn_scMap (h : SchwarzChristoffelParams a b x) :
    ContinuousOn (scMap a b x) closedUpperHalfPlane := by
  intro z₀ hz₀
  have hind : ∀ z : ℂ, scMap a b x z = a * ∫ σ, (Ioi z.re).indicator
      (fun σ : ℝ => scIntegrand b x (σ + z.im * I)) σ := by
    intro z; rw [scMap, integral_indicator measurableSet_Ioi]
  rw [show scMap a b x = _ from funext hind]
  refine continuousWithinAt_const.mul ?_
  refine continuousWithinAt_of_dominated (bound := scDensity b x) ?_ ?_ (integrable_scDensity h) ?_
  · exact Filter.Eventually.of_forall fun z =>
      ((measurable_scIntegrand_line b x z.im).indicator measurableSet_Ioi).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    filter_upwards [ae_ne_nodes x] with σ hσ
    rw [norm_indicator_eq_indicator_norm]
    by_cases hm : σ ∈ Ioi z.re
    · rw [indicator_of_mem hm]; exact norm_scIntegrand_le h.pos hσ
    · rw [indicator_of_notMem hm]; exact scDensity_nonneg σ
  · have hne : ∀ᵐ σ : ℝ, σ ≠ z₀.re := by
      have := (Set.countable_singleton z₀.re).ae_notMem (volume : Measure ℝ)
      simpa using this
    filter_upwards [ae_ne_nodes x, hne] with σ hσ hσ₀
    rcases lt_or_gt_of_ne hσ₀ with hlt | hgt
    · -- `σ < re z₀`: the indicator vanishes near `z₀`
      have hev : ∀ᶠ z in 𝓝[closedUpperHalfPlane] z₀, (Ioi z.re).indicator
          (fun σ : ℝ => scIntegrand b x (σ + z.im * I)) σ = 0 := by
        have : ∀ᶠ z in 𝓝 z₀, σ < z.re :=
          (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hlt
        filter_upwards [nhdsWithin_le_nhds this] with z hz
        exact indicator_of_notMem (fun h : z.re < σ => lt_asymm hz h) _
      refine (continuousWithinAt_const (b := (0 : ℂ))).congr_of_eventuallyEq hev ?_
      exact indicator_of_notMem (fun h : z₀.re < σ => lt_asymm hlt h) _
    · -- `σ > re z₀`: the indicator is one near `z₀`
      have hev : ∀ᶠ z in 𝓝[closedUpperHalfPlane] z₀, (Ioi z.re).indicator
          (fun σ : ℝ => scIntegrand b x (σ + z.im * I)) σ =
            scIntegrand b x (σ + z.im * I) := by
        have : ∀ᶠ z in 𝓝 z₀, z.re < σ :=
          (continuous_re.isOpen_preimage _ isOpen_Iio).mem_nhds hgt
        filter_upwards [nhdsWithin_le_nhds this] with z hz
        exact indicator_of_mem (show σ ∈ Ioi z.re from hz) _
      refine ContinuousWithinAt.congr_of_eventuallyEq ?_ hev
        (indicator_of_mem (show σ ∈ Ioi z₀.re from hgt) _)
      unfold scIntegrand
      refine tendsto_finsetProd _ fun i _ => ?_
      have hmaps : MapsTo (fun z : ℂ => (σ : ℂ) + z.im * I - x i) closedUpperHalfPlane
          closedUpperHalfPlane := fun z hz => by simpa [closedUpperHalfPlane] using hz
      have hne0 : (σ : ℂ) + z₀.im * I - x i ≠ 0 := by
        intro h0
        have := congrArg re h0
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
          sub_re, zero_re] at this
        exact hσ i (by linarith)
      exact ContinuousWithinAt.comp (g := fun ζ : ℂ => ζ ^ (-(b i : ℂ)))
        (f := fun z : ℂ => (σ : ℂ) + z.im * I - x i)
        (continuousWithinAt_cpow_const_closedUpperHalfPlane _ hne0)
        (by fun_prop : Continuous fun z : ℂ => (σ : ℂ) + z.im * I - x i).continuousWithinAt hmaps

/-- **Boundary limits and vertices of the Schwarz–Christoffel map** (Carlson §8.2): for every
real `t`, `w(z) = R_{-a}(b; z - x)` tends to `a ∫_t^∞ ∏ (σ - xᵢ)^{-bᵢ} dσ` (upper-edge phases)
as `z → t` in the upper half-plane. At `t = xᵢ` this is the vertex `w(xᵢ)` of Theorem 8.2-1,
which is finite because `bᵢ < 1`. -/
theorem tendsto_carlsonR_sub_nhdsWithin (h : SchwarzChristoffelParams a b x) (t : ℝ) :
    Tendsto (fun z => carlsonR (-(a : ℂ)) (fun i => (b i : ℂ)) (fun i => z - x i))
      (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ))
      (𝓝 (a * ∫ σ in Ioi t, ∏ i, (((σ - x i : ℝ)) : ℂ) ^ (-(b i : ℂ)))) := by
  have hc := continuousOn_scMap h (t : ℂ) (by simp [closedUpperHalfPlane])
  have hval : scMap a b x t = a * ∫ σ in Ioi t, ∏ i, (((σ - x i : ℝ)) : ℂ) ^ (-(b i : ℂ)) := by
    simp [scMap, scIntegrand]
  rw [← hval]
  refine ((hc.mono fun z (hz : 0 < z.im) => (le_of_lt hz : 0 ≤ z.im)).tendsto).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact scMap_eq_carlsonR h hz

/-- `arg z + arg w = arg (z w)` when `z` and `z w` lie in the upper half-plane and `re w > 0`. -/
theorem arg_add_arg_mem_Ioo_of_re_pos {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.re)
    (hzw : 0 < (z * w).im) : arg z + arg w ∈ Ioo (-π) π := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (arg_mul_coe_angle hz0 hw0).symm
  have h1 : 0 ≤ arg z := arg_nonneg_iff.mpr hz.le
  have h2 : arg z < π := arg_lt_pi_iff.mpr (Or.inr hz.ne')
  have h3 : |arg w| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have h4 : 0 ≤ arg (z * w) := arg_nonneg_iff.mpr hzw.le
  have h5 : arg (z * w) < π := arg_lt_pi_iff.mpr (Or.inr hzw.ne')
  rw [abs_lt] at h3
  have hk0 : k = 0 := by
    have hπ := Real.pi_pos
    have hlt : (k : ℝ) < 1 := by
      by_contra hc
      push Not at hc
      nlinarith
    have hgt : (-1 : ℝ) < k := by
      by_contra hc
      push Not at hc
      nlinarith
    have : k < 1 := by exact_mod_cast hlt
    have : -1 < k := by exact_mod_cast hgt
    omega
  subst hk0
  simp at hk
  constructor <;> linarith

/-- **`w(∞) = 0` on the upper half-plane**, by homogeneity:
`R_{-a}(b; z - x) = Γ(∑ b) z^{-a} R_{-a}(b; 1 - x/z)/Γ(∑ b)` for large `z`. -/
theorem tendsto_carlsonR_sub_cobounded (h : SchwarzChristoffelParams a b x) :
    Tendsto (fun z => carlsonR (-(a : ℂ)) (fun i => (b i : ℂ)) (fun i => z - x i))
      (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 < z.im}) (𝓝 0) := by
  set B : ι → ℂ := fun i => (b i : ℂ)
  set F : ℂ → ℂ := fun z => Gamma (∑ i, B i) * (z ^ (-(a : ℂ)) *
    regCarlsonR (-(a : ℂ)) B (fun i => 1 - x i * z⁻¹))
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  -- the eventual identity
  have hlarge : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, ∀ i, 0 < (1 - (x i : ℂ) * z⁻¹).re := by
    have : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, ∀ i, ‖(x i : ℂ) * z⁻¹‖ < 1 := by
      rw [Filter.eventually_all]
      intro i
      have ht : Tendsto (fun z : ℂ => x i * z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
        simpa using hinv.const_mul (x i : ℂ)
      have := ht.norm.eventually (eventually_lt_nhds (show ‖(0 : ℂ)‖ < 1 by simp))
      exact this
    filter_upwards [this] with z hz i
    have := re_le_norm (x i * z⁻¹)
    have := hz i
    simp only [sub_re, one_re]
    linarith [re_le_norm (x i * z⁻¹)]
  have heq : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 < z.im},
      carlsonR (-(a : ℂ)) B (fun i => z - x i) = F z := by
    filter_upwards [inf_le_left (b := 𝓟 {z : ℂ | 0 < z.im}) hlarge,
      inf_le_right (a := Bornology.cobounded ℂ) (mem_principal_self _)] with z hz hzim
    have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hzim
    have hzim : 0 < z.im := hzim
    have hfac : ∀ i, z - x i = z * (1 - x i * z⁻¹) := fun i => by field_simp
    have hdom : (fun i => 1 - (x i : ℂ) * z⁻¹) ∈ carlsonRSlitDomain := fun i =>
      Or.inl (hz i)
    have hμ : z ∈ slitPlane := Or.inr hzim.ne'
    have harg : ∀ i, arg z + arg (1 - x i * z⁻¹) ∈ Ioo (-π) π := fun i =>
      arg_add_arg_mem_Ioo_of_re_pos hzim (hz i) (by rw [← hfac]; simpa using hzim)
    have hmul := regCarlsonR_mul_of_arg_add (-(a : ℂ)) B hdom hμ harg
    simp only [F, carlsonR]
    rw [← hmul]
    congr 2
    funext i
    exact hfac i
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  -- the limit of `F`
  have hR : Tendsto (fun z : ℂ => regCarlsonR (-(a : ℂ)) B (fun i => 1 - x i * z⁻¹))
      (Bornology.cobounded ℂ) (𝓝 (regCarlsonR (-(a : ℂ)) B (fun _ => 1))) := by
    have hone : (fun _ : ι => (1 : ℂ)) ∈ carlsonRSlitDomain := fun _ => one_mem_slitPlane
    have hc := (analyticOnNhd_regCarlsonR (-(a : ℂ)) B _ hone).continuousAt
    refine hc.tendsto.comp ?_
    rw [tendsto_pi_nhds]
    intro i
    simpa using (hinv.const_mul (x i : ℂ)).const_sub 1
  have hpow : Tendsto (fun z : ℂ => z ^ (-(a : ℂ))) (Bornology.cobounded ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : (fun z : ℂ => ‖z ^ (-(a : ℂ))‖) = fun z => ‖z‖ ^ (-a) := by
      funext z
      rw [show -(a : ℂ) = ((-a : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
    rw [this]
    exact (tendsto_rpow_neg_atTop h.a_pos).comp tendsto_norm_cobounded_atTop
  have hF : Tendsto F (Bornology.cobounded ℂ) (𝓝 0) := by
    have := (hpow.mul hR).const_mul (Gamma (∑ i, B i))
    simpa [F] using this
  exact hF.mono_left inf_le_left

/-- **`w(∞) = 0`**: the Schwarz–Christoffel map tends to `0` at infinity in the closed upper
half-plane. -/
theorem tendsto_scMap_cobounded (h : SchwarzChristoffelParams a b x) :
    Tendsto (scMap a b x) (Bornology.cobounded ℂ ⊓ 𝓟 closedUpperHalfPlane) (𝓝 0) := by
  have hH := tendsto_carlsonR_sub_cobounded h
  rw [Metric.tendsto_nhds] at hH ⊢
  intro ε hε
  have hH' := hH (ε / 2) (by linarith)
  rw [Filter.eventually_inf_principal] at hH'
  obtain ⟨R, hR⟩ : ∃ R, ∀ z : ℂ, R < ‖z‖ → 0 < z.im → dist (carlsonR (-(a : ℂ))
      (fun i => (b i : ℂ)) (fun i => z - x i)) 0 < ε / 2 := by
    rcases (Filter.hasBasis_cobounded_norm (E := ℂ)).eventually_iff.mp hH' with ⟨R, -, hR⟩
    exact ⟨R, fun z hz him => hR (show R ≤ ‖z‖ from hz.le) him⟩
  rw [Filter.eventually_inf_principal]
  have hbig : ∀ᶠ z in Bornology.cobounded ℂ, R < ‖z‖ :=
    tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)
  filter_upwards [hbig] with z hz hzH
  -- approximate `z` from inside the upper half-plane
  have hlim : Tendsto (fun n : ℕ => z + ((n : ℂ) + 1)⁻¹ * I) atTop (𝓝 z) := by
    have : Tendsto (fun n : ℕ => ((n : ℂ) + 1)⁻¹) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
      simpa [one_div] using this
    simpa using tendsto_const_nhds.add (this.mul_const I)
  have hmem : ∀ n : ℕ, 0 < (z + ((n : ℂ) + 1)⁻¹ * I).im := by
    intro n
    have hzH : 0 ≤ z.im := hzH
    have : ((n : ℂ) + 1)⁻¹ = ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    positivity
  have hnorm : ∀ n : ℕ, ‖z‖ ≤ ‖z + ((n : ℂ) + 1)⁻¹ * I‖ := by
    intro n
    have hzH : 0 ≤ z.im := hzH
    have : ((n : ℂ) + 1)⁻¹ = ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_eq_sqrt_sq_add_sq, norm_eq_sqrt_sq_add_sq]
    apply Real.sqrt_le_sqrt
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im]
    have : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    nlinarith
  have hcont := (continuousOn_scMap h z hzH).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall fun n =>
      show 0 ≤ (z + ((n : ℂ) + 1)⁻¹ * I).im from (hmem n).le⟩)
  have hle : dist (scMap a b x z) 0 ≤ ε / 2 := by
    refine le_of_tendsto (Filter.Tendsto.dist hcont tendsto_const_nhds) ?_
    refine Filter.Eventually.of_forall fun n => ?_
    simp only [Function.comp_apply]
    rw [scMap_eq_carlsonR h (hmem n)]
    exact (hR _ (lt_of_lt_of_le hz (hnorm n)) (hmem n)).le
  linarith

/-- **The polygon closes**: `∫_{-∞}^{∞} ∏ (σ - xᵢ)^{-bᵢ} dσ = 0` with upper-edge phases, since
`w(t) → 0` both as `t → +∞` and as `t → -∞`. -/
theorem integral_scIntegrand_eq_zero (h : SchwarzChristoffelParams a b x) :
    ∫ σ : ℝ, scIntegrand b x σ = 0 := by
  have hint : Integrable fun σ : ℝ => scIntegrand b x σ := by
    simpa using integrable_scIntegrand_line h 0
  have hmono : Monotone fun n : ℕ => Ioi (-(n : ℝ)) := fun m n hmn =>
    Ioi_subset_Ioi (by simpa using hmn)
  have hU : (⋃ n : ℕ, Ioi (-(n : ℝ))) = univ := by
    ext σ
    simp only [mem_iUnion, mem_Ioi, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (-σ)
    exact ⟨n, by linarith⟩
  have h1 := tendsto_setIntegral_of_monotone (μ := volume)
    (fun n => measurableSet_Ioi) hmono hint.integrableOn
  rw [hU, Measure.restrict_univ] at h1
  have h2 : Tendsto (fun n : ℕ => scMap a b x (-(n : ℝ))) atTop (𝓝 0) := by
    refine (tendsto_scMap_cobounded h).comp ?_
    refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr (Filter.Eventually.of_forall fun n => by
      simp [closedUpperHalfPlane])⟩
    refine tendsto_norm_atTop_iff_cobounded.mp ?_
    simpa using tendsto_natCast_atTop_atTop (R := ℝ)
  have h3 : Tendsto (fun n : ℕ => scMap a b x (-(n : ℝ))) atTop
      (𝓝 (a * ∫ σ : ℝ, scIntegrand b x σ)) := by
    have := h1.const_mul (a : ℂ)
    refine this.congr fun n => ?_
    simp [scMap]
  have := tendsto_nhds_unique h3 h2
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast h.a_pos.ne'
  exact (mul_eq_zero.mp this).resolve_left ha

end Carlson
