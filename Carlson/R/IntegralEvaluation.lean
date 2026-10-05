/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SingleIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Evaluation of Euler-type integrals by Carlson R-functions

This file is the home for the general integral evaluations of [Carl77, Section 8.1].  We
first use the unit-interval parameterization; oriented complex line-segment versions can be
derived from it without building phase choices into the basic definition.

## Main results

* `Carlson.carlsonEulerSegmentIntegral_eq_rIntegral`: Carlson's Formula 8.1-1 in unit-interval
  form, with the principal-log compatibility hypothesis needed to extract the endpoint powers.
* `Carlson.integral_segment_eq_regCarlsonR`: Formula 8.1-1 along the straight path from `x` to
  `y`, for arbitrary complex Dirichlet parameters, when each `zᵢ + wᵢ t` stays in the slit plane.
  The branch lemma `Carlson.arg_add_arg_segment_mem` shows that the continuous phase along such a
  segment is the principal one.
* `Carlson.integral_Ioi_ray_eq_regCarlsonR`, `Carlson.integral_Ioi_ray_neg_eq_regCarlsonR`:
  Formulas 8.1-2 and 8.1-3 (equations (8.1-3), (8.1-4)) for arbitrary complex Dirichlet
  parameters, with the principal-phase condition stated explicitly.
* `Carlson.carlsonEulerRayIntegral_eq_rIntegral`: Carlson's Formulas 8.1-2 and 8.1-3, with the
  principal-log compatibility hypothesis needed to extract the ray-direction powers.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory Set
open scoped Real
@[expose] public noncomputable section CarlsonR
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The Euler-type unit-interval integral underlying Carlson's Formula 8.1-1. -/
def carlsonEulerSegmentIntegral (a a' : ℂ) (b p q : ι → ℂ) : ℂ :=
  ∫ u : ℝ in Set.Ioo 0 1,
    (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
      ∏ i, ((1 - u : ℂ) * p i + (u : ℂ) * q i) ^ (-b i)

/-- Componentwise endpoint ratio used in Carlson's finite-segment evaluation. -/
def carlsonEndpointRatio (p q : ι → ℂ) : ι → ℂ :=
  fun i => q i / p i

/-- The principal logarithms used to factor an affine endpoint segment are compatible.

This is the exact branch condition needed for
`((1-u) * p i + u * q i) ^ c = (p i) ^ c * ((1-u) + u * q i / p i) ^ c`.
It cannot in general be replaced by nonvanishing of the segment. -/
def CompatibleCarlsonSegmentLogs (p q : ι → ℂ) : Prop :=
  ∀ i u, u ∈ Set.Ioo (0 : ℝ) 1 →
    log ((1 - u : ℂ) * p i + (u : ℂ) * q i) =
      log (p i) + log ((1 - u : ℂ) + (u : ℂ) * (q i / p i))

/-- Carlson's Formula 8.1-1 in unit-interval form, with the principal-log compatibility
hypothesis needed to extract the endpoint powers. -/
theorem carlsonEulerSegmentIntegral_eq_rIntegral
    {a a' : ℂ} {b p q : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i)
    (hb : b ∈ mvBetaConvergent)
    (hp : ∀ i, p i ≠ 0)
    (hsegment : ∀ i, ∀ u : ℝ, u ∈ Set.Icc 0 1 →
      (1 - u : ℂ) * p i + (u : ℂ) * q i ≠ 0)
    (hlog : CompatibleCarlsonSegmentLogs p q)
    (hratio : carlsonEndpointRatio p q ∈ carlsonRVariableDomain) :
    carlsonEulerSegmentIntegral a a' b p q =
      betaIntegral a a' * (∏ i, (p i) ^ (-b i)) *
        carlsonRIntegral (-a) b (carlsonEndpointRatio p q) := by
  let P : ℂ := ∏ i, (p i) ^ (-b i)
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
      (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
          ∏ i, ((1 - u : ℂ) * p i + (u : ℂ) * q i) ^ (-b i) =
        P * ((u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
          ∏ i, ((1 - u : ℂ) + (u : ℂ) * carlsonEndpointRatio p q i) ^ (-b i)) := by
    have hfactor (i : ι) :
        (1 - u : ℂ) * p i + (u : ℂ) * q i =
          p i * ((1 - u : ℂ) + (u : ℂ) * (q i / p i)) := by
      field_simp [hp i]
    have hpow (i : ι) :
        ((1 - u : ℂ) * p i + (u : ℂ) * q i) ^ (-b i) =
          (p i) ^ (-b i) *
            ((1 - u : ℂ) + (u : ℂ) * carlsonEndpointRatio p q i) ^ (-b i) := by
      change ((1 - u : ℂ) * p i + (u : ℂ) * q i) ^ (-b i) =
        (p i) ^ (-b i) * ((1 - u : ℂ) + (u : ℂ) * (q i / p i)) ^ (-b i)
      have haff : (1 - u : ℂ) * p i + (u : ℂ) * q i ≠ 0 :=
        hsegment i u ⟨hu.1.le, hu.2.le⟩
      have hnorm : (1 - u : ℂ) + (u : ℂ) * (q i / p i) ≠ 0 := by
        intro hz
        apply haff
        rw [hfactor i, hz, mul_zero]
      rw [cpow_def_of_ne_zero haff, cpow_def_of_ne_zero (hp i),
        cpow_def_of_ne_zero hnorm, hlog i u hu, add_mul, exp_add]
    have hprod :
        (∏ i, ((1 - u : ℂ) * p i + (u : ℂ) * q i) ^ (-b i)) =
          P * ∏ i,
            ((1 - u : ℂ) + (u : ℂ) * carlsonEndpointRatio p q i) ^ (-b i) := by
      calc
        _ = ∏ i, (p i) ^ (-b i) *
            ((1 - u : ℂ) + (u : ℂ) * carlsonEndpointRatio p q i) ^ (-b i) := by
              apply Finset.prod_congr rfl
              intro i _
              exact hpow i
        _ = _ := by rw [Finset.prod_mul_distrib]
    rw [hprod]
    ring
  unfold carlsonEulerSegmentIntegral
  calc
    (∫ u : ℝ in Set.Ioo 0 1,
        (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
          ∏ i, ((1 - u : ℂ) * p i + (u : ℂ) * q i) ^ (-b i)) =
      P * carlsonRUnitIntervalIntegral a a' b (carlsonEndpointRatio p q) := by
        rw [carlsonRUnitIntervalIntegral, ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro u hu
        exact hpoint u hu
    _ = betaIntegral a a' * (∏ i, (p i) ^ (-b i)) *
        carlsonRIntegral (-a) b (carlsonEndpointRatio p q) := by
      rw [carlsonRUnitIntervalIntegral_eq ha ha' hsum hb hratio]
      dsimp only [P]
      ring

/-- The ray integral underlying Carlson's Formulas 8.1-2 and 8.1-3.  The choice of endpoint
values `p` and ray directions `w` accommodates either orientation. -/
def carlsonEulerRayIntegral (a : ℂ) (b p w : ι → ℂ) : ℂ :=
  ∫ s : ℝ in Set.Ioi 0,
    (s : ℂ) ^ (a - 1) * ∏ i, (p i + (s : ℂ) * w i) ^ (-b i)

/-- The principal logarithms used to factor a Carlson ray are compatible. -/
def CompatibleCarlsonRayLogs (p w : ι → ℂ) : Prop :=
  ∀ i (s : ℝ), 0 < s →
    log (p i + (s : ℂ) * w i) =
      log (w i) + log (p i / w i + (s : ℂ))

/-- Carlson's Formulas 8.1-2 and 8.1-3, with the principal-log compatibility hypothesis
needed to extract the ray-direction powers. -/
theorem carlsonEulerRayIntegral_eq_rIntegral
    {a a' : ℂ} {b p w : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i) (hb : b ∈ mvBetaConvergent)
    (hw : ∀ i, w i ≠ 0)
    (hray : ∀ i, ∀ s : ℝ, 0 ≤ s → p i + (s : ℂ) * w i ≠ 0)
    (hlog : CompatibleCarlsonRayLogs p w)
    (hvars : (fun i => p i / w i) ∈ carlsonRVariableDomain) :
    carlsonEulerRayIntegral a b p w =
      betaIntegral a a' * (∏ i, (w i) ^ (-b i)) *
        carlsonRIntegral (-a') b (fun i => p i / w i) := by
  let W : ℂ := ∏ i, (w i) ^ (-b i)
  have hpoint (s : ℝ) (hs : s ∈ Set.Ioi (0 : ℝ)) :
      (s : ℂ) ^ (a - 1) * ∏ i, (p i + (s : ℂ) * w i) ^ (-b i) =
        W * ((s : ℂ) ^ (a - 1) *
          ∏ i, (p i / w i + (s : ℂ)) ^ (-b i)) := by
    have hfactor (i : ι) :
        p i + (s : ℂ) * w i = w i * (p i / w i + (s : ℂ)) := by
      field_simp [hw i]
    have hpow (i : ι) :
        (p i + (s : ℂ) * w i) ^ (-b i) =
          (w i) ^ (-b i) * (p i / w i + (s : ℂ)) ^ (-b i) := by
      have haff : p i + (s : ℂ) * w i ≠ 0 := hray i s hs.le
      have hnorm : p i / w i + (s : ℂ) ≠ 0 := by
        intro hz
        apply haff
        rw [hfactor i, hz, mul_zero]
      rw [cpow_def_of_ne_zero haff, cpow_def_of_ne_zero (hw i),
        cpow_def_of_ne_zero hnorm, hlog i s hs, add_mul, exp_add]
    have hprod :
        (∏ i, (p i + (s : ℂ) * w i) ^ (-b i)) =
          W * ∏ i, (p i / w i + (s : ℂ)) ^ (-b i) := by
      calc
        _ = ∏ i, (w i) ^ (-b i) * (p i / w i + (s : ℂ)) ^ (-b i) := by
              apply Finset.prod_congr rfl
              intro i _
              exact hpow i
        _ = _ := by rw [Finset.prod_mul_distrib]
    rw [hprod]
    ring
  unfold carlsonEulerRayIntegral
  calc
    (∫ s : ℝ in Set.Ioi 0,
        (s : ℂ) ^ (a - 1) * ∏ i, (p i + (s : ℂ) * w i) ^ (-b i)) =
      W * carlsonRPositiveRayIntegral a b (fun i => p i / w i) := by
        rw [carlsonRPositiveRayIntegral, ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro s hs
        exact hpoint s hs
    _ = betaIntegral a a' * (∏ i, (w i) ^ (-b i)) *
        carlsonRIntegral (-a') b (fun i => p i / w i) := by
      rw [carlsonRPositiveRayIntegral_eq ha ha' hsum hb hvars]
      dsimp only [W]
      ring

/-- If the segment `[p, q]` lies in the slit plane, then along it the principal argument is
`arg p` plus the principal argument of `(1 - u) + u q/p`: the continuous phase along the
segment is the principal one. -/
theorem arg_add_arg_segment_mem {p q : ℂ}
    (hseg : ∀ u ∈ Set.Icc (0 : ℝ) 1, (1 - u : ℂ) * p + (u : ℂ) * q ∈ slitPlane)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1 - u : ℂ) + (u : ℂ) * (q / p) ∈ slitPlane ∧
      arg p + arg ((1 - u : ℂ) + (u : ℂ) * (q / p)) ∈ Set.Ioc (-π) π := by
  have hp : p ≠ 0 := slitPlane_ne_zero (by simpa using hseg 0 ⟨le_rfl, zero_le_one⟩)
  set g : ℝ → ℂ := fun u => (1 - u : ℂ) * p + (u : ℂ) * q
  set D : ℝ → ℝ := fun u => arg (g u) - arg p
  have hg : Continuous g := by fun_prop
  have hD : ContinuousOn D (Icc 0 1) := fun u hu =>
    ((ContinuousAt.comp (g := arg) (f := g) (continuousAt_arg (hseg u hu))
      hg.continuousAt).sub continuousAt_const).continuousWithinAt
  have hD0 : D 0 = 0 := by simp [D, g]
  -- `D` never reaches `±π`
  have hnot : ∀ u ∈ Set.Icc (0 : ℝ) 1, D u ≠ π ∧ D u ≠ -π := by
    intro u hu
    have key : ∀ ε : ℝ, exp ((ε : ℂ) * I) = -1 → arg (g u) = arg p + ε → False := by
      intro ε hneg h
      have hgu := norm_mul_exp_arg_mul_I (g u)
      have hpp := norm_mul_exp_arg_mul_I p
      set lam : ℝ := ‖g u‖ / ‖p‖
      have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
      have hgu0 : g u ≠ 0 := slitPlane_ne_zero (hseg u hu)
      have hlam : 0 < lam := div_pos (norm_pos_iff.mpr hgu0) hpn
      have hpc : (‖p‖ : ℂ) ≠ 0 := by exact_mod_cast hpn.ne'
      have hgl : g u = -(lam : ℂ) * p := by
        rw [← hgu, h, ofReal_add, add_mul, exp_add, hneg]
        conv_rhs => rw [← hpp]
        simp only [lam]
        push_cast
        field_simp
      set θ : ℝ := 1 / (1 + lam)
      have hθ0 : 0 < θ := by positivity
      have hθ1 : θ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hmem : θ * u ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨mul_nonneg hθ0.le hu.1, by nlinarith [hu.1, hu.2]⟩
      have h0 : g (θ * u) = 0 := by
        have : g (θ * u) = (1 - θ : ℂ) * p + (θ : ℂ) * g u := by simp only [g]; push_cast; ring
        rw [this, hgl]
        have h1 : (1 + (lam : ℂ)) ≠ 0 := by exact_mod_cast (by linarith : (1 : ℝ) + lam ≠ 0)
        simp only [θ]
        push_cast
        field_simp
        ring
      exact slitPlane_ne_zero (hseg _ hmem) h0
    constructor
    · intro h
      exact key π exp_pi_mul_I (by simp only [D] at h; linarith)
    · intro h
      exact key (-π) (by rw [ofReal_neg, neg_mul, exp_neg, exp_pi_mul_I]; norm_num)
        (by simp only [D] at h; linarith)
  have hsmall : D u ∈ Set.Ioo (-π) π := by
    by_contra hc
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hc
    rcases hc with hc | hc
    · obtain ⟨v, hv, hv'⟩ := intermediate_value_Icc' hu.1 (hD.mono (Icc_subset_Icc le_rfl hu.2))
        ⟨hc, by rw [hD0]; linarith [Real.pi_pos]⟩
      exact (hnot v ⟨hv.1, hv.2.trans hu.2⟩).2 hv'
    · obtain ⟨v, hv, hv'⟩ := intermediate_value_Icc hu.1 (hD.mono (Icc_subset_Icc le_rfl hu.2))
        ⟨by rw [hD0]; linarith [Real.pi_pos], hc⟩
      exact (hnot v ⟨hv.1, hv.2.trans hu.2⟩).1 hv'
  have hv : (1 - u : ℂ) + (u : ℂ) * (q / p) = g u / p := by simp only [g]; field_simp
  have hgu0 : g u ≠ 0 := slitPlane_ne_zero (hseg u hu)
  have harg : arg (g u / p) = D u := by
    have hgu := norm_mul_exp_arg_mul_I (g u)
    have hpp := norm_mul_exp_arg_mul_I p
    have : g u / p = ((‖g u‖ / ‖p‖ : ℝ) : ℂ) * exp ((D u : ℝ) * I) := by
      conv_lhs => rw [← hgu, ← hpp]
      simp only [D]
      push_cast
      rw [sub_mul, exp_sub]
      field_simp
    rw [this, arg_real_mul _ (div_pos (norm_pos_iff.mpr hgu0) (norm_pos_iff.mpr hp)),
      arg_exp_mul_I, toIocMod_eq_self]
    constructor <;> linarith [hsmall.1, hsmall.2]
  rw [hv]
  refine ⟨mem_slitPlane_iff_arg.mpr ⟨by rw [harg]; exact hsmall.2.ne, div_ne_zero hgu0 hp⟩, ?_⟩
  rw [harg]
  simp only [D, add_sub_cancel]
  exact arg_mem_Ioc _

/-- Along a segment in the slit plane, principal powers factor at the initial point. -/
theorem segment_cpow_eq {p q : ℂ}
    (hseg : ∀ u ∈ Set.Icc (0 : ℝ) 1, (1 - u : ℂ) * p + (u : ℂ) * q ∈ slitPlane)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (c : ℂ) :
    ((1 - u : ℂ) * p + (u : ℂ) * q) ^ c = p ^ c * ((1 - u : ℂ) + (u : ℂ) * (q / p)) ^ c := by
  obtain ⟨hv, harg⟩ := arg_add_arg_segment_mem hseg hu
  have hp : p ≠ 0 := slitPlane_ne_zero (by simpa using hseg 0 ⟨le_rfl, zero_le_one⟩)
  have hv0 := slitPlane_ne_zero hv
  have hprod : (1 - u : ℂ) * p + (u : ℂ) * q = p * ((1 - u : ℂ) + (u : ℂ) * (q / p)) := by
    field_simp
  rw [hprod, cpow_def_of_ne_zero (mul_ne_zero hp hv0), cpow_def_of_ne_zero hp,
    cpow_def_of_ne_zero hv0, (log_mul_eq_add_log_iff hp hv0).mpr harg, add_mul, exp_add]


/-- **Carlson's Formula 8.1-1** along the straight path from `x` to `y`, with `t = x + u (y - x)`:
`∫_x^y (t - x)^{a-1} (y - t)^{a'-1} ∏ (zᵢ + wᵢ t)^{-bᵢ} dt
  = B(a, a') (y - x)^{a+a'-1} ∏ (zᵢ + wᵢ x)^{-bᵢ} R_{-a}(b; (z + w y)/(z + w x))`,
for `re a, re a' > 0`, `a + a' = ∑ bᵢ`, and arbitrary complex `b`. Carlson's phases are the
principal ones: each `zᵢ + wᵢ t` stays in the slit plane along the path. -/
theorem integral_segment_eq_regCarlsonR {a a' : ℂ} {b z w : ι → ℂ} {x y : ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a + a' = ∑ i, b i) (hxy : x ≠ y)
    (hseg : ∀ i, ∀ u ∈ Set.Icc (0 : ℝ) 1, z i + w i * (x + u * (y - x)) ∈ slitPlane) :
    (y - x) * ∫ u in Set.Ioo (0 : ℝ) 1, (x + u * (y - x) - x) ^ (a - 1) *
        (y - (x + u * (y - x))) ^ (a' - 1) * ∏ i, (z i + w i * (x + u * (y - x))) ^ (-b i) =
      Gamma a * Gamma a' * (y - x) ^ (a + a' - 1) * (∏ i, (z i + w i * x) ^ (-b i)) *
        regCarlsonR (-a) b (fun i => (z i + w i * y) / (z i + w i * x)) := by
  set p : ι → ℂ := fun i => z i + w i * x
  set q : ι → ℂ := fun i => z i + w i * y
  have hpq : ∀ i (u : ℝ), z i + w i * (x + u * (y - x)) = (1 - u : ℂ) * p i + (u : ℂ) * q i :=
    fun i u => by simp only [p, q]; ring
  have hseg' : ∀ i, ∀ u ∈ Set.Icc (0 : ℝ) 1, (1 - u : ℂ) * p i + (u : ℂ) * q i ∈ slitPlane :=
    fun i u hu => hpq i u ▸ hseg i u hu
  have hr : (fun i => q i / p i) ∈ carlsonRSlitDomain := fun i => by
    simpa using (arg_add_arg_segment_mem (hseg' i) (u := 1) ⟨zero_le_one, le_rfl⟩).1
  have hd : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  set C : ℂ := (y - x) ^ (a - 1) * (y - x) ^ (a' - 1) * ∏ i, p i ^ (-b i)
  have hpoint : ∀ u ∈ Set.Ioo (0 : ℝ) 1, (x + u * (y - x) - x) ^ (a - 1) *
      (y - (x + u * (y - x))) ^ (a' - 1) * ∏ i, (z i + w i * (x + u * (y - x))) ^ (-b i) =
      C * ((u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
        ∏ i, ((1 - u : ℂ) + (u : ℂ) * (q i / p i)) ^ (-b i)) := by
    intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hu
    rw [show x + u * (y - x) - x = (u : ℂ) * (y - x) by ring,
      show y - (x + u * (y - x)) = ((1 - u : ℝ) : ℂ) * (y - x) by push_cast; ring,
      ofReal_pos_mul_cpow _ _ hu.1 hd, ofReal_pos_mul_cpow _ _ (by linarith [hu.2]) hd]
    simp_rw [hpq, fun i => segment_cpow_eq (hseg' i) hu' (-b i)]
    rw [Finset.prod_mul_distrib]
    simp only [C]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpoint, integral_const_mul]
  change (y - x) * (C * carlsonRUnitIntervalIntegral a a' b (fun i => q i / p i)) = _
  rw [carlsonRUnitIntervalIntegral_eq_Gamma_mul_regCarlsonR ha ha' hsum hr]
  simp only [C]
  rw [show a + a' - 1 = (a - 1) + (a' - 1) + 1 by ring, cpow_add _ _ hd, cpow_add _ _ hd, cpow_one]
  ring

/-- The ray integral with Carlson's phase convention built in: for `cᵢ` in the slit plane,
`∫₀^∞ s^{a'-1} ∏ wᵢ^{-bᵢ} (cᵢ + s)^{-bᵢ} ds = Γ(a) Γ(a') ∏ wᵢ^{-bᵢ} R_{-a}(b; c)/Γ(∑ bᵢ)`, with the
regularized `R`. -/
theorem integral_Ioi_prod_cpow_eq_regCarlsonR {a a' : ℂ} {b c w : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a + a' = ∑ i, b i) (hc : c ∈ carlsonRSlitDomain) :
    ∫ s in Set.Ioi (0 : ℝ), (s : ℂ) ^ (a' - 1) * ∏ i, (w i ^ (-b i) * (c i + s) ^ (-b i)) =
      Gamma a * Gamma a' * (∏ i, w i ^ (-b i)) * regCarlsonR (-a) b c := by
  have h := carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR ha' ha
    (by rw [add_comm]; exact hsum) hc
  unfold carlsonRPositiveRayIntegral at h
  simp_rw [Finset.prod_mul_distrib]
  rw [show (fun s : ℝ => (s : ℂ) ^ (a' - 1) * ((∏ i, w i ^ (-b i)) * ∏ i, (c i + s) ^ (-b i))) =
      fun s : ℝ => (∏ i, w i ^ (-b i)) * ((s : ℂ) ^ (a' - 1) * ∏ i, (c i + s) ^ (-b i)) by
    funext s; ring, integral_const_mul, h]
  ring

/-- **Carlson's Formula 8.1-2** (equation (8.1-3)): along the ray `t = x + s`, `s > 0`,
`∫_x^∞ (t - x)^{a'-1} ∏ (zᵢ + wᵢ t)^{-bᵢ} dt = B(a, a') ∏ wᵢ^{-bᵢ} R_{-a}(b; x + z/w)`, in
regularized form, for arbitrary complex `b`. Carlson's continuous phase of `zᵢ + wᵢ t`, which
tends to `ph wᵢ`, is the principal one exactly when `arg wᵢ + arg (t + zᵢ/wᵢ) ∈ (-π, π]`. -/
theorem integral_Ioi_ray_eq_regCarlsonR {a a' : ℂ} {b z w : ι → ℂ} {x : ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a + a' = ∑ i, b i) (hw : ∀ i, w i ≠ 0)
    (hc : ∀ i, x + z i / w i ∈ slitPlane)
    (hphase : ∀ i, ∀ s : ℝ, 0 < s → arg (w i) + arg (x + z i / w i + s) ∈ Set.Ioc (-π) π) :
    ∫ s in Set.Ioi (0 : ℝ), (s : ℂ) ^ (a' - 1) * ∏ i, (z i + w i * (x + s)) ^ (-b i) =
      Gamma a * Gamma a' * (∏ i, w i ^ (-b i)) *
        regCarlsonR (-a) b (fun i => x + z i / w i) := by
  rw [← integral_Ioi_prod_cpow_eq_regCarlsonR ha ha' hsum (c := fun i => x + z i / w i) hc]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hne : x + z i / w i + s ≠ 0 := by
    intro h0
    have := hc i
    rw [show x + z i / w i = ((-s : ℝ) : ℂ) by push_cast; linear_combination h0] at this
    exact (ofReal_mem_slitPlane.mp this).not_ge (by linarith [show (0 : ℝ) < s from hs])
  rw [show z i + w i * (x + s) = w i * (x + z i / w i + s) by field_simp [hw i]; ring,
    cpow_def_of_ne_zero (mul_ne_zero (hw i) hne), cpow_def_of_ne_zero (hw i),
    cpow_def_of_ne_zero hne, (log_mul_eq_add_log_iff (hw i) hne).mpr (hphase i s hs), add_mul,
    exp_add]

/-- **Carlson's Formula 8.1-3** (equation (8.1-4)): along the ray `t = x - s`, `s > 0`,
`∫_{-∞}^x (x - t)^{a'-1} ∏ (zᵢ - wᵢ t)^{-bᵢ} dt = B(a, a') ∏ wᵢ^{-bᵢ} R_{-a}(b; z/w - x)`, in
regularized form. -/
theorem integral_Ioi_ray_neg_eq_regCarlsonR {a a' : ℂ} {b z w : ι → ℂ} {x : ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a + a' = ∑ i, b i) (hw : ∀ i, w i ≠ 0)
    (hc : ∀ i, z i / w i - x ∈ slitPlane)
    (hphase : ∀ i, ∀ s : ℝ, 0 < s → arg (w i) + arg (z i / w i - x + s) ∈ Set.Ioc (-π) π) :
    ∫ s in Set.Ioi (0 : ℝ), (s : ℂ) ^ (a' - 1) * ∏ i, (z i - w i * (x - s)) ^ (-b i) =
      Gamma a * Gamma a' * (∏ i, w i ^ (-b i)) *
        regCarlsonR (-a) b (fun i => z i / w i - x) := by
  have h := integral_Ioi_ray_eq_regCarlsonR (x := -x) (z := z) ha ha' hsum hw
    (fun i => by simpa [neg_add_eq_sub] using hc i)
    (fun i s hs => by simpa [neg_add_eq_sub] using hphase i s hs)
  simp only [neg_add_eq_sub] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  ring_nf

end Carlson
end CarlsonR
