/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Addition
public import Carlson.R.SingleIntegral.PositiveRay
public import ComplexAnalysis.HalfPlane
public import Carlson.R.SmallVariableJoint
public import Carlson.Aggregation

/-!
# A reduction theorem: `R_{-1}(1/2, 1/2, 1/2, 1/2)` as `R_F` (Carlson's Theorem 9.8-1)

Let `X = AB + CD`, `Y = AC + BD` and `Z = AD + BC`. Carlson's Theorem 9.8-1 states
`∫₀^∞ [(s + A²)(s + B²)(s + C²)(s + D²)]^{-1/2} ds = ∫₀^∞ [(t + X²)(t + Y²)(t + Z²)]^{-1/2} dt`
(9.8-3), or equivalently
`R_{-1}(1/2, 1/2, 1/2, 1/2; A², B², C², D²) = 2 R_F(X², Y², Z²)` (9.8-4).

For positive `A, B, C, D` the proof is Carlson's change of variables
`t = (αβ + γδ)² - X²`, where `α = (s + A²)^{1/2}`, … (9.8-5). Then `t + X² = (αβ + γδ)²`,
`t + Y² = (αγ + βδ)²`, `t + Z² = (αδ + βγ)²` and
`dt/ds = (αβ + γδ)(αγ + βδ)(αδ + βγ)/(αβγδ)`, (9.8-7) and (9.8-8).

Both sides of (9.8-4) are holomorphic in each of `A, B, C, D` where `A, B, C, D, X, Y, Z` have
positive real parts. For each variable in turn, with the later variables positive, this
condition defines a convex set of values of that variable, which contains a ray of positive
numbers. The identity theorem in one variable then extends (9.8-4) from positive values to the
whole domain, one variable at a time.

Carlson also allows one of `A, B, C, D` to be `0`. With `D = 0` the left side of (9.8-4) is
`2 R_{-1}(1/2, 1/2, 1/2; A², B², C²)` (the limit `D → 0`), and the theorem becomes
`R_{-1}(1/2, 1/2, 1/2; A², B², C²) = R_F((AB)², (AC)², (BC)²)`. We prove this for positive
`A, B, C` as the limit `D → 0+` of (9.8-4), and extend it in the same way.

## Main results

* `Carlson.integral_quartic_eq_integral_cubic_ofReal`: (9.8-3) for positive `A, B, C, D`.
* `Carlson.carlsonR_quartic_eq_carlsonRF`: Theorem 9.8-1, (9.8-4).
* `Carlson.integral_quartic_eq_integral_cubic`: Theorem 9.8-1, (9.8-3).
* `Carlson.tendsto_carlsonR_quartic_zero`, `Carlson.carlsonR_triple_eq_carlsonRF`: the case
  `D = 0`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §9.8.
-/

open Complex Set Filter Dirichlet MeasureTheory
open scoped Real Topology
@[expose] public noncomputable section

namespace Carlson

/-! ### Positive variables: Carlson's change of variables -/

/-- For `x > 0`, `x^{-1/2} = (x^{1/2})⁻¹`. -/
private theorem rpow_neg_half_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (-1 / 2 : ℝ) = (√x)⁻¹ := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hx, Real.sqrt_eq_rpow]

/-- **Carlson's (9.8-3)** for positive `A, B, C, D`:
`∫₀^∞ [(A² + s)(B² + s)(C² + s)(D² + s)]^{-1/2} ds = ∫₀^∞ [(X² + t)(Y² + t)(Z² + t)]^{-1/2} dt`
with `X = AB + CD`, `Y = AC + BD`, `Z = AD + BC`. -/
theorem integral_quartic_eq_integral_cubic_ofReal {A B C D : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hD : 0 < D) :
    ∫ s in Ioi (0 : ℝ), (A ^ 2 + s) ^ (-1 / 2 : ℝ) * (B ^ 2 + s) ^ (-1 / 2 : ℝ) *
        (C ^ 2 + s) ^ (-1 / 2 : ℝ) * (D ^ 2 + s) ^ (-1 / 2 : ℝ) =
      ∫ t in Ioi (0 : ℝ), ((A * B + C * D) ^ 2 + t) ^ (-1 / 2 : ℝ) *
        ((A * C + B * D) ^ 2 + t) ^ (-1 / 2 : ℝ) * ((A * D + B * C) ^ 2 + t) ^ (-1 / 2 : ℝ) := by
  set X := A * B + C * D
  set Y := A * C + B * D
  set Z := A * D + B * C
  set α : ℝ → ℝ := fun s => √(A ^ 2 + s)
  set β : ℝ → ℝ := fun s => √(B ^ 2 + s)
  set γ : ℝ → ℝ := fun s => √(C ^ 2 + s)
  set δ : ℝ → ℝ := fun s => √(D ^ 2 + s)
  set φ : ℝ → ℝ := fun s => (α s * β s + γ s * δ s) ^ 2 - X ^ 2
  set φ' : ℝ → ℝ := fun s => 2 * (α s * β s + γ s * δ s) *
    (1 / (2 * α s) * β s + α s * (1 / (2 * β s)) + (1 / (2 * γ s) * δ s + γ s * (1 / (2 * δ s))))
  have hpos : ∀ {E : ℝ}, 0 < E → ∀ {s : ℝ}, 0 ≤ s → 0 < E ^ 2 + s := fun hE _ hs => by positivity
  have hsq : ∀ {E : ℝ}, 0 < E → ∀ {s : ℝ}, 0 ≤ s → √(E ^ 2 + s) ^ 2 = E ^ 2 + s :=
    fun hE _ hs => Real.sq_sqrt (hpos hE hs).le
  have hsqrt_pos : ∀ {E : ℝ}, 0 < E → ∀ {s : ℝ}, 0 ≤ s → 0 < √(E ^ 2 + s) :=
    fun hE _ hs => Real.sqrt_pos.mpr (hpos hE hs)
  have hsqrtE : ∀ {E : ℝ}, 0 < E → √(E ^ 2 + 0) = E := fun hE => by
    rw [add_zero, Real.sqrt_sq hE.le]
  -- `φ` is continuous, strictly increasing, vanishes at `0` and tends to infinity
  have hφ0 : φ 0 = 0 := by
    simp only [φ, α, β, γ, δ, hsqrtE hA, hsqrtE hB, hsqrtE hC, hsqrtE hD, X]
    ring
  have hφcont : Continuous φ := by
    simp only [φ, α, β, γ, δ]
    fun_prop
  have hmono : StrictMonoOn φ (Ici 0) := by
    intro s hs s' hs' hss'
    have hs : (0 : ℝ) ≤ s := hs
    have hs' : (0 : ℝ) ≤ s' := hs'
    have hlt : ∀ {E : ℝ}, 0 < E → √(E ^ 2 + s) < √(E ^ 2 + s') := fun hE =>
      Real.sqrt_lt_sqrt (hpos hE hs).le (by linarith)
    have h1 : α s * β s < α s' * β s' :=
      mul_lt_mul'' (hlt hA) (hlt hB) (hsqrt_pos hA hs).le (hsqrt_pos hB hs).le
    have h2 : γ s * δ s < γ s' * δ s' :=
      mul_lt_mul'' (hlt hC) (hlt hD) (hsqrt_pos hC hs).le (hsqrt_pos hD hs).le
    have h0 : 0 ≤ α s * β s + γ s * δ s :=
      add_nonneg (mul_pos (hsqrt_pos hA hs) (hsqrt_pos hB hs)).le
        (mul_pos (hsqrt_pos hC hs) (hsqrt_pos hD hs)).le
    have := pow_lt_pow_left₀ (add_lt_add h1 h2) h0 two_ne_zero
    simp only [φ]
    linarith
  have htop : Tendsto φ atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-X ^ 2) tendsto_id)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hge : ∀ {E : ℝ}, 0 < E → √s ≤ √(E ^ 2 + s) := fun hE =>
      Real.sqrt_le_sqrt (by nlinarith)
    have hss : √s * √s = s := Real.mul_self_sqrt (by linarith)
    have hab : s ≤ α s * β s :=
      calc s = √s * √s := hss.symm
        _ ≤ α s * β s := mul_le_mul (hge hA) (hge hB) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hcd : 0 ≤ γ s * δ s := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    simp only [φ, id]
    nlinarith
  have himage : φ '' Ioi 0 = Ioi 0 := by
    apply Subset.antisymm
    · rintro _ ⟨s, hs, rfl⟩
      rw [← hφ0]
      exact hmono self_mem_Ici (mem_Ici_of_Ioi hs) hs
    · have := intermediate_value_Ioi (a := (0 : ℝ)) hφcont.continuousOn htop
      rwa [hφ0] at this
  -- the derivative
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (φ' s) (Ioi 0) s := by
    intro s hs
    have hs : (0 : ℝ) ≤ s := le_of_lt hs
    have hd : ∀ {E : ℝ}, 0 < E → HasDerivAt (fun s => √(E ^ 2 + s)) (1 / (2 * √(E ^ 2 + s))) s :=
      fun {E} hE => by
        have := ((hasDerivAt_id s).const_add (E ^ 2)).sqrt (hpos hE hs).ne'
        exact this
    have := ((((hd hA).mul (hd hB)).add ((hd hC).mul (hd hD))).pow 2).sub_const (X ^ 2)
    refine HasDerivAt.hasDerivWithinAt ?_
    convert this using 1
    simp only [φ', α, β, γ, δ]
    norm_num
  -- the change of variables
  symm
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv
    (hmono.injOn.mono Ioi_subset_Ici_self), himage]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have hs : (0 : ℝ) ≤ s := le_of_lt hs
  have ha := hsqrt_pos hA hs
  have hb := hsqrt_pos hB hs
  have hc := hsqrt_pos hC hs
  have hd := hsqrt_pos hD hs
  have ha2 := hsq hA hs
  have hb2 := hsq hB hs
  have hc2 := hsq hC hs
  have hd2 := hsq hD hs
  set a := √(A ^ 2 + s)
  set b := √(B ^ 2 + s)
  set c := √(C ^ 2 + s)
  set d := √(D ^ 2 + s)
  have hP : 0 < a * b + c * d := by positivity
  have hQ : 0 < a * c + b * d := by positivity
  have hR : 0 < a * d + b * c := by positivity
  -- (9.8-7): the three factors are squares
  have hφs : φ s = (a * b + c * d) ^ 2 - X ^ 2 := rfl
  have hX : X ^ 2 + φ s = (a * b + c * d) ^ 2 := by rw [hφs]; ring
  have hY : Y ^ 2 + φ s = (a * c + b * d) ^ 2 := by
    rw [hφs]
    linear_combination (b ^ 2 - c ^ 2) * (ha2 - hd2) + (A ^ 2 - D ^ 2) * (hb2 - hc2)
  have hZ : Z ^ 2 + φ s = (a * d + b * c) ^ 2 := by
    rw [hφs]
    linear_combination (b ^ 2 - d ^ 2) * (ha2 - hc2) + (A ^ 2 - C ^ 2) * (hb2 - hd2)
  -- (9.8-8): the derivative
  have hφ's : φ' s = 2 * (a * b + c * d) *
      (1 / (2 * a) * b + a * (1 / (2 * b)) + (1 / (2 * c) * d + c * (1 / (2 * d)))) := rfl
  have hφ'pos : 0 < φ' s := by rw [hφ's]; positivity
  beta_reduce
  rw [hX, hY, hZ, abs_of_pos hφ'pos, smul_eq_mul,
    rpow_neg_half_eq (sq_nonneg _), rpow_neg_half_eq (sq_nonneg _),
    rpow_neg_half_eq (sq_nonneg _), Real.sqrt_sq hP.le, Real.sqrt_sq hQ.le, Real.sqrt_sq hR.le,
    rpow_neg_half_eq (hpos hA hs).le, rpow_neg_half_eq (hpos hB hs).le,
    rpow_neg_half_eq (hpos hC hs).le, rpow_neg_half_eq (hpos hD hs).le, hφ's]
  field_simp
  ring

/-! ### From the integrals to the `R` functions -/

/-- The positive-ray integral (6.8-6) for `R_{-1}(1/2, 1/2, 1/2, 1/2; z)`:
`R_{-1}(1/2, 1/2, 1/2, 1/2; z) = ∫₀^∞ ∏ᵢ (zᵢ + s)^{-1/2} ds` on the slit domain. -/
theorem carlsonR_quartic_eq_integral {z : Fin 4 → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    carlsonR (-1) (fun _ => 1 / 2) z = ∫ s in Ioi (0 : ℝ), ∏ i, (z i + s) ^ (-1 / 2 : ℂ) := by
  have h := carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR (a := 1) (a' := 1)
    (b := fun _ : Fin 4 => (1 / 2 : ℂ)) (by norm_num) (by norm_num) (by simp; norm_num) hz
  unfold carlsonRPositiveRayIntegral at h
  simp only [sub_self, cpow_zero, one_mul, Gamma_one, mul_one,
    show -(1 / 2 : ℂ) = -1 / 2 by ring] at h
  unfold carlsonR
  rw [h, show ∑ _i : Fin 4, (1 / 2 : ℂ) = 1 + 1 by simp; norm_num, Gamma_add_one _ one_ne_zero,
    Gamma_one]
  ring

/-- A real `x ≥ 0` has `x^{-1/2}` real. -/
private theorem ofReal_cpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) ^ (-1 / 2 : ℂ) = ((x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [ofReal_cpow hx]
  push_cast
  ring_nf

/-- **Carlson's (9.8-4)** for positive `A, B, C, D`. -/
theorem carlsonR_quartic_eq_carlsonRF_ofReal {A B C D : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hD : 0 < D) :
    carlsonR (-1) (fun _ => 1 / 2) ![(A : ℂ) ^ 2, (B : ℂ) ^ 2, (C : ℂ) ^ 2, (D : ℂ) ^ 2] =
      2 * carlsonRF (((A : ℂ) * B + C * D) ^ 2) (((A : ℂ) * C + B * D) ^ 2)
        (((A : ℂ) * D + B * C) ^ 2) := by
  have hmem : ∀ {x : ℝ}, 0 < x → ((x : ℂ) ^ 2) ∈ slitPlane := fun hx => by
    rw [← ofReal_pow]; exact ofReal_mem_slitPlane.2 (by positivity)
  have hs : ![(A : ℂ) ^ 2, (B : ℂ) ^ 2, (C : ℂ) ^ 2, (D : ℂ) ^ 2] ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    exacts [hmem hA, hmem hB, hmem hC, hmem hD]
  have hX : ((A : ℂ) * B + C * D) = ((A * B + C * D : ℝ) : ℂ) := by push_cast; ring
  have hY : ((A : ℂ) * C + B * D) = ((A * C + B * D : ℝ) : ℂ) := by push_cast; ring
  have hZ : ((A : ℂ) * D + B * C) = ((A * D + B * C : ℝ) : ℂ) := by push_cast; ring
  rw [carlsonR_quartic_eq_integral hs, hX, hY, hZ,
    carlsonRF_eq_integral (hmem (by positivity)) (hmem (by positivity)) (hmem (by positivity))]
  have hL : ∫ s in Ioi (0 : ℝ), ∏ i, (![(A : ℂ) ^ 2, (B : ℂ) ^ 2, (C : ℂ) ^ 2, (D : ℂ) ^ 2] i +
      s) ^ (-1 / 2 : ℂ) = ∫ s in Ioi (0 : ℝ), (((A ^ 2 + s) ^ (-1 / 2 : ℝ) *
        (B ^ 2 + s) ^ (-1 / 2 : ℝ) * (C ^ 2 + s) ^ (-1 / 2 : ℝ) *
          (D ^ 2 + s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs : (0 : ℝ) ≤ s := le_of_lt hs
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    have e : ∀ E : ℝ, ((E : ℂ) ^ 2 + s) ^ (-1 / 2 : ℂ) = (((E ^ 2 + s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) :=
      fun E => by
        rw [← ofReal_cpow_neg_half (by positivity)]
        push_cast
        ring_nf
    rw [e A, e B, e C, e D]
    push_cast
    ring
  have hR : ∫ t in Ioi (0 : ℝ), (((A * B + C * D : ℝ) : ℂ) ^ 2 + t) ^ (-1 / 2 : ℂ) *
      (((A * C + B * D : ℝ) : ℂ) ^ 2 + t) ^ (-1 / 2 : ℂ) *
        (((A * D + B * C : ℝ) : ℂ) ^ 2 + t) ^ (-1 / 2 : ℂ) =
      ∫ t in Ioi (0 : ℝ), ((((A * B + C * D) ^ 2 + t) ^ (-1 / 2 : ℝ) *
        ((A * C + B * D) ^ 2 + t) ^ (-1 / 2 : ℝ) *
          ((A * D + B * C) ^ 2 + t) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : (0 : ℝ) ≤ t := le_of_lt ht
    have e : ∀ E : ℝ, ((E : ℂ) ^ 2 + t) ^ (-1 / 2 : ℂ) = (((E ^ 2 + t) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) :=
      fun E => by
        rw [← ofReal_cpow_neg_half (by positivity)]
        push_cast
        ring_nf
    rw [e, e, e]
    push_cast
    ring
  rw [hL, hR, integral_complex_ofReal, integral_complex_ofReal,
    integral_quartic_eq_integral_cubic_ofReal hA hB hC hD]
  ring

/-! ### Extension to complex variables -/

/-- The defect in (9.8-4). -/
private def quarticDefect (A B C D : ℂ) : ℂ :=
  carlsonR (-1) (fun _ => 1 / 2) ![A ^ 2, B ^ 2, C ^ 2, D ^ 2] -
    2 * carlsonRF ((A * B + C * D) ^ 2) ((A * C + B * D) ^ 2) ((A * D + B * C) ^ 2)

/-- The domain of Theorem 9.8-1: `A, B, C, D, X, Y, Z` have positive real parts. -/
private def QuarticGood (A B C D : ℂ) : Prop :=
  0 < A.re ∧ 0 < B.re ∧ 0 < C.re ∧ 0 < D.re ∧ 0 < (A * B + C * D).re ∧
    0 < (A * C + B * D).re ∧ 0 < (A * D + B * C).re

/-- The defect of (9.8-4) is holomorphic along holomorphic curves in the domain. -/
private theorem analyticAt_quarticDefect_comp {fA fB fC fD : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ fA p) (hB : AnalyticAt ℂ fB p) (hC : AnalyticAt ℂ fC p)
    (hD : AnalyticAt ℂ fD p) (hp : QuarticGood (fA p) (fB p) (fC p) (fD p)) :
    AnalyticAt ℂ (fun q => quarticDefect (fA q) (fB q) (fC q) (fD q)) p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hp
  unfold quarticDefect carlsonR
  refine (analyticAt_const.mul (analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
    ?_ ?_)).sub (analyticAt_const.mul (analyticAt_carlsonRF_comp ?_ ?_ ?_
      (sq_mem_slitPlane_of_re_pos h5) (sq_mem_slitPlane_of_re_pos h6)
        (sq_mem_slitPlane_of_re_pos h7)))
  · refine analyticAt_pi_iff.mpr fun i => ?_
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] <;> fun_prop
  · intro i; fin_cases i
    exacts [sq_mem_slitPlane_of_re_pos h1, sq_mem_slitPlane_of_re_pos h2,
      sq_mem_slitPlane_of_re_pos h3, sq_mem_slitPlane_of_re_pos h4]
  all_goals fun_prop

/-- A slice of the domain in one variable: an intersection of four open half-planes. -/
private def quarticSlice (u₁ v₁ u₂ v₂ u₃ v₃ : ℂ) : Set ℂ :=
  {ζ | 0 < ζ.re ∧ 0 < (u₁ * ζ + v₁).re ∧ 0 < (u₂ * ζ + v₂).re ∧ 0 < (u₃ * ζ + v₃).re}

/-- The identity theorem on a slice: a function holomorphic on the slice that vanishes at the
real points of the slice vanishes on the slice. -/
private theorem eq_zero_of_quarticSlice {u₁ v₁ u₂ v₂ u₃ v₃ : ℂ} (h₁ : 0 < u₁.re)
    (h₂ : 0 < u₂.re) (h₃ : 0 < u₃.re) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (quarticSlice u₁ v₁ u₂ v₂ u₃ v₃))
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ quarticSlice u₁ v₁ u₂ v₂ u₃ v₃ → g t = 0) {w : ℂ}
    (hw : w ∈ quarticSlice u₁ v₁ u₂ v₂ u₃ v₃) : g w = 0 := by
  set U := quarticSlice u₁ v₁ u₂ v₂ u₃ v₃
  have hre : ∀ u v : ℂ, Continuous fun ζ : ℂ => (u * ζ + v).re := fun u v => by fun_prop
  have hopen : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter ((isOpen_lt continuous_const (hre _ _)).inter
      ((isOpen_lt continuous_const (hre _ _)).inter (isOpen_lt continuous_const (hre _ _))))
  have hconv : Convex ℝ U := by
    have hhalf : ∀ u v : ℂ, Convex ℝ {ζ : ℂ | 0 < (u * ζ + v).re} := by
      intro u v x hx y hy a b ha hb hab
      simp only [mem_ofPred_eq] at hx hy ⊢
      have : (u * (a • x + b • y) + v).re = a * (u * x + v).re + b * (u * y + v).re := by
        simp only [Complex.real_smul, add_re, mul_re, add_im, mul_im, ofReal_re, ofReal_im]
        linear_combination (v.re) * hab.symm
      rw [this]
      rcases ha.lt_or_eq with ha | ha
      · positivity
      · subst ha; simp only [zero_add] at hab; subst hab; simpa using hy
    have h0 : Convex ℝ {ζ : ℂ | 0 < ζ.re} := by simpa using hhalf 1 0
    exact h0.inter ((hhalf _ _).inter ((hhalf _ _).inter (hhalf _ _)))
  -- large real numbers lie in the slice
  have hev : ∀ᶠ t : ℝ in atTop, (t : ℂ) ∈ U := by
    have hlin : ∀ u v : ℂ, 0 < u.re → ∀ᶠ t : ℝ in atTop, 0 < (u * t + v).re := fun u v hu => by
      have : Tendsto (fun t : ℝ => u.re * t + v.re) atTop atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hu)
      filter_upwards [this.eventually_gt_atTop 0] with t ht
      simpa using ht
    filter_upwards [eventually_gt_atTop (0 : ℝ), hlin _ v₁ h₁, hlin _ v₂ h₂, hlin _ v₃ h₃]
      with t ht ht₁ ht₂ ht₃
    exact ⟨by simpa using ht, ht₁, ht₂, ht₃⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  have hT1 : ((T + 1 : ℝ) : ℂ) ∈ U := hT _ (by linarith)
  have hfreq : ∃ᶠ z in 𝓝[≠] ((T + 1 : ℝ) : ℂ), g z = 0 := by
    have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (T + 1)) (𝓝[≠] ((T + 1 : ℝ) : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_ofReal.tendsto (T + 1)).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun t (ht : t ≠ T + 1) h => ht (ofReal_injective h))
    refine htend.frequently (Eventually.frequently ?_)
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (show T < T + 1 by linarith))] with t ht
    exact hreal t (hT t (le_of_lt ht))
  exact hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hconv.isPreconnected hT1 hfreq hw

/-- Theorem 9.8-1 on the domain, in terms of the defect. -/
private theorem quarticDefect_eq_zero {A B C D : ℂ} (h : QuarticGood A B C D) :
    quarticDefect A B C D = 0 := by
  -- positive reals
  have P0 : ∀ a b c d : ℝ, 0 < a → 0 < b → 0 < c → 0 < d → quarticDefect a b c d = 0 :=
    fun a b c d ha hb hc hd => by
      unfold quarticDefect
      rw [carlsonR_quartic_eq_carlsonRF_ofReal ha hb hc hd, sub_self]
  -- vary `A`
  have P1 : ∀ (A : ℂ) (b c d : ℝ), QuarticGood A b c d → quarticDefect A b c d = 0 := by
    intro A b c d hg
    obtain ⟨hA, hb, hc, hd, -, -, -⟩ := hg
    have hb' : 0 < b := by simpa using hb
    have hc' : 0 < c := by simpa using hc
    have hd' : 0 < d := by simpa using hd
    refine eq_zero_of_quarticSlice (u₁ := b) (v₁ := c * d) (u₂ := c) (v₂ := b * d) (u₃ := d)
      (v₃ := b * c) hb hc hd (fun ζ hζ => analyticAt_quarticDefect_comp analyticAt_id
        analyticAt_const analyticAt_const analyticAt_const ?_) (fun t ht => ?_) ?_
    · obtain ⟨h0, h1, h2, h3⟩ := hζ
      exact ⟨h0, hb, hc, hd, by simpa [mul_comm] using h1, by simpa [mul_comm] using h2,
        by simpa [mul_comm] using h3⟩
    · exact P0 t b c d (by simpa using ht.1) hb' hc' hd'
    · refine ⟨hA, ?_, ?_, ?_⟩ <;> simp [hA, hb', hc', hd', add_pos]
  -- vary `B`
  have P2 : ∀ (A B : ℂ) (c d : ℝ), QuarticGood A B c d → quarticDefect A B c d = 0 := by
    intro A B c d hg
    obtain ⟨hA, hB, hc, hd, h5, h6, h7⟩ := hg
    refine eq_zero_of_quarticSlice (u₁ := A) (v₁ := c * d) (u₂ := d) (v₂ := A * c) (u₃ := c)
      (v₃ := A * d) hA hd hc (fun ζ hζ => analyticAt_quarticDefect_comp analyticAt_const
        analyticAt_id analyticAt_const analyticAt_const ?_) (fun t ht => ?_) ?_
    · obtain ⟨h0, h1, h2, h3⟩ := hζ
      exact ⟨hA, h0, hc, hd, h1, by simpa [add_comm, mul_comm] using h2,
        by simpa [add_comm, mul_comm] using h3⟩
    · obtain ⟨h0, h1, h2, h3⟩ := ht
      exact P1 A t c d ⟨hA, h0, hc, hd, h1, by simpa [add_comm, mul_comm] using h2,
        by simpa [add_comm, mul_comm] using h3⟩
    · exact ⟨hB, h5, by simpa [add_comm, mul_comm] using h6,
        by simpa [add_comm, mul_comm] using h7⟩
  -- vary `C`
  have P3 : ∀ (A B C : ℂ) (d : ℝ), QuarticGood A B C d → quarticDefect A B C d = 0 := by
    intro A B C d hg
    obtain ⟨hA, hB, hC, hd, h5, h6, h7⟩ := hg
    refine eq_zero_of_quarticSlice (u₁ := d) (v₁ := A * B) (u₂ := A) (v₂ := B * d) (u₃ := B)
      (v₃ := A * d) hd hA hB (fun ζ hζ => analyticAt_quarticDefect_comp analyticAt_const
        analyticAt_const analyticAt_id analyticAt_const ?_) (fun t ht => ?_) ?_
    · obtain ⟨h0, h1, h2, h3⟩ := hζ
      exact ⟨hA, hB, h0, hd, by simpa [add_comm, mul_comm] using h1, h2,
        by simpa [add_comm, mul_comm] using h3⟩
    · obtain ⟨h0, h1, h2, h3⟩ := ht
      exact P2 A B t d ⟨hA, hB, h0, hd, by simpa [add_comm, mul_comm] using h1, h2,
        by simpa [add_comm, mul_comm] using h3⟩
    · exact ⟨hC, by simpa [add_comm, mul_comm] using h5, h6,
        by simpa [add_comm, mul_comm] using h7⟩
  -- vary `D`
  obtain ⟨hA, hB, hC, hD, h5, h6, h7⟩ := h
  refine eq_zero_of_quarticSlice (g := fun ζ => quarticDefect A B C ζ) (u₁ := C) (v₁ := A * B)
    (u₂ := B) (v₂ := A * C) (u₃ := A) (v₃ := B * C) hC hB hA
    (fun ζ hζ => analyticAt_quarticDefect_comp analyticAt_const analyticAt_const analyticAt_const
      analyticAt_id ?_) (fun t ht => ?_) ?_
  · obtain ⟨h0, h1, h2, h3⟩ := hζ
    exact ⟨hA, hB, hC, h0, by simpa [add_comm, mul_comm] using h1,
      by simpa [add_comm, mul_comm] using h2, by simpa [add_comm, mul_comm] using h3⟩
  · obtain ⟨h0, h1, h2, h3⟩ := ht
    exact P3 A B C t ⟨hA, hB, hC, h0, by simpa [add_comm, mul_comm] using h1,
      by simpa [add_comm, mul_comm] using h2, by simpa [add_comm, mul_comm] using h3⟩
  · exact ⟨hD, by simpa [add_comm, mul_comm] using h5, by simpa [add_comm, mul_comm] using h6,
      by simpa [add_comm, mul_comm] using h7⟩

/-- **Carlson's Theorem 9.8-1**, (9.8-4): if `A, B, C, D` and `X = AB + CD`, `Y = AC + BD`,
`Z = AD + BC` have positive real parts, then
`R_{-1}(1/2, 1/2, 1/2, 1/2; A², B², C², D²) = 2 R_F(X², Y², Z²)`. -/
theorem carlsonR_quartic_eq_carlsonRF {A B C D : ℂ} (hA : 0 < A.re) (hB : 0 < B.re)
    (hC : 0 < C.re) (hD : 0 < D.re) (hX : 0 < (A * B + C * D).re)
    (hY : 0 < (A * C + B * D).re) (hZ : 0 < (A * D + B * C).re) :
    carlsonR (-1) (fun _ => 1 / 2) ![A ^ 2, B ^ 2, C ^ 2, D ^ 2] =
      2 * carlsonRF ((A * B + C * D) ^ 2) ((A * C + B * D) ^ 2) ((A * D + B * C) ^ 2) :=
  sub_eq_zero.mp (quarticDefect_eq_zero ⟨hA, hB, hC, hD, hX, hY, hZ⟩)

/-- **Carlson's Theorem 9.8-1**, (9.8-3): under the hypotheses of
`Carlson.carlsonR_quartic_eq_carlsonRF`,
`∫₀^∞ [(A² + s)(B² + s)(C² + s)(D² + s)]^{-1/2} ds = ∫₀^∞ [(X² + t)(Y² + t)(Z² + t)]^{-1/2} dt`,
each factor with its principal square root. -/
theorem integral_quartic_eq_integral_cubic {A B C D : ℂ} (hA : 0 < A.re) (hB : 0 < B.re)
    (hC : 0 < C.re) (hD : 0 < D.re) (hX : 0 < (A * B + C * D).re)
    (hY : 0 < (A * C + B * D).re) (hZ : 0 < (A * D + B * C).re) :
    ∫ s in Ioi (0 : ℝ), (A ^ 2 + s) ^ (-1 / 2 : ℂ) * (B ^ 2 + s) ^ (-1 / 2 : ℂ) *
        (C ^ 2 + s) ^ (-1 / 2 : ℂ) * (D ^ 2 + s) ^ (-1 / 2 : ℂ) =
      ∫ t in Ioi (0 : ℝ), ((A * B + C * D) ^ 2 + t) ^ (-1 / 2 : ℂ) *
        ((A * C + B * D) ^ 2 + t) ^ (-1 / 2 : ℂ) * ((A * D + B * C) ^ 2 + t) ^ (-1 / 2 : ℂ) := by
  have hs : ![A ^ 2, B ^ 2, C ^ 2, D ^ 2] ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    exacts [sq_mem_slitPlane_of_re_pos hA, sq_mem_slitPlane_of_re_pos hB,
      sq_mem_slitPlane_of_re_pos hC, sq_mem_slitPlane_of_re_pos hD]
  have h := carlsonR_quartic_eq_carlsonRF hA hB hC hD hX hY hZ
  rw [carlsonR_quartic_eq_integral hs, carlsonRF_eq_integral (sq_mem_slitPlane_of_re_pos hX)
    (sq_mem_slitPlane_of_re_pos hY) (sq_mem_slitPlane_of_re_pos hZ)] at h
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
  rw [h]
  ring

/-! ### One variable zero -/

/-- **The left side of (9.8-4) with `D → 0`**: for right half-plane nodes,
`R_{-1}(1/2, 1/2, 1/2, 1/2; x, y, z, w) → 2 R_{-1}(1/2, 1/2, 1/2; x, y, z)` as `w → 0`. -/
theorem tendsto_carlsonR_quartic_zero {x y z : ℂ} (hx : 0 < x.re) (hy : 0 < y.re)
    (hz : 0 < z.re) :
    Tendsto (carlsonR (-1) (fun _ : Fin 4 => 1 / 2)) (𝓝[carlsonRVariableDomain] ![x, y, z, 0])
      (𝓝 (2 * carlsonR (-1) (fun _ : Fin 3 => 1 / 2) ![x, y, z])) := by
  have H := tendsto_regCarlsonR_nhdsWithin_zero (ι := Fin 4) 3 (a := 1) (a' := 1)
    (b := fun _ => 1 / 2) (z₀ := ![x, y, z, 0]) (by simp; norm_num) (by norm_num) rfl
    (fun j hj => by fin_cases j <;> simp_all) ⟨0, by decide⟩
  set q : {j : Fin 4 // j ≠ 3} → Fin 3 := fun j =>
    if j.1 = 0 then 0 else if j.1 = 1 then 1 else 2
  have hq : Function.Surjective q := by
    intro k; fin_cases k
    · exact ⟨⟨0, by decide⟩, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl⟩
    · exact ⟨⟨2, by decide⟩, rfl⟩
  have hs : ![x, y, z] ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    exacts [mem_slitPlane_iff.mpr (Or.inl hx), mem_slitPlane_iff.mpr (Or.inl hy),
      mem_slitPlane_iff.mpr (Or.inl hz)]
  have hcomp : eraseCarlsonVariable 3 (![x, y, z, 0] : Fin 4 → ℂ) = ![x, y, z] ∘ q := by
    funext j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · rfl
    · rfl
    · rfl
    · exact absurd rfl hj
  have hagg : stdSimplexAggregate q (eraseCarlsonParameter 3 (fun _ : Fin 4 => (1 / 2 : ℂ))) =
      fun _ => 1 / 2 := by
    funext k
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    fin_cases k
    · have : (Finset.univ.filter fun j : {j : Fin 4 // j ≠ 3} => q j = 0) = {⟨0, by decide⟩} := by
        decide
      show (Finset.univ.filter fun j => q j = 0).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
    · have : (Finset.univ.filter fun j : {j : Fin 4 // j ≠ 3} => q j = 1) = {⟨1, by decide⟩} := by
        decide
      show (Finset.univ.filter fun j => q j = 1).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
    · have : (Finset.univ.filter fun j : {j : Fin 4 // j ≠ 3} => q j = 2) = {⟨2, by decide⟩} := by
        decide
      show (Finset.univ.filter fun j => q j = 2).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
  rw [hcomp, regCarlsonR_aggregate_of_slit hq _ hs, hagg] at H
  have g2 : Gamma (2 : ℂ) = 1 := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, Gamma_add_one _ one_ne_zero, Gamma_one]; ring
  have H' := H.const_mul (Gamma 2)
  have hval : Gamma 2 * (Gamma (1 - 1 / 2) * ((Gamma 1)⁻¹ *
      regCarlsonR (-1) (fun _ : Fin 3 => 1 / 2) ![x, y, z])) =
        2 * carlsonR (-1) (fun _ : Fin 3 => 1 / 2) ![x, y, z] := by
    unfold carlsonR
    rw [show ∑ _i : Fin 3, (1 / 2 : ℂ) = 1 / 2 + 1 by simp; norm_num,
      Gamma_add_one _ (by norm_num), g2, Gamma_one, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]
    ring
  rw [hval] at H'
  refine H'.congr fun w => ?_
  unfold carlsonR
  rw [show ∑ _i : Fin 4, (1 / 2 : ℂ) = 2 by simp; norm_num]

/-- The defect in Theorem 9.8-1 with `D = 0`. -/
private def tripleDefect (A B C : ℂ) : ℂ :=
  carlsonR (-1) (fun _ => 1 / 2) ![A ^ 2, B ^ 2, C ^ 2] -
    carlsonRF ((A * B) ^ 2) ((A * C) ^ 2) ((B * C) ^ 2)

/-- The domain of Theorem 9.8-1 with `D = 0`. -/
private def TripleGood (A B C : ℂ) : Prop :=
  0 < A.re ∧ 0 < B.re ∧ 0 < C.re ∧ 0 < (A * B).re ∧ 0 < (A * C).re ∧ 0 < (B * C).re

/-- The defect with `D = 0` is holomorphic along holomorphic curves in the domain. -/
private theorem analyticAt_tripleDefect_comp {fA fB fC : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ fA p) (hB : AnalyticAt ℂ fB p) (hC : AnalyticAt ℂ fC p)
    (hp : TripleGood (fA p) (fB p) (fC p)) :
    AnalyticAt ℂ (fun q => tripleDefect (fA q) (fB q) (fC q)) p := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  unfold tripleDefect carlsonR
  refine (analyticAt_const.mul (analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
    ?_ ?_)).sub (analyticAt_carlsonRF_comp ?_ ?_ ?_
      (sq_mem_slitPlane_of_re_pos h4) (sq_mem_slitPlane_of_re_pos h5)
        (sq_mem_slitPlane_of_re_pos h6))
  · refine analyticAt_pi_iff.mpr fun i => ?_
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> fun_prop
  · intro i; fin_cases i
    exacts [sq_mem_slitPlane_of_re_pos h1, sq_mem_slitPlane_of_re_pos h2,
      sq_mem_slitPlane_of_re_pos h3]
  all_goals fun_prop

/-- Theorem 9.8-1 with `D = 0` for positive `A, B, C`, as a limit of (9.8-4). -/
private theorem tripleDefect_ofReal {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    tripleDefect a b c = 0 := by
  have hre : ∀ {e : ℝ}, 0 < e → 0 < ((e : ℂ) ^ 2).re := fun he => by
    rw [← ofReal_pow, ofReal_re]; positivity
  have hmem : ∀ {e : ℝ}, 0 < e → ((e : ℂ) ^ 2) ∈ slitPlane := fun he =>
    mem_slitPlane_iff.mpr (Or.inl (hre he))
  -- the left side of (9.8-4)
  have hvec : Tendsto (fun δ : ℝ => (![(a : ℂ) ^ 2, (b : ℂ) ^ 2, (c : ℂ) ^ 2, (δ : ℂ) ^ 2] :
      Fin 4 → ℂ)) (𝓝[>] 0)
        (𝓝[carlsonRVariableDomain] ![(a : ℂ) ^ 2, (b : ℂ) ^ 2, (c : ℂ) ^ 2, 0]) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · rw [tendsto_pi_nhds]
      intro i; fin_cases i
      · exact tendsto_const_nhds
      · exact tendsto_const_nhds
      · exact tendsto_const_nhds
      · have : Tendsto (fun δ : ℝ => (δ : ℂ) ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2 : ℂ)) :=
          ((continuous_ofReal.pow 2).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) i
      fin_cases i
      exacts [hre ha, hre hb, hre hc, hre hδ]
  have hL := (tendsto_carlsonR_quartic_zero (hre ha) (hre hb) (hre hc)).comp hvec
  -- the right side of (9.8-4)
  have hR : Tendsto (fun δ : ℝ => 2 * carlsonRF (((a : ℂ) * b + c * δ) ^ 2)
      (((a : ℂ) * c + b * δ) ^ 2) (((a : ℂ) * δ + b * c) ^ 2)) (𝓝[>] 0)
        (𝓝 (2 * carlsonRF (((a : ℂ) * b) ^ 2) (((a : ℂ) * c) ^ 2) (((b : ℂ) * c) ^ 2))) := by
    have hcont : ContinuousAt (fun q : ℂ => 2 * carlsonRF (((a : ℂ) * b + c * q) ^ 2)
        (((a : ℂ) * c + b * q) ^ 2) (((a : ℂ) * q + b * c) ^ 2)) 0 := by
      refine (analyticAt_const.mul (analyticAt_carlsonRF_comp (by fun_prop) (by fun_prop)
        (by fun_prop) ?_ ?_ ?_)).continuousAt
      · simpa [← ofReal_mul] using hmem (mul_pos ha hb)
      · simpa [← ofReal_mul] using hmem (mul_pos ha hc)
      · simpa [← ofReal_mul] using hmem (mul_pos hb hc)
    have := hcont.tendsto.comp ((continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0)))
    simp only [mul_zero, add_zero, zero_add] at this
    exact this
  have heq : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (carlsonR (-1) (fun _ : Fin 4 => 1 / 2) ∘
      fun δ : ℝ => (![(a : ℂ) ^ 2, (b : ℂ) ^ 2, (c : ℂ) ^ 2, (δ : ℂ) ^ 2] : Fin 4 → ℂ)) δ =
        2 * carlsonRF (((a : ℂ) * b + c * δ) ^ 2) (((a : ℂ) * c + b * δ) ^ 2)
          (((a : ℂ) * δ + b * c) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    exact carlsonR_quartic_eq_carlsonRF_ofReal ha hb hc hδ
  have := tendsto_nhds_unique (hL.congr' heq) hR
  unfold tripleDefect
  rw [sub_eq_zero]
  linear_combination (1 / 2 : ℂ) * this

/-- **Carlson's Theorem 9.8-1 with `D = 0`**: if `A, B, C` and `AB, AC, BC` have positive real
parts, then `R_{-1}(1/2, 1/2, 1/2; A², B², C²) = R_F((AB)², (AC)², (BC)²)`. By
`Carlson.tendsto_carlsonR_quartic_zero` the left side is half the value at `D = 0` of the left
side of (9.8-4), while `X, Y, Z` become `AB, AC, BC`. -/
theorem carlsonR_triple_eq_carlsonRF {A B C : ℂ} (hA : 0 < A.re) (hB : 0 < B.re)
    (hC : 0 < C.re) (hAB : 0 < (A * B).re) (hAC : 0 < (A * C).re) (hBC : 0 < (B * C).re) :
    carlsonR (-1) (fun _ => 1 / 2) ![A ^ 2, B ^ 2, C ^ 2] =
      carlsonRF ((A * B) ^ 2) ((A * C) ^ 2) ((B * C) ^ 2) := by
  refine sub_eq_zero.mp ?_
  change tripleDefect A B C = 0
  -- vary `A`
  have P1 : ∀ (A : ℂ) (b c : ℝ), TripleGood A b c → tripleDefect A b c = 0 := by
    intro A b c hg
    obtain ⟨hA, hb, hc, -, -, -⟩ := hg
    have hb' : 0 < b := by simpa using hb
    have hc' : 0 < c := by simpa using hc
    refine eq_zero_of_quarticSlice (u₁ := b) (v₁ := 0) (u₂ := c) (v₂ := 0) (u₃ := 1) (v₃ := 0)
      hb hc one_pos (fun ζ hζ => analyticAt_tripleDefect_comp analyticAt_id analyticAt_const
        analyticAt_const ?_) (fun t ht => ?_) ?_
    · obtain ⟨h0, h1, h2, -⟩ := hζ
      exact ⟨h0, hb, hc, by simpa [mul_comm] using h1, by simpa [mul_comm] using h2,
        by simp [hb', hc']⟩
    · exact tripleDefect_ofReal (by simpa using ht.1) hb' hc'
    · refine ⟨hA, ?_, ?_, ?_⟩ <;> simp [hA, hb', hc']
  -- vary `B`
  have P2 : ∀ (A B : ℂ) (c : ℝ), TripleGood A B c → tripleDefect A B c = 0 := by
    intro A B c hg
    obtain ⟨hA, hB, hc, h4, h5, h6⟩ := hg
    refine eq_zero_of_quarticSlice (u₁ := A) (v₁ := 0) (u₂ := c) (v₂ := 0) (u₃ := 1) (v₃ := 0)
      hA hc one_pos (fun ζ hζ => analyticAt_tripleDefect_comp analyticAt_const analyticAt_id
        analyticAt_const ?_) (fun t ht => ?_) ?_
    · obtain ⟨h0, h1, h2, -⟩ := hζ
      exact ⟨hA, h0, hc, by simpa using h1, h5, by simpa [mul_comm] using h2⟩
    · obtain ⟨h0, h1, h2, -⟩ := ht
      exact P1 A t c ⟨hA, h0, hc, by simpa using h1, h5, by simpa [mul_comm] using h2⟩
    · exact ⟨hB, by simpa using h4, by simpa [mul_comm] using h6, by simpa using hB⟩
  -- vary `C`
  refine eq_zero_of_quarticSlice (g := fun ζ => tripleDefect A B ζ) (u₁ := A) (v₁ := 0)
    (u₂ := B) (v₂ := 0) (u₃ := 1) (v₃ := 0) hA hB one_pos
    (fun ζ hζ => analyticAt_tripleDefect_comp analyticAt_const analyticAt_const analyticAt_id ?_)
    (fun t ht => ?_) ?_
  · obtain ⟨h0, h1, h2, -⟩ := hζ
    exact ⟨hA, hB, h0, hAB, by simpa using h1, by simpa using h2⟩
  · obtain ⟨h0, h1, h2, -⟩ := ht
    exact P2 A B t ⟨hA, hB, h0, hAB, by simpa using h1, by simpa using h2⟩
  · exact ⟨hC, by simpa using hAC, by simpa using hBC, by simpa using hC⟩

end Carlson
