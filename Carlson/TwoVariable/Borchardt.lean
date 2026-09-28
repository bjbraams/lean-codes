/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.QuadraticHybrid
public import Carlson.R.ContourRepresentation

/-!
# The accelerated Borchardt algorithm

Borchardt's algorithm (Example 6.10-5) computes `R_C(x₀², y₀²) = 1/L` as the common limit `L`
of the sequences `xₙ₊₁ = (xₙ + yₙ)/2`, `yₙ₊₁ = (xₙ₊₁ yₙ)^{1/2}`, whose squares differ by
`4⁻ⁿ (x₀² - y₀²)` (6.10-25). Carlson accelerates it with `σₙ = (xₙ + 2yₙ)/3` (6.10-27) and states
`σₙ/L = 1 + 4^{-2n-1} (x₀² - y₀²)²/(45 L⁴) + O(4^{-3n})` (6.10-28), whence the extrapolation
`σₙ + (σₙ - σₙ₋₁)/15` has error `O(64⁻ⁿ)` (6.10-29).

The proof of (6.10-28) uses the Dirichlet average `R_C(X, Y) = (1/2) ∫₀¹ u^{-1/2} w^{-1/2} du`,
`w = uX + (1-u)Y`, and the exact cubic remainder of the quadratic Taylor polynomial of
`w^{-1/2}` at the mean `A = (X + 2Y)/3`: `R_C(X, Y) = A^{-1/2}(1 + (X - Y)²/(30 A²)) + O(|X - Y|³)`.
Since `R_C` is invariant along the sequences, one step of the algebra at `(xₙ, yₙ)` gives the
estimate at every `n` with a uniform constant.

## Main definitions

* `Carlson.TwoVariable.borchardtSigma`: `σₙ` of (6.10-27).

## Main results

* `Carlson.TwoVariable.carlsonRC_eq_euler`: `R_C` as a real Euler integral.
* `Carlson.TwoVariable.abs_carlsonRC_sub_le`: the cubic expansion of `R_C` near the diagonal.
* `Carlson.TwoVariable.borchardtSeq_sq_sub`: (6.10-25).
* `Carlson.TwoVariable.carlsonRC_borchardtSeq`: the invariance of `R_C` along the sequences.
* `Carlson.TwoVariable.exists_borchardtSigma_expansion`: (6.10-28).
* `Carlson.TwoVariable.exists_borchardtSigma_extrapolation`: (6.10-29).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.10.
-/

open Complex MeasureTheory Filter Set Dirichlet
open scoped Topology Real
@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- For positive real nodes, `R_C(X, Y) = (1/2) ∫₀¹ u^{-1/2} (u X + (1 - u) Y)^{-1/2} du`, the
Dirichlet average of `w^{-1/2}` with parameters `(1/2, 1)`. -/
theorem carlsonRC_eq_euler {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    carlsonRC X Y = (((1 / 2 : ℝ) * ∫ u in Ioo (0 : ℝ) 1,
      u ^ (-(1 / 2 : ℝ)) * (u * X + (1 - u) * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hb : pair (1 / 2 : ℂ) 1 ∈ mvBetaConvergent := by
    intro i; fin_cases i <;> simp [pair]
  have hz : pair (X : ℂ) (Y : ℂ) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · simpa [carlsonRightHalfPlane] using hX
    · simpa [carlsonRightHalfPlane] using hY
  unfold carlsonRC carlsonR
  rw [regCarlsonR_eq_regCarlsonRIntegral _ hb hz, regCarlsonRIntegral,
    regCarlsonDirichletAverage_pair_eq, regEulerIntegral, sum_pair,
    show (1 / 2 : ℂ) + 1 = 1 / 2 + 1 from rfl, Gamma_add_one _ (by norm_num), Gamma_one, mul_one]
  have hG : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  rw [← mul_assoc, show 1 / 2 * Gamma (1 / 2 : ℂ) * (Gamma (1 / 2))⁻¹ = 1 / 2 by field_simp]
  push_cast
  congr 1
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hw : 0 < u * X + (1 - u) * Y := by nlinarith [hu.1, hu.2]
  push_cast
  rw [ofReal_cpow hu.1.le, show (1 - (u : ℂ)) ^ ((1 : ℂ) - 1) = 1 by simp,
    show (u : ℂ) * X + (1 - u) * Y = ((u * X + (1 - u) * Y : ℝ) : ℂ) by push_cast; ring,
    ofReal_cpow hw.le]
  push_cast
  ring_nf

/-- `∫₀¹ uʳ du = 1/(r + 1)` for `r > -1`, over the open interval. -/
theorem integral_Ioo_rpow {r : ℝ} (hr : -1 < r) : ∫ u in Ioo (0 : ℝ) 1, u ^ r = 1 / (r + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl hr), Real.one_rpow, Real.zero_rpow (by linarith)]
  ring

/-- `u ↦ uʳ` is integrable on `(0, 1)` for `r > -1`. -/
theorem integrableOn_Ioo_rpow {r : ℝ} (hr : -1 < r) : IntegrableOn (fun u : ℝ => u ^ r) (Ioo 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' hr)

/-- The exact cubic remainder of the quadratic Taylor polynomial of `w^{-1/2}` at `A = a²`,
with `w = s²`. -/
theorem inv_eq_taylor_add {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    s⁻¹ = a⁻¹ - (s ^ 2 - a ^ 2) / (2 * a ^ 3) + 3 * (s ^ 2 - a ^ 2) ^ 2 / (8 * a ^ 5) -
      (s - a) ^ 3 * (3 * s ^ 2 + 9 * a * s + 8 * a ^ 2) / (8 * a ^ 5 * s) := by
  field_simp
  ring

/-- A bound for the cubic remainder when `a, s ∈ [r, R]`. -/
theorem abs_taylor_remainder_le {a s r R : ℝ} (hr : 0 < r) (hra : r ≤ a) (hrs : r ≤ s)
    (haR : a ≤ R) (hsR : s ≤ R) :
    |(s - a) ^ 3 * (3 * s ^ 2 + 9 * a * s + 8 * a ^ 2) / (8 * a ^ 5 * s)| ≤
      |s ^ 2 - a ^ 2| ^ 3 * (20 * R ^ 2 / (64 * r ^ 9)) := by
  have ha : 0 < a := hr.trans_le hra
  have hs : 0 < s := hr.trans_le hrs
  have hsa : |s - a| = |s ^ 2 - a ^ 2| / (s + a) := by
    rw [show s ^ 2 - a ^ 2 = (s - a) * (s + a) by ring, abs_mul,
      abs_of_pos (by linarith : 0 < s + a)]
    field_simp
  rw [abs_div, abs_mul, abs_pow, hsa,
    abs_of_pos (by positivity : 0 < 3 * s ^ 2 + 9 * a * s + 8 * a ^ 2),
    abs_of_pos (by positivity : 0 < 8 * a ^ 5 * s)]
  set D := |s ^ 2 - a ^ 2|
  have hD : 0 ≤ D := abs_nonneg _
  have h1 : 2 * r ≤ s + a := by linarith
  have h2 : 3 * s ^ 2 + 9 * a * s + 8 * a ^ 2 ≤ 20 * R ^ 2 := by nlinarith
  have h3 : 8 * r ^ 6 ≤ 8 * a ^ 5 * s := by
    have : r ^ 5 ≤ a ^ 5 := pow_le_pow_left₀ hr.le hra 5
    nlinarith [pow_pos hr 5]
  rw [div_pow, div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]
  calc D ^ 3 * (3 * s ^ 2 + 9 * a * s + 8 * a ^ 2)
      ≤ D ^ 3 * (20 * R ^ 2) := by gcongr
    _ = D ^ 3 * (20 * R ^ 2 / (64 * r ^ 9)) * (64 * r ^ 9) := by field_simp
    _ ≤ D ^ 3 * (20 * R ^ 2 / (64 * r ^ 9)) * ((s + a) ^ 3 * (8 * a ^ 5 * s)) := by
        have h64 : 64 * r ^ 9 ≤ (s + a) ^ 3 * (8 * a ^ 5 * s) :=
          calc 64 * r ^ 9 = (2 * r) ^ 3 * (8 * r ^ 6) := by ring
            _ ≤ (s + a) ^ 3 * (8 * a ^ 5 * s) := by gcongr
        exact mul_le_mul_of_nonneg_left h64 (by positivity)

/-- **The expansion of `R_C` near the diagonal** (the ingredient of Carlson's (6.10-28)): for
`X, Y ∈ [r², R²]`, with `A = (X + 2Y)/3`,
`|R_C(X, Y) - A^{-1/2} (1 + (X - Y)²/(30 A²))| ≤ K |X - Y|³`, `K = 20 R²/(64 r⁹)`. -/
theorem abs_carlsonRC_sub_le {X Y r R : ℝ} (hr : 0 < r) (hRr : r ≤ R) (hX : r ^ 2 ≤ X)
    (hX' : X ≤ R ^ 2)
    (hY : r ^ 2 ≤ Y) (hY' : Y ≤ R ^ 2) :
    |(carlsonRC X Y).re - (Real.sqrt ((X + 2 * Y) / 3))⁻¹ *
        (1 + (X - Y) ^ 2 / (30 * ((X + 2 * Y) / 3) ^ 2))| ≤
      |X - Y| ^ 3 * (20 * R ^ 2 / (64 * r ^ 9)) := by
  have hX0 : 0 < X := (by positivity : 0 < r ^ 2).trans_le hX
  have hY0 : 0 < Y := (by positivity : 0 < r ^ 2).trans_le hY
  rw [carlsonRC_eq_euler hX0 hY0, ofReal_re]
  set A := (X + 2 * Y) / 3
  set a := Real.sqrt A
  set D := X - Y
  set K := 20 * R ^ 2 / (64 * r ^ 9)
  have hA : r ^ 2 ≤ A := by simp only [A]; linarith
  have hA' : A ≤ R ^ 2 := by simp only [A]; linarith
  have hsqrt : ∀ {v : ℝ}, r ^ 2 ≤ v → v ≤ R ^ 2 → r ≤ Real.sqrt v ∧ Real.sqrt v ≤ R := by
    intro v h1 h2
    exact ⟨Real.le_sqrt_of_sq_le h1, Real.sqrt_le_iff.mpr ⟨hr.le.trans hRr, h2⟩⟩
  obtain ⟨hra, haR⟩ := hsqrt hA hA'
  have ha : 0 < a := hr.trans_le hra
  have haA : a ^ 2 = A := Real.sq_sqrt (by linarith [sq_nonneg r])
  -- the weights of the three polynomial terms
  set p := D / (2 * a ^ 3)
  set q := 3 * D ^ 2 / (8 * a ^ 5)
  set c₀ := a⁻¹ + p / 3 + q / 9
  set c₁ := -p - 2 * q / 3
  set c₂ := q
  set w : ℝ → ℝ := fun u => u * X + (1 - u) * Y
  have hw : ∀ u ∈ Ioo (0 : ℝ) 1, r ^ 2 ≤ w u ∧ w u ≤ R ^ 2 := fun u hu => by
    simp only [w]; constructor <;> nlinarith [hu.1, hu.2]
  set G : ℝ → ℝ := fun u => u ^ (-(1 / 2 : ℝ)) * w u ^ (-(1 / 2 : ℝ))
  set P : ℝ → ℝ := fun u => c₀ * u ^ (-(1 / 2 : ℝ)) + c₁ * u ^ (1 / 2 : ℝ) + c₂ * u ^ (3 / 2 : ℝ)
  have hP : IntegrableOn P (Ioo 0 1) :=
    (((integrableOn_Ioo_rpow (by norm_num)).const_mul c₀).add
      ((integrableOn_Ioo_rpow (by norm_num)).const_mul c₁)).add
      ((integrableOn_Ioo_rpow (by norm_num)).const_mul c₂)
  have hG : IntegrableOn G (Ioo 0 1) := by
    refine Integrable.mono' ((integrableOn_Ioo_rpow (r := -(1 / 2)) (by norm_num)).const_mul r⁻¹)
      ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioo
      obtain ⟨h1, _⟩ := hw u hu
      have hwu : 0 < w u := (by positivity : (0 : ℝ) < r ^ 2).trans_le h1
      exact ((Real.continuousAt_rpow_const _ _ (Or.inl hu.1.ne')).mul
        ((Real.continuousAt_rpow_const _ _ (Or.inl hwu.ne')).comp
          (by fun_prop : Continuous w).continuousAt)).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun u hu => ?_)
      obtain ⟨h1, _⟩ := hw u hu
      have hwu : 0 < w u := (by positivity : (0 : ℝ) < r ^ 2).trans_le h1
      have hu0 : 0 ≤ u ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hu.1.le _
      rw [Real.norm_of_nonneg (mul_nonneg hu0 (Real.rpow_nonneg hwu.le _)), mul_comm r⁻¹]
      refine mul_le_mul_of_nonneg_left ?_ hu0
      rw [Real.rpow_neg hwu.le, ← Real.sqrt_eq_rpow]
      exact inv_anti₀ hr (hsqrt h1 (hw u hu).2).1
  -- the pointwise identity `G = P - u^{-1/2} E`
  set E : ℝ → ℝ := fun u => (Real.sqrt (w u) - a) ^ 3 *
    (3 * Real.sqrt (w u) ^ 2 + 9 * a * Real.sqrt (w u) + 8 * a ^ 2) / (8 * a ^ 5 * Real.sqrt (w u))
  have hGP : ∀ u ∈ Ioo (0 : ℝ) 1, P u - G u = u ^ (-(1 / 2 : ℝ)) * E u := by
    intro u hu
    obtain ⟨h1, h2⟩ := hw u hu
    have hwu : 0 < w u := (by positivity : (0 : ℝ) < r ^ 2).trans_le h1
    have hs : 0 < Real.sqrt (w u) := Real.sqrt_pos.mpr hwu
    have hT := inv_eq_taylor_add ha hs
    have hs2 : Real.sqrt (w u) ^ 2 - a ^ 2 = (u - 1 / 3) * D := by
      rw [Real.sq_sqrt hwu.le, haA]; simp only [w, A, D]; ring
    rw [hs2] at hT
    have hu12 : u ^ (1 / 2 : ℝ) = u ^ (-(1 / 2 : ℝ)) * u := by
      rw [← Real.rpow_add_one hu.1.ne']; norm_num
    have hu32 : u ^ (3 / 2 : ℝ) = u ^ (-(1 / 2 : ℝ)) * u ^ 2 := by
      rw [show (3 / 2 : ℝ) = -(1 / 2) + 2 by norm_num, Real.rpow_add hu.1, Real.rpow_two]
    simp only [P, G, E]
    rw [hu12, hu32, Real.rpow_neg hwu.le (1 / 2), ← Real.sqrt_eq_rpow, hT]
    simp only [c₀, c₁, c₂, p, q]
    ring
  have hE : ∀ u ∈ Ioo (0 : ℝ) 1, |E u| ≤ |D| ^ 3 * K := by
    intro u hu
    obtain ⟨h1, h2⟩ := hw u hu
    have hwu : 0 < w u := (by positivity : (0 : ℝ) < r ^ 2).trans_le h1
    obtain ⟨hrs, hsR⟩ := hsqrt h1 h2
    refine (abs_taylor_remainder_le hr hra hrs haR hsR).trans ?_
    rw [Real.sq_sqrt hwu.le, haA, show w u - A = (u - 1 / 3) * D by simp only [w, A, D]; ring,
      abs_mul]
    have : |u - 1 / 3| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    have hK : 0 ≤ K := by positivity
    gcongr
    calc |u - 1 / 3| * |D| ≤ 1 * |D| := by gcongr
      _ = |D| := one_mul _
  -- integrate
  have hint : ∫ u in Ioo (0 : ℝ) 1, G u =
      (∫ u in Ioo (0 : ℝ) 1, P u) - ∫ u in Ioo (0 : ℝ) 1, (P u - G u) := by
    rw [integral_sub hP hG]; ring
  have hPint : ∫ u in Ioo (0 : ℝ) 1, P u = 2 * (a⁻¹ + D ^ 2 / (30 * a ^ 5)) := by
    simp only [P]
    have i1 := (integrableOn_Ioo_rpow (r := -(1 / 2)) (by norm_num)).const_mul c₀
    have i2 := (integrableOn_Ioo_rpow (r := 1 / 2) (by norm_num)).const_mul c₁
    have i3 := (integrableOn_Ioo_rpow (r := 3 / 2) (by norm_num)).const_mul c₂
    have i12 : Integrable (fun u : ℝ => c₀ * u ^ (-(1 / 2 : ℝ)) + c₁ * u ^ (1 / 2 : ℝ))
        (volume.restrict (Ioo 0 1)) := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_Ioo_rpow (r := -(1 / 2)) (by norm_num), integral_Ioo_rpow (r := 1 / 2) (by norm_num),
      integral_Ioo_rpow (r := 3 / 2) (by norm_num)]
    simp only [c₀, c₁, c₂, p, q]
    field_simp
    ring
  have hEint : |∫ u in Ioo (0 : ℝ) 1, (P u - G u)| ≤ 2 * (|D| ^ 3 * K) := by
    have hbound : ∀ u ∈ Ioo (0 : ℝ) 1, ‖P u - G u‖ ≤ (|D| ^ 3 * K) * u ^ (-(1 / 2 : ℝ)) := by
      intro u hu
      rw [hGP u hu, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu.1 _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hE u hu) (Real.rpow_pos_of_pos hu.1 _).le
    have hgi : IntegrableOn (fun u : ℝ => (|D| ^ 3 * K) * u ^ (-(1 / 2 : ℝ))) (Ioo 0 1) :=
      (integrableOn_Ioo_rpow (by norm_num)).const_mul _
    have h := norm_integral_le_of_norm_le hgi
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall hbound))
    rw [integral_const_mul, integral_Ioo_rpow (by norm_num), Real.norm_eq_abs] at h
    refine h.trans (le_of_eq ?_)
    norm_num; ring
  have hA2 : A ^ 2 = a ^ 4 := by rw [← haA]; ring
  have htarget : a⁻¹ * (1 + D ^ 2 / (30 * A ^ 2)) = a⁻¹ + D ^ 2 / (30 * a ^ 5) := by
    rw [hA2]; field_simp
  rw [htarget, hint, hPint]
  calc |1 / 2 * (2 * (a⁻¹ + D ^ 2 / (30 * a ^ 5)) - ∫ u in Ioo (0 : ℝ) 1, (P u - G u)) -
        (a⁻¹ + D ^ 2 / (30 * a ^ 5))|
      = 1 / 2 * |∫ u in Ioo (0 : ℝ) 1, (P u - G u)| := by
        rw [show 1 / 2 * (2 * (a⁻¹ + D ^ 2 / (30 * a ^ 5)) - ∫ u in Ioo (0 : ℝ) 1, (P u - G u)) -
          (a⁻¹ + D ^ 2 / (30 * a ^ 5)) = -(1 / 2 * ∫ u in Ioo (0 : ℝ) 1, (P u - G u)) by ring,
          abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ 1 / 2 * (2 * (|D| ^ 3 * K)) := by gcongr
    _ = |D| ^ 3 * K := by ring

/-- A crude bound for `u³ + u²v + uv² + v³`. -/
theorem abs_cube_sum_le {u v B : ℝ} (hu : |u| ≤ B) (hv : |v| ≤ B) :
    |u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3| ≤ 4 * B ^ 3 := by
  have hB : 0 ≤ B := (abs_nonneg _).trans hu
  have h1 : |u ^ 3| ≤ B ^ 3 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hu 3
  have h2 : |u ^ 2 * v| ≤ B ^ 3 := by
    rw [abs_mul, abs_pow]
    calc |u| ^ 2 * |v| ≤ B ^ 2 * B := by gcongr
      _ = B ^ 3 := by ring
  have h3 : |u * v ^ 2| ≤ B ^ 3 := by
    rw [abs_mul, abs_pow]
    calc |u| * |v| ^ 2 ≤ B * B ^ 2 := by gcongr
      _ = B ^ 3 := by ring
  have h4 : |v ^ 3| ≤ B ^ 3 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hv 3
  have := abs_add_le (u ^ 3 + u ^ 2 * v + u * v ^ 2) (v ^ 3)
  have := abs_add_le (u ^ 3 + u ^ 2 * v) (u * v ^ 2)
  have := abs_add_le (u ^ 3) (u ^ 2 * v)
  linarith

/-- The decomposition of the Borchardt error into five small terms. -/
theorem borchardt_decomposition {σ a t D R : ℝ} (ha : a ≠ 0) (hsq : σ ^ 2 - a ^ 2 = -2 * t / 9) :
    σ * R - 1 - D ^ 2 * R ^ 4 / 180 =
      σ * (R - (a⁻¹ + D ^ 2 / (30 * a ^ 5))) +
        -(D ^ 2 * (R ^ 4 - (a⁻¹ + D ^ 2 / (30 * a ^ 5)) ^ 4) / 180) +
        -(σ - a) ^ 2 / (2 * a ^ 2) + (σ - a) / a * (D ^ 2 / (30 * a ^ 4)) +
        (D ^ 2 / (36 * a ^ 4) - t / (9 * a ^ 2)) +
        -(D ^ 2 * ((a⁻¹ + D ^ 2 / (30 * a ^ 5)) ^ 4 - (a⁻¹) ^ 4) / 180) := by
  rw [show t = -9 * (σ ^ 2 - a ^ 2) / 2 by linarith [hsq]]
  field_simp
  ring

/-- The bound `|σ - a| ≤ |D|²/(36 m³)` from `σ² - a² = -2t/9` and `t ≤ |D|²/(4m²)`. -/
theorem abs_sub_le_of_sq_sub {m σ a t D : ℝ} (hm : 0 < m) (hma : m ≤ a) (hσ : m ≤ σ)
    (ht0 : 0 ≤ t) (htD : t ≤ |D| ^ 2 / (4 * m ^ 2)) (hsq : σ ^ 2 - a ^ 2 = -2 * t / 9) :
    |σ - a| ≤ |D| ^ 2 / (36 * m ^ 3) := by
  have hs9 : 0 < 9 * (σ + a) := by linarith
  have hsa : σ - a = -2 * t / (9 * (σ + a)) := by
    rw [eq_div_iff hs9.ne']; linear_combination 9 * hsq
  rw [hsa, abs_div, abs_of_pos hs9, abs_of_nonpos (by linarith),
    div_le_div_iff₀ hs9 (by positivity)]
  have h1 : t * (2 * m) ≤ t * (σ + a) := mul_le_mul_of_nonneg_left (by linarith) ht0
  have h2 : t * (4 * m ^ 2) ≤ |D| ^ 2 := by rwa [le_div_iff₀ (by positivity)] at htD
  nlinarith [pow_pos hm 3]

/-- Bounds for the two terms of the decomposition that involve `σ - a`. -/
theorem abs_borchardt_T₁₂_le {m M σ a D : ℝ} (hm : 0 < m) (hma : m ≤ a) (hD : |D| ≤ M ^ 2)
    (h9 : |σ - a| ≤ |D| ^ 2 / (36 * m ^ 3)) :
    |-(σ - a) ^ 2 / (2 * a ^ 2)| + |(σ - a) / a * (D ^ 2 / (30 * a ^ 4))| ≤
      (M ^ 2 / (4 * m ^ 8) + M ^ 2 / (4 * m ^ 8)) * |D| ^ 3 := by
  have ha : 0 < a := hm.trans_le hma
  have hD0 : 0 ≤ |D| := abs_nonneg _
  have hD4 : |D| ^ 4 ≤ M ^ 2 * |D| ^ 3 := by
    calc |D| ^ 4 = |D| * |D| ^ 3 := by ring
      _ ≤ M ^ 2 * |D| ^ 3 := by gcongr
  have h1 : |-(σ - a) ^ 2 / (2 * a ^ 2)| ≤ |D| ^ 4 / (2592 * m ^ 8) := by
    rw [abs_div, abs_neg, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < 2 * a ^ 2)]
    calc |σ - a| ^ 2 / (2 * a ^ 2) ≤ (|D| ^ 2 / (36 * m ^ 3)) ^ 2 / (2 * m ^ 2) := by gcongr
      _ = |D| ^ 4 / (2592 * m ^ 8) := by field_simp; ring
  have h2 : |(σ - a) / a * (D ^ 2 / (30 * a ^ 4))| ≤ |D| ^ 4 / (1080 * m ^ 8) := by
    rw [abs_mul, abs_div, abs_div, abs_of_pos ha, abs_of_pos (by positivity : (0 : ℝ) < 30 * a ^ 4),
      abs_pow]
    calc |σ - a| / a * (|D| ^ 2 / (30 * a ^ 4))
        ≤ (|D| ^ 2 / (36 * m ^ 3)) / m * (|D| ^ 2 / (30 * m ^ 4)) := by gcongr
      _ = |D| ^ 4 / (1080 * m ^ 8) := by field_simp; ring
  have h3 : |D| ^ 4 / (2592 * m ^ 8) + |D| ^ 4 / (1080 * m ^ 8) ≤
      (M ^ 2 / (4 * m ^ 8) + M ^ 2 / (4 * m ^ 8)) * |D| ^ 3 := by
    have hm8 : 0 < m ^ 8 := by positivity
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
    have : (M ^ 2 / (4 * m ^ 8) + M ^ 2 / (4 * m ^ 8)) * |D| ^ 3 * (2592 * m ^ 8 * (1080 * m ^ 8)) =
        M ^ 2 * |D| ^ 3 * (1399680 * m ^ 8) := by field_simp; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hD4 (by positivity : (0 : ℝ) ≤ 3672 * m ^ 8),
      mul_nonneg (mul_nonneg (sq_nonneg M) (pow_nonneg hD0 3)) hm8.le]
  linarith

/-- `|D² (u⁴ - v⁴)/180| ≤ c |u - v| D²` when `|u|, |v| ≤ B`. -/
theorem abs_sq_mul_pow_four_sub_le {D u v B : ℝ} (hu : |u| ≤ B) (hv : |v| ≤ B) :
    |D ^ 2 * (u ^ 4 - v ^ 4) / 180| ≤ |D| ^ 2 * (|u - v| * (4 * B ^ 3)) / 180 := by
  rw [show u ^ 4 - v ^ 4 = (u - v) * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) by ring,
    abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 180), abs_pow]
  gcongr
  exact abs_cube_sum_le hu hv

/-- The abstract algebra behind (6.10-28). -/
theorem borchardt_algebra_core {m M K c₃ σ a t D R : ℝ} (hm : 0 < m) (hmM : m ≤ M) (hK : 0 ≤ K)
    (hma : m ≤ a) (hσ : m ≤ σ) (hσM : σ ≤ M) (ht0 : 0 ≤ t)
    (htD : t ≤ |D| ^ 2 / (4 * m ^ 2)) (hD : |D| ≤ M ^ 2) (hsq : σ ^ 2 - a ^ 2 = -2 * t / 9)
    (hT₃ : |D ^ 2 / (36 * a ^ 4) - t / (9 * a ^ 2)| ≤ c₃ * |D| ^ 3)
    (hR : |R - (a⁻¹ + D ^ 2 / (30 * a ^ 5))| ≤ K * |D| ^ 3) :
    |σ * R - 1 - D ^ 2 * R ^ 4 / 180| ≤
      (M * K + M ^ 4 * K * 4 * (1 / m + M ^ 4 / (30 * m ^ 5) + K * M ^ 6) ^ 3 / 180 +
        (M ^ 2 / (4 * m ^ 8) + M ^ 2 / (4 * m ^ 8)) + c₃ +
        M ^ 2 * 4 * (1 / m + M ^ 4 / (30 * m ^ 5) + K * M ^ 6) ^ 3 / (5400 * m ^ 5)) *
          |D| ^ 3 := by
  set B : ℝ := 1 / m + M ^ 4 / (30 * m ^ 5) + K * M ^ 6
  set r₀ := a⁻¹ + D ^ 2 / (30 * a ^ 5)
  have ha : 0 < a := hm.trans_le hma
  have hD0 : 0 ≤ |D| := abs_nonneg _
  have hDD : |D| ^ 2 ≤ M ^ 4 := by
    calc |D| ^ 2 ≤ (M ^ 2) ^ 2 := pow_le_pow_left₀ hD0 hD 2
      _ = M ^ 4 := by ring
  have hD3 : |D| ^ 3 ≤ M ^ 6 := by
    calc |D| ^ 3 ≤ (M ^ 2) ^ 3 := pow_le_pow_left₀ hD0 hD 3
      _ = M ^ 6 := by ring
  have hr₀ : |r₀| ≤ 1 / m + M ^ 4 / (30 * m ^ 5) := by
    simp only [r₀]
    rw [abs_of_nonneg (by positivity)]
    gcongr
    · rw [one_div]; exact inv_anti₀ hm hma
    · rw [← sq_abs]; exact hDD
  have hKM : 0 ≤ K * M ^ 6 := by positivity
  have hM4 : 0 ≤ M ^ 4 / (30 * m ^ 5) := by positivity
  have hrB : |r₀| ≤ B := by simp only [B]; linarith
  have hRB : |R| ≤ B := by
    have h := abs_add_le r₀ (R - r₀)
    rw [add_sub_cancel] at h
    have : |R - r₀| ≤ K * M ^ 6 := hR.trans (mul_le_mul_of_nonneg_left hD3 hK)
    simp only [B]; linarith
  have hainvB : |a⁻¹| ≤ B := by
    rw [abs_of_pos (inv_pos.mpr ha)]
    have : a⁻¹ ≤ 1 / m := by rw [one_div]; exact inv_anti₀ hm hma
    simp only [B]; linarith
  have h9 := abs_sub_le_of_sq_sub hm hma hσ ht0 htD hsq
  have hT₁₂ := abs_borchardt_T₁₂_le hm hma hD h9
  have hE0 : |σ * (R - r₀)| ≤ M * K * |D| ^ 3 := by
    rw [abs_mul, abs_of_pos (hm.trans_le hσ), mul_assoc]
    exact mul_le_mul hσM hR (abs_nonneg _) (hm.le.trans hmM)
  have hE1 : |-(D ^ 2 * (R ^ 4 - r₀ ^ 4) / 180)| ≤ M ^ 4 * K * 4 * B ^ 3 / 180 * |D| ^ 3 := by
    rw [abs_neg]
    refine (abs_sq_mul_pow_four_sub_le hRB hrB).trans ?_
    calc |D| ^ 2 * (|R - r₀| * (4 * B ^ 3)) / 180
        ≤ M ^ 4 * (K * |D| ^ 3 * (4 * B ^ 3)) / 180 := by gcongr
      _ = M ^ 4 * K * 4 * B ^ 3 / 180 * |D| ^ 3 := by ring
  have hT₄ : |-(D ^ 2 * (r₀ ^ 4 - (a⁻¹) ^ 4) / 180)| ≤
      M ^ 2 * 4 * B ^ 3 / (5400 * m ^ 5) * |D| ^ 3 := by
    rw [abs_neg]
    refine (abs_sq_mul_pow_four_sub_le hrB hainvB).trans ?_
    have hdiff : |r₀ - a⁻¹| ≤ |D| ^ 2 / (30 * m ^ 5) := by
      simp only [r₀, add_sub_cancel_left]
      rw [abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < 30 * a ^ 5)]
      gcongr
    have hD4 : |D| ^ 4 ≤ M ^ 2 * |D| ^ 3 := by
      calc |D| ^ 4 = |D| * |D| ^ 3 := by ring
        _ ≤ M ^ 2 * |D| ^ 3 := by gcongr
    calc |D| ^ 2 * (|r₀ - a⁻¹| * (4 * B ^ 3)) / 180
        ≤ |D| ^ 2 * (|D| ^ 2 / (30 * m ^ 5) * (4 * B ^ 3)) / 180 := by gcongr
      _ = |D| ^ 4 * (4 * B ^ 3) / (5400 * m ^ 5) := by field_simp; ring
      _ ≤ M ^ 2 * |D| ^ 3 * (4 * B ^ 3) / (5400 * m ^ 5) := by gcongr
      _ = M ^ 2 * 4 * B ^ 3 / (5400 * m ^ 5) * |D| ^ 3 := by ring
  rw [borchardt_decomposition ha.ne' hsq]
  set e₀ := σ * (R - r₀)
  set e₁ := -(D ^ 2 * (R ^ 4 - r₀ ^ 4) / 180)
  set e₂ := -(σ - a) ^ 2 / (2 * a ^ 2)
  set e₃ := (σ - a) / a * (D ^ 2 / (30 * a ^ 4))
  set e₄ := D ^ 2 / (36 * a ^ 4) - t / (9 * a ^ 2)
  set e₅ := -(D ^ 2 * (r₀ ^ 4 - (a⁻¹) ^ 4) / 180)
  have h1 := abs_add_le (e₀ + e₁ + e₂ + e₃ + e₄) e₅
  have h2 := abs_add_le (e₀ + e₁ + e₂ + e₃) e₄
  have h3 := abs_add_le (e₀ + e₁ + e₂) e₃
  have h4 := abs_add_le (e₀ + e₁) e₂
  have h5 := abs_add_le e₀ e₁
  have : (M * K + M ^ 4 * K * 4 * B ^ 3 / 180 + (M ^ 2 / (4 * m ^ 8) + M ^ 2 / (4 * m ^ 8)) + c₃ +
      M ^ 2 * 4 * B ^ 3 / (5400 * m ^ 5)) * |D| ^ 3 =
      M * K * |D| ^ 3 + M ^ 4 * K * 4 * B ^ 3 / 180 * |D| ^ 3 +
        (M ^ 2 / (4 * m ^ 8) + M ^ 2 / (4 * m ^ 8)) * |D| ^ 3 + c₃ * |D| ^ 3 +
          M ^ 2 * 4 * B ^ 3 / (5400 * m ^ 5) * |D| ^ 3 := by ring
  rw [this]
  linarith

/-- The term `D²/(36 a⁴) - t/(9 a²)` of the decomposition, with `a² = (x² + 2y²)/3`,
`t = (x - y)²`, is `O(|D|³)`. -/
theorem abs_borchardt_T₃_le {m M x y a : ℝ} (hm : 0 < m) (hx : m ≤ x) (hx' : x ≤ M) (hy : m ≤ y)
    (hy' : y ≤ M) (ha : a ^ 2 = (x ^ 2 + 2 * y ^ 2) / 3) :
    |(x ^ 2 - y ^ 2) ^ 2 / (36 * a ^ 4) - (x - y) ^ 2 / (9 * a ^ 2)| ≤
      M / (144 * m ^ 7) * |x ^ 2 - y ^ 2| ^ 3 := by
  have hxy : 2 * m ≤ x + y := by linarith
  have hxy0 : 0 < x + y := by linarith
  have hA : m ^ 2 ≤ a ^ 2 := by rw [ha]; nlinarith
  have ha2 : 0 < a ^ 2 := (by positivity : (0 : ℝ) < m ^ 2).trans_le hA
  have hid : (x ^ 2 - y ^ 2) ^ 2 / (36 * a ^ 4) - (x - y) ^ 2 / (9 * a ^ 2) =
      -((x ^ 2 - y ^ 2) ^ 2 * (x ^ 2 - y ^ 2) * (x - 5 * y)) /
        (108 * (a ^ 2) ^ 2 * (x + y) ^ 3) := by
    have h4 : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [h4]
    have hxy' : x - y = (x ^ 2 - y ^ 2) / (x + y) := by field_simp; ring
    rw [hxy']
    rw [ha]
    field_simp
    ring
  rw [hid, abs_div, abs_neg, abs_mul, abs_mul, abs_pow,
    abs_of_pos (by positivity : (0 : ℝ) < 108 * (a ^ 2) ^ 2 * (x + y) ^ 3)]
  have h5 : |x - 5 * y| ≤ 6 * M := by rw [abs_le]; constructor <;> linarith
  set D := |x ^ 2 - y ^ 2|
  have hD : 0 ≤ D := abs_nonneg _
  calc D ^ 2 * D * |x - 5 * y| / (108 * (a ^ 2) ^ 2 * (x + y) ^ 3)
      ≤ D ^ 2 * D * (6 * M) / (108 * (m ^ 2) ^ 2 * (2 * m) ^ 3) := by
        have : 0 ≤ M := hm.le.trans (hx.trans hx')
        gcongr
    _ = M / (144 * m ^ 7) * D ^ 3 := by field_simp; ring

/-- The expansion (6.10-28) in one step of Borchardt's algorithm: for `x, y ∈ [m, M]`, with
`R = R_C(x², y²)`, `σ = (x + 2y)/3` and `D = x² - y²`,
`|σ R - 1 - D² R⁴/180| ≤ C |D|³`. -/
theorem exists_borchardt_step_bound {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    ∃ C : ℝ, ∀ x y : ℝ, m ≤ x → x ≤ M → m ≤ y → y ≤ M →
      |(x + 2 * y) / 3 * (carlsonRC ((x : ℂ) ^ 2) ((y : ℂ) ^ 2)).re - 1 -
        (x ^ 2 - y ^ 2) ^ 2 * (carlsonRC ((x : ℂ) ^ 2) ((y : ℂ) ^ 2)).re ^ 4 / 180| ≤
        C * |x ^ 2 - y ^ 2| ^ 3 := by
  set K := 20 * M ^ 2 / (64 * m ^ 9)
  have hK : 0 ≤ K := by positivity
  refine ⟨_, fun x y hx hx' hy hy' => borchardt_algebra_core
    (a := Real.sqrt ((x ^ 2 + 2 * y ^ 2) / 3))
    (t := (x - y) ^ 2) (c₃ := M / (144 * m ^ 7)) hm hmM hK ?_ ?_ ?_ (sq_nonneg _) ?_ ?_ ?_ ?_ ?_⟩
  · exact Real.le_sqrt_of_sq_le (by nlinarith)
  · linarith
  · linarith
  · -- `t ≤ |D|²/(4 m²)`
    rw [sq_abs, le_div_iff₀ (by positivity)]
    have : (x ^ 2 - y ^ 2) ^ 2 = (x - y) ^ 2 * (x + y) ^ 2 := by ring
    rw [this]
    have hxy : 4 * m ^ 2 ≤ (x + y) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hxy (sq_nonneg _)
  · rw [abs_le]; constructor <;> nlinarith
  · rw [Real.sq_sqrt (by positivity)]; ring
  · exact abs_borchardt_T₃_le hm hx hx' hy hy' (Real.sq_sqrt (by positivity))
  · have hx0 : 0 < x := hm.trans_le hx
    have hy0 : 0 < y := hm.trans_le hy
    have h := abs_carlsonRC_sub_le (X := x ^ 2) (Y := y ^ 2) hm hmM (by nlinarith) (by nlinarith)
      (by nlinarith) (by nlinarith)
    push_cast at h
    have ha : 0 < Real.sqrt ((x ^ 2 + 2 * y ^ 2) / 3) := Real.sqrt_pos.mpr (by positivity)
    have hA := Real.sq_sqrt (show 0 ≤ (x ^ 2 + 2 * y ^ 2) / 3 by positivity)
    generalize Real.sqrt ((x ^ 2 + 2 * y ^ 2) / 3) = a at h ha hA ⊢
    rw [show a⁻¹ + (x ^ 2 - y ^ 2) ^ 2 / (30 * a ^ 5) =
      a⁻¹ * (1 + (x ^ 2 - y ^ 2) ^ 2 / (30 * ((x ^ 2 + 2 * y ^ 2) / 3) ^ 2)) by
        rw [← hA]; field_simp]
    rw [mul_comm K]
    exact h

/-- Borchardt's sequences stay below the larger starting value. -/
theorem borchardtSeq_le_max {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    (borchardtSeq x y n).1 ≤ max x y ∧ (borchardtSeq x y n).2 ≤ max x y := by
  induction n with
  | zero => simp [borchardtSeq]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hb := borchardtSeq_bounds hx hy n
    have hm : 0 < min x y := lt_min hx hy
    rw [borchardtSeq_succ]
    have hw : ((borchardtSeq x y n).1 + (borchardtSeq x y n).2) / 2 ≤ max x y := by linarith
    refine ⟨hw, ?_⟩
    rw [Real.sqrt_le_left (by positivity)]
    have hv : 0 ≤ (borchardtSeq x y n).2 := by linarith [hb.2.1]
    have hw0 : 0 ≤ ((borchardtSeq x y n).1 + (borchardtSeq x y n).2) / 2 := by
      linarith [hb.1, hb.2.1]
    calc ((borchardtSeq x y n).1 + (borchardtSeq x y n).2) / 2 * (borchardtSeq x y n).2
        ≤ max x y * max x y := mul_le_mul hw h2 hv (by positivity)
      _ = max x y ^ 2 := by ring

/-- Carlson's (6.10-25): `xₙ² - yₙ² = 4⁻ⁿ (x₀² - y₀²)`. -/
theorem borchardtSeq_sq_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    (borchardtSeq x y n).1 ^ 2 - (borchardtSeq x y n).2 ^ 2 = (x ^ 2 - y ^ 2) / 4 ^ n := by
  induction n with
  | zero => simp [borchardtSeq]
  | succ n ih =>
    have hb := borchardtSeq_bounds hx hy n
    have hm : 0 < min x y := lt_min hx hy
    rw [borchardtSeq_succ]
    simp only
    rw [Real.sq_sqrt (by nlinarith [hb.1, hb.2.1]), show (4 : ℝ) ^ (n + 1) = 4 ^ n * 4 from
      pow_succ 4 n, ← div_div, ← ih]
    ring

/-- The invariance of `R_C(xₙ², yₙ²)` along Borchardt's sequences. -/
theorem carlsonRC_borchardtSeq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    carlsonRC (((borchardtSeq x y n).1 : ℂ) ^ 2) (((borchardtSeq x y n).2 : ℂ) ^ 2) =
      carlsonRC ((x : ℂ) ^ 2) ((y : ℂ) ^ 2) := by
  have hb := borchardtSeq_bounds hx hy
  have hm : 0 < min x y := lt_min hx hy
  have hre : ∀ w : ℝ, 0 < w → 0 < (w : ℂ).re := fun w hw => by simpa using hw
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih, carlsonRC_sq_eq _ _ (hre _ (hm.trans_le (hb n).1)) (hre _ (hm.trans_le (hb n).2.1)),
      borchardtSeq_succ]
    congr 1
    · push_cast; ring
    · rw [← ofReal_pow, Real.sq_sqrt (by nlinarith [(hb n).1, (hb n).2.1])]
      push_cast; ring

/-- Carlson's accelerated approximation (6.10-27), `σₙ = (xₙ + 2 yₙ)/3`. -/
def borchardtSigma (x y : ℝ) (n : ℕ) : ℝ :=
  ((borchardtSeq x y n).1 + 2 * (borchardtSeq x y n).2) / 3

/-- **Carlson's (6.10-28)**: for positive `x₀, y₀` with Borchardt limit `L`,
`σₙ/L = 1 + 4^{-2n-1} (x₀² - y₀²)²/(45 L⁴) + O(4^{-3n})`. -/
theorem exists_borchardtSigma_expansion {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ∃ L : ℝ, 0 < L ∧ carlsonRC ((x : ℂ) ^ 2) ((y : ℂ) ^ 2) = ((L : ℂ))⁻¹ ∧
      ∃ C : ℝ, ∀ n : ℕ, |borchardtSigma x y n / L - 1 -
        (x ^ 2 - y ^ 2) ^ 2 / (45 * 4 ^ (2 * n + 1) * L ^ 4)| ≤ C / 64 ^ n := by
  obtain ⟨L, hL, -, -, hRC⟩ := exists_borchardt_limit hx hy
  have hm : 0 < min x y := lt_min hx hy
  obtain ⟨C₀, hC₀⟩ := exists_borchardt_step_bound hm (min_le_max)
  refine ⟨L, hL, hRC, C₀ * |x ^ 2 - y ^ 2| ^ 3, fun n => ?_⟩
  have hb := borchardtSeq_bounds hx hy n
  have hM := borchardtSeq_le_max hx hy n
  have h := hC₀ _ _ hb.1 hM.1 hb.2.1 hM.2
  rw [carlsonRC_borchardtSeq hx hy n, hRC, borchardtSeq_sq_sub hx hy n] at h
  simp only [← ofReal_inv, ofReal_re] at h
  have h4 : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hkey : borchardtSigma x y n / L - 1 - (x ^ 2 - y ^ 2) ^ 2 / (45 * 4 ^ (2 * n + 1) * L ^ 4) =
      ((borchardtSeq x y n).1 + 2 * (borchardtSeq x y n).2) / 3 * L⁻¹ - 1 -
        ((x ^ 2 - y ^ 2) / 4 ^ n) ^ 2 * L⁻¹ ^ 4 / 180 := by
    unfold borchardtSigma
    rw [show (4 : ℝ) ^ (2 * n + 1) = (4 ^ n) ^ 2 * 4 by ring]
    field_simp
    ring
  rw [hkey]
  refine h.trans (le_of_eq ?_)
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ n), div_pow, ← pow_mul,
    show (64 : ℝ) ^ n = (4 ^ n) ^ 3 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  ring

/-- **Carlson's (6.10-29)**: the extrapolation `σₙ₊₁ + (σₙ₊₁ - σₙ)/15` approximates the Borchardt
limit `L` with error `O(64⁻ⁿ)`. -/
theorem exists_borchardtSigma_extrapolation {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ∃ L : ℝ, 0 < L ∧ carlsonRC ((x : ℂ) ^ 2) ((y : ℂ) ^ 2) = ((L : ℂ))⁻¹ ∧
      ∃ C : ℝ, ∀ n : ℕ, |borchardtSigma x y (n + 1) +
        (borchardtSigma x y (n + 1) - borchardtSigma x y n) / 15 - L| ≤ C / 64 ^ n := by
  obtain ⟨L, hL, hRC, C, hC⟩ := exists_borchardtSigma_expansion hx hy
  refine ⟨L, hL, hRC, L * (16 * C / 64 / 15 + C / 15), fun n => ?_⟩
  set c := (x ^ 2 - y ^ 2) ^ 2 / (45 * 4 * L ^ 4)
  set e : ℕ → ℝ := fun k => borchardtSigma x y k / L - 1 - c / 16 ^ k
  have he : ∀ k, |e k| ≤ C / 64 ^ k := fun k => by
    have := hC k
    convert this using 3
    simp only [c]
    rw [show (4 : ℝ) ^ (2 * k + 1) = 16 ^ k * 4 by rw [pow_succ, pow_mul]; norm_num]
    field_simp
  have hσ : ∀ k, borchardtSigma x y k = L * (1 + c / 16 ^ k + e k) := fun k => by
    simp only [e]; field_simp; ring
  rw [hσ, hσ, show L * (1 + c / 16 ^ (n + 1) + e (n + 1)) +
      (L * (1 + c / 16 ^ (n + 1) + e (n + 1)) - L * (1 + c / 16 ^ n + e n)) / 15 - L =
      L * (16 / 15 * e (n + 1) - e n / 15) by rw [pow_succ]; field_simp; ring]
  rw [abs_mul, abs_of_pos hL, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hL.le
  have h1 := he (n + 1)
  have h2 := he n
  rw [pow_succ] at h1
  calc |16 / 15 * e (n + 1) - e n / 15| ≤ 16 / 15 * |e (n + 1)| + |e n| / 15 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_div (e n), abs_of_pos (by norm_num : (0 : ℝ) < 16 / 15),
          abs_of_pos (by norm_num : (0 : ℝ) < 15)]
    _ ≤ 16 / 15 * (C / (64 ^ n * 64)) + C / 64 ^ n / 15 := by gcongr
    _ = (16 * C / 64 / 15 + C / 15) / 64 ^ n := by field_simp

end Carlson.TwoVariable
