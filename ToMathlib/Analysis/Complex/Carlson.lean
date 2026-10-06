/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Carlson's theorem

**Carlson's theorem** (F. Carlson, 1914): a function holomorphic on the closed right half-plane,
of exponential type there and of type less than `π` on the imaginary axis, that vanishes at the
natural numbers vanishes identically. The constant `π` is sharp, as `sin (π z)` shows.

## Proof

The quotient `G = f / sin (π z)` (`sinPiQuot`, with the removable singularities at the integers
filled in through `dslope`) is holomorphic. It is of exponential type: off the `1/4`-discs around
the integers `‖sin (π z)‖ ≥ 1/4` (`quarter_le_norm_sin_pi_mul`), on the discs around positive
integers the maximum modulus principle applies, and near `0` compactness. On the imaginary axis
`‖sin (π i y)‖ ≥ e^(π |y|) / 4`, so `G` decays like `e^((c - π) |y|)`. The damping factor
`e^(-α (z + 1) log (z + 1))` (`carlsonDamping`) with `α = 2 (π - c) / π` grows at most like
`e^(α π |y| / 2)` on the imaginary axis and decays superexponentially on the positive real axis.
The product is bounded on the imaginary axis, of exponential type, and superexponentially
decaying on the real axis, so it vanishes by the Phragmén–Lindelöf principle
(`PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay`).

## Main results

* `Complex.eqOn_zero_of_natCast_eq_zero`: Carlson's theorem.
* `Complex.eqOn_zero_of_natCast_eq_zero_pi`, `Complex.eqOn_of_natCast_eq_pi`: Carlson's theorem
  in several variables, by induction on the coordinates, and uniqueness of continuations of
  data on `ℕ^ι`.
* `Complex.quarter_le_norm_sin_pi_mul`, `Complex.exp_div_four_le_norm_sin_pi_mul_I`: lower bounds
  for `sin (π z)`.
* `Complex.sinPiQuot`: the quotient `f / sin (π z)` and its regularity.

## References

* F. Carlson, *Sur une classe de séries de Taylor*, thesis, Uppsala, 1914.
* E. C. Titchmarsh, *The Theory of Functions*, 2nd ed., Oxford, 1939, §5.81.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics Metric
open scoped Topology Real

namespace Complex

/-- The squared norm of `sin (x + y i)` is `sin² x + sinh² y`. -/
theorem norm_sin_add_mul_I_sq (x y : ℝ) :
    ‖sin (x + y * I)‖ ^ 2 = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  rw [sin_add_mul_I, ← ofReal_sin, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sinh, Complex.sq_norm,
    normSq_apply]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, add_im, mul_im]
  nlinarith [Real.sin_sq_add_cos_sq x, Real.cosh_sq y]

/-- Away from the integers, `sin (π z)` is bounded below: if `z` has distance at least `1/4`
from every integer, then `1/4 ≤ ‖sin (π z)‖`. -/
theorem quarter_le_norm_sin_pi_mul {z : ℂ} (hz : ∀ n : ℤ, 1 / 4 ≤ ‖z - n‖) :
    1 / 4 ≤ ‖sin (π * z)‖ := by
  set x := z.re
  set y := z.im
  have hzxy : π * z = ((π * x : ℝ) : ℂ) + ((π * y : ℝ) : ℂ) * I := by
    conv_lhs => rw [← re_add_im z]
    push_cast; ring
  have hsq := norm_sin_add_mul_I_sq (π * x) (π * y)
  rw [← hzxy] at hsq
  have key : 1 / 16 ≤ Real.sin (π * x) ^ 2 + Real.sinh (π * y) ^ 2 := by
    by_cases hy : 1 / 8 ≤ |y|
    · have h1 : π / 8 ≤ |π * y| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [Real.pi_pos]
      have h2 : |π * y| ≤ |Real.sinh (π * y)| := by
        rw [Real.abs_sinh]
        exact Real.self_le_sinh_iff.mpr (abs_nonneg _)
      have h3 : 1 / 4 ≤ |Real.sinh (π * y)| := by linarith [Real.pi_gt_three]
      nlinarith [sq_abs (Real.sinh (π * y)), sq_nonneg (Real.sin (π * x))]
    · push Not at hy
      set r := round x
      set t := x - r
      have ht : |t| ≤ 1 / 2 := abs_sub_round x
      have hdist := hz r
      have hzr : ‖z - r‖ ^ 2 = t ^ 2 + y ^ 2 := by
        rw [Complex.sq_norm, normSq_apply]; simp [t, x, y]; ring
      have ht2 : 3 / 64 ≤ t ^ 2 := by
        nlinarith [sq_abs y, abs_nonneg y, norm_nonneg (z - r)]
      have ht5 : 1 / 5 ≤ |t| := by nlinarith [sq_abs t, abs_nonneg t]
      have hsin : |Real.sin (π * x)| = Real.sin (π * |t|) := by
        have : π * x = π * t + r * π := by simp only [t]; ring
        rw [this, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
        rcases le_total 0 t with h | h
        · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
            (by positivity) (by nlinarith [Real.pi_pos, abs_of_nonneg h]))]
        · have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := -(π * t))
            (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos, abs_of_nonpos h])
          rw [Real.sin_neg] at hs
          rw [abs_of_nonpos h, mul_neg, Real.sin_neg, abs_of_nonpos (by linarith)]
      have hj := Real.mul_le_sin (x := π * |t|) (by positivity)
        (by nlinarith [Real.pi_pos])
      have h25 : 2 / 5 ≤ |Real.sin (π * x)| := by
        rw [hsin]
        calc (2 : ℝ) / 5 ≤ 2 / π * (π * |t|) := by
              rw [← mul_assoc, div_mul_cancel₀ _ Real.pi_ne_zero]; linarith
          _ ≤ _ := hj
      nlinarith [sq_abs (Real.sin (π * x)), sq_nonneg (Real.sinh (π * y))]
  nlinarith [norm_nonneg (sin (π * z))]

/-- On the imaginary axis, `‖sin (π i y)‖ ≥ e^(π |y|) / 4` for `|y| ≥ 1/4`. -/
theorem exp_div_four_le_norm_sin_pi_mul_I {y : ℝ} (hy : 1 / 4 ≤ |y|) :
    Real.exp (π * |y|) / 4 ≤ ‖sin (π * (y * I))‖ := by
  have hsq := norm_sin_add_mul_I_sq 0 (π * y)
  rw [show ((0 : ℝ) : ℂ) + ((π * y : ℝ) : ℂ) * I = π * (y * I) by push_cast; ring,
    Real.sin_zero] at hsq
  have hsh : Real.exp (π * |y|) / 4 ≤ |Real.sinh (π * y)| := by
    rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos, Real.sinh_eq]
    set u := π * |y|
    have hu : 1 / 2 ≤ u := by
      simp only [u]; nlinarith [Real.pi_gt_three]
    have h2 : 2 ≤ Real.exp (2 * u) := by
      linarith [Real.add_one_le_exp (2 * u)]
    have : Real.exp (-u) * Real.exp (2 * u) = Real.exp u := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (-u), Real.exp_pos u]
  have h0 : 0 ≤ Real.exp (π * |y|) / 4 := by positivity
  nlinarith [sq_abs (Real.sinh (π * y)), norm_nonneg (sin (π * (y * I)))]

/-- The zeros of `sin (π z)` are the integers. -/
theorem sin_pi_mul_eq_zero_iff {z : ℂ} : sin (π * z) = 0 ↔ ∃ n : ℤ, z = n := by
  rw [sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, mul_left_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) ?_⟩
    rw [hk]; ring
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

/-- `sin (π z)` has no zeros at distance in `(0, 1)` from an integer. -/
theorem sin_pi_mul_ne_zero_of_norm_sub_lt_one {z : ℂ} {n : ℤ} (hz : z ≠ n)
    (h1 : ‖z - n‖ < 1) : sin (π * z) ≠ 0 := by
  rintro h
  obtain ⟨m, rfl⟩ := sin_pi_mul_eq_zero_iff.mp h
  have hmn : m ≠ n := fun h => hz (by rw [h])
  have : (1 : ℝ) ≤ ‖((m : ℂ) - n)‖ := by
    rw [← Int.cast_sub, norm_intCast]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
  linarith

/-- The quotient `f z / sin (π z)`, with the value `f' z / (π cos (π z))` at the integers. When
`f` vanishes at an integer and is differentiable there, the singularity is removable. -/
def sinPiQuot (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if sin (π * z) = 0 then deriv f z / (π * cos (π * z)) else f z / sin (π * z)

/-- The quotient away from the integers. -/
theorem sinPiQuot_of_ne {f : ℂ → ℂ} {z : ℂ} (hz : sin (π * z) ≠ 0) :
    sinPiQuot f z = f z / sin (π * z) := by simp [sinPiQuot, hz]

/-- The slope of `sin (π w)` at an integer is nonzero: it is `π cos (π n) = ± π`. -/
theorem dslope_sin_pi_mul_intCast_ne_zero (n : ℤ) :
    dslope (fun w : ℂ => sin (π * w)) n n ≠ 0 := by
  rw [dslope_same]
  have hder : deriv (fun w : ℂ => sin (π * w)) n = π * cos (π * n) := by
    simp [mul_comm]
  rw [hder]
  refine mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) ?_
  rw [show (π : ℂ) * n = ((n * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos, Real.cos_int_mul_pi]
  exact_mod_cast zpow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)

/-- Near an integer zero of `f`, the quotient is a quotient of slopes. -/
theorem sinPiQuot_eventuallyEq_dslope {f : ℂ → ℂ} {n : ℤ} (hn : f n = 0) :
    sinPiQuot f =ᶠ[𝓝 (n : ℂ)]
      fun w => dslope f n w / dslope (fun w => sin (π * w)) n w := by
  have hball : ball (n : ℂ) 1 ∈ 𝓝 (n : ℂ) := ball_mem_nhds _ one_pos
  filter_upwards [hball] with w hw
  by_cases hwn : w = n
  · subst hwn
    have hsin : sin (π * (n : ℂ)) = 0 := sin_pi_mul_eq_zero_iff.mpr ⟨n, rfl⟩
    have hder : deriv (fun w : ℂ => sin (π * w)) n = π * cos (π * n) := by
      simp [mul_comm]
    simp only [sinPiQuot, hsin, ite_true, dslope_same, hder]
  · have hs := sin_pi_mul_ne_zero_of_norm_sub_lt_one hwn (by simpa [dist_eq_norm] using hw)
    have hsub : w - n ≠ 0 := sub_ne_zero.mpr hwn
    have hsn : sin (π * (n : ℂ)) = 0 := sin_pi_mul_eq_zero_iff.mpr ⟨n, rfl⟩
    rw [sinPiQuot_of_ne hs, dslope_of_ne _ hwn, dslope_of_ne _ hwn, slope_def_field,
      slope_def_field, hn, hsn]
    field_simp
    ring

/-- The quotient is continuous at an integer zero of `f` where `f` is differentiable. -/
theorem continuousAt_sinPiQuot_intCast {f : ℂ → ℂ} {n : ℤ} (hn : f n = 0)
    (hf : DifferentiableAt ℂ f n) : ContinuousAt (sinPiQuot f) n := by
  refine ContinuousAt.congr ?_ (sinPiQuot_eventuallyEq_dslope hn).symm
  have hs : DifferentiableAt ℂ (fun w : ℂ => sin (π * w)) n := by fun_prop
  exact (continuousAt_dslope_same.mpr hf).div (continuousAt_dslope_same.mpr hs)
    (dslope_sin_pi_mul_intCast_ne_zero n)

/-- The quotient is differentiable at an integer zero of `f` near which `f` is differentiable. -/
theorem differentiableAt_sinPiQuot_intCast {f : ℂ → ℂ} {n : ℤ} (hn : f n = 0) {U : Set ℂ}
    (hU : U ∈ 𝓝 (n : ℂ)) (hf : DifferentiableOn ℂ f U) :
    DifferentiableAt ℂ (sinPiQuot f) n := by
  refine DifferentiableAt.congr_of_eventuallyEq ?_ (sinPiQuot_eventuallyEq_dslope hn)
  have h1 := ((differentiableOn_dslope hU).mpr hf).differentiableAt hU
  have h2 := ((differentiableOn_dslope hU).mpr
    (fun w _ => (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => sin (π * w)) w)
      |>.differentiableWithinAt)).differentiableAt hU
  exact h1.div h2 (dslope_sin_pi_mul_intCast_ne_zero n)

/-- Away from the integers the quotient is continuous where `f` is. -/
theorem continuousAt_sinPiQuot_of_ne {f : ℂ → ℂ} {z : ℂ} (hz : sin (π * z) ≠ 0)
    (hf : ContinuousAt f z) : ContinuousAt (sinPiQuot f) z := by
  have hev : ∀ᶠ w in 𝓝 z, sin (π * w) ≠ 0 :=
    (by fun_prop : Continuous fun w : ℂ => sin (π * w)).continuousAt.eventually_ne hz
  refine ContinuousAt.congr (hf.div (g := fun w => sin (π * w)) (by fun_prop) hz) ?_
  filter_upwards [hev] with w hw
  exact (sinPiQuot_of_ne hw).symm

/-- Away from the integers the quotient is differentiable where `f` is. -/
theorem differentiableAt_sinPiQuot_of_ne {f : ℂ → ℂ} {z : ℂ} (hz : sin (π * z) ≠ 0)
    (hf : DifferentiableAt ℂ f z) : DifferentiableAt ℂ (sinPiQuot f) z := by
  have hev : ∀ᶠ w in 𝓝 z, sin (π * w) ≠ 0 :=
    (by fun_prop : Continuous fun w : ℂ => sin (π * w)).continuousAt.eventually_ne hz
  refine DifferentiableAt.congr_of_eventuallyEq
    (hf.div (d := fun w => sin (π * w)) (by fun_prop) hz) ?_
  filter_upwards [hev] with w hw
  exact sinPiQuot_of_ne hw

/-- The damping factor `e^(-α (z + 1) log (z + 1))` of the proof of Carlson's theorem: it grows at
most like `e^(α π |Im z| / 2)` in the closed right half-plane and decays superexponentially on
the positive real axis. -/
def carlsonDamping (α : ℝ) (z : ℂ) : ℂ := exp (-(α : ℂ) * ((z + 1) * log (z + 1)))

/-- The norm of the damping factor. -/
theorem norm_carlsonDamping (α : ℝ) (z : ℂ) :
    ‖carlsonDamping α z‖ =
      Real.exp (-α * ((z + 1).re * Real.log ‖z + 1‖ - (z + 1).im * arg (z + 1))) := by
  rw [carlsonDamping, norm_exp]
  congr 1
  simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, log_re, log_im, neg_zero, zero_mul,
    sub_zero]

/-- The damping factor grows at most like `e^(α π |Im z| / 2)` in the closed right half-plane. -/
theorem norm_carlsonDamping_le {α : ℝ} (hα : 0 ≤ α) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖carlsonDamping α z‖ ≤ Real.exp (α * (π / 2) * |z.im|) := by
  rw [norm_carlsonDamping]
  refine Real.exp_le_exp.mpr ?_
  have hre : 1 ≤ (z + 1).re := by simp; linarith
  have hlog : 0 ≤ Real.log ‖z + 1‖ :=
    Real.log_nonneg (hre.trans ((le_abs_self _).trans (abs_re_le_norm _)))
  have harg : |arg (z + 1)| ≤ π / 2 := abs_arg_le_pi_div_two_iff.mpr (by linarith)
  have him : (z + 1).im * arg (z + 1) ≤ |z.im| * (π / 2) := by
    have : (z + 1).im = z.im := by simp
    rw [this]
    calc z.im * arg (z + 1) ≤ |z.im * arg (z + 1)| := le_abs_self _
      _ = |z.im| * |arg (z + 1)| := abs_mul _ _
      _ ≤ |z.im| * (π / 2) := mul_le_mul_of_nonneg_left harg (abs_nonneg _)
  nlinarith [mul_nonneg (zero_le_one.trans hre) hlog]

/-- On the positive real axis the damping factor is `e^(-α (x + 1) log (x + 1))`. -/
theorem norm_carlsonDamping_ofReal (α : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ‖carlsonDamping α x‖ = Real.exp (-α * ((x + 1) * Real.log (x + 1))) := by
  rw [norm_carlsonDamping]
  have h1 : ((x : ℂ) + 1) = ((x + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ofReal_re, ofReal_im, zero_mul, sub_zero, norm_real, Real.norm_of_nonneg (by linarith)]

/-- The damping factor is differentiable to the right of `-1`. -/
theorem differentiableAt_carlsonDamping (α : ℝ) {z : ℂ} (hz : -1 < z.re) :
    DifferentiableAt ℂ (carlsonDamping α) z := by
  have hs : z + 1 ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  have h1 : DifferentiableAt ℂ (fun w : ℂ => w + 1) z := by fun_prop
  exact ((h1.mul (h1.clog hs)).const_mul _).cexp

/-- **Carlson's theorem.** Let `f` be holomorphic on the closed right half-plane, of exponential
type there, `‖f z‖ ≤ C e^(τ ‖z‖)`, and of type `c < π` on the imaginary axis,
`‖f (i y)‖ ≤ C e^(c |y|)`. If `f` vanishes at the natural numbers, then `f` vanishes on the closed
right half-plane. -/
theorem eqOn_zero_of_natCast_eq_zero {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z) {C τ c : ℝ}
    (hexp : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ C * Real.exp (τ * ‖z‖))
    (him : ∀ y : ℝ, ‖f (y * I)‖ ≤ C * Real.exp (c * |y|)) (hc : c < π)
    (hzero : ∀ n : ℕ, f n = 0) : ∀ z : ℂ, 0 ≤ z.re → f z = 0 := by
  set G := sinPiQuot f
  have hnat : ∀ n : ℤ, 0 ≤ ((n : ℂ)).re → f n = 0 := fun n hn => by
    have h0 : 0 ≤ n := by exact_mod_cast (show (0 : ℝ) ≤ n by simpa using hn)
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    simpa using hzero m
  -- Regularity of the quotient.
  have hGc : ∀ z : ℂ, 0 ≤ z.re → ContinuousAt G z := by
    intro z hz
    by_cases hs : sin (π * z) = 0
    · obtain ⟨n, rfl⟩ := sin_pi_mul_eq_zero_iff.mp hs
      exact continuousAt_sinPiQuot_intCast (hnat n hz) (hf _ hz)
    · exact continuousAt_sinPiQuot_of_ne hs (hf z hz).continuousAt
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hfU : DifferentiableOn ℂ f {z | 0 < z.re} := fun z hz =>
    (hf z (le_of_lt hz)).differentiableWithinAt
  have hGd : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ G z := by
    intro z hz
    by_cases hs : sin (π * z) = 0
    · obtain ⟨n, rfl⟩ := sin_pi_mul_eq_zero_iff.mp hs
      exact differentiableAt_sinPiQuot_intCast (hnat n hz.le) (hopen.mem_nhds hz) hfU
    · exact differentiableAt_sinPiQuot_of_ne hs (hf z hz.le)
  -- Exponential type of the quotient.
  set C' := max C 0
  set τ' := |τ|
  have hC' : 0 ≤ C' := le_max_right _ _
  have hexp' : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ C' * Real.exp (τ' * ‖z‖) := fun z hz =>
    (hexp z hz).trans (mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_abs_self τ) (norm_nonneg _))) (by positivity) hC')
  have hoff : ∀ z : ℂ, 0 ≤ z.re → (∀ n : ℤ, 1 / 4 ≤ ‖z - n‖) →
      ‖G z‖ ≤ 4 * C' * Real.exp (τ' * ‖z‖) := by
    intro z hz hd
    have hq := quarter_le_norm_sin_pi_mul hd
    have hs : sin (π * z) ≠ 0 := fun h => by rw [h, norm_zero] at hq; norm_num at hq
    rw [show G z = f z / sin (π * z) from sinPiQuot_of_ne hs, norm_div,
      div_le_iff₀ (norm_pos_iff.mpr hs)]
    calc ‖f z‖ ≤ C' * Real.exp (τ' * ‖z‖) := hexp' z hz
      _ = 4 * C' * Real.exp (τ' * ‖z‖) * (1 / 4) := by ring
      _ ≤ 4 * C' * Real.exp (τ' * ‖z‖) * ‖sin (π * z)‖ := by gcongr
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, ∀ z ∈ closedBall (0 : ℂ) 1 ∩ {z | 0 ≤ z.re}, ‖G z‖ ≤ K₀ :=
    ((isCompact_closedBall 0 1).inter_right
      (isClosed_le continuous_const continuous_re)).exists_bound_of_continuousOn
      fun z hz => (hGc z hz.2).continuousWithinAt
  set M := max K₀ (4 * C' * Real.exp (τ' / 2))
  have hM0 : 0 ≤ M := le_trans (by positivity) (le_max_right _ _)
  have hGbd : ∀ z : ℂ, 0 ≤ z.re → ‖G z‖ ≤ M * Real.exp (τ' * ‖z‖) := by
    intro z hz
    have hM1 : M ≤ M * Real.exp (τ' * ‖z‖) :=
      le_mul_of_one_le_right hM0 (Real.one_le_exp (by positivity))
    by_cases hnear : ∃ n : ℤ, ‖z - n‖ < 1 / 4
    · obtain ⟨n, hn⟩ := hnear
      have hre : |z.re - n| < 1 / 4 :=
        calc |z.re - n| = |(z - n).re| := by simp
          _ ≤ ‖z - n‖ := abs_re_le_norm _
          _ < 1 / 4 := hn
      have hn0 : 0 ≤ n := by
        have : (-1 : ℝ) < n := by linarith [(abs_lt.mp hre).2]
        exact_mod_cast (show (-1 : ℤ) < n by exact_mod_cast this)
      rcases hn0.eq_or_lt with h0 | h1
      · subst h0
        have hz1 : z ∈ closedBall (0 : ℂ) 1 := by
          rw [mem_closedBall, dist_zero_right]
          simp only [Int.cast_zero, sub_zero] at hn
          linarith
        exact (hK₀ z ⟨hz1, hz⟩).trans ((le_max_left _ _).trans hM1)
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
        have hball : closedBall (n : ℂ) (1 / 4) ⊆ {w | 0 < w.re} := by
          intro w hw
          have : |w.re - n| ≤ 1 / 4 :=
            calc |w.re - n| = |(w - n).re| := by simp
              _ ≤ ‖w - n‖ := abs_re_le_norm _
              _ ≤ 1 / 4 := by rwa [mem_closedBall, dist_eq_norm] at hw
          show 0 < w.re
          linarith [(abs_le.mp this).1]
        have hdc : DiffContOnCl ℂ G (ball (n : ℂ) (1 / 4)) := by
          refine ⟨fun w hw => (hGd w (hball (ball_subset_closedBall hw))).differentiableWithinAt,
            ?_⟩
          rw [closure_ball _ (by norm_num)]
          exact fun w hw => (hGc w (hball hw).le).continuousWithinAt
        have hzb : z ∈ ball (n : ℂ) (1 / 4) := by rwa [mem_ball, dist_eq_norm]
        have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc
          (C := 4 * C' * Real.exp (τ' * (‖z‖ + 1 / 2))) ?_ (subset_closure hzb)
        · refine hmax.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.exp_pos _).le))
          rw [mul_add, Real.exp_add]; ring_nf
        · intro w hw
          rw [frontier_ball _ (by norm_num), mem_sphere, dist_eq_norm] at hw
          have hd : ∀ m : ℤ, 1 / 4 ≤ ‖w - m‖ := by
            intro m
            by_cases hm : m = n
            · rw [hm, hw]
            · have h1 : (1 : ℝ) ≤ ‖(n : ℂ) - m‖ := by
                rw [← Int.cast_sub, norm_intCast]
                exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hm))
              have := norm_sub_le_norm_sub_add_norm_sub (n : ℂ) w m
              rw [norm_sub_rev (n : ℂ) w] at this
              linarith
          have hwre : 0 ≤ w.re := (hball (sphere_subset_closedBall (by
            rw [mem_sphere, dist_eq_norm, hw]))).le
          refine (hoff w hwre hd).trans ?_
          gcongr
          have := norm_sub_le_norm_sub_add_norm_sub w (n : ℂ) z
          have h2 := norm_le_norm_add_norm_sub' w z
          rw [norm_sub_rev (n : ℂ) z] at this
          linarith
    · push Not at hnear
      refine (hoff z hz hnear).trans ?_
      gcongr
      exact (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))).trans
        (le_max_right _ _)
  -- The quotient on the imaginary axis.
  have hGim : ∀ y : ℝ, 1 / 4 ≤ |y| → ‖G (y * I)‖ ≤ 4 * C' * Real.exp ((c - π) * |y|) := by
    intro y hy
    have hq := exp_div_four_le_norm_sin_pi_mul_I hy
    have hpos : 0 < ‖sin (π * (y * I))‖ := lt_of_lt_of_le (by positivity) hq
    have hs : sin (π * (y * I)) ≠ 0 := norm_pos_iff.mp hpos
    rw [show G (y * I) = f (y * I) / sin (π * (y * I)) from sinPiQuot_of_ne hs, norm_div,
      div_le_iff₀ hpos]
    have hf' : ‖f (y * I)‖ ≤ C' * Real.exp (c * |y|) :=
      (him y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    calc ‖f (y * I)‖ ≤ C' * Real.exp (c * |y|) := hf'
      _ = 4 * C' * Real.exp ((c - π) * |y|) * (Real.exp (π * |y|) / 4) := by
          rw [sub_mul, Real.exp_sub]; field_simp
      _ ≤ _ := by gcongr
  -- The damped function.
  set α := 2 * (π - c) / π
  have hα : 0 < α := div_pos (by linarith) Real.pi_pos
  have hαπ : (c - π) + α * (π / 2) = 0 := by
    simp only [α]; field_simp; ring
  set K := fun z => G z * carlsonDamping α z
  have hKd : DiffContOnCl ℂ K {z | 0 < z.re} := by
    refine ⟨fun z hz => ((hGd z hz).mul (differentiableAt_carlsonDamping α
      (by simp only [mem_ofPred_eq] at hz; linarith))).differentiableWithinAt, ?_⟩
    rw [closure_setOfPred_lt_re]
    exact fun z hz => ((hGc z hz).mul (differentiableAt_carlsonDamping α
      (by simp only [mem_ofPred_eq] at hz; linarith)).continuousAt).continuousWithinAt
  have hKexp : ∃ c < (2 : ℝ), ∃ B,
      K =O[Bornology.cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}] fun z => Real.exp (B * ‖z‖ ^ c) := by
    refine ⟨1, one_lt_two, τ' + α * (π / 2), IsBigO.of_bound M ?_⟩
    refine eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)
    have hz' : 0 ≤ z.re := le_of_lt hz
    rw [Real.rpow_one, Real.norm_of_nonneg (Real.exp_pos _).le, norm_mul]
    calc ‖G z‖ * ‖carlsonDamping α z‖
        ≤ (M * Real.exp (τ' * ‖z‖)) * Real.exp (α * (π / 2) * ‖z‖) :=
          mul_le_mul (hGbd z hz') ((norm_carlsonDamping_le hα.le hz').trans
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_im_le_norm z)
              (by positivity)))) (norm_nonneg _) (by positivity)
      _ = M * Real.exp ((τ' + α * (π / 2)) * ‖z‖) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hKim : ∃ C, ∀ x : ℝ, ‖K (x * I)‖ ≤ C := by
    refine ⟨max (4 * C') (M * Real.exp (τ' / 4) * Real.exp (α * (π / 2) / 4)), fun y => ?_⟩
    have hre : 0 ≤ ((y : ℂ) * I).re := by simp
    have himy : |((y : ℂ) * I).im| = |y| := by simp
    have hD := norm_carlsonDamping_le hα.le hre
    rw [himy] at hD
    simp only [K, norm_mul]
    by_cases hy : 1 / 4 ≤ |y|
    · refine le_trans ?_ (le_max_left _ _)
      calc ‖G (y * I)‖ * ‖carlsonDamping α (y * I)‖
          ≤ 4 * C' * Real.exp ((c - π) * |y|) * Real.exp (α * (π / 2) * |y|) :=
            mul_le_mul (hGim y hy) hD (norm_nonneg _) (by positivity)
        _ = 4 * C' := by
            rw [mul_assoc, ← Real.exp_add, ← add_mul, hαπ, zero_mul, Real.exp_zero, mul_one]
    · push Not at hy
      refine le_trans ?_ (le_max_right _ _)
      have hn : ‖(y : ℂ) * I‖ = |y| := by simp
      have h1 := hGbd _ hre
      rw [hn] at h1
      have hτ : 0 ≤ τ' := abs_nonneg _
      have hy' : |y| ≤ 1 / 4 := hy.le
      refine mul_le_mul (h1.trans ?_) (hD.trans ?_) (norm_nonneg _) (by positivity)
      · gcongr; nlinarith
      · gcongr; nlinarith [Real.pi_pos]
  have hKre : SuperpolynomialDecay atTop Real.exp fun x : ℝ => ‖K x‖ := by
    intro n
    set L : ℝ := n + τ'
    have hb : ∀ x : ℝ, 0 ≤ x → Real.exp x ^ n * ‖K x‖ ≤
        M * Real.exp (L * x - α * ((x + 1) * Real.log (x + 1))) := by
      intro x hx
      have hG := hGbd x (by simpa using hx)
      rw [norm_real, Real.norm_of_nonneg hx] at hG
      simp only [K, norm_mul, norm_carlsonDamping_ofReal α hx]
      calc Real.exp x ^ n * (‖G x‖ * Real.exp (-α * ((x + 1) * Real.log (x + 1))))
          ≤ Real.exp x ^ n * ((M * Real.exp (τ' * x)) *
              Real.exp (-α * ((x + 1) * Real.log (x + 1)))) := by gcongr
        _ = M * Real.exp (L * x - α * ((x + 1) * Real.log (x + 1))) := by
            rw [← Real.exp_nat_mul]
            simp only [L]
            rw [show (↑n + τ') * x - α * ((x + 1) * Real.log (x + 1)) =
              ↑n * x + τ' * x + -α * ((x + 1) * Real.log (x + 1)) by ring,
              Real.exp_add, Real.exp_add]
            ring
    have ht : Tendsto (fun x : ℝ => L * x - α * ((x + 1) * Real.log (x + 1))) atTop atBot := by
      refine tendsto_atBot_mono' atTop ?_ tendsto_neg_atTop_atBot
      have hL : 0 ≤ L := by positivity
      filter_upwards [eventually_ge_atTop (Real.exp ((L + 1) / α)), eventually_ge_atTop 0]
        with x hx hx0
      have hlog : (L + 1) / α ≤ Real.log (x + 1) :=
        (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith)
      have hlog' : L + 1 ≤ α * Real.log (x + 1) := by
        rwa [div_le_iff₀ hα, mul_comm] at hlog
      nlinarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using (Real.tendsto_exp_atBot.comp ht).const_mul M) ?_ ?_
    · exact Eventually.of_forall fun x => by positivity
    · filter_upwards [eventually_ge_atTop 0] with x hx using hb x hx
  have hK0 := PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay hKd hKexp
    hKre hKim
  intro z hz
  have hKz : K z = 0 := hK0 hz
  have hGz : G z = 0 := (mul_eq_zero.mp hKz).resolve_right (exp_ne_zero _)
  by_cases hs : sin (π * z) = 0
  · obtain ⟨n, rfl⟩ := sin_pi_mul_eq_zero_iff.mp hs
    exact hnat n hz
  · rw [show G z = f z / sin (π * z) from sinPiQuot_of_ne hs, div_eq_zero_iff] at hGz
    exact hGz.resolve_right hs

/-- **Carlson's theorem in several variables.** Let `F` be holomorphic on the closed product of
right half-planes `Re b i ≥ 0`, with `‖F b‖ ≤ C exp (∑ i, (τ |Re b i| + c |Im b i|))` there and
`c < π`. If `F` vanishes on `ℕ^ι`, then `F` vanishes on the closed product of half-planes. -/
theorem eqOn_zero_of_natCast_eq_zero_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : (ι → ℂ) → ℂ} (hF : ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) → DifferentiableAt ℂ F b)
    {C τ c : ℝ}
    (hbd : ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) →
      ‖F b‖ ≤ C * Real.exp (∑ i, (τ * |(b i).re| + c * |(b i).im|)))
    (hc : c < π) (hzero : ∀ n : ι → ℕ, F (fun i => n i) = 0) :
    ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) → F b = 0 := by
  -- Induction on the set of coordinates that are allowed to be non-natural.
  suffices H : ∀ s : Finset ι, ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) →
      (∀ i ∉ s, ∃ n : ℕ, b i = n) → F b = 0 by
    intro b hb
    exact H Finset.univ b hb fun i hi => absurd (Finset.mem_univ i) hi
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro b _ hnat
    choose n hn using fun i => hnat i (Finset.notMem_empty i)
    have : b = fun i => (n i : ℂ) := funext hn
    rw [this]
    exact hzero n
  | insert j s hj ih =>
    intro b hb hnat
    set f : ℂ → ℂ := fun z => F (Function.update b j z)
    have hupd : ∀ z : ℂ, 0 ≤ z.re → ∀ i, 0 ≤ (Function.update b j z i).re := by
      intro z hz i
      by_cases hi : i = j
      · subst hi; simpa using hz
      · simpa [Function.update_of_ne hi] using hb i
    have hf : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z := by
      intro z hz
      have hu : DifferentiableAt ℂ (fun z : ℂ => Function.update b j z) z := by
        refine differentiableAt_pi.mpr fun i => ?_
        by_cases hi : i = j
        · subst hi; simp only [Function.update_self]; exact differentiableAt_id
        · simp only [Function.update_of_ne hi]; exact differentiableAt_const _
      exact (hF _ (hupd z hz)).comp z hu
    set K : ℝ := ∑ i ∈ Finset.univ.erase j, (τ * |(b i).re| + c * |(b i).im|)
    have hsplit : ∀ z : ℂ, ∑ i, (τ * |(Function.update b j z i).re| +
        c * |(Function.update b j z i).im|) = (τ * |z.re| + c * |z.im|) + K := by
      intro z
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      simp only [Function.update_self, K]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    set C' : ℝ := max C 0 * Real.exp K
    have hfb : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ C' * Real.exp (τ * |z.re| + c * |z.im|) := by
      intro z hz
      refine (hbd _ (hupd z hz)).trans ?_
      rw [hsplit, Real.exp_add, ← mul_assoc, mul_right_comm]
      simp only [C']
      gcongr
      · exact le_max_left _ _
    have hzf := eqOn_zero_of_natCast_eq_zero (f := f) hf (C := C') (τ := |τ| + |c|) (c := c)
      (fun z hz => (hfb z hz).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        have h1 : τ * |z.re| ≤ |τ| * ‖z‖ :=
          (le_abs_self _).trans (by rw [abs_mul, abs_abs]; gcongr; exact abs_re_le_norm z)
        have h2 : c * |z.im| ≤ |c| * ‖z‖ :=
          (le_abs_self _).trans (by rw [abs_mul, abs_abs]; gcongr; exact abs_im_le_norm z)
        nlinarith)) (by positivity)))
      (fun y => by simpa using hfb (y * I) (by simp)) hc
      (fun n => ih _ (hupd n (by simp)) fun i hi => by
        by_cases hij : i = j
        · subst hij; exact ⟨n, by simp⟩
        · rw [Function.update_of_ne hij]
          exact hnat i (by simp [hij, hi]))
      (b j) (hb j)
    simpa [f] using hzf

/-- **Uniqueness of the continuation of lattice data.** Two functions holomorphic on the closed
product of right half-planes, with bounds `C exp (∑ i, (τ |Re b i| + c |Im b i|))`, `c < π`, that
agree on `ℕ^ι` agree on the closed product of half-planes. -/
theorem eqOn_of_natCast_eq_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F₁ F₂ : (ι → ℂ) → ℂ}
    (hF₁ : ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) → DifferentiableAt ℂ F₁ b)
    (hF₂ : ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) → DifferentiableAt ℂ F₂ b) {C τ c : ℝ}
    (hbd₁ : ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) →
      ‖F₁ b‖ ≤ C * Real.exp (∑ i, (τ * |(b i).re| + c * |(b i).im|)))
    (hbd₂ : ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) →
      ‖F₂ b‖ ≤ C * Real.exp (∑ i, (τ * |(b i).re| + c * |(b i).im|)))
    (hc : c < π) (heq : ∀ n : ι → ℕ, F₁ (fun i => n i) = F₂ (fun i => n i)) :
    ∀ b : ι → ℂ, (∀ i, 0 ≤ (b i).re) → F₁ b = F₂ b := by
  intro b hb
  have h := eqOn_zero_of_natCast_eq_zero_pi (F := F₁ - F₂) (fun b hb => (hF₁ b hb).sub (hF₂ b hb))
    (C := 2 * C) (τ := τ) (c := c) (fun b hb => by
      refine (norm_sub_le _ _).trans ?_
      have := add_le_add (hbd₁ b hb) (hbd₂ b hb)
      linarith) hc (fun n => by simp [heq n]) b hb
  simpa [sub_eq_zero] using h

end Complex
