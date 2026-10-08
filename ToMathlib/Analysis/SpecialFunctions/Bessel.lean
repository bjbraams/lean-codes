/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Series and bounds for Bessel functions of integer order, and the modified Bessel function

The regularized `₀F₁` is the sum of its series `∑ zᵏ / (k! Γ(c + k))`, and for `c = n + 1` it is
bounded by `exp ‖z‖ / n!`. Consequently `‖Jₘ(x)‖ ≤ exp (‖x‖²/4) (‖x‖/2)^{|m|} / |m|!` for every
integer `m`. The series is differentiated termwise, and the regularized `₀F₁` satisfies a
contiguous relation and a reflection formula at integer parameters.

## Main results

* `Complex.hasSum_regularizedHGFun_zero_singleton`: the series of the regularized `₀F₁`.
* `Complex.iteratedDeriv_regularizedHGFun_zero_singleton`: `(d/dz)ⁿ F̃₀₁(c; z) = F̃₀₁(c + n; z)`,
  Carlson's (6.9-23).
* `Complex.regularizedHGFun_zero_singleton_sub_one`: the contiguous relation
  `F̃₀₁(c - 1; z) = (c - 1) F̃₀₁(c; z) + z F̃₀₁(c + 1; z)`.
* `Complex.iteratedDeriv_cpow_mul_regularizedHGFun`: `dⁿ/dzⁿ [z^{c-1} F̃₀₁(c; z)] =
  z^{c-n-1} F̃₀₁(c - n; z)` on the slit plane (Carlson, Exercise 6.9-20).
* `Complex.regularizedHGFun_zero_singleton_one_sub_int`: the reflection formula (6.9-24),
  `F̃₀₁(1 - n; z) = zⁿ F̃₀₁(1 + n; z)` for `n ∈ ℤ` and `z ≠ 0`.
* `Complex.norm_besselJ_intCast_le`: the bound for integer orders.
* `Complex.hasSum_regularizedHGFun`: the series of an entire regularized hypergeometric function.
* `Complex.besselI`: the modified Bessel function `Iₐ`, with `Jₘ(ix) = iᵐ Iₘ(x)`
  (`Complex.besselJ_intCast_I_mul`) and `I₋ₘ = Iₘ` (`Complex.besselI_neg_int`) for integers `m`.
-/

@[expose] public noncomputable section

namespace Complex

/-- The regularized `₀F₁` is the sum of its power series `∑ zⁿ / (n! Γ(c + n))`. -/
theorem hasSum_regularizedHGFun_zero_singleton (c z : ℂ) :
    HasSum (fun n : ℕ ↦ z ^ n / (n.factorial * Gamma (c + n)))
      (regularizedHGFun 0 {c} z) := by
  have h := (regularizedHGFunSeries 0 {c}).hasSum
    (x := z) (by simp [radius_regularizedHGFunSeries_zero_eq_top])
  show HasSum _ ((regularizedHGFunSeries 0 {c}).sum z)
  convert h using 1
  funext n
  rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq]
  simp [regularizedHGFunCoeff, div_eq_mul_inv, mul_comm]

/-- The series of the regularized `₀F₁` converges absolutely. -/
theorem summable_norm_regularizedHGFun_zero_singleton (c z : ℂ) :
    Summable fun n : ℕ ↦ ‖z ^ n / (n.factorial * Gamma (c + n))‖ := by
  have h := (regularizedHGFunSeries 0 {c}).summable_norm_apply (x := z)
    (by simp [radius_regularizedHGFunSeries_zero_eq_top])
  refine h.congr fun n ↦ ?_
  rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq]
  simp [regularizedHGFunCoeff, div_eq_mul_inv, mul_comm]

/-- The derivative of the regularized `₀F₁`: `d/dz F̃₀₁(c; z) = F̃₀₁(c + 1; z)`. -/
theorem hasDerivAt_regularizedHGFun_zero_singleton (c y : ℂ) :
    HasDerivAt (regularizedHGFun 0 {c}) (regularizedHGFun 0 {c + 1} y) y := by
  set R : ℝ := ‖y‖ + 1
  have hR : 0 ≤ R := by positivity
  set g : ℕ → ℂ → ℂ := fun n z ↦ z ^ n / (n.factorial * Gamma (c + n))
  set g' : ℕ → ℂ → ℂ := fun n z ↦ n * z ^ (n - 1) / (n.factorial * Gamma (c + n))
  set u : ℕ → ℝ := fun n ↦ ‖g' n R‖
  have hshift (n : ℕ) (z : ℂ) :
      g' (n + 1) z = z ^ n / (n.factorial * Gamma (c + 1 + n)) := by
    simp only [g', Nat.factorial_succ, Nat.add_sub_cancel]
    push_cast
    rw [show c + (n + 1 : ℂ) = c + 1 + n by ring]
    have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    field_simp
  have hu : Summable u := by
    rw [← summable_nat_add_iff 1]
    refine (summable_norm_regularizedHGFun_zero_singleton (c + 1) R).congr fun n ↦ ?_
    simp only [u, hshift]
  have hg (n : ℕ) (z : ℂ) (_ : z ∈ Metric.ball (0 : ℂ) R) : HasDerivAt (g n) (g' n z) z :=
    (hasDerivAt_pow n z).div_const _
  have hg' (n : ℕ) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) R) : ‖g' n z‖ ≤ u n := by
    rw [mem_ball_zero_iff] at hz
    simp only [u, g', norm_div, norm_mul, norm_pow, norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hR]
    gcongr
  have hyR : y ∈ Metric.ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; simp only [R]; linarith
  have H := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected hg hg' hyR
    (summable_norm_regularizedHGFun_zero_singleton c y).of_norm hyR
  have hf : regularizedHGFun 0 {c} = fun z ↦ ∑' n, g n z := by
    funext z; exact (hasSum_regularizedHGFun_zero_singleton c z).tsum_eq.symm
  rw [hf]
  convert H using 1
  have hs : HasSum (fun n ↦ g' n y) (regularizedHGFun 0 {c + 1} y) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    rw [Finset.range_one, Finset.sum_singleton, show g' 0 y = 0 by simp [g'], sub_zero]
    exact (hasSum_regularizedHGFun_zero_singleton (c + 1) y).congr_fun fun n ↦ hshift n y
  exact hs.tsum_eq.symm

/-- The iterated derivatives of the regularized `₀F₁`:
`(d/dz)ⁿ F̃₀₁(c; z) = F̃₀₁(c + n; z)`. -/
theorem iteratedDeriv_regularizedHGFun_zero_singleton (c : ℂ) (n : ℕ) :
    iteratedDeriv n (regularizedHGFun 0 {c}) = regularizedHGFun 0 {c + n} := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ', show c + ((n + 1 : ℕ) : ℂ) = c + 1 + n by push_cast; ring, ← ih]
    congr 1
    funext y
    exact (hasDerivAt_regularizedHGFun_zero_singleton c y).deriv


/-- The contiguous relation `F̃₀₁(c - 1; z) = (c - 1) F̃₀₁(c; z) + z F̃₀₁(c + 1; z)`. -/
theorem regularizedHGFun_zero_singleton_sub_one (c z : ℂ) :
    regularizedHGFun 0 {c - 1} z =
      (c - 1) * regularizedHGFun 0 {c} z + z * regularizedHGFun 0 {c + 1} z := by
  set b : ℕ → ℂ := fun k ↦ z ^ k / (k.factorial * Gamma (c + 1 + k))
  set b' : ℕ → ℂ := fun k ↦ if k = 0 then 0 else z * b (k - 1)
  have hb' : HasSum b' (z * regularizedHGFun 0 {c + 1} z) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    simp only [b', Finset.range_one, Finset.sum_singleton, ↓reduceIte, sub_zero,
      Nat.add_one_ne_zero, Nat.add_sub_cancel]
    exact (hasSum_regularizedHGFun_zero_singleton (c + 1) z).mul_left z
  have H := ((hasSum_regularizedHGFun_zero_singleton c z).mul_left (c - 1)).add hb'
  refine ((hasSum_regularizedHGFun_zero_singleton (c - 1) z).unique (H.congr_fun fun k ↦ ?_))
  rcases k with _ | k
  · simp only [b', ↓reduceIte, add_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul,
      Nat.cast_zero]
    rw [one_div, one_div, one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c - 1), sub_add_cancel]
  · simp only [b, b', Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    rw [show c - 1 + (k + 1) = c + k by ring, show c + (k + 1) = c + 1 + k by ring,
      div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv, mul_inv, mul_inv,
      one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + k), show c + k + 1 = c + 1 + k by ring]
    have : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast k.succ_ne_zero
    field_simp
    ring

/-- The derivative of `z^{c-1} F̃₀₁(c; z)` on the slit plane is `z^{c-2} F̃₀₁(c - 1; z)`. -/
theorem hasDerivAt_cpow_mul_regularizedHGFun (c : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun y ↦ y ^ (c - 1) * regularizedHGFun 0 {c} y)
      (z ^ (c - 1 - 1) * regularizedHGFun 0 {c - 1} z) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have h := ((hasStrictDerivAt_cpow_const (c := c - 1) hz).hasDerivAt).mul
    (hasDerivAt_regularizedHGFun_zero_singleton c z)
  have hp : z ^ (c - 1) = z ^ (c - 1 - 1) * z := by
    conv_lhs => rw [show c - 1 = c - 1 - 1 + 1 by ring]
    rw [cpow_add _ _ hz0, cpow_one]
  convert h using 1
  rw [regularizedHGFun_zero_singleton_sub_one, hp]
  ring

/-- **Exercise 6.9-20** (second formula): on the slit plane,
`dⁿ/dzⁿ [z^{c-1} F̃₀₁(c; z)] = z^{c-n-1} F̃₀₁(c - n; z)`. -/
theorem iteratedDeriv_cpow_mul_regularizedHGFun (c : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun y ↦ y ^ (c - 1) * regularizedHGFun 0 {c} y) z =
      z ^ (c - n - 1) * regularizedHGFun 0 {c - n} z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun y ↦ y ^ (c - 1) * regularizedHGFun 0 {c} y) =ᶠ[nhds z]
        fun y ↦ y ^ (c - n - 1) * regularizedHGFun 0 {c - n} y :=
      (isOpen_slitPlane.eventually_mem hz).mono fun y hy ↦ ih hy
    rw [he.deriv_eq, (hasDerivAt_cpow_mul_regularizedHGFun (c - n) hz).deriv]
    push_cast
    rw [show c - (n + 1) = c - n - 1 by ring]

/-- **Carlson's reflection formula (6.9-24)** at integer order: for `z ≠ 0` and `n ∈ ℤ`,
`F̃₀₁(1 - n; z) = zⁿ F̃₀₁(1 + n; z)`. -/
theorem regularizedHGFun_zero_singleton_one_sub_int (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
    regularizedHGFun 0 {1 - (n : ℂ)} z = z ^ n * regularizedHGFun 0 {1 + (n : ℂ)} z := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have h := regularizedHGFun_zero_singleton_neg_nat_add_one k z
    rw [show -(k : ℂ) + 1 = 1 - k by ring, add_comm (k : ℂ)] at h
    simpa using h
  · have h := regularizedHGFun_zero_singleton_neg_nat_add_one k z
    rw [show -(k : ℂ) + 1 = 1 - k by ring, add_comm (k : ℂ)] at h
    push_cast
    rw [sub_neg_eq_add, ← sub_eq_add_neg, h, zpow_neg, zpow_natCast, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hz), one_mul]

/-- The regularized `₀F₁(n + 1; z)` is bounded by `exp ‖z‖ / n!`. -/
theorem norm_regularizedHGFun_natCast_add_one_le (n : ℕ) (z : ℂ) :
    ‖regularizedHGFun 0 {(n : ℂ) + 1} z‖ ≤ Real.exp ‖z‖ / n.factorial := by
  have hg := (NormedSpace.expSeries_div_hasSum_exp ‖z‖).div_const (n.factorial : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at hg
  refine (hasSum_regularizedHGFun_zero_singleton _ z).norm_le_of_bounded hg fun k ↦ ?_
  rw [show (n : ℂ) + 1 + k = ((n + k : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial,
    norm_div, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_natCast, div_div]
  gcongr
  omega

/-- A bound for the Bessel functions of natural order. -/
theorem norm_besselJ_natCast_le (n : ℕ) (x : ℂ) :
    ‖besselJ n x‖ ≤ Real.exp (‖x‖ ^ 2 / 4) * ((‖x‖ / 2) ^ n / n.factorial) := by
  simp only [besselJ_def, cpow_natCast]
  rw [ norm_mul, norm_pow, norm_div, RCLike.norm_ofNat]
  have h := norm_regularizedHGFun_natCast_add_one_le n (-(x / 2) ^ 2)
  rw [norm_neg, norm_pow, norm_div, RCLike.norm_ofNat] at h
  calc (‖x‖ / 2) ^ n * ‖regularizedHGFun 0 {(n : ℂ) + 1} (-(x / 2) ^ 2)‖
      ≤ (‖x‖ / 2) ^ n * (Real.exp ((‖x‖ / 2) ^ 2) / n.factorial) := by gcongr
    _ = _ := by rw [div_pow]; ring_nf

/-- A bound for the Bessel functions of integer order. -/
theorem norm_besselJ_intCast_le (m : ℤ) (x : ℂ) :
    ‖besselJ m x‖ ≤ Real.exp (‖x‖ ^ 2 / 4) * ((‖x‖ / 2) ^ m.natAbs / m.natAbs.factorial) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa using norm_besselJ_natCast_le k x
  · rw [show ((-(k : ℤ) : ℤ) : ℂ) = -((k : ℤ) : ℂ) by push_cast; ring, besselJ_neg_int,
      norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
    simpa using norm_besselJ_natCast_le k x

/-- The regularized hypergeometric series sums to its function throughout its convergence ball. -/
theorem hasSum_regularizedHGFun_of_mem_eball {a b : Multiset ℂ} {z : ℂ}
    (hz : z ∈ Metric.eball 0 (regularizedHGFunSeries a b).radius) :
    HasSum (fun n : ℕ ↦ regularizedHGFunCoeff a b n * z ^ n) (regularizedHGFun a b z) := by
  have h := (regularizedHGFunSeries a b).hasSum hz
  show HasSum _ ((regularizedHGFunSeries a b).sum z)
  convert h using 1
  funext n
  rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- In the entire case the regularized hypergeometric series converges at every point. -/
theorem hasSum_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    HasSum (fun n : ℕ ↦ regularizedHGFunCoeff a b n * z ^ n) (regularizedHGFun a b z) :=
  hasSum_regularizedHGFun_of_mem_eball (by simp [radius_regularizedHGFunSeries_eq_top h])

/-- The modified Bessel function of the first kind,
`Iₐ(x) = (x/2)^a ₀F₁(a + 1; (x/2)²)`, with the regularized `₀F₁`. -/
def besselI (a x : ℂ) : ℂ := (x / 2) ^ a * regularizedHGFun 0 {a + 1} ((x / 2) ^ 2)

/-- `J_a(i x) = iᵃ I_a(x)` for integer orders. -/
theorem besselJ_intCast_I_mul (a : ℤ) (x : ℂ) :
    besselJ a (I * x) = I ^ a * besselI a x := by
  rw [besselJ_def, besselI]
  simp only [cpow_intCast]
  rw [show I * x / 2 = I * (x / 2) by ring, mul_zpow, mul_pow, I_sq]
  ring_nf

/-- `I₋ₐ = Iₐ` for integer orders. -/
theorem besselI_neg_int (a : ℤ) (x : ℂ) : besselI (-a) x = besselI a x := by
  have h1 := besselJ_intCast_I_mul (-a) x
  push_cast at h1
  rw [besselJ_neg_int, besselJ_intCast_I_mul, zpow_neg] at h1
  have hI : (I ^ a : ℂ) ≠ 0 := zpow_ne_zero _ I_ne_zero
  rw [(inv_mul_eq_iff_eq_mul₀ hI).mp h1.symm, ← mul_assoc, ← mul_assoc, ← mul_zpow, ← mul_zpow,
    show I * -1 * I = 1 by rw [mul_neg_one, neg_mul, I_mul_I, neg_neg], one_zpow, one_mul]

end Complex
