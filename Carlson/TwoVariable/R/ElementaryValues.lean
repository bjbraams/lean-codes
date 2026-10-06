/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.R.Elementary
public import Carlson.R.IntegerParameters
public import Carlson.TwoVariable.FractionalContinuation
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Carlson.TwoVariable.QuadraticHybrid
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Elementary values of R-functions (Exercises of Chapter 6)

Evaluations of R-functions in elementary terms from Carlson's Chapter 6 exercises. They follow
from the terminating case `R_{-c-N}(b; z) = ∏ zᵢ^(-bᵢ) Γ(c) R_N(b; z⁻¹)/Γ(c)`
(`regCarlsonR_neg_sum_sub_nat`), from Exercise 5.9-13, and from the closed forms of `R_C`
((6.9-15), (6.9-16)). Branches are principal; products of powers are written as products,
which is the form valid on the whole slit plane.

## Main results

* `Carlson.carlsonR_neg_sum`: (6.6-5), `R_{-c}(b; z) = ∏ zᵢ^(-bᵢ)`.
* `Carlson.carlsonR_neg_three_halves`, `carlsonR_neg_five_halves`: Exercises 6.6-16 and 6.8-7.
* `Carlson.regCarlsonR_neg_one_one_neg_nat`: Exercise 6.3-2.
* `Carlson.TwoVariable.regCarlsonR_pair_one_one_exp`, `regCarlsonR_pair_neg_one_exp`,
  `log_eq_mul_regCarlsonR_pair`, `cos_pi_mul_div_two_eq`, `arctan_eq_mul_regCarlsonR`:
  Exercise 6.8-5.
* `Carlson.TwoVariable.regCarlsonR_pair_neg_one_sq`: Exercise 6.8-6.
* `Carlson.TwoVariable.arccos_eq_mul_carlsonRC`, `arctan_eq_mul_carlsonRC`,
  `arctan_inv_eq_carlsonRC`, `arsinh_eq_mul_carlsonRC`, `arcosh_eq_mul_carlsonRC`,
  `artanh_eq_mul_carlsonRC`, `half_log_eq_carlsonRC`: Exercise 6.9-16.
* `Carlson.TwoVariable.carlsonR_cos_sq_eq_sin_div`, `sin_mul_carlsonRC_cos_sq`,
  `pi_eq_four_mul_carlsonRC`, `tendsto_two_mul_carlsonRC_zero`, `carlsonRC_cot_sq_csc_sq_complex`,
  `carlsonRC_coth_sq_csch_sq_complex`: Exercise 6.9-17. The last two hold for `Re θ > 0`,
  `Re φ > 0` only: their right sides are even in the angle.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 6.
-/

open Complex Finset Filter
@[expose] public noncomputable section
namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- `R_{-c}(b; z) = ∏ zᵢ^(-bᵢ)` (Carlson's (6.6-5)) for slit-plane nodes, if `c = ∑ bᵢ` is not a
pole of `Γ`. -/
theorem carlsonR_neg_sum (b : ι → ℂ) (hb : ∀ m : ℕ, ∑ i, b i ≠ -m) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    carlsonR (-(∑ i, b i)) b z = ∏ i, z i ^ (-b i) := by
  have h := regCarlsonR_neg_sum_sub_nat 0 b hz
  rw [Nat.cast_zero, sub_zero, regCarlsonRPolynomial_zero] at h
  rw [carlsonR, h, mul_comm, mul_assoc, inv_mul_cancel₀ (Gamma_ne_zero hb), mul_one]

/-- `R_{-c-1}(b; z) = ∏ zᵢ^(-bᵢ) · c⁻¹ ∑ bᵢ zᵢ⁻¹` for slit-plane nodes, if `c = ∑ bᵢ` is not a
pole of `Γ`. -/
theorem carlsonR_neg_sum_sub_one (b : ι → ℂ) (hb : ∀ m : ℕ, ∑ i, b i ≠ -m) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    carlsonR (-(∑ i, b i) - 1) b z =
      (∏ i, z i ^ (-b i)) * ((∑ i, b i * (z i)⁻¹) / ∑ i, b i) := by
  have h := regCarlsonR_neg_sum_sub_nat 1 b hz
  rw [Nat.cast_one, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
    carlsonRPolynomialNumerator_one, Nat.cast_one] at h
  have hc0 : (∑ i, b i) ≠ 0 := by simpa using hb 0
  have hG := Gamma_ne_zero hb
  rw [carlsonR, h, Complex.Gamma_add_one _ hc0]
  field_simp

/-- **Exercises 6.6-16 and 6.8-7, first relation**: `R_{-3/2}(½, ½, ½; x, y, z) = (xyz)^(-1/2)`,
in the product form `x^(-1/2) y^(-1/2) z^(-1/2)` valid on the slit plane. -/
theorem carlsonR_neg_three_halves {z : Fin 3 → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    carlsonR (-3 / 2) (fun _ => 1 / 2) z = ∏ i, z i ^ (-(1 / 2 : ℂ)) := by
  have h := carlsonR_neg_sum (fun _ : Fin 3 => (1 / 2 : ℂ)) (fun m hm => by
    have := congrArg re hm; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) hz
  rw [show -(∑ _i : Fin 3, (1 / 2 : ℂ)) = -3 / 2 by simp; ring] at h
  exact h

/-- **Exercise 6.8-7, second relation**:
`R_{-5/2}(½, ½, ½; x, y, z) = ⅓ (xyz)^(-3/2)(xy + yz + zx)`,
in the form `x^(-1/2) y^(-1/2) z^(-1/2) · ⅓ (x⁻¹ + y⁻¹ + z⁻¹)` valid on the slit plane. -/
theorem carlsonR_neg_five_halves {z : Fin 3 → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    carlsonR (-5 / 2) (fun _ => 1 / 2) z =
      (∏ i, z i ^ (-(1 / 2 : ℂ))) * ((1 / 3) * ∑ i, (z i)⁻¹) := by
  have h := carlsonR_neg_sum_sub_one (fun _ : Fin 3 => (1 / 2 : ℂ)) (fun m hm => by
    have := congrArg re hm; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) hz
  rw [show -(∑ _i : Fin 3, (1 / 2 : ℂ)) - 1 = -5 / 2 by simp; ring] at h
  rw [h]
  simp only [Fin.sum_univ_three]
  ring

/-- **Exercise 6.3-2**: `R_{-1}(1, -n; x, y)/Γ(1 - n) = n! (y - x)ⁿ x^(-n-1)` for slit-plane
nodes. -/
theorem regCarlsonR_neg_one_one_neg_nat (n : ℕ) {x y : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) :
    regCarlsonR (-1) (TwoVariable.pair 1 (-(n : ℂ))) (TwoVariable.pair x y) =
      (n.factorial : ℂ) * (y - x) ^ n * x⁻¹ ^ (n + 1) := by
  have hz : TwoVariable.pair x y ∈ carlsonRSlitDomain := by intro i; fin_cases i <;> assumption
  have h := regCarlsonR_neg_sum_sub_nat n (TwoVariable.pair 1 (-(n : ℂ))) hz
  rw [TwoVariable.sum_pair, show -(1 + -(n : ℂ)) - n = -1 by ring] at h
  rw [h]
  have hp := TwoVariable.regRPolynomial_one_neg_nat n n x⁻¹ y⁻¹
  rw [ite_eq_left_of_eq_true _ _ (eq_true le_rfl), Nat.sub_self, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_zero,
    mul_one] at hp
  have hpp : TwoVariable.regRPolynomial n 1 (-(n : ℂ)) x⁻¹ y⁻¹ =
      regCarlsonRPolynomial n (TwoVariable.pair 1 (-(n : ℂ)))
        (fun i => (TwoVariable.pair x y i)⁻¹) := by
    congr 1
  rw [← hpp, hp, Fin.prod_univ_two]
  simp only [TwoVariable.pair_zero, TwoVariable.pair_one, neg_neg, cpow_natCast]
  have hx0 := slitPlane_ne_zero hx
  have hy0 := slitPlane_ne_zero hy
  have hyy : y ^ n * y⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hy0, one_pow]
  rw [cpow_neg_one, show x⁻¹ - y⁻¹ = (y - x) * x⁻¹ * y⁻¹ by field_simp, mul_pow,
    mul_pow, pow_succ]
  linear_combination ((n.factorial : ℂ) * (y - x) ^ n * x⁻¹ ^ n * x⁻¹) * hyy

namespace TwoVariable

/-- `exp w` lies in the slit plane if `|Im w| < π`. -/
theorem exp_mem_slitPlane_of_abs_im_lt {w : ℂ} (h : |w.im| < Real.pi) : exp w ∈ slitPlane := by
  have h1 := (abs_lt.mp h).1
  have h2 := (abs_lt.mp h).2
  rw [mem_slitPlane_iff_arg]
  refine ⟨?_, exp_ne_zero _⟩
  rw [← log_im, log_exp h1 h2.le]
  exact h2.ne

/-- `log (exp w) = w` and hence `(exp w)ᵗ = exp (w t)` if `|Im w| < π`. -/
theorem exp_cpow_of_abs_im_lt {w : ℂ} (h : |w.im| < Real.pi) (t : ℂ) :
    exp w ^ t = exp (w * t) := by
  rw [cpow_def_of_ne_zero (exp_ne_zero _), log_exp (abs_lt.mp h).1 (abs_lt.mp h).2.le]

/-- `e^{iθ} - e^{-iθ} = 2i sin θ`. -/
theorem exp_mul_I_sub_exp_neg_mul_I (x : ℂ) : exp (x * I) - exp (-x * I) = 2 * I * sin x := by
  have := two_sin (x := x)
  linear_combination (-I) * this + (exp (x * I) - exp (-x * I)) * I_sq

/-- **Exercise 6.8-5, first relation**: `sin tθ/(t sin θ) = R_{t-1}(1, 1; e^{iθ}, e^{-iθ})`
for `|Re θ| < π`, `t ≠ 0` and `sin θ ≠ 0`. (Here `R = R/Γ(2)` is Carlson's function.) -/
theorem regCarlsonR_pair_one_one_exp {t θ : ℂ} (hθ : |θ.re| < Real.pi) (ht : t ≠ 0)
    (hs : sin θ ≠ 0) :
    regCarlsonR (t - 1) (pair 1 1) (pair (exp (θ * I)) (exp (-θ * I))) =
      sin (t * θ) / (t * sin θ) := by
  have hp : |(θ * I).im| < Real.pi := by simpa using hθ
  have hm : |(-θ * I).im| < Real.pi := by simpa using hθ
  have h := regCarlsonR_pair_one_one t (exp_mem_slitPlane_of_abs_im_lt hp)
    (exp_mem_slitPlane_of_abs_im_lt hm)
  rw [exp_cpow_of_abs_im_lt hp, exp_cpow_of_abs_im_lt hm, exp_mul_I_sub_exp_neg_mul_I,
    show θ * I * t = (t * θ) * I by ring, show -θ * I * t = -(t * θ) * I by ring,
    exp_mul_I_sub_exp_neg_mul_I] at h
  rw [eq_div_iff (mul_ne_zero ht hs)]
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  apply mul_left_cancel₀ h2I
  linear_combination h

/-- **Exercise 6.8-5, third relation**: `θ/sin θ = R_{-1}(1, 1; e^{iθ}, e^{-iθ})` for
`|Re θ| < π` and `sin θ ≠ 0`. -/
theorem regCarlsonR_pair_neg_one_exp {θ : ℂ} (hθ : |θ.re| < Real.pi) (hs : sin θ ≠ 0) :
    regCarlsonR (-1) (pair 1 1) (pair (exp (θ * I)) (exp (-θ * I))) = θ / sin θ := by
  have hp : |(θ * I).im| < Real.pi := by simpa using hθ
  have hm : |(-θ * I).im| < Real.pi := by simpa using hθ
  have h := regCarlsonR_pair_one_one_log (exp_mem_slitPlane_of_abs_im_lt hp)
    (exp_mem_slitPlane_of_abs_im_lt hm)
  rw [exp_mul_I_sub_exp_neg_mul_I, log_exp (abs_lt.mp hp).1 (abs_lt.mp hp).2.le,
    log_exp (abs_lt.mp hm).1 (abs_lt.mp hm).2.le] at h
  rw [eq_div_iff hs]
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  apply mul_left_cancel₀ h2I
  linear_combination h

/-- **Exercise 6.8-5, fourth relation**: `log x = (x - 1) R_{-1}(1, 1; x, 1)` on the slit plane. -/
theorem log_eq_mul_regCarlsonR_pair {x : ℂ} (hx : x ∈ slitPlane) :
    log x = (x - 1) * regCarlsonR (-1) (pair 1 1) (pair x 1) := by
  rw [regCarlsonR_pair_one_one_log hx one_mem_slitPlane, log_one, sub_zero]

/-- **Exercise 6.8-5, second relation**: `cos(πt/2) = (1 + t) R_t(1, 1; i, -i)` for all `t`. -/
theorem cos_pi_mul_div_two_eq (t : ℂ) :
    cos (Real.pi * t / 2) = (1 + t) * regCarlsonR t (pair 1 1) (pair I (-I)) := by
  have hI : I ∈ slitPlane := by simp [mem_slitPlane_iff]
  have hnI : -I ∈ slitPlane := by simp [mem_slitPlane_iff]
  have h := regCarlsonR_pair_one_one (t + 1) hI hnI
  rw [add_sub_cancel_right, cpow_def_of_ne_zero I_ne_zero, cpow_def_of_ne_zero (neg_ne_zero.mpr
    I_ne_zero), log_I, log_neg_I] at h
  have e := exp_mul_I_sub_exp_neg_mul_I (Real.pi / 2 * (t + 1))
  rw [show Real.pi / 2 * (t + 1) = Real.pi * t / 2 + Real.pi / 2 by ring, sin_add_pi_div_two] at e
  rw [show (Real.pi / 2 * I * (t + 1)) = (Real.pi * t / 2 + Real.pi / 2) * I by ring,
    show -(Real.pi / 2) * I * (t + 1) = -(Real.pi * t / 2 + Real.pi / 2) * I by ring, e] at h
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  apply mul_left_cancel₀ h2I
  linear_combination -h

/-- `log (x²) = 2 log x` and `log (x w) = log x + log w` for `x, w` in the right half-plane. -/
theorem log_mul_of_re_pos {x w : ℂ} (hx : 0 < x.re) (hw : 0 < w.re) :
    log (x * w) = log x + log w := by
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hax := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have haw := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  exact (log_mul_eq_add_log_iff hx0 hw0).mpr
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- Products of two right half-plane numbers lie in the slit plane. -/
theorem mul_mem_slitPlane_of_re_pos {x w : ℂ} (hx : 0 < x.re) (hw : 0 < w.re) :
    x * w ∈ slitPlane := by
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  rw [← exp_log hx0, ← exp_log hw0, ← exp_add]
  apply exp_mem_slitPlane_of_abs_im_lt
  have hax := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have haw := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  rw [add_im, log_im, log_im, abs_lt]
  constructor <;> linarith

/-- **Exercise 6.8-6**: `R_{-1}(1, 1; x², y²) = R_{-1}(1, 1; x(x+y)/2, y(x+y)/2)` for `x, y` in
the right half-plane. -/
theorem regCarlsonR_pair_neg_one_sq {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonR (-1) (pair 1 1) (pair (x ^ 2) (y ^ 2)) =
      regCarlsonR (-1) (pair 1 1) (pair (x * ((x + y) / 2)) (y * ((x + y) / 2))) := by
  rcases eq_or_ne x y with rfl | hxy
  · congr 2 <;> ring
  have hw : 0 < ((x + y) / 2).re := by simp; linarith
  have hsq : ∀ z : ℂ, z ^ 2 = z * z := fun z => sq z
  have hx2 : x ^ 2 ∈ slitPlane := by rw [hsq]; exact mul_mem_slitPlane_of_re_pos hx hx
  have hy2 : y ^ 2 ∈ slitPlane := by rw [hsq]; exact mul_mem_slitPlane_of_re_pos hy hy
  have hxw := mul_mem_slitPlane_of_re_pos hx hw
  have hyw := mul_mem_slitPlane_of_re_pos hy hw
  have hxy0 : x + y ≠ 0 := fun h => by have := congrArg re h; simp at this; linarith
  have hd1 : x ^ 2 ≠ y ^ 2 := by
    intro h
    have : (x - y) * (x + y) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact hxy (sub_eq_zero.mp h0)
    · exact hxy0 h0
  have hw0 : (x + y) / 2 ≠ 0 := div_ne_zero hxy0 two_ne_zero
  have hd2 : x * ((x + y) / 2) ≠ y * ((x + y) / 2) := fun h =>
    hxy (mul_right_cancel₀ hw0 h)
  rw [regCarlsonR_pair_neg_one_one_one hx2 hy2 hd1, regCarlsonR_pair_neg_one_one_one hxw hyw hd2,
    hsq, hsq, log_mul_of_re_pos hx hx, log_mul_of_re_pos hy hy, log_mul_of_re_pos hx hw,
    log_mul_of_re_pos hy hw]
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  field_simp
  ring

/-- **Exercise 6.8-5, fifth relation**: `arctan z = z R_{-1}(1, 1; 1 + iz, 1 - iz)` for
`|Im z| < 1` (in particular for all real `z`). -/
theorem arctan_eq_mul_regCarlsonR {z : ℂ} (hz : |z.im| < 1) :
    arctan z = z * regCarlsonR (-1) (pair 1 1) (pair (1 + z * I) (1 - z * I)) := by
  have ha : 0 < (1 + z * I).re := by simp; linarith [(abs_lt.mp hz).2]
  have hb : 0 < (1 - z * I).re := by simp; linarith [(abs_lt.mp hz).1]
  have hb0 : 1 - z * I ≠ 0 := fun h => by simp [h] at hb
  have hbinv : 0 < (1 - z * I)⁻¹.re := by
    rw [inv_re]; exact div_pos hb (normSq_pos.mpr hb0)
  have hargb : (1 - z * I).arg ≠ Real.pi := by
    have := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb))
    linarith [Real.pi_pos]
  have hlog : log ((1 + z * I) / (1 - z * I)) = log (1 + z * I) - log (1 - z * I) := by
    rw [div_eq_mul_inv, log_mul_of_re_pos ha hbinv, log_inv _ hargb]; ring
  have h := regCarlsonR_pair_one_one_log (mem_slitPlane_iff.mpr (Or.inl ha))
    (mem_slitPlane_iff.mpr (Or.inl hb))
  rw [show 1 + z * I - (1 - z * I) = 2 * I * z by ring] at h
  rw [arctan, hlog, ← h]
  linear_combination (-(z * regCarlsonR (-1) (pair 1 1) (pair (1 + z * I) (1 - z * I)))) * I_sq

/-- **Exercise 6.9-16**: `arccos x = (1 - x²)^{1/2} R_C(x², 1)` for `0 < x < 1`. -/
theorem arccos_eq_mul_carlsonRC {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (Real.arccos x : ℂ) = (Real.sqrt (1 - x ^ 2) : ℝ) * carlsonRC (x ^ 2 : ℝ) 1 := by
  have h1 : 0 < x ^ 2 := by positivity
  have h2 : x ^ 2 < 1 := by nlinarith
  rw [show ((1 : ℂ)) = ((1 : ℝ) : ℂ) by simp, carlsonRC_of_lt h1 h2, div_one,
    Real.sqrt_sq hx.le]
  have : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hc : ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
  push_cast
  field_simp

/-- **Exercise 6.9-16**: `arctan x = x R_C(1, 1 + x²)` for all real `x`. -/
theorem arctan_eq_mul_carlsonRC (x : ℝ) :
    (Real.arctan x : ℂ) = x * carlsonRC 1 (1 + x ^ 2 : ℝ) := by
  have hpos : ∀ x : ℝ, 0 < x →
      (Real.arctan x : ℂ) = x * carlsonRC 1 (1 + x ^ 2 : ℝ) := by
    intro x hx
    have h2 : (1 : ℝ) < 1 + x ^ 2 := by nlinarith
    rw [show ((1 : ℂ)) = ((1 : ℝ) : ℂ) by simp, carlsonRC_of_lt one_pos h2,
      show 1 + x ^ 2 - 1 = x ^ 2 by ring, Real.sqrt_sq hx.le]
    have hs : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hz : 0 < Real.sqrt (1 / (1 + x ^ 2)) := Real.sqrt_pos.mpr (by positivity)
    rw [Real.arccos_eq_arctan hz]
    have hval : Real.sqrt (1 - Real.sqrt (1 / (1 + x ^ 2)) ^ 2) /
        Real.sqrt (1 / (1 + x ^ 2)) = x := by
      rw [Real.sq_sqrt (by positivity), show 1 - 1 / (1 + x ^ 2) = x ^ 2 / (1 + x ^ 2) by
        field_simp; ring, Real.sqrt_div' _ (by positivity), Real.sqrt_div' _ (by positivity),
        Real.sqrt_sq hx.le, Real.sqrt_one]
      field_simp
    rw [hval]
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast
    field_simp
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have := hpos (-x) (by linarith)
    rw [Real.arctan_neg, neg_sq] at this
    push_cast at this ⊢
    linear_combination -this
  · simp
  · exact hpos x hx

/-- **Exercise 6.9-16**: `arccot x = arctan (1/x) = R_C(x², x² + 1)` for `x > 0`. -/
theorem arctan_inv_eq_carlsonRC {x : ℝ} (hx : 0 < x) :
    (Real.arctan x⁻¹ : ℂ) = carlsonRC (x ^ 2 : ℝ) (x ^ 2 + 1 : ℝ) := by
  have h1 : 0 < x ^ 2 := by positivity
  rw [carlsonRC_of_lt h1 (by linarith), show x ^ 2 + 1 - x ^ 2 = 1 by ring, Real.sqrt_one,
    div_one]
  have hz : 0 < Real.sqrt (x ^ 2 / (x ^ 2 + 1)) := Real.sqrt_pos.mpr (by positivity)
  rw [Real.arccos_eq_arctan hz]
  congr 2
  rw [Real.sq_sqrt (by positivity), show 1 - x ^ 2 / (x ^ 2 + 1) = 1 / (x ^ 2 + 1) by
    field_simp; ring, Real.sqrt_div' _ (by positivity), Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq hx.le, Real.sqrt_one]
  have hs : 0 < Real.sqrt (x ^ 2 + 1) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- **Exercise 6.9-16**: `arsinh x = x R_C(1 + x², 1)` for all real `x`. -/
theorem arsinh_eq_mul_carlsonRC (x : ℝ) :
    (Real.arsinh x : ℂ) = x * carlsonRC (1 + x ^ 2 : ℝ) 1 := by
  have hpos : ∀ x : ℝ, 0 < x → (Real.arsinh x : ℂ) = x * carlsonRC (1 + x ^ 2 : ℝ) 1 := by
    intro x hx
    rw [show ((1 : ℂ)) = ((1 : ℝ) : ℂ) by simp, carlsonRC_of_gt one_pos (by nlinarith),
      show 1 + x ^ 2 - 1 = x ^ 2 by ring, Real.sqrt_sq hx.le, Real.sqrt_one, div_one,
      Real.arsinh, add_comm x]
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast
    field_simp
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have := hpos (-x) (by linarith)
    rw [Real.arsinh_neg, neg_sq] at this
    push_cast at this ⊢
    linear_combination -this
  · simp
  · exact hpos x hx

/-- **Exercise 6.9-16**: `arcosh x = (x² - 1)^{1/2} R_C(x², 1)` for `x > 1`. -/
theorem arcosh_eq_mul_carlsonRC {x : ℝ} (hx : 1 < x) :
    (Real.arcosh x : ℂ) = (Real.sqrt (x ^ 2 - 1) : ℝ) * carlsonRC (x ^ 2 : ℝ) 1 := by
  rw [show ((1 : ℂ)) = ((1 : ℝ) : ℂ) by simp, carlsonRC_of_gt one_pos (by nlinarith),
    Real.sqrt_sq (by linarith), Real.sqrt_one, div_one, Real.arcosh]
  have : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  have hc : ((Real.sqrt (x ^ 2 - 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
  push_cast
  field_simp

/-- **Exercise 6.9-16**: `artanh x = x R_C(1, 1 - x²)` for `0 < x < 1`. -/
theorem artanh_eq_mul_carlsonRC {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (Real.artanh x : ℂ) = x * carlsonRC 1 (1 - x ^ 2 : ℝ) := by
  have h1 : 0 < 1 - x ^ 2 := by nlinarith
  rw [show ((1 : ℂ)) = ((1 : ℝ) : ℂ) by simp, carlsonRC_of_gt h1 (by nlinarith),
    show 1 - (1 - x ^ 2) = x ^ 2 by ring, Real.sqrt_sq hx.le, Real.sqrt_one, Real.artanh]
  have hq : Real.sqrt ((1 + x) / (1 - x)) = (1 + x) / Real.sqrt (1 - x ^ 2) := by
    have hm : 0 < 1 - x := by linarith
    have hp : 0 < 1 + x := by linarith
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring, Real.sqrt_mul hm.le,
      Real.sqrt_div' _ hm.le]
    have h1' : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.mpr hm
    have h2' : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.mpr hp
    field_simp
    rw [Real.sq_sqrt hp.le]
  rw [hq]
  have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

/-- **Exercise 6.9-16**: `arcoth x = ½ log ((x + 1)/(x - 1)) = R_C(x², x² - 1)` for `x > 1`. -/
theorem half_log_eq_carlsonRC {x : ℝ} (hx : 1 < x) :
    ((1 / 2 * Real.log ((x + 1) / (x - 1)) : ℝ) : ℂ) = carlsonRC (x ^ 2 : ℝ) (x ^ 2 - 1 : ℝ) := by
  have h1 : 0 < x ^ 2 - 1 := by nlinarith
  rw [carlsonRC_of_gt h1 (by linarith), Real.sqrt_sq (by linarith),
    show x ^ 2 - (x ^ 2 - 1) = 1 by ring, Real.sqrt_one, div_one]
  congr 1
  have hm : 0 < x - 1 := by linarith
  have hp : 0 < x + 1 := by linarith
  rw [show x + 1 = Real.sqrt ((x + 1) ^ 2) by rw [Real.sqrt_sq hp.le],
    show x ^ 2 - 1 = (x + 1) * (x - 1) by ring, Real.sqrt_mul hp.le, Real.sqrt_sq hp.le]
  have hsm : 0 < Real.sqrt (x - 1) := Real.sqrt_pos.mpr hm
  have hsp : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.mpr hp
  rw [show (x + 1) / (Real.sqrt (x + 1) * Real.sqrt (x - 1)) =
      Real.sqrt ((x + 1) / (x - 1)) by
    rw [Real.sqrt_div' _ hm.le]
    field_simp
    rw [Real.sq_sqrt hp.le],
    Real.log_sqrt (div_pos hp hm).le]
  ring

/-- For real `0 < x < π/2`, `sin x · R_C(cos² x, 1) = x`. -/
theorem sin_mul_carlsonRC_cos_sq_of_real {x : ℝ} (hx0 : 0 < x) (hx1 : x < Real.pi / 2) :
    (Real.sin x : ℂ) * carlsonRC (Real.cos x ^ 2 : ℝ) 1 = x := by
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos])
  have hc1 : Real.cos x ^ 2 < 1 := by nlinarith [Real.sin_sq_add_cos_sq x]
  rw [show ((1 : ℂ)) = ((1 : ℝ) : ℂ) by simp, carlsonRC_of_lt (by positivity) hc1, div_one,
    Real.sqrt_sq hc.le, Real.arccos_cos hx0.le (by linarith [Real.pi_pos]),
    show 1 - Real.cos x ^ 2 = Real.sin x ^ 2 by nlinarith [Real.sin_sq_add_cos_sq x],
    Real.sqrt_sq hs.le]
  have : (Real.sin x : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [ofReal_div]
  field_simp

/-- `cos θ` lies in the right half-plane for `|Re θ| < π/2`. -/
theorem re_cos_pos {θ : ℂ} (hθ : |θ.re| < Real.pi / 2) : 0 < (Complex.cos θ).re := by
  have h : (Complex.cos θ).re = Real.cos θ.re * Real.cosh θ.im := by
    conv_lhs => rw [← Complex.re_add_im θ]
    rw [Complex.cos_add_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cosh_ofReal_re, Complex.sin_ofReal_re,
      Complex.sinh_ofReal_im, Complex.sin_ofReal_im, Complex.cos_ofReal_im, Complex.cosh_ofReal_im]
  rw [h]
  exact mul_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hθ).1],
    (abs_lt.mp hθ).2⟩) (Real.cosh_pos _)

/-- **Exercise 6.9-17, second relation**: `sin θ · R_C(cos² θ, 1) = θ` for `|Re θ| < π/2`;
equivalently `θ/sin θ = R_C(cos² θ, 1)` when `sin θ ≠ 0`. -/
theorem sin_mul_carlsonRC_cos_sq {θ : ℂ} (hθ : |θ.re| < Real.pi / 2) :
    Complex.sin θ * carlsonRC (Complex.cos θ ^ 2) 1 = θ := by
  set U : Set ℂ := Complex.reLm ⁻¹' Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  have hUmem : ∀ θ : ℂ, θ ∈ U ↔ |θ.re| < Real.pi / 2 := fun θ => by
    simp [U, abs_lt]
  have hUc : Convex ℝ U := (convex_Ioo _ _).is_linear_preimage Complex.reLm.isLinear
  replace hθ : θ ∈ U := (hUmem θ).mpr hθ
  have hslit : ∀ θ ∈ U, Complex.cos θ ^ 2 ∈ slitPlane := fun θ hθ => by
    have hθ' := (hUmem θ).mp hθ
    rw [sq]; exact mul_mem_slitPlane_of_re_pos (re_cos_pos hθ') (re_cos_pos hθ')
  have hL : AnalyticOnNhd ℂ (fun θ => Complex.sin θ * carlsonRC (Complex.cos θ ^ 2) 1) U := by
    intro θ hθ
    refine (Complex.differentiable_sin.analyticAt θ).mul ?_
    unfold carlsonRC carlsonR
    refine analyticAt_const.mul ?_
    refine analyticAt_regCarlsonR_comp (t := fun _ => (-1 / 2 : ℂ))
      (b := fun _ => pair (1 / 2 : ℂ) 1) (z := fun θ => pair (Complex.cos θ ^ 2) 1)
      analyticAt_const analyticAt_const (AnalyticAt.pi fun i => ?_) ?_
    · fin_cases i
      · exact ((Complex.differentiable_cos.pow 2).analyticAt θ)
      · exact analyticAt_const
    · intro i; fin_cases i
      · exact hslit θ hθ
      · exact one_mem_slitPlane
  have hR : AnalyticOnNhd ℂ (fun θ : ℂ => θ) U := fun θ _ => analyticAt_id
  have h0 : (0 : ℂ) ∈ U := (hUmem 0).mpr (by simp [Real.pi_pos])
  have hfreq : ∃ᶠ θ in nhdsWithin (0 : ℂ) {0}ᶜ,
      Complex.sin θ * carlsonRC (Complex.cos θ ^ 2) 1 = θ := by
    have ht : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (nhdsWithin 0 {0}ᶜ) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have := (continuous_ofReal.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat
          |>.comp (tendsto_add_atTop_nat 1))
        rw [ofReal_zero] at this
        refine this.congr fun n => ?_
        simp [Function.comp_def]; ring_nf
      · exact Eventually.of_forall fun n => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_eq_zero]; positivity
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    have hx0 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hx1 : 1 / ((n : ℝ) + 2) < Real.pi / 2 := by
      rw [div_lt_div_iff₀ (by positivity) two_pos]
      nlinarith [Real.pi_gt_three, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h := sin_mul_carlsonRC_cos_sq_of_real hx0 hx1
    rw [← ofReal_sin, ← ofReal_cos]
    exact_mod_cast h
  exact hL.eqOn_of_preconnected_of_frequently_eq hR hUc.isPreconnected h0 hfreq hθ

/-- **Exercise 6.9-17**: `π = 4 R_C(1, 2) = 6 R_C(3, 4)`. -/
theorem pi_eq_four_mul_carlsonRC :
    (Real.pi : ℂ) = 4 * carlsonRC 1 2 ∧ (Real.pi : ℂ) = 6 * carlsonRC 3 4 := by
  constructor
  · have h := carlsonRC_of_lt (x := 1) (y := 2) one_pos (by norm_num)
    rw [show (1 : ℝ) / 2 = (Real.sqrt 2 / 2) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num, Real.sqrt_sq (by positivity),
      ← Real.cos_pi_div_four, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos]),
      show (2 : ℝ) - 1 = 1 by norm_num, Real.sqrt_one, div_one] at h
    push_cast at h; rw [h]; ring
  · have h := carlsonRC_of_lt (x := 3) (y := 4) (by norm_num) (by norm_num)
    rw [show (3 : ℝ) / 4 = (Real.sqrt 3 / 2) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num, Real.sqrt_sq (by positivity),
      ← Real.cos_pi_div_six, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos]),
      show (4 : ℝ) - 3 = 1 by norm_num, Real.sqrt_one, div_one] at h
    push_cast at h; rw [h]; ring

/-- **Exercise 6.9-17**: `θ = R_C(cot² θ, csc² θ)` for `0 < θ < π/2`. -/
theorem carlsonRC_cot_sq_csc_sq {x : ℝ} (hx0 : 0 < x) (hx1 : x < Real.pi / 2) :
    carlsonRC ((Real.cos x / Real.sin x) ^ 2 : ℝ) ((1 / Real.sin x) ^ 2 : ℝ) = x := by
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos])
  have hsc := Real.sin_sq_add_cos_sq x
  have hlt : (Real.cos x / Real.sin x) ^ 2 < (1 / Real.sin x) ^ 2 := by
    rw [div_pow, div_pow]; gcongr; nlinarith
  rw [carlsonRC_of_lt (by positivity) hlt]
  have h1 : (1 / Real.sin x) ^ 2 - (Real.cos x / Real.sin x) ^ 2 = 1 := by
    field_simp; linarith
  have h2 : (Real.cos x / Real.sin x) ^ 2 / (1 / Real.sin x) ^ 2 = Real.cos x ^ 2 := by
    field_simp
  rw [h1, h2, Real.sqrt_one, div_one, Real.sqrt_sq hc.le,
    Real.arccos_cos hx0.le (by linarith [Real.pi_pos])]

/-- **Exercise 6.9-17**: `φ = R_C(coth² φ, csch² φ)` for real `φ > 0`. -/
theorem carlsonRC_coth_sq_csch_sq {x : ℝ} (hx : 0 < x) :
    carlsonRC ((Real.cosh x / Real.sinh x) ^ 2 : ℝ) ((1 / Real.sinh x) ^ 2 : ℝ) = x := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  have hcs := Real.cosh_sq_sub_sinh_sq x
  have hlt : (1 / Real.sinh x) ^ 2 < (Real.cosh x / Real.sinh x) ^ 2 := by
    rw [div_pow, div_pow]; gcongr; nlinarith
  rw [carlsonRC_of_gt (by positivity) hlt]
  have h1 : (Real.cosh x / Real.sinh x) ^ 2 - (1 / Real.sinh x) ^ 2 = 1 := by
    field_simp; linarith
  rw [h1, Real.sqrt_one, div_one, Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
  rw [show (Real.cosh x / Real.sinh x + 1) / (1 / Real.sinh x) = Real.cosh x + Real.sinh x by
    field_simp, Real.cosh_add_sinh, Real.log_exp]

/-- `Re e^{iθ} > 0` for `|Re θ| < π/2`. -/
theorem re_exp_mul_I_pos {θ : ℂ} (hθ : |θ.re| < Real.pi / 2) : 0 < (exp (θ * I)).re := by
  rw [exp_re]
  simp only [mul_re, I_re, mul_zero, I_im, mul_one, zero_sub, mul_im, add_zero]
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hθ).1],
    (abs_lt.mp hθ).2⟩)

/-- **Exercise 6.9-17, first relation**: `sin tθ/(t sin θ) = R_{(t-1)/2}(½ + t/2, 1 - t/2;
cos² θ, 1)` for `|Re θ| < π/2`, `t ≠ 0` and `sin θ ≠ 0`. It is (6.8-5) followed by the first
quadratic transformation. -/
theorem carlsonR_cos_sq_eq_sin_div {t θ : ℂ} (hθ : |θ.re| < Real.pi / 2) (ht : t ≠ 0)
    (hs : sin θ ≠ 0) :
    carlsonR ((t - 1) / 2) (pair (1 / 2 + t / 2) (1 - t / 2)) (pair (cos θ ^ 2) 1) =
      sin (t * θ) / (t * sin θ) := by
  have hθ' : |θ.re| < Real.pi := hθ.trans (by linarith [Real.pi_pos])
  have h1 := regCarlsonR_pair_one_one_exp hθ' ht hs
  have hx : 0 < (exp (θ * I)).re := re_exp_mul_I_pos hθ
  have hy : 0 < (exp (-θ * I)).re := re_exp_mul_I_pos (θ := -θ) (by simpa using hθ)
  have hq := regRSlit_firstQuadratic ((t - 1) / 2) 1 _ _ hx hy
  have hAM : arithmeticMeanSq (exp (θ * I)) (exp (-θ * I)) = cos θ ^ 2 := by
    rw [arithmeticMeanSq, Complex.cos]
  have hGM : geometricMeanSq (exp (θ * I)) (exp (-θ * I)) = 1 := by
    rw [geometricMeanSq, ← exp_add]; ring_nf; exact exp_zero
  rw [show 2 * ((t - 1) / 2) = t - 1 by ring, hAM, hGM, show (1 : ℂ) + (t - 1) / 2 = 1 / 2 + t / 2
    by ring, show (1 : ℂ) / 2 - (t - 1) / 2 = 1 - t / 2 by ring, h1] at hq
  rw [hq]
  unfold carlsonR quadraticGammaRatio
  have hsum : ∑ i, pair (1 / 2 + t / 2) (1 - t / 2) i = 3 / 2 := by
    simp only [Fin.sum_univ_two, pair_zero, pair_one]; ring
  rw [hsum, show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num),
    Gamma_one_half_eq, show (1 : ℂ) - 2 * 1 = -1 by norm_num, cpow_neg_one, Gamma_one]
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsq : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; norm_num
  rw [hsq]
  field_simp

/-- **Exercise 6.9-17**, `π = 2 R_C(0, 1)`, as the boundary value at the node `0`:
`2 R_C(x, 1) → π` as `x → 0⁺`. -/
theorem tendsto_two_mul_carlsonRC_zero :
    Tendsto (fun x : ℝ => 2 * (carlsonRC x 1).re) (nhdsWithin 0 (Set.Ioi 0)) (nhds Real.pi) := by
  have hc : ContinuousAt (fun x : ℝ => 2 * (Real.arccos (Real.sqrt x) / Real.sqrt (1 - x))) 0 :=
    by fun_prop (disch := simp)
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [Real.sqrt_zero, Real.arccos_zero, sub_zero, Real.sqrt_one, div_one] at h
  rw [show 2 * (Real.pi / 2) = Real.pi by ring] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x ⟨hx0, hx1⟩
  rw [show ((1 : ℂ)) = ((1 : ℝ) : ℂ) by norm_num, carlsonRC_of_lt hx0 hx1, ofReal_re, div_one]

/-- Real and imaginary parts of `sin` and `cos`. -/
theorem sin_cos_re_im (θ : ℂ) :
    (sin θ).re = Real.sin θ.re * Real.cosh θ.im ∧ (sin θ).im = Real.cos θ.re * Real.sinh θ.im ∧
      (cos θ).re = Real.cos θ.re * Real.cosh θ.im ∧
        (cos θ).im = -(Real.sin θ.re * Real.sinh θ.im) := by
  have h : θ = θ.re + θ.im * I := (re_add_im θ).symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [h]
  · rw [Complex.sin_add_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cosh_ofReal_re, Complex.sin_ofReal_re,
      Complex.sinh_ofReal_im, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.cosh_ofReal_im, Complex.sinh_ofReal_re]
  · rw [Complex.sin_add_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cosh_ofReal_re, Complex.sin_ofReal_re,
      Complex.sinh_ofReal_im, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.cosh_ofReal_im, Complex.sinh_ofReal_re]
  · rw [Complex.cos_add_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cosh_ofReal_re, Complex.sin_ofReal_re,
      Complex.sinh_ofReal_im, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.cosh_ofReal_im, Complex.sinh_ofReal_re]
  · rw [Complex.cos_add_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cosh_ofReal_re, Complex.sin_ofReal_re,
      Complex.sinh_ofReal_im, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.cosh_ofReal_im, Complex.sinh_ofReal_re]

/-- Real and imaginary parts of `sinh` and `cosh`. -/
theorem sinh_cosh_re_im (φ : ℂ) :
    (sinh φ).re = Real.sinh φ.re * Real.cos φ.im ∧ (sinh φ).im = Real.cosh φ.re * Real.sin φ.im ∧
      (cosh φ).re = Real.cosh φ.re * Real.cos φ.im ∧
        (cosh φ).im = Real.sinh φ.re * Real.sin φ.im := by
  have h : φ = φ.re + φ.im * I := (re_add_im φ).symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [h]
  · rw [sinh_add, sinh_mul_I, cosh_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cosh_ofReal_re, Complex.sin_ofReal_re,
      Complex.sinh_ofReal_im, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.cosh_ofReal_im, Complex.sinh_ofReal_re]
  · rw [sinh_add, sinh_mul_I, cosh_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cosh_ofReal_re, Complex.sin_ofReal_re,
      Complex.sinh_ofReal_im, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.cosh_ofReal_im, Complex.sinh_ofReal_re]
  · rw [cosh_add, sinh_mul_I, cosh_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cosh_ofReal_re, Complex.sin_ofReal_re,
      Complex.sinh_ofReal_im, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.cosh_ofReal_im, Complex.sinh_ofReal_re]
  · rw [cosh_add, sinh_mul_I, cosh_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cosh_ofReal_re, Complex.sin_ofReal_re,
      Complex.sinh_ofReal_im, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.cosh_ofReal_im, Complex.sinh_ofReal_re]

/-- Real points `x ∈ (a, a + ε)` accumulate at `a` in the punctured complex neighbourhood. -/
theorem frequently_ofReal_Ioo {a ε : ℝ} (hε : 0 < ε) {P : ℂ → Prop}
    (h : ∀ x : ℝ, a < x → x < a + ε → P x) : ∃ᶠ z in nhdsWithin (a : ℂ) {(a : ℂ)}ᶜ, P z := by
  have ht : Tendsto (fun n : ℕ => ((a + ε / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop
      (nhdsWithin (a : ℂ) {(a : ℂ)}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h0 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 2)) atTop (nhds 0) := by
        have := (tendsto_const_div_atTop_nhds_zero_nat ε).comp (tendsto_add_atTop_nat 2)
        refine this.congr fun n => ?_
        simp
      have h1 : Tendsto (fun n : ℕ => a + ε / ((n : ℝ) + 2)) atTop (nhds a) := by
        simpa using (tendsto_const_nhds (x := a)).add h0
      exact (continuous_ofReal.tendsto a).comp h1
    · exact Eventually.of_forall fun n => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h0
        have h' : a + ε / ((n : ℝ) + 2) = a := by exact_mod_cast h0
        have : 0 < ε / ((n : ℝ) + 2) := by positivity
        linarith
  refine ht.frequently (Frequently.of_forall fun n => h _ ?_ ?_)
  · have : 0 < ε / ((n : ℝ) + 2) := by positivity
    linarith
  · have : ε / ((n : ℝ) + 2) < ε := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith

/-- `Re (u / v) > 0` from the numerator of `u v̄`. -/
theorem re_div_pos {u v : ℂ} (hv : v ≠ 0) (h : 0 < u.re * v.re + u.im * v.im) :
    0 < (u / v).re := by
  rw [div_re]
  have hn : 0 < normSq v := normSq_pos.mpr hv
  rw [← add_div]; exact div_pos h hn

/-- **Exercise 6.9-17**, `θ = R_C(cot² θ, csc² θ)` for `0 < Re θ < π/2`. Both sides cannot agree on
`Re θ < 0`: the right side is even in `θ`. -/
theorem carlsonRC_cot_sq_csc_sq_complex {θ : ℂ} (h0 : 0 < θ.re) (h1 : θ.re < Real.pi / 2) :
    carlsonRC ((cos θ / sin θ) ^ 2) ((1 / sin θ) ^ 2) = θ := by
  set U : Set ℂ := Complex.reLm ⁻¹' Set.Ioo 0 (Real.pi / 2)
  have hU : ∀ θ : ℂ, θ ∈ U ↔ 0 < θ.re ∧ θ.re < Real.pi / 2 := fun θ => by simp [U]
  have hUc : Convex ℝ U := (convex_Ioo _ _).is_linear_preimage Complex.reLm.isLinear
  have hfacts : ∀ θ ∈ U, sin θ ≠ 0 ∧ (cos θ / sin θ) ^ 2 ∈ slitPlane ∧
      (1 / sin θ) ^ 2 ∈ slitPlane := fun θ hθ => by
    obtain ⟨a0, a1⟩ := (hU θ).mp hθ
    obtain ⟨hsr, hsi, hcr, hci⟩ := sin_cos_re_im θ
    have hsx : 0 < Real.sin θ.re := Real.sin_pos_of_pos_of_lt_pi a0 (by linarith [Real.pi_pos])
    have hcx : 0 < Real.cos θ.re := Real.cos_pos_of_mem_Ioo ⟨by linarith, a1⟩
    have hsre : 0 < (sin θ).re := by rw [hsr]; exact mul_pos hsx (Real.cosh_pos _)
    have hs0 : sin θ ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
    have hcot : 0 < (cos θ / sin θ).re := by
      refine re_div_pos hs0 ?_
      rw [hsr, hsi, hcr, hci]
      have := Real.cosh_sq_sub_sinh_sq θ.im
      nlinarith [mul_pos hsx hcx]
    have hinv : 0 < (1 / sin θ).re := by
      refine re_div_pos hs0 ?_; simpa using hsre
    exact ⟨hs0, by rw [sq]; exact mul_mem_slitPlane_of_re_pos hcot hcot,
      by rw [sq]; exact mul_mem_slitPlane_of_re_pos hinv hinv⟩
  have hL : AnalyticOnNhd ℂ (fun θ => carlsonRC ((cos θ / sin θ) ^ 2) ((1 / sin θ) ^ 2)) U := by
    intro θ hθ
    obtain ⟨hs0, hm1, hm2⟩ := hfacts θ hθ
    unfold carlsonRC carlsonR
    refine analyticAt_const.mul ?_
    refine analyticAt_regCarlsonR_comp (t := fun _ => (-1 / 2 : ℂ))
      (b := fun _ => pair (1 / 2 : ℂ) 1)
      (z := fun θ => pair ((cos θ / sin θ) ^ 2) ((1 / sin θ) ^ 2))
      analyticAt_const analyticAt_const (AnalyticAt.pi fun i => ?_) ?_
    · fin_cases i
      · exact (((Complex.differentiable_cos.analyticAt θ).div
          (Complex.differentiable_sin.analyticAt θ) hs0).pow 2)
      · exact ((analyticAt_const.div (Complex.differentiable_sin.analyticAt θ) hs0).pow 2)
    · intro i; fin_cases i
      · exact hm1
      · exact hm2
  have hR : AnalyticOnNhd ℂ (fun θ : ℂ => θ) U := fun θ _ => analyticAt_id
  have hpt : ((Real.pi / 4 : ℝ) : ℂ) ∈ U :=
    (hU _).mpr (by simp; constructor <;> linarith [Real.pi_pos])
  have hfreq : ∃ᶠ θ in nhdsWithin ((Real.pi / 4 : ℝ) : ℂ) {((Real.pi / 4 : ℝ) : ℂ)}ᶜ,
      carlsonRC ((cos θ / sin θ) ^ 2) ((1 / sin θ) ^ 2) = θ := by
    refine frequently_ofReal_Ioo (ε := Real.pi / 8) (by positivity) fun x hx0 hx1 => ?_
    have h := carlsonRC_cot_sq_csc_sq (x := x) (by linarith [Real.pi_pos]) (by linarith)
    exact_mod_cast h
  exact hL.eqOn_of_preconnected_of_frequently_eq hR hUc.isPreconnected hpt hfreq
    ((hU θ).mpr ⟨h0, h1⟩)

/-- **Exercise 6.9-17**, `φ = R_C(coth² φ, csch² φ)` for `Re φ > 0` and `|Im φ| < π/2`. Both sides
cannot agree on `Re φ < 0`: the right side is even in `φ`. -/
theorem carlsonRC_coth_sq_csch_sq_complex {φ : ℂ} (h0 : 0 < φ.re) (h1 : |φ.im| < Real.pi / 2) :
    carlsonRC ((cosh φ / sinh φ) ^ 2) ((1 / sinh φ) ^ 2) = φ := by
  set U : Set ℂ := Complex.reLm ⁻¹' Set.Ioi 0 ∩ Complex.imLm ⁻¹' Set.Ioo (-(Real.pi / 2))
    (Real.pi / 2)
  have hU : ∀ φ : ℂ, φ ∈ U ↔ 0 < φ.re ∧ |φ.im| < Real.pi / 2 := fun φ => by
    simp [U, abs_lt]
  have hUc : Convex ℝ U := ((convex_Ioi _).is_linear_preimage Complex.reLm.isLinear).inter
    ((convex_Ioo _ _).is_linear_preimage Complex.imLm.isLinear)
  have hfacts : ∀ φ ∈ U, sinh φ ≠ 0 ∧ (cosh φ / sinh φ) ^ 2 ∈ slitPlane ∧
      (1 / sinh φ) ^ 2 ∈ slitPlane := fun φ hφ => by
    obtain ⟨a0, a1⟩ := (hU φ).mp hφ
    obtain ⟨hsr, hsi, hcr, hci⟩ := sinh_cosh_re_im φ
    have hsx : 0 < Real.sinh φ.re := Real.sinh_pos_iff.mpr a0
    have hcy : 0 < Real.cos φ.im := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp a1).1],
      (abs_lt.mp a1).2⟩
    have hsre : 0 < (sinh φ).re := by rw [hsr]; exact mul_pos hsx hcy
    have hs0 : sinh φ ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
    have hcoth : 0 < (cosh φ / sinh φ).re := by
      refine re_div_pos hs0 ?_
      rw [hsr, hsi, hcr, hci]
      have := Real.sin_sq_add_cos_sq φ.im
      nlinarith [mul_pos hsx (Real.cosh_pos φ.re)]
    have hinv : 0 < (1 / sinh φ).re := by
      refine re_div_pos hs0 ?_; simpa using hsre
    exact ⟨hs0, by rw [sq]; exact mul_mem_slitPlane_of_re_pos hcoth hcoth,
      by rw [sq]; exact mul_mem_slitPlane_of_re_pos hinv hinv⟩
  have hL : AnalyticOnNhd ℂ (fun φ => carlsonRC ((cosh φ / sinh φ) ^ 2) ((1 / sinh φ) ^ 2)) U := by
    intro φ hφ
    obtain ⟨hs0, hm1, hm2⟩ := hfacts φ hφ
    unfold carlsonRC carlsonR
    refine analyticAt_const.mul ?_
    refine analyticAt_regCarlsonR_comp (t := fun _ => (-1 / 2 : ℂ))
      (b := fun _ => pair (1 / 2 : ℂ) 1)
      (z := fun φ => pair ((cosh φ / sinh φ) ^ 2) ((1 / sinh φ) ^ 2))
      analyticAt_const analyticAt_const (AnalyticAt.pi fun i => ?_) ?_
    · fin_cases i
      · exact (((Complex.differentiable_cosh.analyticAt φ).div
          (Complex.differentiable_sinh.analyticAt φ) hs0).pow 2)
      · exact ((analyticAt_const.div (Complex.differentiable_sinh.analyticAt φ) hs0).pow 2)
    · intro i; fin_cases i
      · exact hm1
      · exact hm2
  have hR : AnalyticOnNhd ℂ (fun φ : ℂ => φ) U := fun φ _ => analyticAt_id
  have hpt : ((1 : ℝ) : ℂ) ∈ U := (hU _).mpr (by simp [Real.pi_pos])
  have hfreq : ∃ᶠ φ in nhdsWithin ((1 : ℝ) : ℂ) {((1 : ℝ) : ℂ)}ᶜ,
      carlsonRC ((cosh φ / sinh φ) ^ 2) ((1 / sinh φ) ^ 2) = φ := by
    refine frequently_ofReal_Ioo (ε := 1) one_pos fun x hx0 hx1 => ?_
    have h := carlsonRC_coth_sq_csch_sq (x := x) (by linarith)
    exact_mod_cast h
  exact hL.eqOn_of_preconnected_of_frequently_eq hR hUc.isPreconnected hpt hfreq
    ((hU φ).mpr ⟨h0, h1⟩)

end TwoVariable

end Carlson
