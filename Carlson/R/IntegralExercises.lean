/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.IntegralEvaluation
public import Carlson.TwoVariable.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Integral exercises of Carlson's Chapter 8

Formula 8.1-1 on a real segment `(p, q)`, combined with the substitutions `s = t²` and
`s = sin² θ`, evaluates Carlson's Exercises 8.1-1, 8.1-2, 8.1-3 and 8.1-5 in terms of the
regularized R-function `R̃ = R/Γ(c)`. The affine factors are required to stay in the slit plane
on the segment, so that the principal powers are Carlson's continuous ones.

## Main results

* `Carlson.integral_Ioo_real_segment_eq_regCarlsonR`: Formula 8.1-1 on a real segment.
* `Carlson.integral_sq_sub_cpow_mul_cpow`: Exercise 8.1-1.
* `Carlson.integral_one_sub_sq_sin_cpow`: Exercise 8.1-2.
* `Carlson.integral_sin_cos_cpow`: Exercise 8.1-3.
* `Carlson.integral_cpow_mul_affine_sq_cpow`: Exercise 8.1-5.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.1.
-/

open Complex MeasureTheory Set
open scoped Real

@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- The affine substitution `t = p + u (q - p)` for a complex-valued integrand on `(p, q)`. -/
theorem integral_Ioo_eq_integral_Ioo_unit (f : ℝ → ℂ) {p q : ℝ} (h : p < q) :
    ∫ t in Ioo p q, f t = ∫ u in Ioo (0 : ℝ) 1, ((q - p : ℝ) : ℂ) * f (p + u * (q - p)) := by
  have hd : 0 < q - p := by linarith
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
    (f := fun u => p + u * (q - p)) (f' := fun _ => q - p)
    (fun u _ => (((hasDerivAt_id u).mul_const (q - p)).const_add p).hasDerivWithinAt.congr_deriv
      (by simp)) (fun a _ b _ hab => by
        have : a * (q - p) = b * (q - p) := by linarith [hab]
        exact mul_right_cancel₀ hd.ne' this) f
  rw [show (fun u => p + u * (q - p)) '' Ioo (0 : ℝ) 1 = Ioo p q by
    ext t; simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩; constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      exact ⟨(t - p) / (q - p), ⟨div_pos (by linarith) hd, (div_lt_one hd).mpr (by linarith)⟩,
        by field_simp; ring⟩] at hsub
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
  simp [abs_of_pos hd, Complex.real_smul]

/-- **Formula 8.1-1 on a real segment**: for real `p < q`, `re a, re a' > 0`,
`a + a' = ∑ bᵢ`, and affine factors `zᵢ + wᵢ t` in the slit plane for `t ∈ [p, q]`,
`∫_p^q (t - p)^{a-1} (q - t)^{a'-1} ∏ (zᵢ + wᵢ t)^{-bᵢ} dt =
Γ(a) Γ(a') (q - p)^{a+a'-1} ∏ (zᵢ + wᵢ p)^{-bᵢ} R̃_{-a}(b; (z + wq)/(z + wp))`. -/
theorem integral_Ioo_real_segment_eq_regCarlsonR {a a' : ℂ} {b z w : ι → ℂ} {p q : ℝ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a + a' = ∑ i, b i) (hpq : p < q)
    (hseg : ∀ i, ∀ t ∈ Icc p q, z i + w i * (t : ℂ) ∈ slitPlane) :
    ∫ t in Ioo p q, ((t - p : ℝ) : ℂ) ^ (a - 1) * ((q - t : ℝ) : ℂ) ^ (a' - 1) *
        ∏ i, (z i + w i * (t : ℂ)) ^ (-b i) =
      Gamma a * Gamma a' * ((q - p : ℝ) : ℂ) ^ (a + a' - 1) *
        (∏ i, (z i + w i * (p : ℂ)) ^ (-b i)) *
          regCarlsonR (-a) b (fun i => (z i + w i * (q : ℂ)) / (z i + w i * (p : ℂ))) := by
  have hseg' : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, z i + w i * ((p : ℂ) + u * ((q : ℂ) - p)) ∈ slitPlane := by
    intro i u hu
    have ht : p + u * (q - p) ∈ Icc p q := ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
    have := hseg i _ ht
    push_cast at this
    exact this
  have H := integral_segment_eq_regCarlsonR ha ha' hsum
    (show (p : ℂ) ≠ q by exact_mod_cast hpq.ne) hseg'
  rw [integral_Ioo_eq_integral_Ioo_unit _ hpq, integral_const_mul]
  push_cast at H ⊢
  rw [← H]

/-- The substitution `s = t²` on a positive interval. -/
theorem integral_Ioo_sq_eq (G : ℝ → ℂ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    ∫ s in Ioo (x ^ 2) (y ^ 2), G s = ∫ t in Ioo x y, ((2 * t : ℝ) : ℂ) * G (t ^ 2) := by
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Ioo x y) measurableSet_Ioo
    (f := fun t => t ^ 2) (f' := fun t => 2 * t)
    (fun t _ => ((hasDerivAt_pow 2 t).hasDerivWithinAt).congr_deriv (by ring))
    (fun a ha b hb hab => by
      have h1 : 0 < a := lt_of_le_of_lt hx ha.1
      have h2 : 0 < b := lt_of_le_of_lt hx hb.1
      exact (pow_left_inj₀ h1.le h2.le two_ne_zero).mp hab) G
  rw [show (fun t : ℝ => t ^ 2) '' Ioo x y = Ioo (x ^ 2) (y ^ 2) by
    ext s; simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨pow_lt_pow_left₀ h1 hx two_ne_zero,
        pow_lt_pow_left₀ h2 (hx.trans h1.le) two_ne_zero⟩
    · rintro ⟨h1, h2⟩
      have hs : 0 ≤ s := (sq_nonneg x).trans h1.le
      refine ⟨Real.sqrt s, ⟨?_, ?_⟩, Real.sq_sqrt hs⟩
      · rw [← Real.sqrt_sq hx]; exact Real.sqrt_lt_sqrt (sq_nonneg x) h1
      · rw [← Real.sqrt_sq (hx.trans hxy.le)]; exact Real.sqrt_lt_sqrt hs h2] at hsub
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := lt_of_le_of_lt hx ht.1
  simp [abs_of_pos ht0, Complex.real_smul]

/-- `(t²)^w = t^{2w}` for real `t > 0`. -/
theorem ofReal_sq_cpow {t : ℝ} (ht : 0 < t) (w : ℂ) :
    ((t : ℂ) ^ 2) ^ w = (t : ℂ) ^ (2 * w) := by
  rw [← cpow_natCast, ← cpow_mul]
  · push_cast; ring_nf
  · rw [← ofReal_log ht.le]; simp [Real.pi_pos]
  · rw [← ofReal_log ht.le]; simp [Real.pi_pos.le]

/-- **Exercise 8.1-5**: for real `x > 0`, `re α > 0`, and `A + Bs`, `C + Ds` in the slit plane for
`s ∈ [0, x²]`,
`∫₀^x t^{2α-1} (A + Bt²)^β (C + Dt²)^δ dt =
(1/2) Γ(α) x^{2α} A^β C^δ R̃_{-α}(-β, -δ, 1 + α + β + δ; (A + Bx²)/A, (C + Dx²)/C, 1)`.
With `R = Γ(1 + α) R̃` this is Carlson's `x^{2α}/(2α) A^β C^δ R_{-α}(…)`. -/
theorem integral_cpow_mul_affine_sq_cpow {α β δ A B C D : ℂ} {x : ℝ} (hx : 0 < x)
    (hα : 0 < α.re) (hA : ∀ s ∈ Icc (0 : ℝ) (x ^ 2), A + B * (s : ℂ) ∈ slitPlane)
    (hC : ∀ s ∈ Icc (0 : ℝ) (x ^ 2), C + D * (s : ℂ) ∈ slitPlane) :
    ∫ t in Ioo 0 x, (t : ℂ) ^ (2 * α - 1) * (A + B * (t : ℂ) ^ 2) ^ β * (C + D * (t : ℂ) ^ 2) ^ δ =
      1 / 2 * Gamma α * ((x ^ 2 : ℝ) : ℂ) ^ α * A ^ β * C ^ δ *
        regCarlsonR (-α) ![-β, -δ, 1 + α + β + δ]
          ![(A + B * (x ^ 2 : ℝ)) / A, (C + D * (x ^ 2 : ℝ)) / C, 1] := by
  set G : ℝ → ℂ := fun s => ((s - 0 : ℝ) : ℂ) ^ (α - 1) * ((x ^ 2 - s : ℝ) : ℂ) ^ ((1 : ℂ) - 1) *
    ∏ i, (![A, C, 1] i + ![B, D, 0] i * (s : ℂ)) ^ (-![-β, -δ, 1 + α + β + δ] i)
  have hseg : ∀ i, ∀ s ∈ Icc (0 : ℝ) (x ^ 2),
      ![A, C, 1] i + ![B, D, 0] i * (s : ℂ) ∈ slitPlane := by
    intro i s hs
    fin_cases i
    · exact hA s hs
    · exact hC s hs
    · simp
  have H := integral_Ioo_real_segment_eq_regCarlsonR (a := α) (a' := 1)
    (b := ![-β, -δ, 1 + α + β + δ]) hα (by norm_num)
    (by simp [Fin.sum_univ_three]; ring) (by positivity) hseg
  have hsq := integral_Ioo_sq_eq G le_rfl hx
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num] at hsq
  have hI : ∫ t in Ioo 0 x, (t : ℂ) ^ (2 * α - 1) * (A + B * (t : ℂ) ^ 2) ^ β *
      (C + D * (t : ℂ) ^ 2) ^ δ = 1 / 2 * ∫ t in Ioo 0 x, ((2 * t : ℝ) : ℂ) * G (t ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    simp only [G, sub_zero, sub_self, cpow_zero, mul_one, Fin.prod_univ_three]
    simp only [ofReal_mul, ofReal_ofNat, ofReal_pow, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, zero_mul, add_zero, one_cpow, mul_one]
    rw [ofReal_sq_cpow ht.1, show 2 * (α - 1) = 2 * α - 1 - 1 by ring, cpow_sub _ _ ht0, cpow_one]
    have h2 : (t : ℂ) ^ (2 * α) = (t : ℂ) ^ 2 * (t : ℂ) ^ (2 * α - 1 - 1) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0]; push_cast; ring_nf
    field_simp
    rw [h2]; ring
  rw [hI, ← hsq, H]
  simp [Fin.prod_univ_three]
  have hn : (fun i => (![A, C, 1] i + ![B, D, 0] i * (x : ℂ) ^ 2) / ![A, C, 1] i) =
      ![(A + B * (x : ℂ) ^ 2) / A, (C + D * (x : ℂ) ^ 2) / C, 1] := by
    funext i; fin_cases i <;> simp
  rw [hn]; ring

/-- **Exercise 8.1-1**: for real `0 < x < y`, `re α, re β > 0` and `λ ∈ ℂ`,
`∫_x^y (t² - x²)^{α-1} (y² - t²)^{β-1} t^{1-2λ} dt =
(1/2) Γ(α) Γ(β) (y² - x²)^{α+β-1} x^{-2λ} R̃_{-α}(α + β - λ, λ; 1, y²/x²)`. By homogeneity
the R-function equals `x^{2α} R̃_{-α}(α + β - λ, λ; x², y²)`, Carlson's form. -/
theorem integral_sq_sub_cpow_mul_cpow {α β lam : ℂ} {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hα : 0 < α.re) (hβ : 0 < β.re) :
    ∫ t in Ioo x y, ((t ^ 2 - x ^ 2 : ℝ) : ℂ) ^ (α - 1) * ((y ^ 2 - t ^ 2 : ℝ) : ℂ) ^ (β - 1) *
        (t : ℂ) ^ (1 - 2 * lam) =
      1 / 2 * Gamma α * Gamma β * ((y ^ 2 - x ^ 2 : ℝ) : ℂ) ^ (α + β - 1) *
        ((x : ℂ) ^ 2) ^ (-lam) *
          regCarlsonR (-α) (TwoVariable.pair (α + β - lam) lam)
            (TwoVariable.pair 1 ((y : ℂ) ^ 2 / (x : ℂ) ^ 2)) := by
  set b := TwoVariable.pair (α + β - lam) lam
  set G : ℝ → ℂ := fun s => ((s - x ^ 2 : ℝ) : ℂ) ^ (α - 1) * ((y ^ 2 - s : ℝ) : ℂ) ^ (β - 1) *
    ∏ i, (TwoVariable.pair 1 0 i + TwoVariable.pair 0 1 i * (s : ℂ)) ^ (-b i)
  have hx2 : x ^ 2 < y ^ 2 := pow_lt_pow_left₀ hxy hx.le two_ne_zero
  have hseg : ∀ i, ∀ s ∈ Icc (x ^ 2) (y ^ 2),
      TwoVariable.pair 1 0 i + TwoVariable.pair 0 1 i * (s : ℂ) ∈ slitPlane := by
    intro i s hs
    fin_cases i
    · simp [TwoVariable.pair]
    · simpa [TwoVariable.pair] using ofReal_mem_slitPlane.mpr ((sq_pos_of_pos hx).trans_le hs.1)
  have H := integral_Ioo_real_segment_eq_regCarlsonR (a := α) (a' := β) (b := b) hα hβ
    (by simp [b]) hx2 hseg
  have hsq := integral_Ioo_sq_eq G hx.le hxy
  have hI : ∫ t in Ioo x y, ((t ^ 2 - x ^ 2 : ℝ) : ℂ) ^ (α - 1) *
      ((y ^ 2 - t ^ 2 : ℝ) : ℂ) ^ (β - 1) * (t : ℂ) ^ (1 - 2 * lam) =
      1 / 2 * ∫ t in Ioo x y, ((2 * t : ℝ) : ℂ) * G (t ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht0' : 0 < t := hx.trans ht.1
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0'.ne'
    simp only [G, b, Fin.prod_univ_two, TwoVariable.pair, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, zero_add]
    push_cast
    rw [ofReal_sq_cpow ht0', show 1 - 2 * lam = 2 * -lam + 1 by ring, cpow_add _ _ ht0, cpow_one,
      zero_mul, add_zero, one_cpow]
    ring
  rw [hI, ← hsq, H]
  simp only [b, Fin.prod_univ_two, TwoVariable.pair, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul, zero_add]
  have hn : (fun i => (![(1 : ℂ), 0] i + ![(0 : ℂ), 1] i * ((y ^ 2 : ℝ) : ℂ)) /
      (![(1 : ℂ), 0] i + ![(0 : ℂ), 1] i * ((x ^ 2 : ℝ) : ℂ))) =
        ![1, (y : ℂ) ^ 2 / (x : ℂ) ^ 2] := by
    funext i; fin_cases i <;> simp
  rw [hn]
  push_cast
  ring_nf
  rw [one_cpow, mul_one]

/-- The substitution `w = sin² θ` on `(0, φ)` for `0 < φ < π/2`. -/
theorem integral_Ioo_sin_sq_eq (G : ℝ → ℂ) {φ : ℝ} (hφ : 0 < φ) (hφ' : φ < π / 2) :
    ∫ w in Ioo 0 (Real.sin φ ^ 2), G w =
      ∫ θ in Ioo 0 φ, ((2 * Real.sin θ * Real.cos θ : ℝ) : ℂ) * G (Real.sin θ ^ 2) := by
  have hmono : StrictMonoOn (fun θ => Real.sin θ ^ 2) (Icc 0 φ) := by
    intro u hu v hv huv
    have hsu : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu.1 (by linarith [hu.2])
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hu.1]) (by linarith [hv.2]) huv
    exact pow_lt_pow_left₀ this hsu two_ne_zero
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 φ) measurableSet_Ioo
    (f := fun θ => Real.sin θ ^ 2) (f' := fun θ => 2 * Real.sin θ * Real.cos θ)
    (fun θ _ => ((Real.hasDerivAt_sin θ).pow 2).hasDerivWithinAt.congr_deriv (by ring))
    (hmono.injOn.mono Ioo_subset_Icc_self) G
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ (by linarith)
  have himg : (fun θ => Real.sin θ ^ 2) '' Ioo 0 φ = Ioo 0 (Real.sin φ ^ 2) := by
    ext w; simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨θ, ⟨h1, h2⟩, rfl⟩
      have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h1 (by linarith)
      exact ⟨by positivity, hmono ⟨h1.le, h2.le⟩ ⟨hφ.le, le_rfl⟩ h2⟩
    · rintro ⟨h1, h2⟩
      have hr : 0 < Real.sqrt w := Real.sqrt_pos.mpr h1
      have hrφ : Real.sqrt w < Real.sin φ := by
        rw [← Real.sqrt_sq hsφ.le]; exact Real.sqrt_lt_sqrt h1.le h2
      have hr1 : Real.sqrt w ≤ 1 := hrφ.le.trans (Real.sin_le_one φ)
      refine ⟨Real.arcsin (Real.sqrt w), ⟨Real.arcsin_pos.mpr hr, ?_⟩, ?_⟩
      · calc Real.arcsin (Real.sqrt w) < Real.arcsin (Real.sin φ) :=
              Real.arcsin_lt_arcsin (by linarith) hrφ (Real.sin_le_one φ)
          _ = φ := Real.arcsin_sin (by linarith) (by linarith)
      · rw [Real.sin_arcsin (by linarith) hr1, Real.sq_sqrt h1.le]
  rw [himg] at hsub
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  simp [abs_of_pos (by positivity : 0 < 2 * Real.sin θ * Real.cos θ), Complex.real_smul]

/-- **Exercise 8.1-3**: for `0 < φ < π/2`, `re a > 0`, and `1 - k² s`, `1 - α² s` in the slit
plane for `s ∈ [0, sin² φ]`,
`∫₀^φ (sin θ)^{2a-1} (cos θ)^{1-2β} (1 - k² sin² θ)^{-γ} (1 - α² sin² θ)^{-δ} dθ =
(1/2) Γ(a) (sin φ)^{2a} R̃_{-a}(β, γ, 1 + a - β - γ - δ, δ; cos² φ, 1 - k² sin² φ, 1,
1 - α² sin² φ)`. With `R = Γ(1 + a) R̃` this is Carlson's `(sin φ)^{2a}/(2a) R_{-a}(…)`. -/
theorem integral_sin_cos_cpow {a β γ δ k α : ℂ} {φ : ℝ} (hφ : 0 < φ) (hφ' : φ < π / 2)
    (ha : 0 < a.re) (hk : ∀ s ∈ Icc (0 : ℝ) (Real.sin φ ^ 2), 1 - k ^ 2 * (s : ℂ) ∈ slitPlane)
    (hα : ∀ s ∈ Icc (0 : ℝ) (Real.sin φ ^ 2), 1 - α ^ 2 * (s : ℂ) ∈ slitPlane) :
    ∫ θ in Ioo 0 φ, (Real.sin θ : ℂ) ^ (2 * a - 1) * (Real.cos θ : ℂ) ^ (1 - 2 * β) *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-γ) * (1 - α ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-δ) =
      1 / 2 * Gamma a * (((Real.sin φ : ℂ) ^ 2) ^ a) *
        regCarlsonR (-a) ![β, γ, 1 + a - β - γ - δ, δ]
          ![(Real.cos φ : ℂ) ^ 2, 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2, 1,
            1 - α ^ 2 * (Real.sin φ : ℂ) ^ 2] := by
  set b : Fin 4 → ℂ := ![β, γ, 1 + a - β - γ - δ, δ]
  set z : Fin 4 → ℂ := ![1, 1, 1, 1]
  set w : Fin 4 → ℂ := ![-1, -k ^ 2, 0, -α ^ 2]
  set G : ℝ → ℂ := fun s => ((s - 0 : ℝ) : ℂ) ^ (a - 1) * ((Real.sin φ ^ 2 - s : ℝ) : ℂ) ^
    ((1 : ℂ) - 1) * ∏ i, (z i + w i * (s : ℂ)) ^ (-b i)
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ (by linarith)
  have hsφ1 : Real.sin φ ^ 2 < 1 := by
    have h1 := Real.sin_sq_add_cos_sq φ
    have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hφ'⟩
    nlinarith
  have hseg : ∀ i, ∀ s ∈ Icc (0 : ℝ) (Real.sin φ ^ 2), z i + w i * (s : ℂ) ∈ slitPlane := by
    intro i s hs
    fin_cases i
    · simp only [z, w]
      simpa [sub_eq_add_neg] using ofReal_mem_slitPlane.mpr (by linarith [hs.2] : (0:ℝ) < 1 - s)
    · simpa [z, w, sub_eq_add_neg] using hk s hs
    · simp [z, w]
    · simpa [z, w, sub_eq_add_neg] using hα s hs
  have H := integral_Ioo_real_segment_eq_regCarlsonR (a := a) (a' := 1) (b := b) ha (by norm_num)
    (by simp [b, Fin.sum_univ_four]; ring) (by positivity) hseg
  have hsub := integral_Ioo_sin_sq_eq G hφ hφ'
  have hI : ∫ θ in Ioo 0 φ, (Real.sin θ : ℂ) ^ (2 * a - 1) * (Real.cos θ : ℂ) ^ (1 - 2 * β) *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-γ) * (1 - α ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-δ) =
      1 / 2 * ∫ θ in Ioo 0 φ, ((2 * Real.sin θ * Real.cos θ : ℝ) : ℂ) * G (Real.sin θ ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hsc := Real.sin_sq_add_cos_sq θ
    generalize Real.sin θ = sθ at hs hsc ⊢
    generalize Real.cos θ = cθ at hc hsc ⊢
    have hs0 : (sθ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    have hc0 : (cθ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
    have hcs : ((Real.sin φ ^ 2 - sθ ^ 2 : ℝ) : ℂ) ^ ((1 : ℂ) - 1) = 1 := by simp
    have h1 : (1 : ℂ) + -1 * ((sθ ^ 2 : ℝ) : ℂ) = (cθ : ℂ) ^ 2 := by
      push_cast
      linear_combination (-1 : ℂ) * (by exact_mod_cast hsc : (sθ : ℂ) ^ 2 + (cθ : ℂ) ^ 2 = 1)
    simp only [G, b, z, w, sub_zero, hcs, mul_one, Fin.prod_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, zero_mul, add_zero, one_cpow]
    rw [h1]
    push_cast
    rw [ofReal_sq_cpow hs, ofReal_sq_cpow hc, show 2 * (a - 1) = 2 * a - 1 - 1 by ring,
      cpow_sub _ _ hs0, cpow_one, show 2 * -β = 1 - 2 * β - 1 by ring, cpow_sub _ _ hc0, cpow_one]
    field_simp
    ring_nf
    rw [cpow_neg, show (-2 + a * 2) = a * 2 - 2 by ring, cpow_sub _ _ hs0, cpow_ofNat]
    field_simp
    rw [cpow_neg (cθ : ℂ)]
    field_simp
  rw [hI, ← hsub, H]
  have hn : (fun i => (z i + w i * ((Real.sin φ ^ 2 : ℝ) : ℂ)) / (z i + w i * ((0 : ℝ) : ℂ))) =
      ![(Real.cos φ : ℂ) ^ 2, 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2, 1,
        1 - α ^ 2 * (Real.sin φ : ℂ) ^ 2] := by
    have hc : Complex.cos (φ : ℂ) ^ 2 = 1 - Complex.sin (φ : ℂ) ^ 2 := by
      linear_combination Complex.sin_sq_add_cos_sq (φ : ℂ)
    funext i; fin_cases i <;> simp [z, w, hc] <;> ring
  rw [hn]
  simp [b, z, Gamma_one, Fin.prod_univ_four]
  ring

/-- **Exercise 8.1-2**: for `0 < φ < π/2` and `1 - k² s` in the slit plane for
`s ∈ [0, sin² φ]`,
`∫₀^φ (1 - k² sin² θ)^{-β} dθ = (1/2) Γ(1/2) sin φ R̃_{-1/2}(1/2, β, 1 - β; cos² φ,
1 - k² sin² φ, 1)`. With `R = Γ(3/2) R̃` this is Carlson's `sin φ R_{-1/2}(…)`. -/
theorem integral_one_sub_sq_sin_cpow {β k : ℂ} {φ : ℝ} (hφ : 0 < φ) (hφ' : φ < π / 2)
    (hk : ∀ s ∈ Icc (0 : ℝ) (Real.sin φ ^ 2), 1 - k ^ 2 * (s : ℂ) ∈ slitPlane) :
    ∫ θ in Ioo 0 φ, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-β) =
      1 / 2 * Gamma (1 / 2) * (Real.sin φ : ℂ) *
        regCarlsonR (-(1 / 2)) ![1 / 2, β, 1 - β]
          ![(Real.cos φ : ℂ) ^ 2, 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2, 1] := by
  set b : Fin 3 → ℂ := ![1 / 2, β, 1 - β]
  set z : Fin 3 → ℂ := ![1, 1, 1]
  set w : Fin 3 → ℂ := ![-1, -k ^ 2, 0]
  set G : ℝ → ℂ := fun s => ((s - 0 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1) *
    ((Real.sin φ ^ 2 - s : ℝ) : ℂ) ^ ((1 : ℂ) - 1) * ∏ i, (z i + w i * (s : ℂ)) ^ (-b i)
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ (by linarith)
  have hsφ1 : Real.sin φ ^ 2 < 1 := by
    have h1 := Real.sin_sq_add_cos_sq φ
    have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hφ'⟩
    nlinarith
  have hseg : ∀ i, ∀ s ∈ Icc (0 : ℝ) (Real.sin φ ^ 2), z i + w i * (s : ℂ) ∈ slitPlane := by
    intro i s hs
    fin_cases i
    · simp only [z, w]
      simpa [sub_eq_add_neg] using ofReal_mem_slitPlane.mpr (by linarith [hs.2] : (0:ℝ) < 1 - s)
    · simpa [z, w, sub_eq_add_neg] using hk s hs
    · simp [z, w]
  have H := integral_Ioo_real_segment_eq_regCarlsonR (a := 1 / 2) (a' := 1) (b := b)
    (by norm_num) (by norm_num) (by simp [b, Fin.sum_univ_three]) (by positivity) hseg
  have hsub := integral_Ioo_sin_sq_eq G hφ hφ'
  have hI : ∫ θ in Ioo 0 φ, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-β) =
      1 / 2 * ∫ θ in Ioo 0 φ, ((2 * Real.sin θ * Real.cos θ : ℝ) : ℂ) * G (Real.sin θ ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hsc := Real.sin_sq_add_cos_sq θ
    generalize Real.sin θ = sθ at hs hsc ⊢
    generalize Real.cos θ = cθ at hc hsc ⊢
    have hs0 : (sθ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    have hc0 : (cθ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
    have hcs : ((Real.sin φ ^ 2 - sθ ^ 2 : ℝ) : ℂ) ^ ((1 : ℂ) - 1) = 1 := by simp
    have h1 : (1 : ℂ) + -1 * ((sθ ^ 2 : ℝ) : ℂ) = (cθ : ℂ) ^ 2 := by
      push_cast
      linear_combination (-1 : ℂ) * (by exact_mod_cast hsc : (sθ : ℂ) ^ 2 + (cθ : ℂ) ^ 2 = 1)
    simp only [G, b, z, w, sub_zero, hcs, mul_one, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, zero_mul, add_zero, one_cpow]
    rw [h1]
    push_cast
    rw [ofReal_sq_cpow hs, ofReal_sq_cpow hc, show 2 * ((1 : ℂ) / 2 - 1) = -1 by ring,
      show 2 * -((1 : ℂ) / 2) = -1 by ring, cpow_neg_one, cpow_neg_one]
    field_simp
    ring_nf
  rw [hI, ← hsub, H]
  have hn : (fun i => (z i + w i * ((Real.sin φ ^ 2 : ℝ) : ℂ)) / (z i + w i * ((0 : ℝ) : ℂ))) =
      ![(Real.cos φ : ℂ) ^ 2, 1 - k ^ 2 * (Real.sin φ : ℂ) ^ 2, 1] := by
    have hc : Complex.cos (φ : ℂ) ^ 2 = 1 - Complex.sin (φ : ℂ) ^ 2 := by
      linear_combination Complex.sin_sq_add_cos_sq (φ : ℂ)
    funext i; fin_cases i <;> simp [z, w, hc] <;> ring
  rw [hn]
  have hsq : (((Real.sin φ ^ 2 - 0 : ℝ) : ℂ)) ^ ((1 : ℂ) / 2 + 1 - 1) = (Real.sin φ : ℂ) := by
    rw [sub_zero, add_sub_cancel_right, ofReal_pow, ofReal_sq_cpow hsφ]; norm_num
  rw [hsq]
  simp [b, z, Gamma_one, Fin.prod_univ_three]
  ring

end Carlson
