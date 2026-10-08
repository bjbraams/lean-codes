/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.MellinBarnes
public import ToMathlib.Analysis.Complex.Carlson
public import ToMathlib.Analysis.SpecialFunctions.Pow

/-!
# Ramanujan's master theorem

**Ramanujan's master theorem** in Hardy's form. Let `φ` be holomorphic on `Re z > -δ`
(`0 < δ < 1`) with `‖φ z‖ ≤ C e^(P Re z + A |Im z|)` and `A < π` (`RamanujanClass`). The
Mellin–Barnes integral
`F(x) = (1 / 2πi) ∫_{(c)} π / sin (π s) · φ(-s) x^(-s) ds`, `0 < c < δ`
(`ramanujanFunction`) is the continuation to `x > 0` of `∑ φ(k) (-x)^k`, and
`∫₀^∞ x^(s-1) F(x) dx = π / sin (π s) · φ(-s)` for `0 < Re s < δ`
(`ramanujan_master_theorem`).

## Proof

* The integrand `x^(-s) π / sin (π s) φ(-s)` decays like `e^((A - π) |Im s|)` on vertical
  strips (`norm_ramanujanIntegrand_le`) and has simple poles at `s = -k` with residues
  `φ(k) (-x)^k` (`RamanujanClass.exists_pole`).
* Moving the line of integration to `Re s = -N - 1/2` across these poles
  (`Complex.integral_vertical_sub_eq_of_simplePole`) gives the partial sums of the series plus
  a remainder bounded by `K (x e^P)^(N + 1/2)`, which tends to zero for `x < e^(-P)`
  (`RamanujanClass.hasSum_mellinInv`).
* Within `0 < Re s < δ` the line can be moved freely (`RamanujanClass.mellinInv_eq_mellinInv`),
  which bounds `F(x)` by `x^(-σ)` for every `σ ∈ (0, δ)` and gives Mellin convergence. Mellin
  inversion in the reverse direction (`mellin_mellinInv_eq`) gives the transform.

## References

* G. H. Hardy, *Ramanujan: Twelve Lectures on Subjects Suggested by His Life and Work*,
  Cambridge, 1940, §11.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology Real

namespace Complex

/-- On a vertical line, `‖sin (π (σ + t I))‖ ≥ |sin (π σ)| cosh (π t)`. -/
theorem abs_sin_mul_cosh_le_norm_sin_pi (σ t : ℝ) :
    |Real.sin (π * σ)| * Real.cosh (π * t) ≤ ‖sin (π * ((σ : ℂ) + t * I))‖ := by
  have hsq := norm_sin_add_mul_I_sq (π * σ) (π * t)
  rw [show (((π * σ : ℝ) : ℂ) + ((π * t : ℝ) : ℂ) * I) = π * ((σ : ℂ) + t * I) by
    push_cast; ring] at hsq
  have hc := Real.cosh_sq (π * t)
  have hs1 : Real.sin (π * σ) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  have hkey : (|Real.sin (π * σ)| * Real.cosh (π * t)) ^ 2 ≤ ‖sin (π * ((σ : ℂ) + t * I))‖ ^ 2 := by
    rw [mul_pow, sq_abs, hsq]
    nlinarith [sq_nonneg (Real.sinh (π * t)), sq_nonneg (Real.sin (π * σ))]
  exact (pow_le_pow_iff_left₀ (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le) (norm_nonneg _)
    two_ne_zero).mp hkey

/-- On a vertical line, `‖sin (π (σ + t I))‖ ≥ |sinh (π t)|`. -/
theorem abs_sinh_le_norm_sin_pi (σ t : ℝ) :
    |Real.sinh (π * t)| ≤ ‖sin (π * ((σ : ℂ) + t * I))‖ := by
  have hsq := norm_sin_add_mul_I_sq (π * σ) (π * t)
  rw [show (((π * σ : ℝ) : ℂ) + ((π * t : ℝ) : ℂ) * I) = π * ((σ : ℂ) + t * I) by
    push_cast; ring] at hsq
  have hkey : |Real.sinh (π * t)| ^ 2 ≤ ‖sin (π * ((σ : ℂ) + t * I))‖ ^ 2 := by
    rw [sq_abs, hsq]; nlinarith [sq_nonneg (Real.sin (π * σ))]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).mp hkey

/-- `cosh x ≥ e^|x| / 2`. -/
theorem exp_abs_div_two_le_cosh (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  linarith [Real.exp_pos (-|x|)]

/-- `|sinh x| ≥ e^|x| / 4` for `|x| ≥ 1/2`. -/
theorem exp_abs_div_four_le_abs_sinh {x : ℝ} (hx : 1 / 2 ≤ |x|) :
    Real.exp |x| / 4 ≤ |Real.sinh x| := by
  rw [Real.abs_sinh, Real.sinh_eq]
  set u := |x|
  have h2 : 2 ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have : Real.exp (-u) * Real.exp (2 * u) = Real.exp u := by rw [← Real.exp_add]; ring_nf
  nlinarith [Real.exp_pos (-u), Real.exp_pos u]

/-- Exponential decay beats `(1 + |t|)^(-2)`: `e^(-κ |t|) ≤ m⁻² (1 + |t|)^(-2)`,
`m = min 1 (κ / 2)`, for `κ > 0`. -/
theorem exp_neg_mul_abs_le {κ : ℝ} (hκ : 0 < κ) (t : ℝ) :
    Real.exp (-(κ * |t|)) ≤ (min 1 (κ / 2))⁻¹ ^ 2 * (1 + |t|) ^ (-2 : ℝ) := by
  set m := min 1 (κ / 2)
  have hm : 0 < m := lt_min one_pos (by positivity)
  have hu := abs_nonneg t
  have h1 : m * (1 + |t|) ≤ 1 + κ * |t| / 2 := by
    have := min_le_left 1 (κ / 2)
    have := min_le_right 1 (κ / 2)
    nlinarith
  have h2 : (1 + κ * |t| / 2) ^ 2 ≤ Real.exp (κ * |t|) := by
    have := Real.quadratic_le_exp_of_nonneg (mul_nonneg hκ.le hu)
    nlinarith [mul_nonneg hκ.le hu]
  have h3 : (m * (1 + |t|)) ^ 2 ≤ Real.exp (κ * |t|) :=
    (pow_le_pow_left₀ (by positivity) h1 2).trans h2
  rw [Real.exp_neg, Real.rpow_neg (by positivity), Real.rpow_two, inv_pow, ← mul_inv,
    ← mul_pow]
  exact inv_anti₀ (by positivity) h3

/-- The **Ramanujan kernel** `Ψ(s) = π / sin (π s) · φ(-s)`. -/
def ramanujanKernel (φ : ℂ → ℂ) (s : ℂ) : ℂ := π / sin (π * s) * φ (-s)

/-- The Mellin–Barnes integrand `x^(-s) Ψ(s)`. -/
def ramanujanIntegrand (φ : ℂ → ℂ) (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ (-s) * ramanujanKernel φ s

/-- **The integrand is uniformly small for large `|t|`.** For `x > 0` and `a ≤ σ ≤ b < δ`,
`|t| ≥ 1`, `‖x^(-s) Ψ(s)‖ ≤ 4πC (x^(-a) + x^(-b)) (e^(-Pa) + e^(-Pb)) e^((A - π)|t|)`. -/
theorem norm_ramanujanIntegrand_le {φ : ℂ → ℂ} {δ C P A : ℝ}
    (hbd : ∀ z : ℂ, -δ < z.re → ‖φ z‖ ≤ C * Real.exp (P * z.re + A * |z.im|))
    {x : ℝ} (hx : 0 < x) {a b σ t : ℝ} (ha : a ≤ σ) (hb : σ ≤ b) (hbδ : b < δ) (ht : 1 ≤ |t|) :
    ‖ramanujanIntegrand φ x (σ + t * I)‖ ≤
      4 * π * C * (x ^ (-a) + x ^ (-b)) * (Real.exp (-P * a) + Real.exp (-P * b)) *
        Real.exp ((A - π) * |t|) := by
  have hz : -δ < (-((σ : ℂ) + t * I)).re := by simp; linarith
  have hφ := hbd _ hz
  simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, neg_im, add_im, mul_im, zero_add, abs_neg] at hφ
  have hC : 0 ≤ C := by
    by_contra h
    have := mul_neg_of_neg_of_pos (not_le.mp h) (Real.exp_pos (P * -σ + A * |t|))
    linarith [norm_nonneg (φ (-((σ : ℂ) + t * I)))]
  have hsinh : Real.exp (π * |t|) / 4 ≤ ‖sin (π * ((σ : ℂ) + t * I))‖ := by
    have h1 := exp_abs_div_four_le_abs_sinh (x := π * t) (by
      rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [Real.pi_gt_three])
    rw [abs_mul, abs_of_pos Real.pi_pos] at h1
    exact h1.trans (abs_sinh_le_norm_sin_pi σ t)
  have hspos : 0 < ‖sin (π * ((σ : ℂ) + t * I))‖ := lt_of_lt_of_le (by positivity) hsinh
  have hxpow : ‖(x : ℂ) ^ (-((σ : ℂ) + t * I))‖ ≤ x ^ (-a) + x ^ (-b) := by
    rw [norm_cpow_eq_rpow_re_of_pos hx]
    simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    have := Real.rpow_le_rpow_add_rpow hx (neg_le_neg hb) (neg_le_neg ha)
    linarith
  have hexpP : Real.exp (P * -σ) ≤ Real.exp (-P * a) + Real.exp (-P * b) := by
    have := Real.rpow_le_rpow_add_rpow (Real.exp_pos (-P)) ha hb
    simp only [← Real.exp_mul] at this
    rw [show P * -σ = -P * σ by ring]
    exact this
  unfold ramanujanIntegrand ramanujanKernel
  rw [norm_mul, norm_mul, norm_div, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  calc ‖(x : ℂ) ^ (-((σ : ℂ) + t * I))‖ * (π / ‖sin (π * ((σ : ℂ) + t * I))‖ *
        ‖φ (-((σ : ℂ) + t * I))‖)
      ≤ (x ^ (-a) + x ^ (-b)) * (π / (Real.exp (π * |t|) / 4) *
          (C * (Real.exp (P * -σ) * Real.exp (A * |t|)))) := by
        rw [← Real.exp_add]
        gcongr
    _ ≤ (x ^ (-a) + x ^ (-b)) * (π / (Real.exp (π * |t|) / 4) *
          (C * ((Real.exp (-P * a) + Real.exp (-P * b)) * Real.exp (A * |t|)))) := by gcongr
    _ = _ := by
        rw [show (A - π) * |t| = A * |t| + -(π * |t|) by ring, Real.exp_add, Real.exp_neg]
        field_simp

/-- **Hardy's class** for Ramanujan's master theorem: `φ` is holomorphic on `Re z > -δ`
(`0 < δ < 1`) with `‖φ z‖ ≤ C e^(P Re z + A |Im z|)` there, `A < π`. -/
structure RamanujanClass (φ : ℂ → ℂ) (δ C P A : ℝ) : Prop where
  /-- The half-plane `Re z > -δ` reaches to the left of `0`. -/
  delta_pos : 0 < δ
  /-- The half-plane `Re z > -δ` does not reach `-1`. -/
  delta_lt_one : δ < 1
  /-- The type in the imaginary direction is less than `π`. -/
  lt_pi : A < π
  /-- `φ` is holomorphic on `Re z > -δ`. -/
  differentiableAt : ∀ z : ℂ, -δ < z.re → DifferentiableAt ℂ φ z
  /-- The growth bound. -/
  bound : ∀ z : ℂ, -δ < z.re → ‖φ z‖ ≤ C * Real.exp (P * z.re + A * |z.im|)

namespace RamanujanClass

variable {φ : ℂ → ℂ} {δ C P A : ℝ}

/-- The integrand is holomorphic at every non-integer point with `Re s < δ`. -/
theorem differentiableAt_integrand (h : RamanujanClass φ δ C P A) {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs : s.re < δ) (hsin : sin (π * s) ≠ 0) :
    DifferentiableAt ℂ (ramanujanIntegrand φ x) s := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have h1 : DifferentiableAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (-s)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hx0)
  have h2 : DifferentiableAt ℂ (fun s : ℂ ↦ φ (-s)) s :=
    (h.differentiableAt (-s) (by simp; linarith)).comp s differentiableAt_id.neg
  have h3 : DifferentiableAt ℂ (fun s : ℂ ↦ (π : ℂ) / sin (π * s)) s :=
    (differentiableAt_const _).div (by fun_prop) hsin
  exact h1.mul (h3.mul h2)

/-- A tail bound `K (1 + |t|)^(-2)` for the integrand on `a ≤ Re s ≤ b < δ`, `|t| ≥ 1`. -/
theorem exists_tail_bound (h : RamanujanClass φ δ C P A) {x : ℝ} (hx : 0 < x) {a b : ℝ}
    (hbδ : b < δ) :
    ∃ K, ∀ σ t : ℝ, a ≤ σ → σ ≤ b → 1 ≤ |t| →
      ‖ramanujanIntegrand φ x (σ + t * I)‖ ≤ K * (1 + |t|) ^ (-2 : ℝ) := by
  have hκ : 0 < π - A := by linarith [h.lt_pi]
  set K₀ := 4 * π * C * (x ^ (-a) + x ^ (-b)) * (Real.exp (-P * a) + Real.exp (-P * b))
  refine ⟨|K₀| * (min 1 ((π - A) / 2))⁻¹ ^ 2, fun σ t h1 h2 ht ↦ ?_⟩
  refine (norm_ramanujanIntegrand_le h.bound hx h1 h2 hbδ ht).trans ?_
  have he := exp_neg_mul_abs_le hκ t
  rw [show (A - π) * |t| = -((π - A) * |t|) by ring]
  calc K₀ * Real.exp (-((π - A) * |t|)) ≤ |K₀| * Real.exp (-((π - A) * |t|)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _ ≤ |K₀| * ((min 1 ((π - A) / 2))⁻¹ ^ 2 * (1 + |t|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left he (abs_nonneg _)
    _ = _ := by ring

/-- The pole of the integrand at `-k`: `x^(-s) Ψ(s) = r / (s + k) + (holomorphic)` near `-k` with
residue `r = φ(k) (-x)^k`. -/
theorem exists_pole (h : RamanujanClass φ δ C P A) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    ∃ g : ℂ → ℂ, DifferentiableAt ℂ g (-(k : ℂ)) ∧
      ∀ᶠ s in 𝓝[≠] (-(k : ℂ)), ramanujanIntegrand φ x s =
        φ k * (-(x : ℂ)) ^ k / (s - -(k : ℂ)) + g s := by
  set s₀ : ℂ := -(k : ℂ)
  have hs₀ : s₀ = ((-(k : ℤ) : ℤ) : ℂ) := by simp [s₀]
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  set N : ℂ → ℂ := fun s ↦ (x : ℂ) ^ (-s) * φ (-s)
  set D : ℂ → ℂ := dslope (fun w : ℂ ↦ sin (π * w)) s₀
  have hsin0 : sin (π * s₀) = 0 := sin_pi_mul_eq_zero_iff.mpr ⟨-(k : ℤ), hs₀⟩
  have hD0 : D s₀ ≠ 0 := by
    have := dslope_sin_pi_mul_intCast_ne_zero (-(k : ℤ))
    rwa [← hs₀] at this
  have hDd : Differentiable ℂ D := fun z ↦
    ((differentiableOn_dslope (Filter.univ_mem)).mpr
      (fun w _ ↦ (by fun_prop : DifferentiableAt ℂ (fun w : ℂ ↦ sin (π * w)) w)
        |>.differentiableWithinAt)).differentiableAt Filter.univ_mem
  -- A neighbourhood of `s₀` where `N` is holomorphic and `D` does not vanish.
  set U : Set ℂ := {s | s.re < δ} ∩ {s | D s ≠ 0}
  have hU : IsOpen U := (isOpen_lt continuous_re continuous_const).inter
    (isOpen_ne_fun hDd.continuous continuous_const)
  have hs₀U : s₀ ∈ U := ⟨by simp [s₀]; linarith [h.delta_pos], hD0⟩
  have hNd : DifferentiableOn ℂ N U := fun s hs ↦
    (((differentiableAt_id.neg).const_cpow (Or.inl hx0)).mul
      ((h.differentiableAt (-s) (by simp; linarith [show s.re < δ from hs.1])).comp s
        differentiableAt_id.neg)
      ).differentiableWithinAt
  set H : ℂ → ℂ := fun s ↦ π * N s / D s
  have hHd : DifferentiableOn ℂ H U := fun s hs ↦
    ((differentiableAt_const _).mul (hNd s hs |>.differentiableAt (hU.mem_nhds hs))
      |>.div (hDd s) hs.2).differentiableWithinAt
  refine ⟨dslope H s₀, ((differentiableOn_dslope (hU.mem_nhds hs₀U)).mpr hHd).differentiableAt
    (hU.mem_nhds hs₀U), ?_⟩
  have hr : H s₀ = φ k * (-(x : ℂ)) ^ k := by
    have hder : D s₀ = π * cos (π * s₀) := by
      simp only [D, dslope_same]
      simp [mul_comm]
    have hcos : cos (π * s₀) = (-1) ^ k := by
      rw [show (π : ℂ) * s₀ = ((-(k * π) : ℝ) : ℂ) by simp [s₀]; ring, ← ofReal_cos, Real.cos_neg,
        Real.cos_nat_mul_pi]
      push_cast; ring
    have hN : N s₀ = (x : ℂ) ^ k * φ k := by
      simp only [N, s₀, neg_neg]
      rw [cpow_natCast]
    simp only [H, hder, hcos, hN]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [neg_pow (x : ℂ) k]
    rcases neg_one_pow_eq_or ℂ k with h1 | h1 <;> rw [h1] <;> field_simp
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hs₀U),
    self_mem_nhdsWithin] with s hsU hne
  have hsub : s - s₀ ≠ 0 := sub_ne_zero.mpr hne
  have hsin : sin (π * s) = (s - s₀) * D s := by
    simp only [D]
    rw [dslope_of_ne _ hne, slope_def_field, hsin0, sub_zero]
    field_simp
  have hH : H s = H s₀ + (s - s₀) * dslope H s₀ s := by
    have := sub_smul_dslope H s₀ s
    rw [smul_eq_mul] at this
    linear_combination -this
  rw [← hr]
  have hfs : ramanujanIntegrand φ x s = H s / (s - s₀) := by
    simp only [ramanujanIntegrand, ramanujanKernel, H, N, hsin]
    field_simp [hsU.2]
  rw [hfs, hH]
  field_simp

/-- The inverse Mellin transform of the Ramanujan kernel as an integral of the integrand. -/
theorem mellinInv_ramanujanKernel (σ x : ℝ) :
    mellinInv σ (ramanujanKernel φ) x =
      (1 / (2 * π) : ℝ) • ∫ y : ℝ, ramanujanIntegrand φ x (σ + y * I) := by
  simp only [mellinInv, ramanujanIntegrand, smul_eq_mul]

/-- **Crossing the pole at `-k`.** -/
theorem mellinInv_sub_mellinInv (h : RamanujanClass φ δ C P A) {x : ℝ} (hx : 0 < x) (k : ℕ)
    {a b : ℝ} (ha1 : -(k : ℝ) - 1 < a) (ha : a < -(k : ℝ)) (hb : -(k : ℝ) < b)
    (hb1 : b < -(k : ℝ) + 1) (hbδ : b < δ) :
    mellinInv b (ramanujanKernel φ) x - mellinInv a (ramanujanKernel φ) x =
      φ k * (-(x : ℂ)) ^ k := by
  obtain ⟨g, hg, hpole⟩ := h.exists_pole hx k
  obtain ⟨K, hK⟩ := h.exists_tail_bound hx (a := a) hbδ
  have hre : (-(k : ℂ)).re = -(k : ℝ) := by simp
  have hcross := integral_vertical_sub_eq_of_simplePole (f := ramanujanIntegrand φ x)
    (s₀ := -(k : ℂ)) (by rw [hre]; exact ha) (by rw [hre]; exact hb)
    (fun s hs1 hs2 hne ↦ h.differentiableAt_integrand hx (hs2.trans_lt hbδ)
      (sin_pi_mul_ne_zero_of_re (k := -(k : ℤ)) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; exact hne)))
    hg hpole (T₀ := 1) (fun σ t h1 h2 ht ↦ hK σ t h1 h2 ht)
  rw [mellinInv_ramanujanKernel, mellinInv_ramanujanKernel, ← smul_sub, hcross.2.2]
  rw [Complex.real_smul]
  push_cast
  field_simp

/-- **Shifting the Mellin–Barnes line to `Re s = -N - 1/2`** picks up the first `N + 1` terms of
the series. -/
theorem mellinInv_eq_sum_add (h : RamanujanClass φ δ C P A) {x : ℝ} (hx : 0 < x) {c : ℝ}
    (hc0 : 0 < c) (hcδ : c < δ) (N : ℕ) :
    mellinInv c (ramanujanKernel φ) x =
      ∑ k ∈ Finset.range (N + 1), φ k * (-(x : ℂ)) ^ k +
        mellinInv (-(N : ℝ) - 1 / 2) (ramanujanKernel φ) x := by
  have hc1 : c < 1 := hcδ.trans h.delta_lt_one
  induction N with
  | zero =>
    have := h.mellinInv_sub_mellinInv hx 0 (a := -1 / 2) (b := c) (by norm_num) (by norm_num)
      (by simpa using hc0) (by simpa using hc1) hcδ
    rw [Finset.sum_range_one]
    norm_num at this ⊢
    linear_combination this
  | succ N ih =>
    have := h.mellinInv_sub_mellinInv hx (N + 1) (a := -((N : ℝ) + 1) - 1 / 2)
      (b := -(N : ℝ) - 1 / 2) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) (by linarith [h.delta_pos])
    rw [ih, Finset.sum_range_succ (fun k ↦ φ k * (-(x : ℂ)) ^ k) (N + 1)]
    push_cast at this ⊢
    linear_combination this

/-- `|sin (π (-N - 1/2))| = 1`. -/
theorem abs_sin_pi_neg_nat_sub_half (N : ℕ) : |Real.sin (π * (-(N : ℝ) - 1 / 2))| = 1 := by
  rw [show π * (-(N : ℝ) - 1 / 2) = -(π / 2 + N * π) by ring, Real.sin_neg, abs_neg,
    Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one, abs_pow, abs_neg, abs_one, one_pow]

/-- **The remainder.** `‖ℳ⁻¹_{-N-1/2} Ψ (x)‖ ≤ K (x e^P)^(N + 1/2)` with `K` independent of `N`. -/
theorem exists_norm_mellinInv_le (h : RamanujanClass φ δ C P A) {x : ℝ} (hx : 0 < x) :
    ∃ K, ∀ N : ℕ, ‖mellinInv (-(N : ℝ) - 1 / 2) (ramanujanKernel φ) x‖ ≤
      K * (x * Real.exp P) ^ ((N : ℝ) + 1 / 2) := by
  have hκ : 0 < π - A := by linarith [h.lt_pi]
  set m := min 1 ((π - A) / 2)
  set I₀ : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)
  have hI₀ : 0 ≤ I₀ := integral_nonneg fun t ↦ by positivity
  refine ⟨|C| * m⁻¹ ^ 2 * I₀, fun N ↦ ?_⟩
  set σ : ℝ := -(N : ℝ) - 1 / 2
  set q : ℝ := x * Real.exp P
  have hq : 0 < q := by positivity
  have hpt : ∀ t : ℝ, ‖ramanujanIntegrand φ x (σ + t * I)‖ ≤
      2 * π * (|C| * m⁻¹ ^ 2 * q ^ ((N : ℝ) + 1 / 2)) * (1 + |t|) ^ (-2 : ℝ) := by
    intro t
    have hz : -δ < (-((σ : ℂ) + t * I)).re := by
      simp [σ]; linarith [h.delta_pos, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have hφ := h.bound _ hz
    simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, neg_im, add_im, mul_im, zero_add, abs_neg] at hφ
    have hsin := abs_sin_mul_cosh_le_norm_sin_pi σ t
    rw [abs_sin_pi_neg_nat_sub_half, one_mul] at hsin
    have hcosh := exp_abs_div_two_le_cosh (π * t)
    rw [abs_mul, abs_of_pos Real.pi_pos] at hcosh
    have hspos : 0 < ‖sin (π * ((σ : ℂ) + t * I))‖ :=
      lt_of_lt_of_le (by positivity) (hcosh.trans hsin)
    have hxpow : ‖(x : ℂ) ^ (-((σ : ℂ) + t * I))‖ = x ^ ((N : ℝ) + 1 / 2) := by
      rw [norm_cpow_eq_rpow_re_of_pos hx]
      congr 1
      simp [σ]
      ring
    have hexp : Real.exp (P * -σ) = Real.exp P ^ ((N : ℝ) + 1 / 2) := by
      rw [← Real.exp_mul]; congr 1; simp only [σ]; ring
    have he := exp_neg_mul_abs_le hκ t
    unfold ramanujanIntegrand ramanujanKernel
    rw [norm_mul, norm_mul, norm_div, norm_real, Real.norm_of_nonneg Real.pi_pos.le, hxpow]
    calc x ^ ((N : ℝ) + 1 / 2) * (π / ‖sin (π * ((σ : ℂ) + t * I))‖ * ‖φ (-((σ : ℂ) + t * I))‖)
        ≤ x ^ ((N : ℝ) + 1 / 2) * (π / (Real.exp (π * |t|) / 2) *
            (|C| * (Real.exp (P * -σ) * Real.exp (A * |t|)))) := by
          rw [← Real.exp_add]
          gcongr
          · exact hcosh.trans hsin
          · exact hφ.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
      _ = 2 * π * |C| * q ^ ((N : ℝ) + 1 / 2) * Real.exp (-((π - A) * |t|)) := by
          rw [hexp, show q = x * Real.exp P from rfl,
            Real.mul_rpow hx.le (Real.exp_pos P).le,
            show -((π - A) * |t|) = A * |t| + -(π * |t|) by ring, Real.exp_add, Real.exp_neg]
          field_simp
      _ ≤ 2 * π * |C| * q ^ ((N : ℝ) + 1 / 2) * (m⁻¹ ^ 2 * (1 + |t|) ^ (-2 : ℝ)) := by
          gcongr
      _ = _ := by ring
  rw [mellinInv_ramanujanKernel, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hint : Integrable fun t : ℝ ↦
      2 * π * (|C| * m⁻¹ ^ 2 * q ^ ((N : ℝ) + 1 / 2)) * (1 + |t|) ^ (-2 : ℝ) :=
    integrable_one_add_abs_rpow_neg_two.const_mul _
  calc 1 / (2 * π) * ‖∫ y : ℝ, ramanujanIntegrand φ x (σ + y * I)‖
      ≤ 1 / (2 * π) * ∫ t : ℝ, 2 * π * (|C| * m⁻¹ ^ 2 * q ^ ((N : ℝ) + 1 / 2)) *
          (1 + |t|) ^ (-2 : ℝ) := by
        gcongr
        exact norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = |C| * m⁻¹ ^ 2 * I₀ * q ^ ((N : ℝ) + 1 / 2) := by
        rw [MeasureTheory.integral_const_mul]
        simp only [I₀]
        field_simp

/-- **The Mellin–Barnes integral continues the series.** For `0 < x < e^(-P)` the series
`∑ φ(k) (-x)^k` converges absolutely to the Mellin–Barnes integral `ℳ⁻¹_c Ψ (x)`, `0 < c < δ`. -/
theorem hasSum_mellinInv (h : RamanujanClass φ δ C P A) {x : ℝ} (hx : 0 < x)
    (hxP : x < Real.exp (-P)) {c : ℝ} (hc0 : 0 < c) (hcδ : c < δ) :
    HasSum (fun k : ℕ ↦ φ k * (-(x : ℂ)) ^ k) (mellinInv c (ramanujanKernel φ) x) := by
  set q : ℝ := x * Real.exp P
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by
    have := mul_lt_mul_of_pos_right hxP (Real.exp_pos P)
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  -- Absolute convergence.
  have hterm : ∀ k : ℕ, ‖φ k * (-(x : ℂ)) ^ k‖ ≤ |C| * q ^ k := by
    intro k
    have hb := h.bound (k : ℂ) (by simp; linarith [h.delta_pos, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    simp only [natCast_re, natCast_im, abs_zero, mul_zero, add_zero] at hb
    rw [norm_mul, norm_pow, norm_neg, norm_real, Real.norm_of_nonneg hx.le]
    calc ‖φ k‖ * x ^ k ≤ |C| * Real.exp (P * k) * x ^ k := by
          gcongr
          exact hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
      _ = |C| * q ^ k := by
          rw [show P * (k : ℝ) = k * P by ring, Real.exp_nat_mul, mul_pow]; ring
  have hsum : Summable fun k : ℕ ↦ φ k * (-(x : ℂ)) ^ k :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0.le hq1).mul_left |C|) hterm
  -- The partial sums converge to the Mellin–Barnes integral.
  obtain ⟨K, hK⟩ := h.exists_norm_mellinInv_le hx
  have hrem : Tendsto (fun N : ℕ ↦ mellinInv (-(N : ℝ) - 1 / 2) (ramanujanKernel φ) x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm hK ?_
    have h1 : Tendsto (fun N : ℕ ↦ K * (q ^ (1 / 2 : ℝ) * q ^ N)) atTop
        (𝓝 (K * (q ^ (1 / 2 : ℝ) * 0))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul _).const_mul _
    simp only [mul_zero] at h1
    refine h1.congr fun N ↦ ?_
    rw [Real.rpow_add hq0, Real.rpow_natCast]
    ring
  refine (hsum.hasSum_iff_tendsto_nat).mpr ?_
  rw [← tendsto_add_atTop_iff_nat 1]
  have := (tendsto_const_nhds (x := mellinInv c (ramanujanKernel φ) x)).sub hrem
  rw [sub_zero] at this
  refine this.congr fun N ↦ ?_
  rw [h.mellinInv_eq_sum_add hx hc0 hcδ N]
  ring

/-- The kernel is holomorphic at non-integer points with `Re s < δ`. -/
theorem differentiableAt_kernel (h : RamanujanClass φ δ C P A) {s : ℂ} (hs : s.re < δ)
    (hsin : sin (π * s) ≠ 0) : DifferentiableAt ℂ (ramanujanKernel φ) s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ ↦ (π : ℂ) / sin (π * s)) s :=
    (differentiableAt_const _).div (by fun_prop) hsin
  have h2 : DifferentiableAt ℂ (fun s : ℂ ↦ φ (-s)) s :=
    (h.differentiableAt (-s) (by simp; linarith)).comp s differentiableAt_id.neg
  exact h1.mul h2

/-- On a line `Re s = σ ∈ (0, δ)` the kernel is continuous and bounded by `K (1 + |t|)^(-2)`. -/
theorem kernel_line (h : RamanujanClass φ δ C P A) {σ : ℝ} (hσ0 : 0 < σ) (hσδ : σ < δ) :
    Continuous (fun t : ℝ ↦ ramanujanKernel φ (σ + t * I)) ∧
      ∃ K, ∀ t : ℝ, ‖ramanujanKernel φ (σ + t * I)‖ ≤ K * (1 + |t|) ^ (-2 : ℝ) := by
  have hσ1 : σ < 1 := hσδ.trans h.delta_lt_one
  have hre : ∀ t : ℝ, ((σ : ℂ) + t * I).re = σ := fun t ↦ by simp
  refine ⟨continuous_iff_continuousAt.mpr fun t ↦ ?_, ?_⟩
  · exact (h.differentiableAt_kernel (by rw [hre]; exact hσδ)
      (sin_pi_mul_ne_zero_of_re_mem (by rw [hre]; exact hσ0) (by rw [hre]; exact hσ1))
      ).continuousAt.comp (by fun_prop)
  have hκ : 0 < π - A := by linarith [h.lt_pi]
  have hsinσ : 0 < |Real.sin (π * σ)| :=
    abs_pos.mpr (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne'
  set m := min 1 ((π - A) / 2)
  refine ⟨2 * π * |C| * Real.exp (-P * σ) / |Real.sin (π * σ)| * m⁻¹ ^ 2, fun t ↦ ?_⟩
  have hz : -δ < (-((σ : ℂ) + t * I)).re := by simp; linarith
  have hφ := h.bound _ hz
  simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, neg_im, add_im, mul_im, zero_add, abs_neg] at hφ
  have hsin := abs_sin_mul_cosh_le_norm_sin_pi σ t
  have hcosh := exp_abs_div_two_le_cosh (π * t)
  rw [abs_mul, abs_of_pos Real.pi_pos] at hcosh
  have hlow : |Real.sin (π * σ)| * (Real.exp (π * |t|) / 2) ≤ ‖sin (π * ((σ : ℂ) + t * I))‖ :=
    (mul_le_mul_of_nonneg_left hcosh (abs_nonneg _)).trans hsin
  have he := exp_neg_mul_abs_le hκ t
  unfold ramanujanKernel
  rw [norm_mul, norm_div, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  calc π / ‖sin (π * ((σ : ℂ) + t * I))‖ * ‖φ (-((σ : ℂ) + t * I))‖
      ≤ π / (|Real.sin (π * σ)| * (Real.exp (π * |t|) / 2)) *
          (|C| * (Real.exp (-P * σ) * Real.exp (A * |t|))) := by
        rw [← Real.exp_add]
        gcongr
        refine hφ.trans (mul_le_mul (le_abs_self C) (le_of_eq (by ring_nf)) (by positivity)
          (abs_nonneg _))
    _ = 2 * π * |C| * Real.exp (-P * σ) / |Real.sin (π * σ)| *
          Real.exp (-((π - A) * |t|)) := by
        rw [show -((π - A) * |t|) = A * |t| + -(π * |t|) by ring, Real.exp_add, Real.exp_neg]
        field_simp
    _ ≤ 2 * π * |C| * Real.exp (-P * σ) / |Real.sin (π * σ)| *
          (m⁻¹ ^ 2 * (1 + |t|) ^ (-2 : ℝ)) := by gcongr
    _ = _ := by ring

/-- The kernel is integrable on lines `Re s = σ ∈ (0, δ)`. -/
theorem integrable_kernel_line (h : RamanujanClass φ δ C P A) {σ : ℝ} (hσ0 : 0 < σ)
    (hσδ : σ < δ) : Integrable fun t : ℝ ↦ ramanujanKernel φ (σ + t * I) := by
  obtain ⟨hc, K, hK⟩ := h.kernel_line hσ0 hσδ
  exact (integrable_one_add_abs_rpow_neg_two.const_mul K).mono' hc.aestronglyMeasurable
    (Eventually.of_forall hK)

/-- **Independence of the line** `Re s = σ ∈ (0, δ)`. -/
theorem mellinInv_eq_mellinInv (h : RamanujanClass φ δ C P A) {σ₁ σ₂ : ℝ} (h1 : 0 < σ₁)
    (h1δ : σ₁ < δ) (h2 : 0 < σ₂) (h2δ : σ₂ < δ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ₁ (ramanujanKernel φ) x = mellinInv σ₂ (ramanujanKernel φ) x := by
  have key : ∀ a b : ℝ, 0 < a → a ≤ b → b < δ →
      mellinInv a (ramanujanKernel φ) x = mellinInv b (ramanujanKernel φ) x := by
    intro a b ha hab hbδ
    obtain ⟨K, hK⟩ := h.exists_tail_bound hx (a := a) hbδ
    rw [mellinInv_ramanujanKernel, mellinInv_ramanujanKernel,
      integral_vertical_eq_of_tail_bound hab (fun s hs1 hs2 ↦ h.differentiableAt_integrand hx
        (hs2.trans_lt hbδ) (sin_pi_mul_ne_zero_of_re_mem (ha.trans_le hs1)
          (hs2.trans_lt (hbδ.trans h.delta_lt_one)))) (T₀ := 1) hK]
  rcases le_total σ₁ σ₂ with h12 | h21
  · exact key σ₁ σ₂ h1 h12 h2δ
  · exact (key σ₂ σ₁ h2 h21 h1δ).symm

/-- `‖ℳ⁻¹_σ Ψ (x)‖ ≤ K x^(-σ)`, with `K = (2π)⁻¹ ∫ ‖Ψ (σ + t I)‖ dt`. -/
theorem exists_norm_mellinInv_le_rpow (φ : ℂ → ℂ) (σ : ℝ) :
    ∃ K, ∀ x : ℝ, 0 < x → ‖mellinInv σ (ramanujanKernel φ) x‖ ≤ K * x ^ (-σ) := by
  set I₁ := ∫ t : ℝ, ‖ramanujanKernel φ (σ + t * I)‖
  refine ⟨1 / (2 * π) * I₁, fun x hx ↦ ?_⟩
  have hnorm : ∀ t : ℝ, ‖ramanujanIntegrand φ x (σ + t * I)‖ =
      x ^ (-σ) * ‖ramanujanKernel φ (σ + t * I)‖ := by
    intro t
    rw [ramanujanIntegrand, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
    simp
  rw [mellinInv_ramanujanKernel, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc 1 / (2 * π) * ‖∫ y : ℝ, ramanujanIntegrand φ x (σ + y * I)‖
      ≤ 1 / (2 * π) * ∫ y : ℝ, ‖ramanujanIntegrand φ x (σ + y * I)‖ := by
        gcongr; exact norm_integral_le_integral_norm _
    _ = 1 / (2 * π) * I₁ * x ^ (-σ) := by
        simp_rw [hnorm]
        rw [MeasureTheory.integral_const_mul]
        ring

/-- The Mellin–Barnes integral is continuous on `(0, ∞)`. -/
theorem continuousOn_mellinInv (h : RamanujanClass φ δ C P A) {σ : ℝ} (hσ0 : 0 < σ)
    (hσδ : σ < δ) : ContinuousOn (mellinInv σ (ramanujanKernel φ)) (Ioi 0) := by
  obtain ⟨hc, -⟩ := h.kernel_line hσ0 hσδ
  have hi := h.integrable_kernel_line hσ0 hσδ
  intro x₀ hx₀
  refine ContinuousAt.continuousWithinAt ?_
  have heq : mellinInv σ (ramanujanKernel φ) = fun x : ℝ ↦
      (1 / (2 * π) : ℝ) • ∫ y : ℝ, ramanujanIntegrand φ x (σ + y * I) :=
    funext fun x ↦ mellinInv_ramanujanKernel σ x
  rw [heq]
  suffices hI : ContinuousAt (fun x : ℝ ↦ ∫ y : ℝ, ramanujanIntegrand φ x (σ + y * I)) x₀ from
    hI.tendsto.const_smul _
  refine continuousAt_of_dominated (bound := fun y ↦ (x₀ / 2) ^ (-σ) *
    ‖ramanujanKernel φ (σ + y * I)‖) ?_ ?_ (hi.norm.const_mul _) ?_
  · filter_upwards [lt_mem_nhds (show x₀ / 2 < x₀ by linarith [mem_Ioi.mp hx₀])] with x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith [mem_Ioi.mp hx₀])
    refine (Continuous.aestronglyMeasurable ?_)
    refine continuous_iff_continuousAt.mpr fun y ↦ ?_
    exact (((by fun_prop : Continuous fun y : ℝ ↦ -((σ : ℂ) + y * I)).continuousAt.const_cpow
      (Or.inl hx0)).mul hc.continuousAt)
  · filter_upwards [lt_mem_nhds (show x₀ / 2 < x₀ by linarith [mem_Ioi.mp hx₀])] with x hx
    refine Eventually.of_forall fun y ↦ ?_
    have hxpos : 0 < x := by linarith [mem_Ioi.mp hx₀]
    rw [ramanujanIntegrand, norm_mul, norm_cpow_eq_rpow_re_of_pos hxpos]
    simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos
      (by linarith [mem_Ioi.mp hx₀]) hx.le (by linarith [hσ0])) (norm_nonneg _)
  · refine Eventually.of_forall fun y ↦ ?_
    have hslit : (x₀ : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx₀
    exact ((continuous_ofReal.continuousAt).cpow continuousAt_const hslit).mul continuousAt_const

/-- **Mellin convergence** of the Mellin–Barnes integral on `0 < Re s < δ`. -/
theorem mellinConvergent_mellinInv (h : RamanujanClass φ δ C P A) {σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    (hσ₀δ : σ₀ < δ) {s : ℂ} (hs0 : 0 < s.re) (hsδ : s.re < δ) :
    MellinConvergent (mellinInv σ₀ (ramanujanKernel φ)) s := by
  set σ₁ := s.re / 2
  set σ₂ := (s.re + δ) / 2
  have h1 : 0 < σ₁ := by simp only [σ₁]; linarith
  have h1δ : σ₁ < δ := by simp only [σ₁]; linarith
  have h2 : 0 < σ₂ := by simp only [σ₂]; linarith
  have h2δ : σ₂ < δ := by simp only [σ₂]; linarith
  obtain ⟨K₁, hK₁⟩ := exists_norm_mellinInv_le_rpow φ σ₁
  obtain ⟨K₂, hK₂⟩ := exists_norm_mellinInv_le_rpow φ σ₂
  have hcont := h.continuousOn_mellinInv hσ₀ hσ₀δ
  have hmeas : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • mellinInv σ₀ (ramanujanKernel φ) t)
      (Ioi 0) := fun t ht ↦
    (((continuous_ofReal.continuousAt).cpow continuousAt_const
      (ofReal_mem_slitPlane.mpr ht)).continuousWithinAt).smul (hcont t ht)
  have hnorm : ∀ t ∈ Ioi (0 : ℝ), ∀ σ, 0 < σ → σ < δ →
      ‖(t : ℂ) ^ (s - 1) • mellinInv σ₀ (ramanujanKernel φ) t‖ =
        t ^ (s.re - 1) * ‖mellinInv σ (ramanujanKernel φ) t‖ := by
    intro t ht σ hσ hσδ
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, h.mellinInv_eq_mellinInv hσ₀ hσ₀δ hσ hσδ ht]
    simp
  rw [MellinConvergent, ← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hb : IntegrableOn (fun t : ℝ ↦ |K₁| * t ^ (s.re - 1 - σ₁)) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (r := s.re - 1 - σ₁)
        (by simp only [σ₁]; linarith) (a := 0) (b := 1))
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
      exact this.const_mul _
    refine hb.mono' ((hmeas.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := ht.1
    rw [hnorm t htpos σ₁ h1 h1δ]
    calc t ^ (s.re - 1) * ‖mellinInv σ₁ (ramanujanKernel φ) t‖
        ≤ t ^ (s.re - 1) * (|K₁| * t ^ (-σ₁)) := by
          gcongr
          exact (hK₁ t htpos).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      _ = |K₁| * t ^ (s.re - 1 - σ₁) := by
          rw [sub_eq_add_neg (s.re - 1), Real.rpow_add htpos]; ring
  · have hb : IntegrableOn (fun t : ℝ ↦ |K₂| * t ^ (s.re - 1 - σ₂)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by simp only [σ₂]; linarith) one_pos).const_mul _
    refine hb.mono' ((hmeas.mono fun t ht ↦ lt_trans one_pos ht).aestronglyMeasurable
      measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := lt_trans one_pos ht
    rw [hnorm t htpos σ₂ h2 h2δ]
    calc t ^ (s.re - 1) * ‖mellinInv σ₂ (ramanujanKernel φ) t‖
        ≤ t ^ (s.re - 1) * (|K₂| * t ^ (-σ₂)) := by
          gcongr
          exact (hK₂ t htpos).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      _ = |K₂| * t ^ (s.re - 1 - σ₂) := by
          rw [sub_eq_add_neg (s.re - 1), Real.rpow_add htpos]; ring

end RamanujanClass

/-- The function of Ramanujan's master theorem: the Mellin–Barnes integral
`F(x) = (1 / 2πi) ∫_{(δ/2)} π / sin (π s) · φ(-s) x^(-s) ds`, the continuation to `x > 0` of
`∑ φ(k) (-x)^k`. -/
def ramanujanFunction (φ : ℂ → ℂ) (δ : ℝ) : ℝ → ℂ := mellinInv (δ / 2) (ramanujanKernel φ)

/-- **Ramanujan's master theorem** (Hardy's form). Let `φ` be holomorphic on `Re z > -δ`,
`0 < δ < 1`, with `‖φ z‖ ≤ C e^(P Re z + A |Im z|)` there and `A < π`. Then
`F = ramanujanFunction φ δ` satisfies
* `F(x) = ∑ φ(k) (-x)^k` (absolutely convergent) for `0 < x < e^(-P)`, and
* `∫₀^∞ x^(s-1) F(x) dx = π / sin (π s) · φ(-s)` for `0 < Re s < δ`, the integral converging. -/
theorem ramanujan_master_theorem {φ : ℂ → ℂ} {δ C P A : ℝ} (h : RamanujanClass φ δ C P A) :
    (∀ x : ℝ, 0 < x → x < Real.exp (-P) →
      HasSum (fun k : ℕ ↦ φ k * (-(x : ℂ)) ^ k) (ramanujanFunction φ δ x)) ∧
    ∀ s : ℂ, 0 < s.re → s.re < δ →
      MellinConvergent (ramanujanFunction φ δ) s ∧
        mellin (ramanujanFunction φ δ) s = π / sin (π * s) * φ (-s) := by
  have hc0 : 0 < δ / 2 := by linarith [h.delta_pos]
  have hcδ : δ / 2 < δ := by linarith [h.delta_pos]
  refine ⟨fun x hx hxP ↦ h.hasSum_mellinInv hx hxP hc0 hcδ, fun s hs0 hsδ ↦ ?_⟩
  refine ⟨h.mellinConvergent_mellinInv hc0 hcδ hs0 hsδ, ?_⟩
  set σ := s.re
  -- Pass to the line through `s`.
  have hF : mellin (ramanujanFunction φ δ) s = mellin (mellinInv σ (ramanujanKernel φ)) s := by
    unfold mellin ramanujanFunction
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [h.mellinInv_eq_mellinInv hc0 hcδ hs0 hsδ ht]
  obtain ⟨hcont, -⟩ := h.kernel_line hs0 hsδ
  have hconv : MellinConvergent (mellinInv σ (ramanujanKernel φ)) (σ : ℂ) :=
    h.mellinConvergent_mellinInv hs0 hsδ (by simpa using hs0) (by simpa using hsδ)
  rw [hF, mellin_mellinInv_eq hcont (h.integrable_kernel_line hs0 hsδ) hconv rfl]
  rfl

end Complex
