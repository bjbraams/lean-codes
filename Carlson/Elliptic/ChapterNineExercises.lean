/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Asymptotic
public import Carlson.Elliptic.QuarticReduction
public import Carlson.Elliptic.SchwarzChristoffel
public import Carlson.TwoVariable.QuadraticHybrid

/-!
# Exercises of Carlson's Chapter 9

## Main results

* `Carlson.isEquivalent_carlsonRK_sq_zero`: Exercise 9.2-1.
* `Carlson.carlsonRF_add_eq_integral_of_slit`, `Carlson.carlsonRH_add_eq_integral`:
  Exercise 9.2-3.
* `Carlson.dupStep_inverse`: Exercise 9.6-2.
* `Carlson.sqrt_eulerP_sub_sq`, `Carlson.eulerMu_eq_sq`, `Carlson.eulerMu_mul_sqrt_sub`:
  Exercises 9.7-1, 9.7-3 and 9.7-4 on the branch (9.7-12); `Carlson.eulerMu_eulerMu`, the
  branch is an involution.
* `Carlson.carlsonRF_add_carlsonRF_shift`, `Carlson.det_shiftCubic_eq_zero`: Exercises 9.7-2
  and 9.7-5. The branch condition of Theorem 9.7-1 is added as a hypothesis; without it
  Exercise 9.7-2 fails (see the docstring).
* `Carlson.carlsonR_neg_one_half_half_one_sq`: Exercise 9.8-5, from Theorem 9.8-1 with
  `C = D = z`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology

@[expose] public noncomputable section

namespace Carlson

open TwoVariable (pair carlsonRK carlsonRC carlsonRK_comm)

/-- **Exercise 9.2-1**: for `y > 0`, `R_K(x², y²) ∼ (2/(π y)) log(4y/x)` as `x → 0+`; this is
(8.3-16) (`isEquivalent_carlsonRK_zero`) after the substitution `(x, y) ↦ (y², x²)`. -/
theorem isEquivalent_carlsonRK_sq_zero {y : ℝ} (hy : 0 < y) :
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun x : ℝ => carlsonRK ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ))
      (fun x : ℝ => ((2 / (π * y) * Real.log (4 * y / x) : ℝ) : ℂ)) := by
  have h := isEquivalent_carlsonRK_zero (x := y ^ 2) (by positivity)
  have hsq : Tendsto (fun x : ℝ => x ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      exact pow_pos hx 2
  have h2 := h.comp_tendsto hsq
  refine (h2.congr_left ?_).congr_right ?_
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    simp only [Function.comp_apply]
    exact carlsonRK_comm (ofReal_mem_slitPlane.mpr (by positivity))
      (ofReal_mem_slitPlane.mpr (by positivity))
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    simp only [Function.comp_apply]
    congr 1
    rw [Real.sqrt_sq hy.le, show 16 * y ^ 2 / x ^ 2 = (4 * y / x) ^ 2 by ring,
      Real.log_pow]
    push_cast
    ring

/-- Adding a nonnegative real number keeps a point in the slit plane. -/
theorem add_ofReal_mem_slitPlane {x : ℂ} (hx : x ∈ slitPlane) {l : ℝ} (hl : 0 ≤ l) :
    x + l ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hx ⊢
  rcases hx with h | h
  · left; simp; linarith
  · right; simpa using h

/-- **Exercise 9.2-3**, first formula: for `x, y, z` in the slit plane and `λ ≥ 0`,
`R_F(x + λ, y + λ, z + λ) = (1/2) ∫_λ^∞ (t + x)^{-1/2} (t + y)^{-1/2} (t + z)^{-1/2} dt`, with
principal powers of the individual factors (the positive real case is
`carlsonRF_add_eq_integral`). -/
theorem carlsonRF_add_eq_integral_of_slit {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) {l : ℝ} (hl : 0 ≤ l) :
    carlsonRF (x + l) (y + l) (z + l) = 1 / 2 * ∫ t in Ioi l,
      (x + t) ^ (-1 / 2 : ℂ) * (y + t) ^ (-1 / 2 : ℂ) * (z + t) ^ (-1 / 2 : ℂ) := by
  rw [carlsonRF_eq_integral (add_ofReal_mem_slitPlane hx hl) (add_ofReal_mem_slitPlane hy hl)
    (add_ofReal_mem_slitPlane hz hl), ← integral_Ioi_zero_add (fun t : ℝ =>
      (x + (t : ℂ)) ^ (-1 / 2 : ℂ) * (y + t) ^ (-1 / 2 : ℂ) * (z + t) ^ (-1 / 2 : ℂ)) l]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  push_cast
  ring_nf

/-- **Exercise 9.2-3**, second formula: for `x, y, z, ρ` in the slit plane and `λ ≥ 0`,
`R_H(x + λ, y + λ, z + λ, ρ + λ) =
(3/4) ∫_λ^∞ (t - λ) (t + x)^{-1/2} (t + y)^{-1/2} (t + z)^{-1/2} (t + ρ)^{-1} dt`. -/
theorem carlsonRH_add_eq_integral {x y z ρ : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) (hρ : ρ ∈ slitPlane) {l : ℝ} (hl : 0 ≤ l) :
    carlsonRH (x + l) (y + l) (z + l) (ρ + l) = 3 / 4 * ∫ t in Ioi l, ((t - l : ℝ) : ℂ) *
      ((x + t) ^ (-1 / 2 : ℂ) * (y + t) ^ (-1 / 2 : ℂ) * (z + t) ^ (-1 / 2 : ℂ) *
        (ρ + t) ^ (-1 : ℂ)) := by
  have hs : ![x + l, y + l, z + l, ρ + l] ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact add_ofReal_mem_slitPlane hx hl
    · exact add_ofReal_mem_slitPlane hy hl
    · exact add_ofReal_mem_slitPlane hz hl
    · exact add_ofReal_mem_slitPlane hρ hl
  have hray := carlsonRPositiveRayIntegral_eq_Gamma_mul_regCarlsonR (a := 2) (a' := 1 / 2)
    (b := ![1 / 2, 1 / 2, 1 / 2, 1]) (by norm_num) (by norm_num)
    (by simp [Fin.sum_univ_four]; norm_num) hs
  unfold carlsonRPositiveRayIntegral at hray
  have hG2 : Gamma (2 : ℂ) = 1 := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, Gamma_add_one _ one_ne_zero, Gamma_one, mul_one]
  have hG52 : Gamma (5 / 2 : ℂ) = 3 / 4 * Gamma (1 / 2) := by
    rw [show (5 / 2 : ℂ) = 1 / 2 + 1 + 1 by norm_num, Gamma_add_one _ (by norm_num),
      Gamma_add_one _ (by norm_num)]
    ring
  rw [carlsonRH, carlsonR, show (∑ i, ![(1 / 2 : ℂ), 1 / 2, 1 / 2, 1] i) = 5 / 2 by
      simp [Fin.sum_univ_four]; norm_num, hG52, show (-1 / 2 : ℂ) = -(1 / 2) by ring]
  rw [hG2, one_mul] at hray
  rw [mul_assoc, ← hray, ← integral_Ioi_zero_add (fun t : ℝ => ((t - l : ℝ) : ℂ) *
      ((x + t) ^ (-(1 / 2) : ℂ) * (y + t) ^ (-(1 / 2) : ℂ) * (z + t) ^ (-(1 / 2) : ℂ) *
        (ρ + t) ^ (-1 : ℂ))) l]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  rw [show (2 : ℂ) - 1 = 1 by norm_num, cpow_one]
  ring_nf

/-- **Exercise 9.6-2**: one step `(x, y, z) ↦ (x', y', z')` of Algorithm 9.6-2 (`dupStep`, from
(9.6-7)) is inverted by `x = x'y'/z' + x'z'/y' - y'z'/x'` and the two similar equations, for
positive `x, y, z`. -/
theorem dupStep_inverse {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    let q := dupStep (x, y, z)
    x = q.1 * q.2.1 / q.2.2 + q.1 * q.2.2 / q.2.1 - q.2.1 * q.2.2 / q.1 ∧
    y = q.2.1 * q.1 / q.2.2 + q.2.1 * q.2.2 / q.1 - q.1 * q.2.2 / q.2.1 ∧
    z = q.2.2 * q.1 / q.2.1 + q.2.2 * q.2.1 / q.1 - q.1 * q.2.1 / q.2.2 := by
  intro q
  have hA := Real.sq_sqrt (show 0 ≤ x + y by linarith)
  have hB := Real.sq_sqrt (show 0 ≤ x + z by linarith)
  have hC := Real.sq_sqrt (show 0 ≤ y + z by linarith)
  have hA0 : 0 < Real.sqrt (x + y) := Real.sqrt_pos.mpr (by linarith)
  have hB0 : 0 < Real.sqrt (x + z) := Real.sqrt_pos.mpr (by linarith)
  have hC0 : 0 < Real.sqrt (y + z) := Real.sqrt_pos.mpr (by linarith)
  simp only [q, dupStep, add_comm y x, add_comm z x, add_comm z y]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> nlinarith [hA, hB, hC]

section Euler

variable {e f g : ℝ} (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 < g)
include he hf hg

/-- The cubic `P(t) = t³ + e t² + f t + g` of (9.7-10). -/
abbrev eulerP (e f g t : ℝ) : ℝ := t ^ 3 + e * t ^ 2 + f * t + g

/-- **Exercise 9.7-3**: `μ = λ^{-2} [P(λ)^{1/2} + g^{1/2}]² - λ - e` on the branch (9.7-12). -/
theorem eulerMu_eq_sq {l : ℝ} (hl : 0 < l) :
    eulerMu e f g l =
      (Real.sqrt (eulerP e f g l) + Real.sqrt g) ^ 2 / l ^ 2 - l - e := by
  have hP := Real.sq_sqrt (show 0 ≤ eulerP e f g l by positivity)
  have hG := Real.sq_sqrt hg.le
  unfold eulerMu
  field_simp
  rw [add_sq, hP, hG]
  ring_nf

omit he hf hg in
/-- `2 √g √P(λ) = λ² μ - f λ - 2g` on the branch (9.7-12). -/
private theorem two_sqrt_mul_sqrt_eulerP {l : ℝ} (hl : 0 < l) :
    2 * (Real.sqrt g * Real.sqrt (eulerP e f g l)) = l ^ 2 * eulerMu e f g l - f * l - 2 * g := by
  unfold eulerMu
  rw [mul_div_cancel₀ _ (pow_ne_zero 2 hl.ne')]
  ring

/-- The branch (9.7-12) is an involution: `λ = μ(μ(λ))`. -/
theorem eulerMu_eulerMu {l : ℝ} (hl : 0 < l) : eulerMu e f g (eulerMu e f g l) = l := by
  obtain ⟨hm, hpos, hQ⟩ := eulerMu_spec he hf hg hl
  exact (eq_eulerMu he hf hg hm (by rw [mul_comm]; linear_combination hQ)
    (by rw [mul_comm]; exact hpos)).symm

/-- **Exercise 9.7-4**: with `μ` given by (9.7-12),
`μ P(λ)^{1/2} - λ P(μ)^{1/2} = (λ - μ) g^{1/2}`. -/
theorem eulerMu_mul_sqrt_sub {l : ℝ} (hl : 0 < l) :
    eulerMu e f g l * Real.sqrt (eulerP e f g l) -
        l * Real.sqrt (eulerP e f g (eulerMu e f g l)) =
      (l - eulerMu e f g l) * Real.sqrt g := by
  set m := eulerMu e f g l
  have hm := (eulerMu_spec he hf hg hl).1
  have h1 := two_sqrt_mul_sqrt_eulerP (e := e) (f := f) (g := g) hl
  have h2 := two_sqrt_mul_sqrt_eulerP (e := e) (f := f) (g := g) hm
  rw [eulerMu_eulerMu he hf hg hl] at h2
  have hG0 : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
  have hG := Real.sq_sqrt hg.le
  apply mul_left_cancel₀ (show 2 * Real.sqrt g ≠ 0 by positivity)
  linear_combination m * h1 - l * h2 + (2 * (m - l)) * hG

/-- **Exercise 9.7-1**: the solution (9.7-11) of (9.7-10) can be written as
`[P(λ)^{1/2} - P(μ)^{1/2}]² = (λ - μ)² (λ + μ + e)`. -/
theorem sqrt_eulerP_sub_sq {l : ℝ} (hl : 0 < l) :
    (Real.sqrt (eulerP e f g l) - Real.sqrt (eulerP e f g (eulerMu e f g l))) ^ 2 =
      (l - eulerMu e f g l) ^ 2 * (l + eulerMu e f g l + e) := by
  set m := eulerMu e f g l
  obtain ⟨hm, -, hQ⟩ := eulerMu_spec he hf hg hl
  have h1 := two_sqrt_mul_sqrt_eulerP (e := e) (f := f) (g := g) hl
  have h2 := two_sqrt_mul_sqrt_eulerP (e := e) (f := f) (g := g) hm
  rw [eulerMu_eulerMu he hf hg hl] at h2
  have hG0 : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
  have hG := Real.sq_sqrt hg.le
  have hd : 2 * Real.sqrt g * (Real.sqrt (eulerP e f g l) - Real.sqrt (eulerP e f g m)) =
      (l - m) * (l * m - f) := by linear_combination h1 - h2
  apply mul_left_cancel₀ (show (2 * Real.sqrt g) ^ 2 ≠ 0 by positivity)
  rw [← mul_pow, hd, mul_pow, show (2 * Real.sqrt g) ^ 2 = 4 * g by rw [mul_pow, hG]; ring]
  linear_combination (l - m) ^ 2 * hQ

end Euler

/-- Merging the two equal nodes of `R_{-1}(1/2, 1/2, 1/2, 1/2; u, v, w, w)`. -/
private theorem carlsonR_quartic_merge {u v w : ℂ} (hu : u ∈ slitPlane) (hv : v ∈ slitPlane)
    (hw : w ∈ slitPlane) :
    carlsonR (-1) (fun _ : Fin 4 => 1 / 2) ![u, v, w, w] =
      carlsonR (-1) ![1 / 2, 1 / 2, 1] ![u, v, w] := by
  have hs : (![u, v, w] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  have hq : Function.Surjective (![0, 1, 2, 2] : Fin 4 → Fin 3) := by
    intro k; fin_cases k
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hcomp : (![u, v, w, w] : Fin 4 → ℂ) = ![u, v, w] ∘ ![0, 1, 2, 2] := by
    funext i; fin_cases i <;> rfl
  have hagg : stdSimplexAggregate (![0, 1, 2, 2] : Fin 4 → Fin 3) (fun _ : Fin 4 => (1 / 2 : ℂ)) =
      ![1 / 2, 1 / 2, 1] := by
    classical
    funext k
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    fin_cases k
    · simp; decide
    · simp; decide
    · simp
      have : (Finset.univ.filter fun x : Fin 4 => (![0, 1, 2, 2] : Fin 4 → Fin 3) x = 2).card =
          2 := by decide
      rw [this]; norm_num
  unfold carlsonR
  rw [hcomp, regCarlsonR_aggregate_of_slit hq _ hs, hagg]
  congr 1
  simp [Fin.sum_univ_three]; norm_num

/-- **Exercise 9.8-5**: for `x, y, z` in the right half-plane with `X = xy + z²` and
`Y = (x + y) z` in the right half-plane,
`R_{-1}(1/2, 1/2, 1; x², y², z²) = 2 R_C(X², Y²)`. This is Theorem 9.8-1 with `C = D = z`. -/
theorem carlsonR_neg_one_half_half_one_sq {x y z : ℂ} (hx : 0 < x.re) (hy : 0 < y.re)
    (hz : 0 < z.re) (hX : 0 < (x * y + z ^ 2).re) (hY : 0 < ((x + y) * z).re) :
    carlsonR (-1) ![1 / 2, 1 / 2, 1] ![x ^ 2, y ^ 2, z ^ 2] =
      2 * carlsonRC ((x * y + z ^ 2) ^ 2) (((x + y) * z) ^ 2) := by
  have hY' : 0 < (x * z + y * z).re := by rw [← add_mul]; exact hY
  rw [← carlsonR_quartic_merge (sq_mem_slitPlane_of_re_pos hx) (sq_mem_slitPlane_of_re_pos hy)
    (sq_mem_slitPlane_of_re_pos hz),
    carlsonR_quartic_eq_carlsonRF hx hy hz hz (by rw [← sq]; exact hX) hY' hY',
    show x * y + z * z = x * y + z ^ 2 by ring, show x * z + y * z = (x + y) * z by ring,
    carlsonRF_self_right (sq_mem_slitPlane_of_re_pos hX) (sq_mem_slitPlane_of_re_pos hY)]

section Shift

variable {x y z l m ν : ℝ}

/-- The cubic `(t + x)(t + y)(t + z)` of Exercise 9.7-2. -/
abbrev shiftCubic (x y z t : ℝ) : ℝ := (t + x) * (t + y) * (t + z)

/-- The algebra behind Exercises 9.7-2 and 9.7-5: with `s` the slope of the chord through
`(λ, P(λ)^{1/2})` and `(μ, P(μ)^{1/2})`, `L` the chord, and `ν = s² - λ - μ - x - y - z`, one has
`P(ν) = L(ν)²` and `(λ - ν)(μ - ν) - f(ν) = -2 s L(ν)`, where `f(ν)` is the second elementary
symmetric function of `x + ν, y + ν, z + ν`. -/
private theorem shift_identities (hlm : l ≠ m) {A B : ℝ} (hA : A ^ 2 = shiftCubic x y z l)
    (hB : B ^ 2 = shiftCubic x y z m)
    (hν : ν = ((A - B) / (l - m)) ^ 2 - l - m - x - y - z) :
    shiftCubic x y z ν = (A + (A - B) / (l - m) * (ν - l)) ^ 2 ∧
      (l - ν) * (m - ν) - ((x + ν) * (y + ν) + (x + ν) * (z + ν) + (y + ν) * (z + ν)) =
        -2 * ((A - B) / (l - m)) * (A + (A - B) / (l - m) * (ν - l)) := by
  set s := (A - B) / (l - m)
  have hd : l - m ≠ 0 := sub_ne_zero.mpr hlm
  have hBs : B = A - s * (l - m) := by simp only [s]; field_simp; ring
  rw [hBs] at hB
  have H1 : A ^ 2 - shiftCubic x y z l = 0 := by rw [hA]; ring
  have H2 : (A - s * (l - m)) ^ 2 - shiftCubic x y z m = 0 := by rw [hB]; ring
  subst hν
  constructor
  · apply mul_right_cancel₀ hd
    simp only [shiftCubic] at H1 H2 ⊢
    linear_combination (-(s ^ 2 - l - m - x - y - z - m)) * H1 +
      (s ^ 2 - l - m - x - y - z - l) * H2
  · apply mul_right_cancel₀ hd
    simp only [shiftCubic] at H1 H2 ⊢
    linear_combination H1 - H2

/-- **Exercise 9.7-2**: for real `x, y, z, ν` with `x + ν, y + ν, z + ν > 0`, `λ, μ > ν`, `λ ≠ μ`,
`ν = {[P(λ)^{1/2} - P(μ)^{1/2}]/(λ - μ)}² - λ - μ - x - y - z` with `P(t) = (t + x)(t + y)(t + z)`,
and on the branch `(λ - ν)(μ - ν) > f(ν)` of Theorem 9.7-1 (with `f(ν)` the second elementary
symmetric function of `x + ν, y + ν, z + ν`),
`R_F(x + λ, y + λ, z + λ) + R_F(x + μ, y + μ, z + μ) = R_F(x + ν, y + ν, z + ν)`.

The branch hypothesis is needed: for `x = y = 1`, `z = 1/100` and `λ, μ > 0` on the other branch
of Euler's relation, Carlson's formula gives `ν = 0` while the identity fails numerically. -/
theorem carlsonRF_add_carlsonRF_shift (hx : 0 < x + ν) (hy : 0 < y + ν) (hz : 0 < z + ν)
    (hl : ν < l) (hm : ν < m) (hlm : l ≠ m)
    (hν : ν = ((Real.sqrt (shiftCubic x y z l) - Real.sqrt (shiftCubic x y z m)) / (l - m)) ^ 2 -
      l - m - x - y - z)
    (hbranch : (x + ν) * (y + ν) + (x + ν) * (z + ν) + (y + ν) * (z + ν) < (l - ν) * (m - ν)) :
    carlsonRF ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
      carlsonRF ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) ((z + m : ℝ) : ℂ) =
        carlsonRF ((x + ν : ℝ) : ℂ) ((y + ν : ℝ) : ℂ) ((z + ν : ℝ) : ℂ) := by
  have hPl : 0 ≤ shiftCubic x y z l := by
    simp only [shiftCubic]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hPm : 0 ≤ shiftCubic x y z m := by
    simp only [shiftCubic]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  obtain ⟨h1, h2⟩ := shift_identities hlm (Real.sq_sqrt hPl) (Real.sq_sqrt hPm) hν
  set s := (Real.sqrt (shiftCubic x y z l) - Real.sqrt (shiftCubic x y z m)) / (l - m)
  set Lν := Real.sqrt (shiftCubic x y z l) + s * (ν - l)
  have hsum : l - ν + (m - ν) + (x + ν) + (y + ν) + (z + ν) = s ^ 2 := by rw [hν]; ring
  have h13 : (l - ν) * (m - ν) - (x + ν) * (y + ν) - (x + ν) * (z + ν) - (y + ν) * (z + ν) =
      2 * Real.sqrt ((x + ν) * (y + ν) * (z + ν)) *
        Real.sqrt (l - ν + (m - ν) + (x + ν) + (y + ν) + (z + ν)) := by
    have hpos : 0 < (l - ν) * (m - ν) - (x + ν) * (y + ν) - (x + ν) * (z + ν) -
        (y + ν) * (z + ν) := by linarith
    have hP : (x + ν) * (y + ν) * (z + ν) = shiftCubic x y z ν := by simp only [shiftCubic]; ring
    have key : (l - ν) * (m - ν) - (x + ν) * (y + ν) - (x + ν) * (z + ν) - (y + ν) * (z + ν) =
        -2 * s * Lν := by linear_combination h2
    have hpos' : 0 < -2 * s * Lν := key ▸ hpos
    rw [hsum, hP, h1, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, key, ← abs_of_pos hpos',
      abs_mul, abs_mul, abs_neg]
    norm_num
    ring
  have h := carlsonRF_add_carlsonRF hx hy hz (sub_pos.mpr hl) (sub_pos.mpr hm) h13
  simp only [show x + ν + (l - ν) = x + l by ring, show y + ν + (l - ν) = y + l by ring,
    show z + ν + (l - ν) = z + l by ring, show x + ν + (m - ν) = x + m by ring,
    show y + ν + (m - ν) = y + m by ring, show z + ν + (m - ν) = z + m by ring] at h
  exact h

/-- **Exercise 9.7-5**: under the hypotheses of `carlsonRF_add_carlsonRF_shift`, the points
`(λ, P(λ)^{1/2})`, `(μ, P(μ)^{1/2})`, `(ν, -P(ν)^{1/2})` are collinear:
`det [[P(λ)^{1/2}, λ, 1], [P(μ)^{1/2}, μ, 1], [-P(ν)^{1/2}, ν, 1]] = 0`. -/
theorem det_shiftCubic_eq_zero (hx : 0 < x + ν) (hy : 0 < y + ν) (hz : 0 < z + ν)
    (hl : ν < l) (hm : ν < m) (hlm : l ≠ m)
    (hν : ν = ((Real.sqrt (shiftCubic x y z l) - Real.sqrt (shiftCubic x y z m)) / (l - m)) ^ 2 -
      l - m - x - y - z)
    (hbranch : (x + ν) * (y + ν) + (x + ν) * (z + ν) + (y + ν) * (z + ν) < (l - ν) * (m - ν)) :
    Matrix.det !![Real.sqrt (shiftCubic x y z l), l, 1; Real.sqrt (shiftCubic x y z m), m, 1;
      -Real.sqrt (shiftCubic x y z ν), ν, 1] = 0 := by
  have hPl : 0 ≤ shiftCubic x y z l := by
    simp only [shiftCubic]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hPm : 0 ≤ shiftCubic x y z m := by
    simp only [shiftCubic]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  obtain ⟨h1, h2⟩ := shift_identities hlm (Real.sq_sqrt hPl) (Real.sq_sqrt hPm) hν
  set A := Real.sqrt (shiftCubic x y z l)
  set B := Real.sqrt (shiftCubic x y z m)
  set s := (A - B) / (l - m)
  have hd : l - m ≠ 0 := sub_ne_zero.mpr hlm
  -- the chord has positive slope, since `P` increases
  have hmono : ∀ {a b : ℝ}, ν < a → a < b → shiftCubic x y z a < shiftCubic x y z b :=
    fun {a b} ha hab => by
      simp only [shiftCubic]
      have h1 : 0 < a + x := by linarith
      have h2 : 0 < a + y := by linarith
      have h3 : 0 < a + z := by linarith
      exact mul_lt_mul'' (mul_lt_mul'' (by linarith) (by linarith) h1.le h2.le) (by linarith)
        (by positivity) h3.le
  have hs : 0 < s := by
    rcases lt_or_gt_of_ne hlm with h | h
    · exact div_pos_of_neg_of_neg (by
        have := Real.sqrt_lt_sqrt hPl (hmono hl h); linarith) (by linarith)
    · exact div_pos (by have := Real.sqrt_lt_sqrt hPm (hmono hm h); linarith) (by linarith)
  have hL : A + s * (ν - l) < 0 := by
    have : 0 < -2 * s * (A + s * (ν - l)) := by rw [← h2]; linarith
    nlinarith
  have hC : -Real.sqrt (shiftCubic x y z ν) = A + s * (ν - l) := by
    rw [h1, Real.sqrt_sq_eq_abs, abs_of_neg hL, neg_neg]
  have hsl : s * (l - m) = A - B := by simp only [s]; field_simp
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const]
  rw [hC]
  linear_combination (ν - l) * hsl

end Shift

end Carlson
