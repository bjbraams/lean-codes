/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Recurrence
public import Carlson.Jacobi.EllipseCoordinates
public import Pochhammer.Estimates
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Sharp growth of monic Jacobi polynomials

Carlson's recurrence coefficients converge to `(r + s)/2` and `(r - s)²/16`, so the monic
recurrence is a small perturbation of a constant-coefficient recurrence whose characteristic
roots have larger modulus equal to the elliptic mean radius `μ(x)`. An elementary estimate for
perturbed two-step recurrences gives `‖pₙ(x)‖ ≤ C (μ(x) + ε)ⁿ`, uniformly on compact sets
avoiding the endpoints. The maximum modulus principle extends the bound to closed elliptic
disks. These are the upper halves of Carlson's Theorems 7.5-1 and 7.5-2 for the polynomials,
for all complex parameters and endpoints, including coincident endpoints.

## Main results

* `norm_le_of_perturbed_recurrence`: growth of perturbed two-step recurrences.
* `tendsto_jacobiRecurrenceV`, `tendsto_jacobiRecurrenceW`: limits of the coefficients.
* `exists_bound_norm_eval_jacobiOn_of_isCompact`: the uniform bound on compact sets.
* `exists_bound_norm_eval_jacobiOn_of_le`: the bound `C (ρ + ε)ⁿ` on closed elliptic disks.
* `exists_bound_norm_eval_jacobiOn`: the pointwise rate (Exercise 7.5-1).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Theorems 7.5-1 and 7.5-2 and Exercises 7.1-6 and 7.5-1.
-/

@[expose] public noncomputable section
open Complex Set Filter Polynomial
open scoped Topology

namespace Carlson.TwoVariable

/-- Reciprocals of natural numbers tend to zero in `ℂ`. -/
private theorem tendsto_natCast_inv_complex :
    Tendsto (fun n : ℕ => ((n : ℂ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_nhds_zero_nat

/-- An affine quotient with slopes `1` and `2` tends to one half. -/
private theorem tendsto_add_div_add_two_mul (a b : ℂ) :
    Tendsto (fun n : ℕ => (a + n) / (b + 2 * n)) atTop (𝓝 (1 / 2)) := by
  have h := ((tendsto_natCast_inv_complex.const_mul a).add_const 1).div
    ((tendsto_natCast_inv_complex.const_mul b).add_const 2) (by norm_num)
  simp only [mul_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [Pi.div_apply]
  field_simp

/-- The reciprocal of an affine function with slope `2` tends to zero. -/
private theorem tendsto_inv_add_two_mul (b : ℂ) :
    Tendsto (fun n : ℕ => (b + 2 * n)⁻¹) atTop (𝓝 0) := by
  have h := tendsto_natCast_inv_complex.div
    ((tendsto_natCast_inv_complex.const_mul b).add_const 2) (by norm_num)
  simp only [mul_zero, zero_add, zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [Pi.div_apply]
  field_simp

/-- Carlson's recurrence coefficients `V_n` tend to the midpoint of the endpoints. -/
theorem tendsto_jacobiRecurrenceV (α β r s : ℂ) :
    Tendsto (fun n => jacobiRecurrenceV α β r s n) atTop (𝓝 ((r + s) / 2)) := by
  have h := (((tendsto_inv_add_two_mul (α + β + 2)).mul
    (tendsto_inv_add_two_mul (α + β + 4))).const_mul ((α ^ 2 - β ^ 2) * (r - s) / 2)).add_const
      ((r + s) / 2)
  simp only [mul_zero, zero_add] at h
  refine h.congr (fun n => ?_)
  simp only [jacobiRecurrenceV]
  rw [show α + β + 2 * (n : ℂ) + 2 = α + β + 2 + 2 * n by ring,
    show α + β + 2 * (n : ℂ) + 4 = α + β + 4 + 2 * n by ring]
  field_simp

/-- Carlson's recurrence coefficients `W_n` tend to one sixteenth of the squared
endpoint difference. -/
theorem tendsto_jacobiRecurrenceW (α β r s : ℂ) :
    Tendsto (fun n => jacobiRecurrenceW α β r s n) atTop (𝓝 ((r - s) ^ 2 / 16)) := by
  have h := ((((tendsto_add_div_add_two_mul 1 (α + β + 2)).mul
    (tendsto_add_div_add_two_mul (α + 1) (α + β + 2))).mul
      (tendsto_add_div_add_two_mul (β + 1) (α + β + 1))).mul
        (tendsto_add_div_add_two_mul (α + β + 1) (α + β + 3))).const_mul ((r - s) ^ 2)
  rw [show (r - s) ^ 2 * (1 / 2 * (1 / 2) * (1 / 2) * (1 / 2) : ℂ) = (r - s) ^ 2 / 16 by ring] at h
  refine h.congr (fun n => ?_)
  simp only [jacobiRecurrenceW]
  rw [show α + β + 2 * (n : ℂ) + 2 = α + β + 2 + 2 * n by ring,
    show α + β + 2 * (n : ℂ) + 1 = α + β + 1 + 2 * n by ring,
    show α + β + 2 * (n : ℂ) + 3 = α + β + 3 + 2 * n by ring]
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, mul_div_assoc']
  exact congrArg₂ (· / ·) (by ring) (by ring)

/-- A two-step recurrence that is a small perturbation of one with characteristic roots
`u, v`, `‖v‖ ≤ ‖u‖`, grows at most at the rate `‖u‖` plus a multiple of the perturbation
size. The estimate only needs `u ≠ v`; it does not require strict dominance. -/
theorem norm_le_of_perturbed_recurrence {u v : ℂ} (huv : u ≠ v) (hvu : ‖v‖ ≤ ‖u‖)
    {y : ℕ → ℂ} {δ : ℝ} (hδ : 0 ≤ δ) {N : ℕ}
    (hrec : ∀ n, N ≤ n →
      ‖y (n + 2) - (u + v) * y (n + 1) + u * v * y n‖ ≤ δ * (‖y (n + 1)‖ + ‖y n‖))
    (n : ℕ) (hn : N ≤ n) :
    ‖y n‖ ≤ 2 * (‖y (N + 1)‖ + ‖u‖ * ‖y N‖) / ‖u - v‖ *
      (‖u‖ + 2 * (‖u‖ + 1) * δ / ‖u - v‖) ^ (n - N) := by
  have hw : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
  set q := ‖u‖ + 2 * (‖u‖ + 1) * δ / ‖u - v‖ with hq
  let m : ℕ → ℝ := fun k => ‖y (k + 1) - u * y k‖ + ‖y (k + 1) - v * y k‖
  have hy0 (k : ℕ) : ‖y k‖ ≤ m k / ‖u - v‖ := by
    rw [le_div_iff₀ hw, ← norm_mul]
    calc
      _ = ‖(y (k + 1) - v * y k) - (y (k + 1) - u * y k)‖ := by congr 1; ring
      _ ≤ m k := (norm_sub_le _ _).trans_eq (add_comm _ _)
  have hy1 (k : ℕ) : ‖y (k + 1)‖ ≤ ‖u‖ * m k / ‖u - v‖ := by
    rw [le_div_iff₀ hw, ← norm_mul]
    calc
      _ = ‖u * (y (k + 1) - v * y k) - v * (y (k + 1) - u * y k)‖ := by congr 1; ring
      _ ≤ ‖u‖ * ‖y (k + 1) - v * y k‖ + ‖v‖ * ‖y (k + 1) - u * y k‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul]
      _ ≤ ‖u‖ * ‖y (k + 1) - v * y k‖ + ‖u‖ * ‖y (k + 1) - u * y k‖ := by gcongr
      _ = ‖u‖ * m k := by ring
  have hstep (k : ℕ) (hk : N ≤ k) : m (k + 1) ≤ q * m k := by
    set e := y (k + 2) - (u + v) * y (k + 1) + u * v * y k
    have he : ‖e‖ ≤ (‖u‖ + 1) * δ / ‖u - v‖ * m k := by
      refine (hrec k hk).trans ?_
      have := add_le_add (hy1 k) (hy0 k)
      calc
        _ ≤ δ * (‖u‖ * m k / ‖u - v‖ + m k / ‖u - v‖) := by gcongr
        _ = _ := by ring
    have hd : y (k + 1 + 1) - u * y (k + 1) = v * (y (k + 1) - u * y k) + e := by
      simp only [e]; ring
    have hg : y (k + 1 + 1) - v * y (k + 1) = u * (y (k + 1) - v * y k) + e := by
      simp only [e]; ring
    change ‖y (k + 1 + 1) - u * y (k + 1)‖ + ‖y (k + 1 + 1) - v * y (k + 1)‖ ≤ q * m k
    rw [hd, hg]
    have hm0 : 0 ≤ m k := by positivity
    calc
      _ ≤ (‖v‖ * ‖y (k + 1) - u * y k‖ + ‖e‖) + (‖u‖ * ‖y (k + 1) - v * y k‖ + ‖e‖) := by
        gcongr <;> exact (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ (‖u‖ * ‖y (k + 1) - u * y k‖ + ‖e‖) + (‖u‖ * ‖y (k + 1) - v * y k‖ + ‖e‖) := by
        gcongr
      _ = ‖u‖ * m k + 2 * ‖e‖ := by simp only [m]; ring
      _ ≤ ‖u‖ * m k + 2 * ((‖u‖ + 1) * δ / ‖u - v‖ * m k) := by gcongr
      _ = q * m k := by rw [hq]; ring
  have hq0 : 0 ≤ q := by positivity
  have hmN : m N ≤ 2 * (‖y (N + 1)‖ + ‖u‖ * ‖y N‖) := by
    simp only [m]
    have h1 := norm_sub_le (y (N + 1)) (u * y N)
    have h2 := norm_sub_le (y (N + 1)) (v * y N)
    rw [norm_mul] at h1 h2
    nlinarith [norm_nonneg (y N)]
  have hgrow (j : ℕ) : m (N + j) ≤ q ^ j * m N := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        m (N + (j + 1)) = m (N + j + 1) := by rw [add_assoc]
        _ ≤ q * m (N + j) := hstep _ (by omega)
        _ ≤ q * (q ^ j * m N) := by gcongr
        _ = q ^ (j + 1) * m N := by ring
  obtain ⟨j, rfl⟩ : ∃ j, n = N + j := ⟨n - N, by omega⟩
  rw [show N + j - N = j by omega]
  calc
    _ ≤ m (N + j) / ‖u - v‖ := hy0 _
    _ ≤ q ^ j * m N / ‖u - v‖ := by gcongr; exact hgrow j
    _ ≤ q ^ j * (2 * (‖y (N + 1)‖ + ‖u‖ * ‖y N‖)) / ‖u - v‖ := by gcongr
    _ = _ := by ring


/-- For all sufficiently large degrees the monic recurrence holds at every point,
for arbitrary complex parameters and endpoints. -/
theorem exists_forall_jacobiOn_three_term (α β r s : ℂ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ x : ℂ, (jacobiOn α β r s (n + 2)).eval x =
      (x - jacobiRecurrenceV α β r s n) * (jacobiOn α β r s (n + 1)).eval x -
        jacobiRecurrenceW α β r s n * (jacobiOn α β r s n).eval x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-(α + β).re)
  refine ⟨N, fun n hn x => ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  simp only [add_re] at hN
  have hre (k : ℕ) : 0 < (α + β + (n : ℂ) + k + 1).re := by
    simp only [add_re, natCast_re, one_re]
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  apply eval_jacobiOn_three_term
  · exact ascPochhammer_eval_ne_zero_of_re_pos (by simpa using hre 0) n
  · exact ascPochhammer_eval_ne_zero_of_re_pos (by push_cast; simpa [add_assoc] using hre 1) _
  · exact ascPochhammer_eval_ne_zero_of_re_pos (by push_cast; simpa [add_assoc] using hre 2) _
  · intro h
    have := congrArg re h
    simp only [add_re, mul_re, natCast_re, natCast_im, one_re, zero_re, re_ofNat, im_ofNat,
      mul_zero, sub_zero] at this
    linarith

/-- Monic Jacobi polynomials grow at most at the elliptic mean-radius rate, uniformly on
compact sets avoiding both endpoints: for every `ε > 0` there is one constant with
`‖pₙ(x)‖ ≤ C (μ(x) + ε)ⁿ` for all degrees and all points of the set. -/
theorem exists_bound_norm_eval_jacobiOn_of_isCompact (α β r s : ℂ) {K : Set ℂ}
    (hK : IsCompact K) (hr : r ∉ K) (hs : s ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ x ∈ K,
      ‖(jacobiOn α β r s n).eval x‖ ≤ C * (jacobiEllipseRadius r s x + ε) ^ n := by
  -- a positive lower bound for `‖x - r‖ * ‖x - s‖` on `K`
  obtain ⟨η, hη, hηK⟩ : ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K, η ≤ ‖x - r‖ * ‖x - s‖ := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne
      ((continuous_norm.comp (continuous_id.sub continuous_const)).mul
        (continuous_norm.comp (continuous_id.sub continuous_const))).continuousOn
    refine ⟨‖x₀ - r‖ * ‖x₀ - s‖, ?_, fun x hx => hmin hx⟩
    exact mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hr (h ▸ hx₀))))
      (norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hs (h ▸ hx₀))))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (continuous_jacobiEllipseRadius r s).continuousOn
  have hM0 : ∀ x ∈ K, jacobiEllipseRadius r s x ≤ |M| := fun x hx =>
    (le_abs_self _).trans ((hM x hx).trans (le_abs_self M))
  set M' := |M|
  have hM'0 : 0 ≤ M' := abs_nonneg M
  set δ₀ := ε * Real.sqrt η / (2 * (M' + 1)) with hδ₀
  have hδ₀pos : 0 < δ₀ := by positivity
  -- the perturbation size tends to zero
  set δ : ℕ → ℝ := fun n => ‖jacobiRecurrenceV α β r s n - (r + s) / 2‖ +
    ‖jacobiRecurrenceW α β r s n - (r - s) ^ 2 / 16‖
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h1 := (tendsto_jacobiRecurrenceV α β r s).sub_const ((r + s) / 2)
    have h2 := (tendsto_jacobiRecurrenceW α β r s).sub_const ((r - s) ^ 2 / 16)
    simpa using (h1.norm.add h2.norm)
  obtain ⟨Nr, hNr⟩ := exists_forall_jacobiOn_three_term α β r s
  obtain ⟨Nδ, hNδ⟩ := (hδ.eventually (gt_mem_nhds hδ₀pos)).exists_forall_of_atTop
  set N := max Nr Nδ
  -- bounds for the initial polynomials
  have hB : ∃ B : ℝ, 0 ≤ B ∧ ∀ k, k ≤ N + 1 → ∀ x ∈ K, ‖(jacobiOn α β r s k).eval x‖ ≤ B := by
    have hk (k : ℕ) := hK.exists_bound_of_continuousOn
      (jacobiOn α β r s k).continuous.continuousOn
    choose Bk hBk using hk
    refine ⟨∑ k ∈ Finset.range (N + 2), |Bk k|, by positivity, fun k hk x hx => ?_⟩
    calc
      _ ≤ |Bk k| := (hBk k x hx).trans (le_abs_self _)
      _ ≤ _ := Finset.single_le_sum (f := fun k => |Bk k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
  obtain ⟨B, hB0, hBK⟩ := hB
  set t := min 1 ε
  have ht : 0 < t := lt_min one_pos hε
  have ht1 : t ≤ 1 := min_le_left _ _
  refine ⟨(2 * (B + M' * B) / Real.sqrt η + B) / t ^ N, by positivity, fun n x hx => ?_⟩
  have hμ0 : 0 ≤ jacobiEllipseRadius r s x :=
    (div_nonneg (norm_nonneg _) (by norm_num)).trans (le_jacobiEllipseRadius r s x)
  have htμ : t ≤ jacobiEllipseRadius r s x + ε := (min_le_right _ _).trans (by linarith)
  have hpow (k : ℕ) : t ^ k ≤ (jacobiEllipseRadius r s x + ε) ^ k :=
    pow_le_pow_left₀ ht.le htμ k
  rcases lt_or_ge n N with hn | hn
  · -- finitely many initial degrees
    calc
      _ ≤ B := hBK n (by omega) x hx
      _ = B * t ^ N / t ^ N := by field_simp
      _ ≤ B * (jacobiEllipseRadius r s x + ε) ^ n / t ^ N := by
        gcongr
        exact (pow_le_pow_of_le_one ht.le ht1 hn.le).trans (hpow n)
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        gcongr
        have : 0 ≤ 2 * (B + M' * B) / Real.sqrt η := by positivity
        linarith
  -- the perturbed recurrence
  obtain ⟨u, v, huv₁, huv₂, hμ⟩ := exists_jacobiCharacteristicRoots r s x
  wlog hvu : ‖v‖ ≤ ‖u‖ generalizing u v
  · exact this v u (by rw [add_comm]; exact huv₁) (by rw [mul_comm]; exact huv₂)
      (by rw [max_comm]; exact hμ) (le_of_not_ge hvu)
  have hμu : jacobiEllipseRadius r s x = ‖u‖ := by rw [hμ, max_eq_left hvu]
  have hsq : (u - v) ^ 2 = (x - r) * (x - s) := by
    linear_combination (u + v + x - (r + s) / 2) * huv₁ - 4 * huv₂
  have hnormsq : ‖u - v‖ ^ 2 = ‖x - r‖ * ‖x - s‖ := by rw [← norm_pow, hsq, norm_mul]
  have hsqrt : Real.sqrt η ≤ ‖u - v‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (u - v)), hnormsq]
    exact Real.sqrt_le_sqrt (hηK x hx)
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have huv : u ≠ v := by
    intro h
    rw [h, sub_self, norm_zero] at hsqrt
    linarith
  have hrec : ∀ k, N ≤ k →
      ‖(jacobiOn α β r s (k + 2)).eval x - (u + v) * (jacobiOn α β r s (k + 1)).eval x +
          u * v * (jacobiOn α β r s k).eval x‖ ≤
        δ₀ * (‖(jacobiOn α β r s (k + 1)).eval x‖ + ‖(jacobiOn α β r s k).eval x‖) := by
    intro k hk
    rw [hNr k (le_trans (le_max_left _ _) hk) x, huv₁, huv₂]
    have hδk := (hNδ k (le_trans (le_max_right _ _) hk)).le
    calc
      _ = ‖((r + s) / 2 - jacobiRecurrenceV α β r s k) * (jacobiOn α β r s (k + 1)).eval x +
            ((r - s) ^ 2 / 16 - jacobiRecurrenceW α β r s k) *
              (jacobiOn α β r s k).eval x‖ := by congr 1; ring
      _ ≤ δ k * ‖(jacobiOn α β r s (k + 1)).eval x‖ + δ k * ‖(jacobiOn α β r s k).eval x‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_sub_rev, norm_sub_rev ((r - s) ^ 2 / 16)]
        gcongr
        · exact le_add_of_nonneg_right (norm_nonneg _)
        · exact le_add_of_nonneg_left (norm_nonneg _)
      _ ≤ _ := by rw [← mul_add]; gcongr
  have hgrow := norm_le_of_perturbed_recurrence (y := fun k => (jacobiOn α β r s k).eval x)
    huv hvu hδ₀pos.le hrec n hn
  have hq : ‖u‖ + 2 * (‖u‖ + 1) * δ₀ / ‖u - v‖ ≤ jacobiEllipseRadius r s x + ε := by
    rw [hμu]
    have hu : ‖u‖ ≤ M' := hμu ▸ hM0 x hx
    have h1 : 2 * (‖u‖ + 1) * δ₀ / ‖u - v‖ ≤ 2 * (‖u‖ + 1) * δ₀ / Real.sqrt η := by gcongr
    have h2 : 2 * (‖u‖ + 1) * δ₀ / Real.sqrt η ≤ ε := by
      rw [div_le_iff₀ hsη, hδ₀]
      have : 0 < M' + 1 := by linarith
      rw [show 2 * (‖u‖ + 1) * (ε * Real.sqrt η / (2 * (M' + 1))) =
        ε * Real.sqrt η * ((‖u‖ + 1) / (M' + 1)) by field_simp]
      have : (‖u‖ + 1) / (M' + 1) ≤ 1 := (div_le_one this).mpr (by linarith)
      nlinarith [mul_pos hε hsη]
    linarith
  have hinit : 2 * (‖(jacobiOn α β r s (N + 1)).eval x‖ + ‖u‖ * ‖(jacobiOn α β r s N).eval x‖) /
      ‖u - v‖ ≤ 2 * (B + M' * B) / Real.sqrt η := by
    have hu : ‖u‖ ≤ M' := hμu ▸ hM0 x hx
    have h1 := hBK (N + 1) le_rfl x hx
    have h2 := hBK N (by omega) x hx
    calc
      _ ≤ 2 * (B + M' * B) / ‖u - v‖ := by gcongr
      _ ≤ _ := by gcongr
  have hsplit : (jacobiEllipseRadius r s x + ε) ^ (n - N) * t ^ N ≤
      (jacobiEllipseRadius r s x + ε) ^ n := by
    calc
      _ ≤ (jacobiEllipseRadius r s x + ε) ^ (n - N) * (jacobiEllipseRadius r s x + ε) ^ N := by
        gcongr
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel hn]
  calc
    _ ≤ _ := hgrow
    _ ≤ 2 * (B + M' * B) / Real.sqrt η * (jacobiEllipseRadius r s x + ε) ^ (n - N) := by
      gcongr
    _ = 2 * (B + M' * B) / Real.sqrt η * ((jacobiEllipseRadius r s x + ε) ^ (n - N) * t ^ N) /
          t ^ N := by field_simp
    _ ≤ 2 * (B + M' * B) / Real.sqrt η * (jacobiEllipseRadius r s x + ε) ^ n / t ^ N := by
      gcongr
    _ = 2 * (B + M' * B) / Real.sqrt η / t ^ N * (jacobiEllipseRadius r s x + ε) ^ n := by ring
    _ ≤ _ := by gcongr; linarith

/-- The mean radius at an endpoint is the minimal value, one quarter of the focal
distance. -/
theorem jacobiEllipseRadius_left (r s : ℂ) : jacobiEllipseRadius r s r = ‖r - s‖ / 4 :=
  (jacobiEllipseRadius_eq_min_iff r s r).mpr (left_mem_segment ℝ r s)

/-- The mean radius at the second endpoint is also one quarter of the focal distance. -/
theorem jacobiEllipseRadius_right (r s : ℂ) : jacobiEllipseRadius r s s = ‖r - s‖ / 4 :=
  (jacobiEllipseRadius_eq_min_iff r s s).mpr (right_mem_segment ℝ r s)

/-- Monic Jacobi polynomials are bounded on closed elliptic disks by `C (ρ + ε)ⁿ`, for
every `ε > 0`. This is the upper half of Carlson's Theorem 7.5-2 for `p̂ₙ(ρ)`, for
arbitrary complex parameters and endpoints. -/
theorem exists_bound_norm_eval_jacobiOn_of_le (α β r s : ℂ) {ρ ε : ℝ}
    (hρ : ‖r - s‖ / 4 < ρ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, jacobiEllipseRadius r s x ≤ ρ →
      ‖(jacobiOn α β r s n).eval x‖ ≤ C * (ρ + ε) ^ n := by
  set K := {x | jacobiEllipseRadius r s x = ρ}
  have hK : IsCompact K :=
    (isCompact_jacobiClosedEllipseDisk r s ρ).of_isClosed_subset
      (isClosed_eq (continuous_jacobiEllipseRadius r s) continuous_const)
      (fun x hx => le_of_eq hx)
  have hrK : r ∉ K := by
    intro h
    change jacobiEllipseRadius r s r = ρ at h
    rw [jacobiEllipseRadius_left] at h
    linarith
  have hsK : s ∉ K := by
    intro h
    change jacobiEllipseRadius r s s = ρ at h
    rw [jacobiEllipseRadius_right] at h
    linarith
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_eval_jacobiOn_of_isCompact α β r s hK hrK hsK hε
  refine ⟨C, hC0, fun n x hx => ?_⟩
  have hKb : ∀ z ∈ K, ‖(jacobiOn α β r s n).eval z‖ ≤ C * (ρ + ε) ^ n := by
    intro z hz
    have := hC n z hz
    rwa [show jacobiEllipseRadius r s z = ρ from hz] at this
  rcases hx.lt_or_eq with hx | hx
  · apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := jacobiEllipseDisk r s ρ)
      (f := fun z => (jacobiOn α β r s n).eval z)
    · exact (isCompact_jacobiClosedEllipseDisk r s ρ).isBounded.subset
        (fun z (hz : jacobiEllipseRadius r s z < ρ) =>
          (le_of_lt hz : jacobiEllipseRadius r s z ≤ ρ))
    · exact (jacobiOn α β r s n).differentiable.diffContOnCl
    · intro z hz
      exact hKb z (frontier_lt_subset_eq (continuous_jacobiEllipseRadius r s)
        continuous_const hz)
    · exact subset_closure hx
  · exact hKb x hx

/-- At every point the monic Jacobi polynomials grow at most at the rate of the confocal
mean radius: `limsup ‖pₙ(x)‖^{1/n} ≤ μ(x)` (Carlson's Exercise 7.5-1), in the form of an
explicit bound for each `ε > 0`. -/
theorem exists_bound_norm_eval_jacobiOn (α β r s x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ‖(jacobiOn α β r s n).eval x‖ ≤ C * (jacobiEllipseRadius r s x + ε) ^ n := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_eval_jacobiOn_of_le α β r s
    (ρ := jacobiEllipseRadius r s x + ε / 2) (ε := ε / 2)
    (by linarith [le_jacobiEllipseRadius r s x]) (by linarith)
  refine ⟨C, hC0, fun n => ?_⟩
  have := hC n x (by linarith)
  rwa [show jacobiEllipseRadius r s x + ε / 2 + ε / 2 = jacobiEllipseRadius r s x + ε by ring]
    at this

end Carlson.TwoVariable
