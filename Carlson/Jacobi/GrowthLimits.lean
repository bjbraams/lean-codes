/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.EllipticExpansion
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Growth limits and ellipses of convergence

Off the focal segment, a bound `‖pₙ(x)‖ ≤ C lⁿ` with `l < μ(x)` would continue the Cauchy kernel
expansion in `y` holomorphically across its pole `y = x`; similarly for the second-kind
functions in `x`. Combined with an elementary Poincaré-type dichotomy for the perturbed
three-term recurrence, which has a strictly dominant characteristic root off the segment, this
gives Carlson's Theorem 7.5-1 for the polynomials: `‖pₙ(x)‖^{1/n} → μ(x)`. Consequences are the
divergence half of Theorem 7.5-3 for polynomial series, and the uniqueness and continuation
statements of Theorem 7.6-2.

## Main results

* `tendsto_norm_eval_jacobiOn_rpow`: Theorem 7.5-1 for the polynomials.
* `exists_lower_bound_norm_eval_jacobiOn`: the lower bound `c (μ(x) - ε)ⁿ ≤ ‖pₙ(x)‖`.
* `not_exists_bound_jacobiSecondKind`: no decay faster than `μ(y)⁻ⁿ` for the second kind.
* `tendstoLocallyUniformlyOn_sum_jacobiOn`, `not_summable_jacobiOn`: Theorem 7.5-3 for
  polynomial series.
* `jacobiContourCoefficient_eq_of_hasSum`: uniqueness from boundedness at one point.
* `hasSum_jacobiContourCoefficient_of_continuation`,
  `analyticOnNhd_tsum_jacobiContourCoefficient_of_bounded`: the ellipse of convergence is the
  boundary of the largest elliptic disk of holomorphy.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Theorems 7.5-1, 7.5-3 and 7.6-2.
-/

@[expose] public noncomputable section
open Complex Set Filter Polynomial
open scoped Topology

namespace Carlson.TwoVariable

/-- Off the segment the monic Jacobi polynomials cannot grow at a rate below the mean radius:
no bound `C λⁿ` with `λ < μ(x)` holds. Otherwise the Cauchy kernel expansion in `y` would
continue holomorphically across its pole `y = x`. -/
theorem not_exists_bound_norm_eval_jacobiOn (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {x : ℂ} (hx : x ∉ segment ℝ r s) {l : ℝ}
    (hl0 : 0 ≤ l) (hl : l < jacobiEllipseRadius r s x) :
    ¬ ∃ C : ℝ, ∀ n, ‖(jacobiOn α β r s n).eval x‖ ≤ C * l ^ n := by
  rintro ⟨C, hC⟩
  have hμx := lt_jacobiEllipseRadius hx
  set l' := max l ((‖r - s‖ / 4 + jacobiEllipseRadius r s x) / 2)
  have hl' : l' < jacobiEllipseRadius r s x := max_lt hl (by linarith)
  have hl'r' : ‖r - s‖ / 4 < l' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hl'r : ‖r - s‖ / 4 ≤ l' := hl'r'.le
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0); simpa using this
  set O := {y : ℂ | l' < jacobiEllipseRadius r s y}
  have hO : IsOpen O := isOpen_lt continuous_const (continuous_jacobiEllipseRadius r s)
  have hOseg : ∀ y ∈ O, y ∉ segment ℝ r s := fun y hy =>
    not_mem_segment_of_lt_jacobiEllipseRadius (lt_of_le_of_lt hl'r hy)
  -- a majorant on each closed exterior `μ ≥ σ` with `σ > l'`
  have hmaj : ∀ σ, l' < σ → ∃ M : ℕ → ℝ, Summable M ∧ ∀ n y, σ ≤ jacobiEllipseRadius r s y →
      ‖(jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y‖ ≤ M n := by
    intro σ hσ
    have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) (lt_of_le_of_lt hl'r hσ)
    have hl'0 : 0 ≤ l' := le_trans (by positivity) hl'r
    set ε := (σ - l') / (2 * σ * (l' + 1))
    have hε : 0 < ε := by simp only [ε]; apply div_pos <;> nlinarith
    obtain ⟨Cq, hCq0, hCq⟩ := exists_bound_jacobiSecondKind_exterior α β r s
      (lt_of_le_of_lt hl'r hσ) hε
    have hrate : l' * (1 / σ + ε) < 1 := by
      simp only [ε]
      rw [show l' * (1 / σ + (σ - l') / (2 * σ * (l' + 1))) =
        l' / σ + l' * (σ - l') / (2 * σ * (l' + 1)) by field_simp]
      have h1 : l' * (σ - l') / (2 * σ * (l' + 1)) ≤ (σ - l') / (2 * σ) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hl'0 (sub_nonneg.mpr hσ.le)]
      have h2 : l' / σ + (σ - l') / (2 * σ) < 1 := by
        rw [div_add_div _ _ hσ0.ne' (by positivity), div_lt_one (by positivity)]
        nlinarith
      linarith
    have hl0' : 0 ≤ l' * (1 / σ + ε) := by positivity
    refine ⟨fun n => C * Cq * (l' * (1 / σ + ε)) ^ n,
      (summable_geometric_of_lt_one hl0' hrate).mul_left _, fun n y hy => ?_⟩
    simp only [norm_mul, mul_pow]
    calc
      _ ≤ (C * l' ^ n) * (Cq * (1 / σ + ε) ^ n) := by
        apply mul_le_mul _ (hCq n y hy) (norm_nonneg _) (by positivity)
        exact (hC n).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hl0 (le_max_left _ _) n) hC0)
      _ = _ := by ring
  set F : ℂ → ℂ := fun y => ∑' n, (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y
  have hlocal : TendstoLocallyUniformlyOn
      (fun N y => ∑ n ∈ Finset.range N, (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y)
      F atTop O := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hO]
    intro K hKsub hK
    rcases K.eq_empty_or_nonempty with he | hne
    · subst he; exact tendstoUniformlyOn_empty
    obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne
      (continuous_jacobiEllipseRadius r s).continuousOn
    obtain ⟨M, hM, hbound⟩ := hmaj _ (hKsub hy₀)
    exact tendstoUniformlyOn_tsum_nat hM
      (f := fun n y => (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y)
      (fun n y hy => hbound n y (hmin hy))
  have hdiff : DifferentiableOn ℂ F O := by
    refine hlocal.differentiableOn (Eventually.of_forall fun N => ?_) hO
    apply DifferentiableOn.fun_sum
    intro n _
    exact (differentiableOn_const _).mul
      (fun y hy => ((analyticOnNhd_jacobiSecondKind α β r s n) y
        (hOseg y hy)).differentiableAt.differentiableWithinAt)
  set G : ℂ → ℂ := fun y => F y * (y - x)
  have hG : AnalyticOnNhd ℂ G O :=
    (hdiff.mul (differentiableOn_id.sub_const x)).analyticOnNhd hO
  -- a far point where the kernel identity holds nearby
  set zf : ℂ := ((4 * jacobiEllipseRadius r s x + ‖r‖ + 1 : ℝ) : ℂ)
  have hzf : jacobiEllipseRadius r s x < jacobiEllipseRadius r s zf := by
    have h1 := quarter_le_jacobiEllipseRadius r s zf
    have h2 : ‖zf‖ = 4 * jacobiEllipseRadius r s x + ‖r‖ + 1 := by
      simp only [zf, norm_real, Real.norm_eq_abs]
      have := le_jacobiEllipseRadius r s x
      have := norm_nonneg (r - s)
      have := norm_nonneg r
      exact abs_of_nonneg (by linarith)
    have h3 := norm_sub_norm_le zf r
    have h4 := norm_nonneg (zf - s)
    linarith
  have hevent : G =ᶠ[𝓝 zf] fun _ => 1 := by
    filter_upwards [(isOpen_lt continuous_const (continuous_jacobiEllipseRadius r s)).mem_nhds
      hzf] with y hy
    have hyx : y - x ≠ 0 := sub_ne_zero.mpr (fun h => by rw [h] at hy; exact lt_irrefl _ hy)
    simp only [G, F, (hasSum_jacobiOn_mul_jacobiSecondKind α β r s hc hy).tsum_eq,
      inv_mul_cancel₀ hyx]
  have heq := hG.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (isPreconnected_jacobiEllipse_exterior r s hl'r') (hl'.trans hzf) hevent
  have := heq (show x ∈ O from hl')
  simp [G] at this


/-- An eventual geometric bound with positive ratio extends to all indices. -/
theorem exists_forall_norm_le_of_eventually {y : ℕ → ℂ} {l : ℝ} (hl : 0 < l) {C : ℝ} {N : ℕ}
    (h : ∀ n, N ≤ n → ‖y n‖ ≤ C * l ^ n) : ∃ C' : ℝ, ∀ n, ‖y n‖ ≤ C' * l ^ n := by
  refine ⟨max C (∑ k ∈ Finset.range N, ‖y k‖ / l ^ k), fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · have hk : ‖y n‖ / l ^ n ≤ ∑ k ∈ Finset.range N, ‖y k‖ / l ^ k :=
      Finset.single_le_sum (f := fun k => ‖y k‖ / l ^ k) (fun k _ => by positivity)
        (Finset.mem_range.mpr hn)
    calc
      ‖y n‖ = ‖y n‖ / l ^ n * l ^ n := by field_simp
      _ ≤ _ := by gcongr; exact hk.trans (le_max_right _ _)
  · exact (h n hn).trans (by gcongr; exact le_max_left _ _)

/-- Poincaré-type lower bound for a perturbed two-step recurrence with a strictly dominant
characteristic root `u`: if the sequence does not grow at any rate below `‖u‖`, then it grows
at least at every rate below `‖u‖`. -/
theorem exists_lower_bound_of_perturbed_recurrence {u v : ℂ} (hvu : ‖v‖ < ‖u‖) {y : ℕ → ℂ}
    (hrec : ∀ η > 0, ∃ N, ∀ n, N ≤ n →
      ‖y (n + 2) - (u + v) * y (n + 1) + u * v * y n‖ ≤ η * (‖y (n + 1)‖ + ‖y n‖))
    (hnot : ∀ l, 0 < l → l < ‖u‖ → ¬ ∃ C : ℝ, ∀ n, ‖y n‖ ≤ C * l ^ n)
    {ε : ℝ} (hε : 0 < ε) (hεuv : ε < ‖u‖ - ‖v‖) :
    ∃ c > 0, ∃ N, ∀ n, N ≤ n → c * (‖u‖ - ε) ^ n ≤ ‖y n‖ := by
  have huv : u ≠ v := fun h => by rw [h] at hvu; exact lt_irrefl _ hvu
  have hw : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
  set κ := (‖u‖ + 1) / ‖u - v‖ with hκ
  have hκ0 : 0 < κ := by positivity
  set η := min ε ((‖u‖ - ‖v‖) / 2) / (2 * κ) with hη
  have hη0 : 0 < η := by
    apply div_pos (lt_min hε (by linarith)) (by positivity)
  have h2ηκ : 2 * η * κ = min ε ((‖u‖ - ‖v‖) / 2) := by simp only [hη]; field_simp
  have hA : 2 * η * κ ≤ ε := h2ηκ ▸ min_le_left _ _
  have hB : 2 * η * κ ≤ (‖u‖ - ‖v‖) / 2 := h2ηκ ▸ min_le_right _ _
  obtain ⟨N, hN⟩ := hrec η hη0
  set d : ℕ → ℂ := fun n => y (n + 1) - u * y n
  set g : ℕ → ℂ := fun n => y (n + 1) - v * y n
  have hyn (n : ℕ) : ‖y n‖ ≤ (‖d n‖ + ‖g n‖) / ‖u - v‖ := by
    rw [le_div_iff₀ hw, ← norm_mul]
    calc
      _ = ‖g n - d n‖ := by congr 1; simp only [d, g]; ring
      _ ≤ _ := (norm_sub_le _ _).trans_eq (add_comm _ _)
  have hyn1 (n : ℕ) : ‖y (n + 1)‖ ≤ ‖u‖ * (‖d n‖ + ‖g n‖) / ‖u - v‖ := by
    rw [le_div_iff₀ hw, ← norm_mul]
    calc
      _ = ‖u * g n - v * d n‖ := by congr 1; simp only [d, g]; ring
      _ ≤ ‖u‖ * ‖g n‖ + ‖v‖ * ‖d n‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ ‖u‖ * ‖g n‖ + ‖u‖ * ‖d n‖ := by gcongr
      _ = _ := by ring
  have he (n : ℕ) (hn : N ≤ n) :
      ‖y (n + 2) - (u + v) * y (n + 1) + u * v * y n‖ ≤ η * κ * (‖d n‖ + ‖g n‖) := by
    refine (hN n hn).trans ?_
    have := add_le_add (hyn1 n) (hyn n)
    calc
      _ ≤ η * (‖u‖ * (‖d n‖ + ‖g n‖) / ‖u - v‖ + (‖d n‖ + ‖g n‖) / ‖u - v‖) := by gcongr
      _ = _ := by simp only [hκ]; ring
  have hd1 (n : ℕ) : d (n + 1) = v * d n + (y (n + 2) - (u + v) * y (n + 1) + u * v * y n) := by
    simp only [d]; ring
  have hg1 (n : ℕ) : g (n + 1) = u * g n + (y (n + 2) - (u + v) * y (n + 1) + u * v * y n) := by
    simp only [g]; ring
  set e : ℕ → ℂ := fun n => y (n + 2) - (u + v) * y (n + 1) + u * v * y n
  have hv0 := norm_nonneg v
  by_cases hcase : ∃ n₀, N ≤ n₀ ∧ ‖d n₀‖ ≤ ‖g n₀‖
  · obtain ⟨n₀, hn₀N, hn₀⟩ := hcase
    set q := ‖u‖ - 2 * η * κ
    have hq : ‖u‖ - ε ≤ q := by linarith
    have hqv : ‖v‖ + 2 * η * κ ≤ q := by linarith
    have hq0 : 0 ≤ q := by linarith
    have hstep (n : ℕ) (hn : N ≤ n) (h : ‖d n‖ ≤ ‖g n‖) :
        ‖d (n + 1)‖ ≤ ‖g (n + 1)‖ ∧ q * ‖g n‖ ≤ ‖g (n + 1)‖ := by
      have heb : ‖e n‖ ≤ 2 * η * κ * ‖g n‖ := by
        have := he n hn
        have hηκ : 0 ≤ η * κ := by positivity
        calc
          ‖e n‖ ≤ η * κ * (‖d n‖ + ‖g n‖) := this
          _ ≤ η * κ * (‖g n‖ + ‖g n‖) := by gcongr
          _ = _ := by ring
      have hdn : ‖d (n + 1)‖ ≤ (‖v‖ + 2 * η * κ) * ‖g n‖ := by
        rw [hd1]
        calc
          _ ≤ ‖v‖ * ‖d n‖ + ‖e n‖ := (norm_add_le _ _).trans (by rw [norm_mul])
          _ ≤ ‖v‖ * ‖g n‖ + 2 * η * κ * ‖g n‖ := by gcongr
          _ = _ := by ring
      have hgn : q * ‖g n‖ ≤ ‖g (n + 1)‖ := by
        rw [hg1]
        have := norm_sub_norm_le (u * g n) (-(e n))
        simp only [sub_neg_eq_add, norm_neg, norm_mul] at this
        change q * ‖g n‖ ≤ ‖u * g n + e n‖
        nlinarith
      exact ⟨hdn.trans ((mul_le_mul_of_nonneg_right hqv (norm_nonneg _)).trans hgn), hgn⟩
    have hind : ∀ j, ‖d (n₀ + j)‖ ≤ ‖g (n₀ + j)‖ ∧ ‖g n₀‖ * q ^ j ≤ ‖g (n₀ + j)‖ := by
      intro j
      induction j with
      | zero => simpa using hn₀
      | succ j ih =>
        obtain ⟨h1, h2⟩ := ih
        obtain ⟨h3, h4⟩ := hstep (n₀ + j) (by omega) h1
        refine ⟨h3, ?_⟩
        calc
          ‖g n₀‖ * q ^ (j + 1) = q * (‖g n₀‖ * q ^ j) := by ring
          _ ≤ q * ‖g (n₀ + j)‖ := by gcongr
          _ ≤ _ := h4
    by_cases hg0 : g n₀ = 0
    · -- the sequence vanishes from `n₀` on
      exfalso
      have hgz : ∀ j, g (n₀ + j) = 0 := by
        intro j
        induction j with
        | zero => simpa using hg0
        | succ j ih =>
          have hdz : d (n₀ + j) = 0 := norm_le_zero_iff.mp (by simpa [ih] using (hind j).1)
          have hez : e (n₀ + j) = 0 := norm_le_zero_iff.mp (by
            simpa [hdz, ih] using he (n₀ + j) (by omega))
          have := hg1 (n₀ + j)
          simp only [e] at hez
          rw [hez, ih, mul_zero, add_zero] at this
          exact this
      have hyz : ∀ n, n₀ ≤ n → ‖y n‖ ≤ 0 * ((‖u‖ + ‖v‖) / 2) ^ n := by
        intro n hn
        obtain ⟨j, rfl⟩ : ∃ j, n = n₀ + j := ⟨n - n₀, by omega⟩
        have hdz : d (n₀ + j) = 0 := norm_le_zero_iff.mp (by simpa [hgz j] using (hind j).1)
        have := hyn (n₀ + j)
        rw [hdz, hgz j, norm_zero, add_zero, zero_div] at this
        simpa using this
      obtain ⟨C', hC'⟩ := exists_forall_norm_le_of_eventually (by linarith) hyz
      exact hnot _ (by linarith) (by linarith) ⟨C', hC'⟩
    have hgpos : 0 < ‖g n₀‖ := norm_pos_iff.mpr hg0
    have hue : 0 < ‖u‖ - ε := by linarith
    refine ⟨(‖u‖ - ‖v‖) * ‖g n₀‖ / (‖u - v‖ * (‖u‖ - ε) ^ (n₀ + 1)), by positivity,
      n₀ + 1, fun n hn => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, n = n₀ + j + 1 := ⟨n - n₀ - 1, by omega⟩
    have hlow : (‖u‖ - ‖v‖) * ‖g (n₀ + j)‖ ≤ ‖u - v‖ * ‖y (n₀ + j + 1)‖ := by
      rw [← norm_mul]
      have he' : (u - v) * y (n₀ + j + 1) = u * g (n₀ + j) - v * d (n₀ + j) := by
        simp only [d, g]; ring
      rw [he']
      have := norm_sub_norm_le (u * g (n₀ + j)) (v * d (n₀ + j))
      rw [norm_mul, norm_mul] at this
      nlinarith [(hind j).1, norm_nonneg (d (n₀ + j))]
    have hpow : (‖u‖ - ε) ^ (n₀ + j + 1) = (‖u‖ - ε) ^ (n₀ + 1) * (‖u‖ - ε) ^ j := by
      rw [← pow_add]; ring_nf
    rw [hpow]
    calc
      (‖u‖ - ‖v‖) * ‖g n₀‖ / (‖u - v‖ * (‖u‖ - ε) ^ (n₀ + 1)) *
          ((‖u‖ - ε) ^ (n₀ + 1) * (‖u‖ - ε) ^ j)
          = (‖u‖ - ‖v‖) * (‖g n₀‖ * (‖u‖ - ε) ^ j) / ‖u - v‖ := by field_simp
      _ ≤ (‖u‖ - ‖v‖) * (‖g n₀‖ * q ^ j) / ‖u - v‖ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hue.le hq j) hgpos.le) (by linarith)) hw.le
      _ ≤ (‖u‖ - ‖v‖) * ‖g (n₀ + j)‖ / ‖u - v‖ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hind j).2 (by linarith)) hw.le
      _ ≤ ‖y (n₀ + j + 1)‖ := by rw [div_le_iff₀ hw]; linarith
  · exfalso
    simp only [not_exists, not_and, not_le] at hcase
    set l := ‖v‖ + 2 * η * κ
    have hl0 : 0 < l := by positivity
    have hlu : l < ‖u‖ := by linarith
    have hdb : ∀ j, ‖d (N + j)‖ ≤ ‖d N‖ * l ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hgd := (hcase (N + j) (by omega)).le
        have heb : ‖e (N + j)‖ ≤ 2 * η * κ * ‖d (N + j)‖ := by
          have := he (N + j) (by omega)
          have hηκ : 0 ≤ η * κ := by positivity
          calc
            ‖e (N + j)‖ ≤ η * κ * (‖d (N + j)‖ + ‖g (N + j)‖) := this
            _ ≤ η * κ * (‖d (N + j)‖ + ‖d (N + j)‖) := by gcongr
            _ = _ := by ring
        rw [show N + (j + 1) = N + j + 1 by ring, hd1]
        calc
          _ ≤ ‖v‖ * ‖d (N + j)‖ + ‖e (N + j)‖ := (norm_add_le _ _).trans (by rw [norm_mul])
          _ ≤ ‖v‖ * ‖d (N + j)‖ + 2 * η * κ * ‖d (N + j)‖ := by gcongr
          _ = l * ‖d (N + j)‖ := by ring
          _ ≤ l * (‖d N‖ * l ^ j) := by gcongr
          _ = _ := by ring
    have hyb : ∀ n, N ≤ n → ‖y n‖ ≤ (2 * ‖d N‖ / (‖u - v‖ * l ^ N)) * l ^ n := by
      intro n hn
      obtain ⟨j, rfl⟩ : ∃ j, n = N + j := ⟨n - N, by omega⟩
      have hgd := (hcase (N + j) (by omega)).le
      calc
        ‖y (N + j)‖ ≤ (‖d (N + j)‖ + ‖g (N + j)‖) / ‖u - v‖ := hyn _
        _ ≤ (2 * (‖d N‖ * l ^ j)) / ‖u - v‖ := by gcongr; linarith [hdb j]
        _ = _ := by rw [pow_add]; field_simp
    obtain ⟨C', hC'⟩ := exists_forall_norm_le_of_eventually hl0 hyb
    exact hnot l hl0 hlu ⟨C', hC'⟩


/-- Off the segment the monic Jacobi polynomials grow at least at every rate below the mean
radius: `c (μ(x) - ε)ⁿ ≤ ‖pₙ(x)‖` for all large `n`. This is the lower half of Carlson's
Theorem 7.5-1 for the polynomials. -/
theorem exists_lower_bound_norm_eval_jacobiOn (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {x : ℂ} (hx : x ∉ segment ℝ r s) {ε : ℝ}
    (hε : 0 < ε) (hεμ : ε ≤ jacobiEllipseRadius r s x) :
    ∃ c > 0, ∃ N, ∀ n, N ≤ n →
      c * (jacobiEllipseRadius r s x - ε) ^ n ≤ ‖(jacobiOn α β r s n).eval x‖ := by
  obtain ⟨u, v, huv₁, huv₂, hu, hvu⟩ := exists_dominant_jacobiCharacteristicRoot r s x hx
  set ε' := min ε ((‖u‖ - ‖v‖) / 2)
  have hε' : 0 < ε' := lt_min hε (by linarith)
  have hε'uv : ε' < ‖u‖ - ‖v‖ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set δ : ℕ → ℝ := fun n => ‖jacobiRecurrenceV α β r s n - (r + s) / 2‖ +
    ‖jacobiRecurrenceW α β r s n - (r - s) ^ 2 / 16‖
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h1 := (tendsto_jacobiRecurrenceV α β r s).sub_const ((r + s) / 2)
    have h2 := (tendsto_jacobiRecurrenceW α β r s).sub_const ((r - s) ^ 2 / 16)
    simpa using (h1.norm.add h2.norm)
  obtain ⟨Nr, hNr⟩ := exists_forall_jacobiOn_three_term α β r s
  have hrec : ∀ η > 0, ∃ N, ∀ n, N ≤ n →
      ‖(jacobiOn α β r s (n + 2)).eval x - (u + v) * (jacobiOn α β r s (n + 1)).eval x +
          u * v * (jacobiOn α β r s n).eval x‖ ≤
        η * (‖(jacobiOn α β r s (n + 1)).eval x‖ + ‖(jacobiOn α β r s n).eval x‖) := by
    intro η hη
    obtain ⟨Nδ, hNδ⟩ := (hδ.eventually (gt_mem_nhds hη)).exists_forall_of_atTop
    refine ⟨max Nr Nδ, fun k hk => ?_⟩
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
  have hnot : ∀ l, 0 < l → l < ‖u‖ →
      ¬ ∃ C : ℝ, ∀ n, ‖(jacobiOn α β r s n).eval x‖ ≤ C * l ^ n := fun l hl0 hlu =>
    not_exists_bound_norm_eval_jacobiOn α β r s hc hx hl0.le (hu ▸ hlu)
  obtain ⟨c, hc0, N, hN⟩ := exists_lower_bound_of_perturbed_recurrence hvu
    (y := fun n => (jacobiOn α β r s n).eval x) hrec hnot hε' hε'uv
  refine ⟨c, hc0, N, fun n hn => (mul_le_mul_of_nonneg_left ?_ hc0.le).trans (hN n hn)⟩
  rw [← hu]
  exact pow_le_pow_left₀ (by linarith) (by linarith [min_le_left ε ((‖u‖ - ‖v‖) / 2)]) n

/-- Carlson's Theorem 7.5-1 for the polynomials: off the segment
`‖pₙ(x)‖^{1/n} → μ(x)`. -/
theorem tendsto_norm_eval_jacobiOn_rpow (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {x : ℂ} (hx : x ∉ segment ℝ r s) :
    Tendsto (fun n : ℕ => ‖(jacobiOn α β r s n).eval x‖ ^ (1 / (n : ℝ))) atTop
      (𝓝 (jacobiEllipseRadius r s x)) := by
  set μ := jacobiEllipseRadius r s x
  have hμ : 0 < μ := lt_of_le_of_lt (by positivity) (lt_jacobiEllipseRadius hx)
  have hroot (C : ℝ) (hC : 0 < C) : Tendsto (fun n : ℕ => C ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
    have h := ((Real.continuousAt_const_rpow hC.ne').tendsto).comp
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [Function.comp_def] using h
  rw [tendsto_order]
  constructor
  · intro a ha
    rcases lt_or_ge a 0 with ha0 | ha0
    · exact Eventually.of_forall fun n => ha0.trans_le (Real.rpow_nonneg (norm_nonneg _) _)
    set ε := (μ - a) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    obtain ⟨c, hc0, N, hN⟩ := exists_lower_bound_norm_eval_jacobiOn α β r s hc hx hε
      (by simp only [ε]; linarith)
    have hlim := (hroot c hc0).mul_const (μ - ε)
    rw [one_mul] at hlim
    filter_upwards [hlim.eventually (lt_mem_nhds (show a < μ - ε by simp only [ε]; linarith)),
      eventually_ge_atTop N, eventually_ne_atTop 0] with n h1 h2 h3
    refine h1.trans_le ?_
    have hbase : 0 ≤ μ - ε := by simp only [ε]; linarith
    calc
      c ^ (1 / (n : ℝ)) * (μ - ε) = (c * (μ - ε) ^ n) ^ (1 / (n : ℝ)) := by
        rw [Real.mul_rpow hc0.le (pow_nonneg hbase n), one_div,
          Real.pow_rpow_inv_natCast hbase h3]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (hN n h2) (by positivity)
  · intro b hb
    set ε := (b - μ) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    obtain ⟨C, hC0, hC⟩ := exists_bound_norm_eval_jacobiOn α β r s x hε
    have hlim := (hroot (C + 1) (by linarith)).mul_const (μ + ε)
    rw [one_mul] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds (show μ + ε < b by simp only [ε]; linarith)),
      eventually_ne_atTop 0] with n h1 h3
    refine lt_of_le_of_lt ?_ h1
    have hbase : 0 ≤ μ + ε := by linarith
    calc
      ‖(jacobiOn α β r s n).eval x‖ ^ (1 / (n : ℝ)) ≤ ((C + 1) * (μ + ε) ^ n) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (norm_nonneg _) ((hC n).trans (by gcongr; linarith)) (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (by linarith) (pow_nonneg hbase n), one_div,
          Real.pow_rpow_inv_natCast hbase h3]

/-- Off the segment the second-kind functions cannot decay faster than the reciprocal mean
radius: no bound `C lⁿ` with `l μ(y) < 1` holds. Otherwise the Cauchy kernel expansion in `x`
would continue holomorphically across its pole `x = y`. -/
theorem not_exists_bound_jacobiSecondKind (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {y : ℂ} (hy : y ∉ segment ℝ r s) {l : ℝ}
    (hl0 : 0 ≤ l) (hl : l * jacobiEllipseRadius r s y < 1) :
    ¬ ∃ C : ℝ, ∀ n, ‖jacobiSecondKind α β r s n y‖ ≤ C * l ^ n := by
  rintro ⟨C, hC⟩
  set m := jacobiEllipseRadius r s y
  have hm := lt_jacobiEllipseRadius hy
  have hC0 : 0 ≤ C := by have := (norm_nonneg _).trans (hC 0); simpa using this
  set ρ' := m + (1 - l * m) / (2 * (l + 1))
  have hρ'm : m < ρ' := by
    simp only [ρ']; have : 0 < (1 - l * m) / (2 * (l + 1)) := by
      apply div_pos <;> nlinarith
    linarith
  have hlρ' : l * ρ' < 1 := by
    simp only [ρ']
    have h1 : l * ((1 - l * m) / (2 * (l + 1))) ≤ (1 - l * m) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  have hρ'r : ‖r - s‖ / 4 < ρ' := hm.trans hρ'm
  have hρ'0 : 0 < ρ' := lt_of_le_of_lt (by positivity) hρ'r
  set O := jacobiEllipseDisk r s ρ'
  have hO : IsOpen O := isOpen_lt (continuous_jacobiEllipseRadius r s) continuous_const
  have hmaj : ∀ ρ, ‖r - s‖ / 4 < ρ → ρ < ρ' → ∃ M : ℕ → ℝ, Summable M ∧ ∀ n x,
      jacobiEllipseRadius r s x ≤ ρ →
        ‖(jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y‖ ≤ M n := by
    intro ρ hρ hρρ'
    obtain ⟨Cp, hCp0, hCp⟩ := exists_bound_norm_eval_jacobiOn_of_le α β r s hρ
      (sub_pos.mpr hρρ')
    refine ⟨fun n => Cp * C * (ρ' * l) ^ n,
      (summable_geometric_of_lt_one (by positivity) (by linarith)).mul_left _,
      fun n x hx => ?_⟩
    simp only [norm_mul, mul_pow]
    calc
      _ ≤ (Cp * (ρ + (ρ' - ρ)) ^ n) * (C * l ^ n) :=
        mul_le_mul (hCp n x hx) (hC n) (norm_nonneg _)
          (mul_nonneg hCp0 (pow_nonneg (by linarith) n))
      _ = _ := by rw [show ρ + (ρ' - ρ) = ρ' by ring]; ring
  set F : ℂ → ℂ := fun x => ∑' n, (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y
  have hlocal : TendstoLocallyUniformlyOn
      (fun N x => ∑ n ∈ Finset.range N, (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y)
      F atTop O := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hO]
    intro K hKsub hK
    rcases K.eq_empty_or_nonempty with he | hne
    · subst he; exact tendstoUniformlyOn_empty
    obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne
      (continuous_jacobiEllipseRadius r s).continuousOn
    have hx₀O : jacobiEllipseRadius r s x₀ < ρ' := hKsub hx₀
    obtain ⟨M, hM, hbound⟩ := hmaj (max (jacobiEllipseRadius r s x₀) ((‖r - s‖ / 4 + ρ') / 2))
      (lt_of_lt_of_le (by linarith) (le_max_right _ _)) (max_lt hx₀O (by linarith))
    exact tendstoUniformlyOn_tsum_nat hM
      (f := fun n x => (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y)
      (fun n x hx => hbound n x ((hmax hx).trans (le_max_left _ _)))
  have hdiff : DifferentiableOn ℂ F O := by
    refine hlocal.differentiableOn (Eventually.of_forall fun N => ?_) hO
    exact (DifferentiableOn.fun_sum fun n _ =>
      ((jacobiOn α β r s n).differentiable.differentiableOn).mul (differentiableOn_const _))
  set G : ℂ → ℂ := fun x => F x * (y - x)
  have hG : AnalyticOnNhd ℂ G O :=
    (hdiff.mul (differentiableOn_const y |>.sub differentiableOn_id)).analyticOnNhd hO
  have hrμ : jacobiEllipseRadius r s r < m := by rw [jacobiEllipseRadius_left]; exact hm
  have hevent : G =ᶠ[𝓝 r] fun _ => 1 := by
    filter_upwards [(isOpen_lt (continuous_jacobiEllipseRadius r s) continuous_const).mem_nhds
      hrμ] with x hx
    have hyx : y - x ≠ 0 := sub_ne_zero.mpr (fun h => by rw [← h] at hx; exact lt_irrefl _ hx)
    simp only [G, F, (hasSum_jacobiOn_mul_jacobiSecondKind α β r s hc hx).tsum_eq,
      inv_mul_cancel₀ hyx]
  have heq := hG.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (convex_jacobiEllipseDisk r s hρ'r).isPreconnected (hrμ.trans hρ'm) hevent
  have := heq (show y ∈ O from hρ'm)
  simp [G] at this

/-- For `0 ≤ ρ < σ` there is `ε > 0` with `(ρ + ε)(1/σ + ε) < 1`. -/
theorem exists_pos_add_mul_add_lt_one {ρ σ : ℝ} (hσ : 0 < σ) (hρσ : ρ < σ) :
    ∃ ε > 0, (ρ + ε) * (1 / σ + ε) < 1 := by
  have hlim : Tendsto (fun ε : ℝ => (ρ + ε) * (1 / σ + ε)) (𝓝 0) (𝓝 (ρ * (1 / σ))) := by
    have := ((continuous_const.add continuous_id).mul (continuous_const.add continuous_id)).tendsto
      (0 : ℝ) (f := fun ε : ℝ => (ρ + ε) * (1 / σ + ε))
    simpa using this
  have hlt : ρ * (1 / σ) < 1 := by rw [mul_one_div, div_lt_one hσ]; exact hρσ
  obtain ⟨ε, hεlt, hε⟩ := (((hlim.eventually (gt_mem_nhds hlt)).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  exact ⟨ε, hε, hεlt⟩

/-- Carlson's Theorem 7.5-3 for polynomial series, convergence part: if the coefficients grow at
most at the rate `1/σ`, the Jacobi series converges absolutely and locally uniformly on the open
elliptic disk of mean radius `σ`. -/
theorem tendstoLocallyUniformlyOn_sum_jacobiOn (α β r s : ℂ) (a : ℕ → ℂ) {σ : ℝ}
    (hσ : ‖r - s‖ / 4 < σ) (ha : ∀ ε > 0, ∃ C : ℝ, ∀ n, ‖a n‖ ≤ C * (1 / σ + ε) ^ n) :
    TendstoLocallyUniformlyOn (fun N x => ∑ n ∈ Finset.range N, a n * (jacobiOn α β r s n).eval x)
      (fun x => ∑' n, a n * (jacobiOn α β r s n).eval x) atTop (jacobiEllipseDisk r s σ) ∧
    ∀ x ∈ jacobiEllipseDisk r s σ, Summable (fun n => ‖a n * (jacobiOn α β r s n).eval x‖) := by
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  have hmaj : ∀ ρ, ‖r - s‖ / 4 < ρ → ρ < σ → ∃ M : ℕ → ℝ, Summable M ∧ ∀ n x,
      jacobiEllipseRadius r s x ≤ ρ → ‖a n * (jacobiOn α β r s n).eval x‖ ≤ M n := by
    intro ρ hρ hρσ
    have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ.le
    obtain ⟨ε, hε, hεlt⟩ := exists_pos_add_mul_add_lt_one hσ0 hρσ
    obtain ⟨C, hC⟩ := ha ε hε
    have hC0 : 0 ≤ C := by have := (norm_nonneg _).trans (hC 0); simpa using this
    obtain ⟨Cp, hCp0, hCp⟩ := exists_bound_norm_eval_jacobiOn_of_le α β r s hρ hε
    refine ⟨fun n => C * Cp * ((ρ + ε) * (1 / σ + ε)) ^ n,
      (summable_geometric_of_lt_one (by positivity) hεlt).mul_left _, fun n x hx => ?_⟩
    simp only [norm_mul, mul_pow]
    calc
      _ ≤ (C * (1 / σ + ε) ^ n) * (Cp * (ρ + ε) ^ n) :=
        mul_le_mul (hC n) (hCp n x hx) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hO : IsOpen (jacobiEllipseDisk r s σ) :=
    isOpen_lt (continuous_jacobiEllipseRadius r s) continuous_const
  refine ⟨?_, fun x hx => ?_⟩
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hO]
    intro K hKsub hK
    rcases K.eq_empty_or_nonempty with he | hne
    · subst he; exact tendstoUniformlyOn_empty
    obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne
      (continuous_jacobiEllipseRadius r s).continuousOn
    obtain ⟨M, hM, hbound⟩ := hmaj (max (jacobiEllipseRadius r s x₀) ((‖r - s‖ / 4 + σ) / 2))
      (lt_of_lt_of_le (by linarith) (le_max_right _ _)) (max_lt (hKsub hx₀) (by linarith))
    exact tendstoUniformlyOn_tsum_nat hM
      (f := fun n x => a n * (jacobiOn α β r s n).eval x)
      (fun n x hx => hbound n x ((hmax hx).trans (le_max_left _ _)))
  · have hxσ : jacobiEllipseRadius r s x < σ := hx
    obtain ⟨M, hM, hbound⟩ := hmaj (max (jacobiEllipseRadius r s x) ((‖r - s‖ / 4 + σ) / 2))
      (lt_of_lt_of_le (by linarith) (le_max_right _ _)) (max_lt hxσ (by linarith))
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => hbound n x (le_max_left _ _)) hM

/-- Carlson's Theorem 7.5-3 for polynomial series, divergence part: if the coefficients grow at
least at the rate `1/σ` infinitely often, the Jacobi series diverges at every point of the open
elliptic exterior of mean radius `σ`; its terms do not tend to zero. -/
theorem not_summable_jacobiOn (α β r s : ℂ) (hc : IsGammaRegular (α + β + 2))
    (a : ℕ → ℂ) {σ : ℝ} (hσ : ‖r - s‖ / 4 < σ)
    (ha : ∀ ε > 0, ∀ C : ℝ, ∃ᶠ n in atTop, C * (1 / σ - ε) ^ n ≤ ‖a n‖) {x : ℂ}
    (hx : σ < jacobiEllipseRadius r s x) :
    ¬ Tendsto (fun n => a n * (jacobiOn α β r s n).eval x) atTop (𝓝 0) := by
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  set m := jacobiEllipseRadius r s x
  have hxs := not_mem_segment_of_lt_jacobiEllipseRadius (hσ.trans hx)
  -- a small `ε` with `(1/σ - ε)(m - ε) > 1`
  have hlim : Tendsto (fun ε : ℝ => (1 / σ - ε) * (m - ε)) (𝓝 0) (𝓝 (1 / σ * m)) := by
    have := ((continuous_const.sub continuous_id).mul (continuous_const.sub continuous_id)).tendsto
      (0 : ℝ) (f := fun ε : ℝ => (1 / σ - ε) * (m - ε))
    simpa using this
  have hgt : 1 < 1 / σ * m := by rw [one_div_mul_eq_div, one_lt_div hσ0]; exact hx
  obtain ⟨ε, ⟨hεgt, hε1, hε2⟩, hε⟩ := ((((hlim.eventually (lt_mem_nhds hgt)).and
    ((tendsto_id.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / σ by positivity))).and
      (tendsto_id.eventually (gt_mem_nhds (show (0 : ℝ) < m by linarith))))).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hε0 : 0 < ε := hε
  obtain ⟨c, hc0, N, hN⟩ := exists_lower_bound_norm_eval_jacobiOn α β r s hc hxs hε0
    (by simp only [id] at hε2; linarith)
  intro htend
  have hfreq := ha ε hε0 (1 / c)
  have hsmall := (htend.norm.eventually (gt_mem_nhds (show ‖(0 : ℂ)‖ < 1 by simp)))
  obtain ⟨n, ⟨hn1, hn2⟩, hnN⟩ := ((hfreq.and_eventually hsmall).and_eventually
    (eventually_ge_atTop N)).exists
  have hpos : 0 < 1 / σ - ε := by simpa using hε1
  have h1 : 1 ≤ ((1 / σ - ε) * (m - ε)) ^ n := one_le_pow₀ hεgt.le
  have h2 : ((1 / σ - ε) * (m - ε)) ^ n ≤ ‖a n * (jacobiOn α β r s n).eval x‖ := by
    rw [norm_mul, mul_pow]
    calc
      (1 / σ - ε) ^ n * (m - ε) ^ n = (1 / c * (1 / σ - ε) ^ n) * (c * (m - ε) ^ n) := by
        field_simp
      _ ≤ ‖a n‖ * ‖(jacobiOn α β r s n).eval x‖ :=
        mul_le_mul hn1 (hN n hnN) (by positivity) (norm_nonneg _)
  linarith

/-- If the terms of a Jacobi series are bounded at one point off the segment, its coefficients
grow at most at the reciprocal of the mean radius of that point. -/
theorem exists_bound_of_bounded_jacobiOn (α β r s : ℂ) (hc : IsGammaRegular (α + β + 2))
    (b : ℕ → ℂ) {x₀ : ℂ} (hx₀ : x₀ ∉ segment ℝ r s)
    (hb : ∃ B : ℝ, ∀ n, ‖b n * (jacobiOn α β r s n).eval x₀‖ ≤ B) :
    ∀ ε > 0, ∃ C : ℝ, ∀ n, ‖b n‖ ≤ C * (1 / jacobiEllipseRadius r s x₀ + ε) ^ n := by
  intro ε hε
  obtain ⟨B, hB⟩ := hb
  set m := jacobiEllipseRadius r s x₀
  have hm : 0 < m := lt_of_le_of_lt (by positivity) (lt_jacobiEllipseRadius hx₀)
  set ε' := min (m / 2) (ε * m ^ 2 / 2)
  have hε' : 0 < ε' := lt_min (by positivity) (by positivity)
  have hε'm : ε' ≤ m / 2 := min_le_left _ _
  have hε'ε : ε' ≤ ε * m ^ 2 / 2 := min_le_right _ _
  have hme : 0 < m - ε' := by linarith
  have hrate : 1 / (m - ε') ≤ 1 / m + ε := by
    rw [div_le_iff₀ hme]
    have h1 : (1 / m + ε) * (m - ε') = 1 + ε * m - ε' / m - ε * ε' := by field_simp; ring
    rw [h1]
    have h2 : ε' / m ≤ ε * m / 2 := by rw [div_le_iff₀ hm]; nlinarith
    nlinarith
  obtain ⟨c, hc0, N, hN⟩ := exists_lower_bound_norm_eval_jacobiOn α β r s hc hx₀ hε' (by linarith)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  apply exists_forall_norm_le_of_eventually (N := N) (C := B / c) (by positivity)
  intro n hn
  have hp := hN n hn
  have hpos : 0 < c * (m - ε') ^ n := by positivity
  have hpn : 0 < ‖(jacobiOn α β r s n).eval x₀‖ := hpos.trans_le hp
  calc
    ‖b n‖ = ‖b n * (jacobiOn α β r s n).eval x₀‖ / ‖(jacobiOn α β r s n).eval x₀‖ := by
      rw [norm_mul]; field_simp
    _ ≤ B / (c * (m - ε') ^ n) := div_le_div₀ hB0 (hB n) hpos hp
    _ = B / c * (1 / (m - ε')) ^ n := by rw [one_div_pow]; field_simp
    _ ≤ B / c * (1 / m + ε) ^ n := by gcongr

/-- Uniqueness in Theorem 7.6-2 in Carlson's form: a Jacobi series whose terms are bounded at a
point off the segment, and which sums to `f` on a confocal ellipse inside the elliptic disk of
that point, has the contour coefficients of `f` on that ellipse. -/
theorem jacobiContourCoefficient_eq_of_hasSum (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) (b : ℕ → ℂ) {x₀ : ℂ} (hx₀ : x₀ ∉ segment ℝ r s)
    (hb : ∃ B : ℝ, ∀ n, ‖b n * (jacobiOn α β r s n).eval x₀‖ ≤ B) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ‖r - s‖ / 4 < σ) (hσx : σ < jacobiEllipseRadius r s x₀) {f : ℂ → ℂ}
    (hf : ∀ x ∈ (jacobiEllipseCycle r s hσ0).range,
      HasSum (fun n => b n * (jacobiOn α β r s n).eval x) (f x)) (n : ℕ) :
    jacobiContourCoefficient α β r s n (jacobiEllipseCycle r s hσ0) f = b n := by
  obtain ⟨hloc, -⟩ := tendstoLocallyUniformlyOn_sum_jacobiOn α β r s b
    (lt_jacobiEllipseRadius hx₀) (exists_bound_of_bounded_jacobiOn α β r s hc b hx₀ hb)
  have hsub : (jacobiEllipseCycle r s hσ0).range ⊆
      jacobiEllipseDisk r s (jacobiEllipseRadius r s x₀) := fun z hz =>
    show jacobiEllipseRadius r s z < jacobiEllipseRadius r s x₀ by
      rw [jacobiEllipseRadius_of_mem_range_jacobiEllipseCycle r s hσ0 hσ.le hz]; exact hσx
  have hunif := ((tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt (continuous_jacobiEllipseRadius r s) continuous_const)).mp hloc _ hsub
      (jacobiEllipseCycle r s hσ0).isCompact_range)
  exact jacobiContourCoefficient_jacobiEllipseCycle_eq_of_tendstoUniformlyOn α β r s hc hσ0 hσ b
    (hunif.congr_right (fun x hx => (hf x hx).tsum_eq)) n

/-- Theorem 7.6-2, continuation: if `f` continues holomorphically to a larger confocal elliptic
disk, its Jacobi series converges to the continuation throughout that disk. -/
theorem hasSum_jacobiContourCoefficient_of_continuation (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {τ ω : ℝ} {f g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (jacobiEllipseDisk r s ω)) (hτω : τ ≤ ω)
    (hfg : EqOn f g (jacobiEllipseDisk r s τ)) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ‖r - s‖ / 4 < σ) (hστ : σ < τ) {x : ℂ} (hx : jacobiEllipseRadius r s x < ω) :
    HasSum (fun n => jacobiContourCoefficient α β r s n (jacobiEllipseCycle r s hσ0) f *
      (jacobiOn α β r s n).eval x) (g x) := by
  set σ' := max σ ((jacobiEllipseRadius r s x + ω) / 2)
  have hσ'0 : 0 < σ' := lt_of_lt_of_le hσ0 (le_max_left _ _)
  have hσ' : ‖r - s‖ / 4 < σ' := lt_of_lt_of_le hσ (le_max_left _ _)
  have hσ'ω : σ' < ω := max_lt (hστ.trans_le hτω) (by linarith)
  have hxσ' : jacobiEllipseRadius r s x < σ' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have h := hasSum_jacobiContourCoefficient_jacobiEllipseCycle α β r s hc hg hσ'0 hσ' hσ'ω hxσ'
  have hind (n : ℕ) : jacobiContourCoefficient α β r s n (jacobiEllipseCycle r s hσ'0) g =
      jacobiContourCoefficient α β r s n (jacobiEllipseCycle r s hσ0) f := by
    rw [jacobiContourCoefficient_jacobiEllipseCycle_eq α β r s n hg hσ'0 hσ0 hσ' hσ hσ'ω
      (hστ.trans_le hτω)]
    unfold jacobiContourCoefficient
    congr 1
    apply Cycle.integral_congr
    intro z hz
    have hzτ : z ∈ jacobiEllipseDisk r s τ := show jacobiEllipseRadius r s z < τ by
      rw [jacobiEllipseRadius_of_mem_range_jacobiEllipseCycle r s hσ0 hσ.le hz]; exact hστ
    simp only [hfg hzτ]
  simpa only [hind] using h

/-- Theorem 7.6-2, ellipse of convergence: if the terms of the Jacobi series of `f` are bounded
at a point `x₀` beyond the disk of holomorphy, its sum is holomorphic on the elliptic disk of
`x₀` and continues `f` there. -/
theorem analyticOnNhd_tsum_jacobiContourCoefficient_of_bounded (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {τ : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (jacobiEllipseDisk r s τ)) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ‖r - s‖ / 4 < σ) (hστ : σ < τ) {x₀ : ℂ} (hx₀ : τ ≤ jacobiEllipseRadius r s x₀)
    (hb : ∃ B : ℝ, ∀ n, ‖jacobiContourCoefficient α β r s n (jacobiEllipseCycle r s hσ0) f *
      (jacobiOn α β r s n).eval x₀‖ ≤ B) :
    AnalyticOnNhd ℂ (fun x => ∑' n, jacobiContourCoefficient α β r s n
        (jacobiEllipseCycle r s hσ0) f * (jacobiOn α β r s n).eval x)
        (jacobiEllipseDisk r s (jacobiEllipseRadius r s x₀)) ∧
      EqOn (fun x => ∑' n, jacobiContourCoefficient α β r s n
        (jacobiEllipseCycle r s hσ0) f * (jacobiOn α β r s n).eval x) f
        (jacobiEllipseDisk r s τ) := by
  have hx₀s : x₀ ∉ segment ℝ r s :=
    not_mem_segment_of_lt_jacobiEllipseRadius ((hσ.trans hστ).trans_le hx₀)
  obtain ⟨hloc, -⟩ := tendstoLocallyUniformlyOn_sum_jacobiOn α β r s _
    (lt_jacobiEllipseRadius hx₀s) (exists_bound_of_bounded_jacobiOn α β r s hc _ hx₀s hb)
  have hO : IsOpen (jacobiEllipseDisk r s (jacobiEllipseRadius r s x₀)) :=
    isOpen_lt (continuous_jacobiEllipseRadius r s) continuous_const
  refine ⟨(hloc.differentiableOn (Eventually.of_forall fun N =>
    DifferentiableOn.fun_sum fun n _ => (differentiableOn_const _).mul
      (jacobiOn α β r s n).differentiable.differentiableOn) hO).analyticOnNhd hO,
    fun x hx => ?_⟩
  exact (hasSum_jacobiContourCoefficient_of_continuation α β r s hc hf le_rfl (fun _ _ => rfl)
    hσ0 hσ hστ (show jacobiEllipseRadius r s x < τ from hx)).tsum_eq

end Carlson.TwoVariable
