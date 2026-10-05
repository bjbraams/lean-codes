/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.GrowthLimits
public import Carlson.Jacobi.Recurrence

/-!
# The second-kind recurrence and growth limits

Computing the Jacobi coefficients of `x ↦ x / (y - x)` on a confocal ellipse in two ways, once
from the Cauchy kernel expansion and once from the polynomial recurrence, gives Carlson's
three-term recurrence for the second-kind functions (Exercise 7.1-6). Off the segment the
second-kind functions are the recessive solution of this recurrence: an elementary dichotomy for
perturbed recurrences, together with the exterior upper bound and the continuation argument,
gives `‖qₙ(y)‖^{1/n} → 1/μ(y)` (Theorem 7.5-1) and hence both halves of Theorem 7.5-3 for
second-kind series.

## Main results

* `exists_jacobiSecondKind_three_term`: the second-kind recurrence.
* `exists_lower_bound_norm_jacobiSecondKind`: the lower bound `c (1/μ(y) - ε)ⁿ ≤ ‖qₙ(y)‖`.
* `tendsto_norm_jacobiSecondKind_rpow`: Theorem 7.5-1 for the second-kind functions.
* `tendstoLocallyUniformlyOn_sum_jacobiSecondKind_exterior`, `not_tendsto_jacobiSecondKind`:
  Theorem 7.5-3 for second-kind series.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Exercise 7.1-6 and Theorems 7.5-1 and 7.5-3.
-/

@[expose] public noncomputable section
open Complex Set Filter Polynomial ContinuousLinearMap
open scoped Topology

namespace Carlson.TwoVariable

/-- The Jacobi coefficient functionals vanish on polynomials of lower degree. -/
theorem carlsonJacobiCoefficient_eq_zero_of_natDegree_lt (α β r s : ℂ) {k : ℕ} {p : ℂ[X]}
    (hp : p.natDegree < k) : carlsonJacobiCoefficient α β r s k p = 0 := by
  rw [carlsonJacobiCoefficient_apply, iterate_derivative_eq_zero hp, map_zero, zero_div]

/-- The monic Jacobi polynomial of degree zero is one. -/
theorem jacobiOn_zero (α β r s : ℂ) : jacobiOn α β r s 0 = 1 := by
  simp [jacobiOn, monicShiftedJacobi]

/-- Contour coefficients depend only on the values of the function on the cycle. -/
theorem jacobiContourCoefficient_congr (α β r s : ℂ) (n : ℕ) (Γ : Cycle) {f g : ℂ → ℂ}
    (h : EqOn f g Γ.range) :
    jacobiContourCoefficient α β r s n Γ f = jacobiContourCoefficient α β r s n Γ g := by
  unfold jacobiContourCoefficient
  congr 1
  apply Cycle.integral_congr
  intro z hz
  simp only [h hz]

/-- Carlson's recurrence for the second-kind functions (Exercise 7.1-6, second relation), for
all sufficiently large degrees and every point off the segment:
`W_{n+1} q_{n+2}(y) = (y - V_n) q_{n+1}(y) - q_n(y)`. It is derived from the polynomial
recurrence by computing the Jacobi coefficients of `x ↦ x / (y - x)` in two ways. -/
theorem exists_jacobiSecondKind_three_term (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ y, y ∉ segment ℝ r s →
      jacobiRecurrenceW α β r s (n + 1) * jacobiSecondKind α β r s (n + 2) y =
        (y - jacobiRecurrenceV α β r s n) * jacobiSecondKind α β r s (n + 1) y -
          jacobiSecondKind α β r s n y := by
  obtain ⟨Nr, hNr⟩ := exists_forall_jacobiOn_three_term α β r s
  have hX : ∀ j, Nr ≤ j → X * jacobiOn α β r s (j + 1) = jacobiOn α β r s (j + 2) +
      C (jacobiRecurrenceV α β r s j) * jacobiOn α β r s (j + 1) +
        C (jacobiRecurrenceW α β r s j) * jacobiOn α β r s j := by
    intro j hj
    apply Polynomial.funext
    intro x
    simp only [eval_mul, eval_add, eval_X, eval_C, hNr j hj x]
    ring
  refine ⟨Nr + 1, fun n hn y hy => ?_⟩
  set k := n + 1
  set q : ℕ → ℂ := fun m => jacobiSecondKind α β r s m y
  set c : ℕ → ℂ := fun m => if m = n then 1 else if m = n + 1 then jacobiRecurrenceV α β r s n
    else if m = n + 2 then jacobiRecurrenceW α β r s (n + 1) else 0
  -- the coefficients of `X * pₘ`
  have hcoef : ∀ m, carlsonJacobiCoefficient α β r s k (X * jacobiOn α β r s m) = c m := by
    intro m
    rcases le_or_gt m Nr with hm | hm
    · have hdeg : (X * jacobiOn α β r s m).natDegree < k := by
        calc
          _ ≤ 1 + (jacobiOn α β r s m).natDegree := natDegree_mul_le.trans (by
            rw [natDegree_X])
          _ ≤ 1 + m := by
            gcongr
            simp only [jacobiOn]
            refine (natDegree_comp_le).trans ?_
            simp only [natDegree_X_sub_C, mul_one]
            exact (natDegree_scaleRoots _ _).le.trans (by
              rw [monicShiftedJacobi]
              exact (natDegree_C_mul_le _ _).trans (natDegree_shiftedJacobi_le _ _ _))
          _ < k := by simp only [k]; omega
      rw [carlsonJacobiCoefficient_eq_zero_of_natDegree_lt α β r s hdeg]
      simp only [c]
      split_ifs <;> first | rfl | (exfalso; omega)
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rw [hX j (by omega), map_add, map_add, show C (jacobiRecurrenceV α β r s j) *
        jacobiOn α β r s (j + 1) = jacobiRecurrenceV α β r s j • jacobiOn α β r s (j + 1) by
          rw [smul_eq_C_mul], show C (jacobiRecurrenceW α β r s j) * jacobiOn α β r s j =
            jacobiRecurrenceW α β r s j • jacobiOn α β r s j by rw [smul_eq_C_mul],
        map_smul, map_smul, carlsonJacobiCoefficient_apply_jacobiOn α β r s hc,
        carlsonJacobiCoefficient_apply_jacobiOn α β r s hc,
        carlsonJacobiCoefficient_apply_jacobiOn α β r s hc]
      simp only [c, k, smul_eq_mul]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> first | ring1 | (exfalso; omega) |
        (obtain rfl : j = n := (by omega); ring1) |
        (obtain rfl : j = n + 1 := (by omega); ring1)
  -- a confocal ellipse inside the elliptic disk of `y`
  have hμy := lt_jacobiEllipseRadius hy
  set ρ := (‖r - s‖ / 4 + jacobiEllipseRadius r s y) / 2
  have hρ : ‖r - s‖ / 4 < ρ := by simp only [ρ]; linarith
  have hρy : ρ < jacobiEllipseRadius r s y := by simp only [ρ]; linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt (by positivity) hρ
  set Γ := jacobiEllipseCycle r s hρ0
  have hΓ := jacobiEllipseCycle_isC1 r s hρ0
  have hΓρ : ∀ x ∈ Γ.range, jacobiEllipseRadius r s x = ρ := fun x hx =>
    jacobiEllipseRadius_of_mem_range_jacobiEllipseCycle r s hρ0 hρ.le hx
  have havoid : Γ.range ⊆ (segment ℝ r s)ᶜ := fun x hx =>
    not_mem_segment_of_lt_jacobiEllipseRadius (by rw [hΓρ x hx]; exact hρ)
  have hind : Γ.index r = 1 :=
    index_jacobiEllipseCycle_of_lt r s hρ0 hρ (by rw [jacobiEllipseRadius_left]; exact hρ)
  -- uniform convergence of the kernel on the ellipse
  have hker := tendstoUniformlyOn_sum_jacobiOn_mul_jacobiSecondKind_ellipse α β r s hc hρ hρy
  have hkerΓ : TendstoUniformlyOn
      (fun M x => ∑ m ∈ Finset.range M, q m * (jacobiOn α β r s m).eval x)
      (fun x => (y - x)⁻¹) atTop Γ.range := by
    rw [Metric.tendstoUniformlyOn_iff] at hker ⊢
    intro ε hε
    filter_upwards [hker ε hε] with M hM x hx
    have := hM (x, y) ⟨(hΓρ x hx).le,
      show jacobiEllipseRadius r s y ≤ jacobiEllipseRadius r s y from le_rfl⟩
    simpa only [q, mul_comm] using this
  -- first computation: the coefficient of `(y - x)⁻¹` is `qₖ(y)`
  have hc1 : jacobiContourCoefficient α β r s k Γ (fun x => (y - x)⁻¹) = q k := by
    rw [jacobiContourCoefficient_eq_of_tendstoUniformlyOn α β r s hc q Γ hΓ havoid hkerΓ k,
      hind, one_mul]
  have hyΓ : ∀ x ∈ Γ.range, y - x ≠ 0 := fun x hx h => by
    have := hΓρ x hx; rw [← sub_eq_zero.mp h] at this; linarith
  have hcont : ContinuousOn (fun x => (y - x)⁻¹) Γ.range :=
    (continuousOn_const.sub continuousOn_id).inv₀ hyΓ
  have hG1 : jacobiContourCoefficient α β r s k Γ (fun x => x * (y - x)⁻¹) = y * q k := by
    have he : EqOn (fun x => x * (y - x)⁻¹) (fun x => y * (y - x)⁻¹ - (1 : ℂ[X]).eval x)
        Γ.range := fun x hx => by
      simp only [eval_one]; field_simp [hyΓ x hx]; ring
    rw [jacobiContourCoefficient_congr α β r s k Γ he,
      jacobiContourCoefficient_sub α β r s k Γ hΓ havoid (f := fun x => y * (y - x)⁻¹)
        (g := fun x => (1 : ℂ[X]).eval x) (continuousOn_const.mul hcont)
        (Polynomial.continuous _).continuousOn,
      jacobiContourCoefficient_const_mul, hc1,
      jacobiContourCoefficient_polynomial α β r s k 1 Γ hΓ havoid, hind, one_mul,
      ← jacobiOn_zero α β r s, carlsonJacobiCoefficient_apply_jacobiOn α β r s hc,
      ite_eq_right (by omega), sub_zero]
  -- second computation through the polynomial partial sums
  set P : ℕ → ℂ[X] := fun M => ∑ m ∈ Finset.range M, q m • (X * jacobiOn α β r s m)
  have hPeval (M : ℕ) (x : ℂ) : (P M).eval x =
      x * ∑ m ∈ Finset.range M, q m * (jacobiOn α β r s m).eval x := by
    simp only [P, eval_finsetSum, eval_smul, eval_mul, eval_X, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _; ring
  obtain ⟨B, hB⟩ := Γ.isCompact_range.exists_bound_of_continuousOn continuousOn_id
  have hPlim : TendstoUniformlyOn (fun M x => (P M).eval x) (fun x => x * (y - x)⁻¹) atTop
      Γ.range := by
    rw [Metric.tendstoUniformlyOn_iff] at hkerΓ ⊢
    intro ε hε
    obtain ⟨δ, hδ, hBδ⟩ := exists_pos_mul_lt hε (|B| + 1)
    filter_upwards [hkerΓ δ hδ] with M hM x hx
    rw [dist_eq_norm, hPeval, ← mul_sub, norm_mul]
    have h1 := hM x hx
    rw [dist_eq_norm] at h1
    calc
      ‖x‖ * ‖(y - x)⁻¹ - ∑ m ∈ Finset.range M, q m * (jacobiOn α β r s m).eval x‖
          ≤ (|B| + 1) * δ := mul_le_mul (((hB x hx).trans (le_abs_self B)).trans (by linarith))
            h1.le (norm_nonneg _) (by positivity)
      _ < ε := by linarith
  have htend := tendsto_jacobiContourCoefficient α β r s k Γ hΓ havoid
    (fun M => (Polynomial.continuous _).continuousOn) hPlim
  have hPcoef : ∀ M, n + 3 ≤ M → jacobiContourCoefficient α β r s k Γ (fun x => (P M).eval x) =
      q n + jacobiRecurrenceV α β r s n * q (n + 1) +
        jacobiRecurrenceW α β r s (n + 1) * q (n + 2) := by
    intro M hM
    rw [jacobiContourCoefficient_polynomial α β r s k _ Γ hΓ havoid, hind, one_mul]
    simp only [P, map_sum, map_smul, hcoef, smul_eq_mul]
    have hexp : ∀ m, q m * c m = (if m = n then q n else 0) +
        (if m = n + 1 then jacobiRecurrenceV α β r s n * q (n + 1) else 0) +
        (if m = n + 2 then jacobiRecurrenceW α β r s (n + 1) * q (n + 2) else 0) := by
      intro m
      simp only [c]
      split_ifs <;> first | ring1 | (exfalso; omega) | (subst_vars; ring1)
    simp only [hexp, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range,
      ite_eq_left (show n < M by omega), ite_eq_left (show n + 1 < M by omega),
      ite_eq_left (show n + 2 < M by omega)]
  have hlim2 : Tendsto (fun M => jacobiContourCoefficient α β r s k Γ (fun x => (P M).eval x))
      atTop (𝓝 (q n + jacobiRecurrenceV α β r s n * q (n + 1) +
        jacobiRecurrenceW α β r s (n + 1) * q (n + 2))) :=
    tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨n + 3, fun M hM => (hPcoef M hM).symm⟩)
  have heq := tendsto_nhds_unique htend hlim2
  rw [hG1] at heq
  simp only [q, k] at heq ⊢
  linear_combination -heq


/-- A geometric sequence with larger ratio cannot be dominated by one with smaller ratio. -/
theorem not_forall_mul_pow_le {c C m l : ℝ} (hc : 0 < c) (hl : 0 ≤ l) (hlm : l < m) (N : ℕ) :
    ¬ ∀ j, N ≤ j → c * m ^ j ≤ C * l ^ j := by
  intro h
  have hm : 0 < m := hl.trans_lt hlm
  rcases eq_or_lt_of_le hl with hl0 | hl0
  · have := h (N + 1) (by omega)
    rw [← hl0, zero_pow (by omega), mul_zero] at this
    have : 0 < c * m ^ (N + 1) := by positivity
    linarith
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (C / c) (one_lt_div hl0 |>.mpr hlm)
  have h1 := h (N + j) (by omega)
  rw [div_pow, lt_div_iff₀ (by positivity)] at hj
  have h2 : c * m ^ (N + j) ≤ C * l ^ (N + j) := h1
  rw [pow_add, pow_add] at h2
  have hlN : 0 < l ^ N := by positivity
  have hmN : l ^ N ≤ m ^ N := pow_le_pow_left₀ hl hlm.le N
  have : c * (l ^ N * m ^ j) ≤ C * (l ^ N * l ^ j) :=
    calc c * (l ^ N * m ^ j) ≤ c * (m ^ N * m ^ j) := by gcongr
      _ ≤ C * (l ^ N * l ^ j) := h2
  have key : C * l ^ j < c * m ^ j := by
    have h3 := mul_lt_mul_of_pos_left hj hc
    rwa [show c * (C / c * l ^ j) = C * l ^ j by field_simp] at h3
  have k2 := mul_lt_mul_of_pos_right key hlN
  have e1 : c * (l ^ N * m ^ j) = c * m ^ j * l ^ N := by ring
  have e2 : C * (l ^ N * l ^ j) = C * l ^ j * l ^ N := by ring
  linarith

/-- Lower bound for the recessive solution of a perturbed two-step recurrence with characteristic
roots `‖a‖ < ‖b‖`: a solution growing more slowly than `‖b‖`, and not faster-decaying than every
rate below `‖a‖`, grows at least at every rate below `‖a‖`. -/
theorem exists_lower_bound_of_perturbed_recurrence_recessive {a b : ℂ} (hab : ‖a‖ < ‖b‖)
    {y : ℕ → ℂ}
    (hrec : ∀ η > 0, ∃ N, ∀ n, N ≤ n →
      ‖y (n + 2) - (a + b) * y (n + 1) + a * b * y n‖ ≤ η * (‖y (n + 1)‖ + ‖y n‖))
    {l : ℝ} (hal : ‖a‖ < l) (hlb : l < ‖b‖) {C : ℝ} (hup : ∀ n, ‖y n‖ ≤ C * l ^ n)
    (hnot : ∀ l', 0 < l' → l' < ‖a‖ → ¬ ∃ C' : ℝ, ∀ n, ‖y n‖ ≤ C' * l' ^ n)
    {ε : ℝ} (hε : 0 < ε) (hεa : ε < ‖a‖) :
    ∃ c > 0, ∃ N, ∀ n, N ≤ n → c * (‖a‖ - ε) ^ n ≤ ‖y n‖ := by
  have hba : a ≠ b := fun h => by rw [h] at hab; exact lt_irrefl _ hab
  have hw : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hba))
  have ha0 : 0 < ‖a‖ := hε.trans hεa
  set κ := (‖b‖ + 1) / ‖b - a‖ with hκ
  have hκ0 : 0 < κ := by positivity
  set t := min ε (min ((‖b‖ - ‖a‖) / 4) ((‖b‖ - l) / 2))
  have ht0 : 0 < t := lt_min hε (lt_min (by linarith) (by linarith))
  set η := t / (2 * κ)
  have hη0 : 0 < η := by positivity
  have h2ηκ : 2 * η * κ = t := by simp only [η]; field_simp
  have hA : 2 * η * κ ≤ ε := h2ηκ ▸ min_le_left _ _
  have hB : 2 * η * κ ≤ (‖b‖ - ‖a‖) / 4 := h2ηκ ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hC : 2 * η * κ ≤ (‖b‖ - l) / 2 := h2ηκ ▸ (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N, hN⟩ := hrec η hη0
  set d : ℕ → ℂ := fun n => y (n + 1) - a * y n
  set g : ℕ → ℂ := fun n => y (n + 1) - b * y n
  set e : ℕ → ℂ := fun n => y (n + 2) - (a + b) * y (n + 1) + a * b * y n
  have hyn (n : ℕ) : ‖y n‖ ≤ (‖d n‖ + ‖g n‖) / ‖b - a‖ := by
    rw [le_div_iff₀ hw, ← norm_mul]
    calc
      _ = ‖d n - g n‖ := by congr 1; simp only [d, g]; ring
      _ ≤ _ := norm_sub_le _ _
  have hyn1 (n : ℕ) : ‖y (n + 1)‖ ≤ ‖b‖ * (‖d n‖ + ‖g n‖) / ‖b - a‖ := by
    rw [le_div_iff₀ hw, ← norm_mul]
    calc
      _ = ‖b * d n - a * g n‖ := by congr 1; simp only [d, g]; ring
      _ ≤ ‖b‖ * ‖d n‖ + ‖a‖ * ‖g n‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ ‖b‖ * ‖d n‖ + ‖b‖ * ‖g n‖ := by gcongr
      _ = _ := by ring
  have he (n : ℕ) (hn : N ≤ n) : ‖e n‖ ≤ η * κ * (‖d n‖ + ‖g n‖) := by
    refine (hN n hn).trans ?_
    have := add_le_add (hyn1 n) (hyn n)
    calc
      _ ≤ η * (‖b‖ * (‖d n‖ + ‖g n‖) / ‖b - a‖ + (‖d n‖ + ‖g n‖) / ‖b - a‖) := by gcongr
      _ = _ := by simp only [hκ]; ring
  have hd1 (n : ℕ) : d (n + 1) = b * d n + e n := by simp only [d, e]; ring
  have hg1 (n : ℕ) : g (n + 1) = a * g n + e n := by simp only [g, e]; ring
  have hηκ : 0 ≤ η * κ := by positivity
  by_cases hcase : ∃ n₀, N ≤ n₀ ∧ ‖g n₀‖ ≤ ‖d n₀‖
  · -- the dominant component takes over, contradicting the upper bound
    exfalso
    obtain ⟨n₀, hn₀N, hn₀⟩ := hcase
    set m := ‖b‖ - 2 * η * κ
    have hm : l < m := by linarith
    have hstep (n : ℕ) (hn : N ≤ n) (h : ‖g n‖ ≤ ‖d n‖) :
        ‖g (n + 1)‖ ≤ ‖d (n + 1)‖ ∧ m * ‖d n‖ ≤ ‖d (n + 1)‖ := by
      have heb : ‖e n‖ ≤ 2 * η * κ * ‖d n‖ := by
        calc ‖e n‖ ≤ η * κ * (‖d n‖ + ‖g n‖) := he n hn
          _ ≤ η * κ * (‖d n‖ + ‖d n‖) := by gcongr
          _ = _ := by ring
      have hdn : m * ‖d n‖ ≤ ‖d (n + 1)‖ := by
        rw [hd1]
        have := norm_sub_norm_le (b * d n) (-(e n))
        simp only [sub_neg_eq_add, norm_neg, norm_mul] at this
        nlinarith
      have hgn : ‖g (n + 1)‖ ≤ (‖a‖ + 2 * η * κ) * ‖d n‖ := by
        rw [hg1]
        calc
          _ ≤ ‖a‖ * ‖g n‖ + ‖e n‖ := (norm_add_le _ _).trans (by rw [norm_mul])
          _ ≤ ‖a‖ * ‖d n‖ + 2 * η * κ * ‖d n‖ := by gcongr
          _ = _ := by ring
      refine ⟨hgn.trans ((mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)).trans hdn),
        hdn⟩
    have hind : ∀ j, ‖g (n₀ + j)‖ ≤ ‖d (n₀ + j)‖ ∧ ‖d n₀‖ * m ^ j ≤ ‖d (n₀ + j)‖ := by
      intro j
      induction j with
      | zero => simpa using hn₀
      | succ j ih =>
        obtain ⟨h3, h4⟩ := hstep (n₀ + j) (by omega) ih.1
        refine ⟨h3, ?_⟩
        calc ‖d n₀‖ * m ^ (j + 1) = m * (‖d n₀‖ * m ^ j) := by ring
          _ ≤ m * ‖d (n₀ + j)‖ := mul_le_mul_of_nonneg_left ih.2 (by linarith)
          _ ≤ _ := h4
    by_cases hd0 : d n₀ = 0
    · -- the solution vanishes from `n₀` on
      have hdz : ∀ j, d (n₀ + j) = 0 ∧ g (n₀ + j) = 0 := by
        intro j
        induction j with
        | zero => exact ⟨by simpa using hd0, norm_le_zero_iff.mp (by simpa [hd0] using hn₀)⟩
        | succ j ih =>
          have hez : e (n₀ + j) = 0 := norm_le_zero_iff.mp (by
            simpa [ih.1, ih.2] using he (n₀ + j) (by omega))
          rw [show n₀ + (j + 1) = n₀ + j + 1 by ring, hd1, hg1, ih.1, ih.2, hez]
          simp
      have hyz : ∀ n, n₀ ≤ n → ‖y n‖ ≤ 0 * (‖a‖ / 2) ^ n := by
        intro n hn
        obtain ⟨j, rfl⟩ : ∃ j, n = n₀ + j := ⟨n - n₀, by omega⟩
        have := hyn (n₀ + j)
        rw [(hdz j).1, (hdz j).2, norm_zero, add_zero, zero_div] at this
        simpa using this
      obtain ⟨C', hC'⟩ := exists_forall_norm_le_of_eventually (by linarith) hyz
      exact hnot _ (by linarith) (by linarith) ⟨C', hC'⟩
    have hdpos : 0 < ‖d n₀‖ := norm_pos_iff.mpr hd0
    apply not_forall_mul_pow_le (c := (‖b‖ - ‖a‖) * ‖d n₀‖ / (‖b - a‖ * m ^ (n₀ + 1)))
      (C := C) (m := m) (l := l) (by have : 0 < m := by linarith
                                     positivity) (by linarith) hm (n₀ + 1)
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = n₀ + j + 1 := ⟨n - n₀ - 1, by omega⟩
    have hm0 : 0 < m := by linarith
    have hlow : (‖b‖ - ‖a‖) * ‖d (n₀ + j)‖ ≤ ‖b - a‖ * ‖y (n₀ + j + 1)‖ := by
      rw [← norm_mul]
      have he' : (b - a) * y (n₀ + j + 1) = b * d (n₀ + j) - a * g (n₀ + j) := by
        simp only [d, g]; ring
      rw [he']
      have := norm_sub_norm_le (b * d (n₀ + j)) (a * g (n₀ + j))
      rw [norm_mul, norm_mul] at this
      nlinarith [(hind j).1, norm_nonneg (g (n₀ + j))]
    refine le_trans ?_ (hup (n₀ + j + 1))
    calc
      (‖b‖ - ‖a‖) * ‖d n₀‖ / (‖b - a‖ * m ^ (n₀ + 1)) * m ^ (n₀ + j + 1)
          = (‖b‖ - ‖a‖) * (‖d n₀‖ * m ^ j) / ‖b - a‖ := by
            rw [show m ^ (n₀ + j + 1) = m ^ (n₀ + 1) * m ^ j by ring]; field_simp
      _ ≤ (‖b‖ - ‖a‖) * ‖d (n₀ + j)‖ / ‖b - a‖ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hind j).2 (by linarith)) hw.le
      _ ≤ ‖y (n₀ + j + 1)‖ := by rw [div_le_iff₀ hw]; linarith
  · simp only [not_exists, not_and, not_le] at hcase
    -- the ratio `‖dₙ‖ / ‖gₙ‖` stays below one half
    have hhalf : ∀ n, N ≤ n → ‖d n‖ < ‖g n‖ / 2 := by
      intro n₁ hn₁
      by_contra hcon
      simp only [not_lt] at hcon
      set lam := (‖b‖ - 3 * η * κ) / (‖a‖ + 2 * η * κ)
      have hden : 0 < ‖a‖ + 2 * η * κ := by positivity
      have hlam : 1 < lam := by rw [one_lt_div hden]; linarith
      have hgrow : ∀ j, lam ^ j * (‖g (n₁ + j)‖ / 2) ≤ ‖d (n₁ + j)‖ := by
        intro j
        induction j with
        | zero => simpa using hcon
        | succ j ih =>
          set n := n₁ + j
          have hdg := hcase n (by omega)
          have hge : ‖g n‖ / 2 ≤ ‖d n‖ :=
            le_trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hlam.le)) ih
          have heb1 : ‖e n‖ ≤ 3 * η * κ * ‖d n‖ := by
            calc ‖e n‖ ≤ η * κ * (‖d n‖ + ‖g n‖) := he n (by omega)
              _ ≤ η * κ * (‖d n‖ + 2 * ‖d n‖) := by gcongr; linarith
              _ = _ := by ring
          have heb2 : ‖e n‖ ≤ 2 * η * κ * ‖g n‖ := by
            calc ‖e n‖ ≤ η * κ * (‖d n‖ + ‖g n‖) := he n (by omega)
              _ ≤ η * κ * (‖g n‖ + ‖g n‖) := by gcongr
              _ = _ := by ring
          have hdn : (‖b‖ - 3 * η * κ) * ‖d n‖ ≤ ‖d (n + 1)‖ := by
            rw [hd1]
            have := norm_sub_norm_le (b * d n) (-(e n))
            simp only [sub_neg_eq_add, norm_neg, norm_mul] at this
            nlinarith
          have hgn : ‖g (n + 1)‖ ≤ (‖a‖ + 2 * η * κ) * ‖g n‖ := by
            rw [hg1]
            calc
              _ ≤ ‖a‖ * ‖g n‖ + ‖e n‖ := (norm_add_le _ _).trans (by rw [norm_mul])
              _ ≤ ‖a‖ * ‖g n‖ + 2 * η * κ * ‖g n‖ := by gcongr
              _ = _ := by ring
          rw [show n₁ + (j + 1) = n + 1 by ring]
          calc
            lam ^ (j + 1) * (‖g (n + 1)‖ / 2)
                ≤ lam ^ (j + 1) * ((‖a‖ + 2 * η * κ) * ‖g n‖ / 2) := by gcongr
            _ = (‖b‖ - 3 * η * κ) * (lam ^ j * (‖g n‖ / 2)) := by
              simp only [lam]; rw [pow_succ]; field_simp
            _ ≤ (‖b‖ - 3 * η * κ) * ‖d n‖ := by
              apply mul_le_mul_of_nonneg_left ih; linarith
            _ ≤ _ := hdn
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt 2 hlam
      have h1 := hgrow j
      have h2 := hcase (n₁ + j) (by omega)
      have hg0 : 0 < ‖g (n₁ + j)‖ := lt_of_le_of_lt (norm_nonneg _) h2
      nlinarith
    -- the recessive component then decays no faster than `‖a‖ - ε`
    have hgN : 0 < ‖g N‖ := by have := hhalf N le_rfl; linarith [norm_nonneg (d N)]
    have hae : 0 < ‖a‖ - ε := by linarith
    have hglow : ∀ j, ‖g N‖ * (‖a‖ - ε) ^ j ≤ ‖g (N + j)‖ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        set n := N + j
        have heb : ‖e n‖ ≤ 2 * η * κ * ‖g n‖ := by
          calc ‖e n‖ ≤ η * κ * (‖d n‖ + ‖g n‖) := he n (by omega)
            _ ≤ η * κ * (‖g n‖ + ‖g n‖) := by
              gcongr; linarith [hhalf n (by omega), norm_nonneg (g n)]
            _ = _ := by ring
        have hgn : (‖a‖ - ε) * ‖g n‖ ≤ ‖g (n + 1)‖ := by
          rw [hg1]
          have := norm_sub_norm_le (a * g n) (-(e n))
          simp only [sub_neg_eq_add, norm_neg, norm_mul] at this
          nlinarith [norm_nonneg (g n)]
        rw [show N + (j + 1) = n + 1 by ring]
        calc ‖g N‖ * (‖a‖ - ε) ^ (j + 1) = (‖a‖ - ε) * (‖g N‖ * (‖a‖ - ε) ^ j) := by ring
          _ ≤ (‖a‖ - ε) * ‖g n‖ := by gcongr
          _ ≤ _ := hgn
    refine ⟨‖g N‖ / (2 * ‖b - a‖ * (‖a‖ - ε) ^ N), by positivity, N, fun n hn => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, n = N + j := ⟨n - N, by omega⟩
    have hy : ‖g (N + j)‖ / 2 ≤ ‖b - a‖ * ‖y (N + j)‖ := by
      rw [← norm_mul]
      have he' : (b - a) * y (N + j) = d (N + j) - g (N + j) := by simp only [d, g]; ring
      rw [he']
      have := norm_sub_norm_le (g (N + j)) (d (N + j))
      rw [norm_sub_rev (g (N + j))] at this
      linarith [hhalf (N + j) (by omega)]
    calc
      ‖g N‖ / (2 * ‖b - a‖ * (‖a‖ - ε) ^ N) * (‖a‖ - ε) ^ (N + j)
          = ‖g N‖ * (‖a‖ - ε) ^ j / (2 * ‖b - a‖) := by rw [pow_add]; field_simp
      _ ≤ ‖g (N + j)‖ / (2 * ‖b - a‖) := by gcongr; exact hglow j
      _ ≤ ‖y (N + j)‖ := by
        rw [div_le_iff₀ (by positivity)]; linarith


/-- Off the segment the second-kind functions decay no faster than every rate below the
reciprocal mean radius: `c (1/μ(y) - ε)ⁿ ≤ ‖qₙ(y)‖` for all large `n`. -/
theorem exists_lower_bound_norm_jacobiSecondKind (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {y : ℂ} (hy : y ∉ segment ℝ r s) {ε : ℝ}
    (hε : 0 < ε) (hεμ : ε < 1 / jacobiEllipseRadius r s y) :
    ∃ c > 0, ∃ N, ∀ n, N ≤ n →
      c * (1 / jacobiEllipseRadius r s y - ε) ^ n ≤ ‖jacobiSecondKind α β r s n y‖ := by
  set μ := jacobiEllipseRadius r s y
  have hμ : 0 < μ := lt_of_le_of_lt (by positivity) (lt_jacobiEllipseRadius hy)
  by_cases hrs : r = s
  · subst hrs
    have hys : y ≠ r := fun h => hy (h ▸ left_mem_segment ℝ r r)
    have hμe : μ = ‖y - r‖ := jacobiEllipseRadius_self r y
    refine ⟨1 / μ, by positivity, 0, fun n _ => ?_⟩
    rw [jacobiSecondKind_self α β r y hc n hys, zpow_neg, norm_inv, norm_zpow,
      show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← hμe,
      ← inv_pow, pow_succ, ← one_div]
    rw [mul_comm]
    gcongr
    linarith
  obtain ⟨u, v, huv₁, huv₂, hu, hvu⟩ := exists_dominant_jacobiCharacteristicRoot r s y hy
  set w := (r - s) ^ 2 / 16
  have hw0 : w ≠ 0 := by
    simp only [w]; exact div_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hrs)) (by norm_num)
  have hu0 : u ≠ 0 := fun h => by rw [h, zero_mul] at huv₂; exact hw0 huv₂.symm
  have hv0 : v ≠ 0 := fun h => by rw [h, mul_zero] at huv₂; exact hw0 huv₂.symm
  set a := u⁻¹
  set b := v⁻¹
  have ha : ‖a‖ = 1 / μ := by simp only [a, norm_inv, hu, one_div]; rfl
  have hab : ‖a‖ < ‖b‖ := by
    simp only [a, b, norm_inv]
    exact inv_strictAnti₀ (norm_pos_iff.mpr hv0) hvu
  have hsum : a + b = (y - (r + s) / 2) / w := by
    rw [← huv₁, ← huv₂]; simp only [a, b]; field_simp; ring
  have hprod : a * b = 1 / w := by rw [← huv₂]; simp only [a, b]; field_simp
  -- the perturbed recurrence for the second-kind functions
  obtain ⟨Nq, hNq⟩ := exists_jacobiSecondKind_three_term α β r s hc
  have hV := tendsto_jacobiRecurrenceV α β r s
  have hW : Tendsto (fun n => jacobiRecurrenceW α β r s (n + 1)) atTop (𝓝 w) :=
    (tendsto_jacobiRecurrenceW α β r s).comp (tendsto_add_atTop_nat 1)
  set K := (‖y - (r + s) / 2‖ + 2) / (‖w‖ / 2)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hrec : ∀ η > 0, ∃ N, ∀ n, N ≤ n →
      ‖jacobiSecondKind α β r s (n + 2) y - (a + b) * jacobiSecondKind α β r s (n + 1) y +
          a * b * jacobiSecondKind α β r s n y‖ ≤
        η * (‖jacobiSecondKind α β r s (n + 1) y‖ + ‖jacobiSecondKind α β r s n y‖) := by
    intro η hη
    have hδ : Tendsto (fun n => (‖w - jacobiRecurrenceW α β r s (n + 1)‖ * K +
        ‖(r + s) / 2 - jacobiRecurrenceV α β r s n‖) / ‖w‖) atTop (𝓝 0) := by
      have h1 := ((tendsto_const_nhds (x := w)).sub hW).norm.mul_const K
      have h2 := ((tendsto_const_nhds (x := (r + s) / 2)).sub hV).norm
      simpa using (h1.add h2).div_const ‖w‖
    have hev : ∀ᶠ n in atTop,
        ‖jacobiSecondKind α β r s (n + 2) y - (a + b) * jacobiSecondKind α β r s (n + 1) y +
          a * b * jacobiSecondKind α β r s n y‖ ≤
        η * (‖jacobiSecondKind α β r s (n + 1) y‖ + ‖jacobiSecondKind α β r s n y‖) := by
      filter_upwards [hδ.eventually (gt_mem_nhds hη),
        hW.norm.eventually (lt_mem_nhds (show ‖w‖ / 2 < ‖w‖ by linarith)),
        (hV.sub_const ((r + s) / 2)).norm.eventually
          (gt_mem_nhds (show ‖(r + s) / 2 - (r + s) / 2‖ < 1 by simp)),
        eventually_ge_atTop Nq] with n hδn hWn hVn hnq
      set Q0 := jacobiSecondKind α β r s n y
      set Q1 := jacobiSecondKind α β r s (n + 1) y
      set Q2 := jacobiSecondKind α β r s (n + 2) y
      set Wn := jacobiRecurrenceW α β r s (n + 1)
      set Vn := jacobiRecurrenceV α β r s n
      have hrecn : Wn * Q2 = (y - Vn) * Q1 - Q0 := hNq n hnq y hy
      have hWn0 : Wn ≠ 0 := fun h => by rw [h, norm_zero] at hWn; linarith
      have hyV : ‖y - Vn‖ ≤ ‖y - (r + s) / 2‖ + 1 := by
        calc ‖y - Vn‖ = ‖(y - (r + s) / 2) - (Vn - (r + s) / 2)‖ := by congr 1; ring
          _ ≤ ‖y - (r + s) / 2‖ + ‖Vn - (r + s) / 2‖ := norm_sub_le _ _
          _ ≤ _ := by linarith
      have hQ2 : ‖Q2‖ ≤ K * (‖Q1‖ + ‖Q0‖) := by
        have hQ2e : Q2 = ((y - Vn) * Q1 - Q0) / Wn := by rw [← hrecn]; field_simp
        rw [hQ2e, norm_div]
        rw [div_le_iff₀ (norm_pos_iff.mpr hWn0)]
        calc ‖(y - Vn) * Q1 - Q0‖ ≤ ‖y - Vn‖ * ‖Q1‖ + ‖Q0‖ := by
              refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
          _ ≤ (‖y - (r + s) / 2‖ + 2) * (‖Q1‖ + ‖Q0‖) := by
              nlinarith [norm_nonneg Q1, norm_nonneg Q0, norm_nonneg (y - (r + s) / 2)]
          _ = K * (‖w‖ / 2) * (‖Q1‖ + ‖Q0‖) := by simp only [K]; field_simp
          _ ≤ K * ‖Wn‖ * (‖Q1‖ + ‖Q0‖) := by gcongr
          _ = K * (‖Q1‖ + ‖Q0‖) * ‖Wn‖ := by ring
      have he : w * (Q2 - (a + b) * Q1 + a * b * Q0) =
          (w - Wn) * Q2 + ((r + s) / 2 - Vn) * Q1 := by
        rw [hsum, hprod, mul_add, mul_sub, ← mul_assoc, ← mul_assoc, mul_div_cancel₀ _ hw0,
          mul_one_div_cancel hw0, one_mul]
        linear_combination hrecn
      have hK0 : 0 ≤ K := by simp only [K]; positivity
      calc ‖Q2 - (a + b) * Q1 + a * b * Q0‖
          = ‖(w - Wn) * Q2 + ((r + s) / 2 - Vn) * Q1‖ / ‖w‖ := by
            rw [← he, norm_mul]; field_simp
        _ ≤ (‖w - Wn‖ * (K * (‖Q1‖ + ‖Q0‖)) + ‖(r + s) / 2 - Vn‖ * (‖Q1‖ + ‖Q0‖)) / ‖w‖ := by
            gcongr
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
            gcongr
            linarith [norm_nonneg Q0]
        _ = (‖w - Wn‖ * K + ‖(r + s) / 2 - Vn‖) / ‖w‖ * (‖Q1‖ + ‖Q0‖) := by ring
        _ ≤ η * (‖Q1‖ + ‖Q0‖) := by gcongr
    exact eventually_atTop.mp hev
  -- the growth hypotheses
  set l := (1 / μ + ‖b‖) / 2
  have hal : ‖a‖ < l := by simp only [l]; linarith
  have hlb : l < ‖b‖ := by simp only [l]; linarith
  obtain ⟨Cq, hCq0, hCq⟩ := exists_bound_jacobiSecondKind_exterior α β r s
    (lt_jacobiEllipseRadius hy) (show 0 < l - 1 / μ by linarith)
  have hup : ∀ n, ‖jacobiSecondKind α β r s n y‖ ≤ Cq * l ^ n := fun n => by
    have := hCq n y le_rfl
    rwa [show 1 / μ + (l - 1 / μ) = l by ring] at this
  have hnot : ∀ l', 0 < l' → l' < ‖a‖ →
      ¬ ∃ C' : ℝ, ∀ n, ‖jacobiSecondKind α β r s n y‖ ≤ C' * l' ^ n := fun l' hl' hla =>
    not_exists_bound_jacobiSecondKind α β r s hc hy hl'.le (by
      rw [ha] at hla; rw [lt_div_iff₀ hμ] at hla; exact hla)
  obtain ⟨c, hc0, N, hN⟩ := exists_lower_bound_of_perturbed_recurrence_recessive hab
    (y := fun n => jacobiSecondKind α β r s n y) hrec hal hlb hup hnot hε (by rw [ha]; exact hεμ)
  exact ⟨c, hc0, N, fun n hn => by simpa [ha] using hN n hn⟩

/-- Carlson's Theorem 7.5-1 for the second-kind functions: off the segment
`‖qₙ(y)‖^{1/n} → 1/μ(y)`. -/
theorem tendsto_norm_jacobiSecondKind_rpow (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {y : ℂ} (hy : y ∉ segment ℝ r s) :
    Tendsto (fun n : ℕ => ‖jacobiSecondKind α β r s n y‖ ^ (1 / (n : ℝ))) atTop
      (𝓝 (1 / jacobiEllipseRadius r s y)) := by
  set L := 1 / jacobiEllipseRadius r s y
  have hμ : 0 < jacobiEllipseRadius r s y :=
    lt_of_le_of_lt (by positivity) (lt_jacobiEllipseRadius hy)
  have hL : 0 < L := by positivity
  have hroot (C : ℝ) (hC : 0 < C) : Tendsto (fun n : ℕ => C ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
    have h := ((Real.continuousAt_const_rpow hC.ne').tendsto).comp
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [Function.comp_def] using h
  rw [tendsto_order]
  constructor
  · intro a ha
    rcases lt_or_ge a 0 with ha0 | ha0
    · exact Eventually.of_forall fun n => ha0.trans_le (Real.rpow_nonneg (norm_nonneg _) _)
    set ε := (L - a) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    obtain ⟨c, hc0, N, hN⟩ := exists_lower_bound_norm_jacobiSecondKind α β r s hc hy hε
      (by simp only [ε, L] at *; linarith)
    have hlim := (hroot c hc0).mul_const (L - ε)
    rw [one_mul] at hlim
    filter_upwards [hlim.eventually (lt_mem_nhds (show a < L - ε by simp only [ε]; linarith)),
      eventually_ge_atTop N, eventually_ne_atTop 0] with n h1 h2 h3
    refine h1.trans_le ?_
    have hbase : 0 ≤ L - ε := by simp only [ε]; linarith
    calc
      c ^ (1 / (n : ℝ)) * (L - ε) = (c * (L - ε) ^ n) ^ (1 / (n : ℝ)) := by
        rw [Real.mul_rpow hc0.le (pow_nonneg hbase n), one_div,
          Real.pow_rpow_inv_natCast hbase h3]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (hN n h2) (by positivity)
  · intro b hb
    set ε := (b - L) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    obtain ⟨C, hC0, hC⟩ := exists_bound_jacobiSecondKind_exterior α β r s
      (lt_jacobiEllipseRadius hy) hε
    have hlim := (hroot (C + 1) (by linarith)).mul_const (L + ε)
    rw [one_mul] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds (show L + ε < b by simp only [ε]; linarith)),
      eventually_ne_atTop 0] with n h1 h3
    refine lt_of_le_of_lt ?_ h1
    have hbase : 0 ≤ L + ε := by linarith
    calc
      ‖jacobiSecondKind α β r s n y‖ ^ (1 / (n : ℝ)) ≤ ((C + 1) * (L + ε) ^ n) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (norm_nonneg _) ((hC n y le_rfl).trans (by gcongr; linarith))
          (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (by linarith) (pow_nonneg hbase n), one_div,
          Real.pow_rpow_inv_natCast hbase h3]

/-- Carlson's Theorem 7.5-3 for second-kind series, convergence part: if the coefficients grow at
most at the rate `τ`, the series converges absolutely and locally uniformly on the open elliptic
exterior of mean radius `τ`, with holomorphic sum. -/
theorem tendstoLocallyUniformlyOn_sum_jacobiSecondKind_exterior (α β r s : ℂ) (b : ℕ → ℂ)
    {τ : ℝ} (hτ : ‖r - s‖ / 4 < τ) (hb : ∀ ε > 0, ∃ C : ℝ, ∀ n, ‖b n‖ ≤ C * (τ + ε) ^ n) :
    TendstoLocallyUniformlyOn
      (fun N y => ∑ n ∈ Finset.range N, b n * jacobiSecondKind α β r s n y)
      (fun y => ∑' n, b n * jacobiSecondKind α β r s n y) atTop
      {y | τ < jacobiEllipseRadius r s y} ∧
    AnalyticOnNhd ℂ (fun y => ∑' n, b n * jacobiSecondKind α β r s n y)
      {y | τ < jacobiEllipseRadius r s y} := by
  have hτ0 : 0 < τ := lt_of_le_of_lt (by positivity) hτ
  have hO : IsOpen {y | τ < jacobiEllipseRadius r s y} :=
    isOpen_lt continuous_const (continuous_jacobiEllipseRadius r s)
  have hmaj : ∀ σ, τ < σ → ∃ M : ℕ → ℝ, Summable M ∧ ∀ n y, σ ≤ jacobiEllipseRadius r s y →
      ‖b n * jacobiSecondKind α β r s n y‖ ≤ M n := by
    intro σ hτσ
    have hσ0 : 0 < σ := hτ0.trans hτσ
    obtain ⟨ε, hε, hεlt⟩ := exists_pos_add_mul_add_lt_one hσ0 hτσ
    obtain ⟨C, hC⟩ := hb ε hε
    have hC0 : 0 ≤ C := by have := (norm_nonneg _).trans (hC 0); simpa using this
    obtain ⟨Cq, hCq0, hCq⟩ := exists_bound_jacobiSecondKind_exterior α β r s (hτ.trans hτσ) hε
    refine ⟨fun n => C * Cq * ((τ + ε) * (1 / σ + ε)) ^ n,
      (summable_geometric_of_lt_one (by positivity) hεlt).mul_left _, fun n y hy => ?_⟩
    simp only [norm_mul, mul_pow]
    calc
      _ ≤ (C * (τ + ε) ^ n) * (Cq * (1 / σ + ε) ^ n) :=
        mul_le_mul (hC n) (hCq n y hy) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hloc : TendstoLocallyUniformlyOn
      (fun N y => ∑ n ∈ Finset.range N, b n * jacobiSecondKind α β r s n y)
      (fun y => ∑' n, b n * jacobiSecondKind α β r s n y) atTop
      {y | τ < jacobiEllipseRadius r s y} := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hO]
    intro K hKsub hK
    rcases K.eq_empty_or_nonempty with he | hne
    · subst he; exact tendstoUniformlyOn_empty
    obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne
      (continuous_jacobiEllipseRadius r s).continuousOn
    obtain ⟨M, hM, hbound⟩ := hmaj _ (hKsub hy₀)
    exact tendstoUniformlyOn_tsum_nat hM
      (f := fun n y => b n * jacobiSecondKind α β r s n y) (fun n y hy => hbound n y (hmin hy))
  refine ⟨hloc, (hloc.differentiableOn (Eventually.of_forall fun N => ?_) hO).analyticOnNhd hO⟩
  exact DifferentiableOn.fun_sum fun n _ => (differentiableOn_const _).mul
    (fun y hy => ((analyticOnNhd_jacobiSecondKind α β r s n) y
      (not_mem_segment_of_lt_jacobiEllipseRadius
        (hτ.trans hy))).differentiableAt.differentiableWithinAt)

/-- Carlson's Theorem 7.5-3 for second-kind series, divergence part: if the coefficients grow at
least at the rate `τ` infinitely often, the series diverges at every point off the segment inside
the elliptic disk of mean radius `τ`; its terms do not tend to zero. -/
theorem not_tendsto_jacobiSecondKind (α β r s : ℂ) (hc : IsGammaRegular (α + β + 2))
    (b : ℕ → ℂ) {τ : ℝ} (hb : ∀ ε > 0, ∀ C : ℝ, ∃ᶠ n in atTop, C * (τ - ε) ^ n ≤ ‖b n‖)
    {y : ℂ} (hy : y ∉ segment ℝ r s) (hyτ : jacobiEllipseRadius r s y < τ) :
    ¬ Tendsto (fun n => b n * jacobiSecondKind α β r s n y) atTop (𝓝 0) := by
  set m := jacobiEllipseRadius r s y
  have hm : 0 < m := lt_of_le_of_lt (by positivity) (lt_jacobiEllipseRadius hy)
  have hlim : Tendsto (fun ε : ℝ => (τ - ε) * (1 / m - ε)) (𝓝 0) (𝓝 (τ * (1 / m))) := by
    have := ((continuous_const.sub continuous_id).mul (continuous_const.sub continuous_id)).tendsto
      (0 : ℝ) (f := fun ε : ℝ => (τ - ε) * (1 / m - ε))
    simpa using this
  have hgt : 1 < τ * (1 / m) := by rw [mul_one_div, one_lt_div hm]; exact hyτ
  obtain ⟨ε, ⟨hεgt, hε1, hε2⟩, hε⟩ := ((((hlim.eventually (lt_mem_nhds hgt)).and
    ((tendsto_id.eventually (gt_mem_nhds (show (0 : ℝ) < τ by linarith))).and
      (tendsto_id.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / m by positivity))))).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hε0 : 0 < ε := hε
  simp only [id] at hε1 hε2
  obtain ⟨c, hc0, N, hN⟩ := exists_lower_bound_norm_jacobiSecondKind α β r s hc hy hε0 hε2
  intro htend
  have hfreq := hb ε hε0 (1 / c)
  have hsmall := htend.norm.eventually (gt_mem_nhds (show ‖(0 : ℂ)‖ < 1 by simp))
  obtain ⟨n, ⟨hn1, hn2⟩, hnN⟩ := ((hfreq.and_eventually hsmall).and_eventually
    (eventually_ge_atTop N)).exists
  have h1 : 1 ≤ ((τ - ε) * (1 / m - ε)) ^ n := one_le_pow₀ hεgt.le
  have h2 : ((τ - ε) * (1 / m - ε)) ^ n ≤ ‖b n * jacobiSecondKind α β r s n y‖ := by
    rw [norm_mul, mul_pow]
    calc
      (τ - ε) ^ n * (1 / m - ε) ^ n = (1 / c * (τ - ε) ^ n) * (c * (1 / m - ε) ^ n) := by
        field_simp
      _ ≤ ‖b n‖ * ‖jacobiSecondKind α β r s n y‖ :=
        mul_le_mul hn1 (hN n hnN) (by positivity) (norm_nonneg _)
  linarith

end Carlson.TwoVariable
