/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.PolynomialGrowth
public import Carlson.Jacobi.SecondKindSaddle
public import Carlson.Jacobi.CauchyKernel
public import Carlson.Jacobi.AnalyticExpansion
public import Carlson.Jacobi.EllipseContour
public import ComplexAnalysis.Cycle.Cauchy

/-!
# Jacobi expansions on elliptic disks

The sharp bounds `‖pₙ(x)‖ ≤ C (ρ + ε)ⁿ` on closed elliptic disks and
`‖qₙ(y)‖ ≤ C (1/σ + ε)ⁿ` on closed elliptic exteriors give a summable geometric majorant for
`pₙ(x) qₙ(y)` whenever `ρ < σ`. Hence the Cauchy kernel expansion holds on Carlson's full domain
`μ(x) < μ(y)` (Lemma 7.6-1), uniformly on products of a closed elliptic disk and a larger closed
elliptic exterior. Integrating against a holomorphic function over a cycle, in particular over a
confocal ellipse, gives Carlson's Theorem 7.6-2: a function holomorphic on an open elliptic disk
is the sum of its Jacobi series throughout the disk, with absolute convergence, uniform
convergence on closed elliptic subdisks, coefficients independent of the ellipse used, and
uniqueness among series converging uniformly on an ellipse.

## Main results

* `hasSum_jacobiOn_mul_jacobiSecondKind`: Lemma 7.6-1 on the domain `μ(x) < μ(y)`.
* `tendstoUniformlyOn_sum_jacobiOn_mul_jacobiSecondKind_ellipse`: its uniform form.
* `hasSum_jacobiContourCoefficient_of_cycle`: Theorem 7.6-2 for a general cycle.
* `hasSum_jacobiContourCoefficient_jacobiEllipseCycle`: Theorem 7.6-2 on elliptic disks.
* `tendstoUniformlyOn_sum_jacobiContourCoefficient_jacobiEllipseCycle`: uniform convergence
  on closed elliptic subdisks.
* `jacobiContourCoefficient_jacobiEllipseCycle_eq`: independence of the ellipse.
* `jacobiContourCoefficient_jacobiEllipseCycle_eq_of_tendstoUniformlyOn`: uniqueness.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Lemma 7.6-1 and Theorem 7.6-2.
-/

@[expose] public noncomputable section
open Complex Set Filter Polynomial ContinuousLinearMap
open scoped Topology

namespace Carlson.TwoVariable

/-- Products of monic Jacobi polynomials on a closed elliptic disk and second-kind functions on
a larger closed elliptic exterior have a summable geometric majorant. -/
theorem exists_summable_jacobiOn_mul_jacobiSecondKind_ellipse (α β r s : ℂ) {ρ σ : ℝ}
    (hρ : ‖r - s‖ / 4 < ρ) (hρσ : ρ < σ) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ n x y, jacobiEllipseRadius r s x ≤ ρ →
      σ ≤ jacobiEllipseRadius r s y →
        ‖(jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y‖ ≤ M n := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt (by positivity) hρ
  have hσ0 : 0 < σ := hρ0.trans hρσ
  have hlim : Tendsto (fun ε : ℝ => (ρ + ε) * (1 / σ + ε)) (𝓝 0) (𝓝 (ρ * (1 / σ))) := by
    have := ((continuous_const.add continuous_id).mul (continuous_const.add continuous_id)).tendsto
      (0 : ℝ) (f := fun ε : ℝ => (ρ + ε) * (1 / σ + ε))
    simpa using this
  have hlt : ρ * (1 / σ) < 1 := by rw [mul_one_div, div_lt_one hσ0]; exact hρσ
  obtain ⟨ε, hεlt, hε⟩ := (((hlim.eventually (gt_mem_nhds hlt)).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hε0 : 0 < ε := hε
  obtain ⟨Cp, hCp0, hCp⟩ := exists_bound_norm_eval_jacobiOn_of_le α β r s hρ hε0
  obtain ⟨Cq, hCq0, hCq⟩ := exists_bound_jacobiSecondKind_exterior α β r s
    (hρ.trans hρσ) hε0
  refine ⟨fun n => Cp * Cq * ((ρ + ε) * (1 / σ + ε)) ^ n,
    (summable_geometric_of_lt_one (by positivity) hεlt).mul_left _, fun n x y hx hy => ?_⟩
  simp only [norm_mul, mul_pow]
  calc
    _ ≤ (Cp * (ρ + ε) ^ n) * (Cq * (1 / σ + ε) ^ n) :=
      mul_le_mul (hCp n x hx) (hCq n y hy) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Carlson's Lemma 7.6-1, uniform form: the Cauchy kernel expansion converges uniformly for
`x` in a closed elliptic disk and `y` in a larger closed elliptic exterior, for arbitrary
endpoints and parameters with admissible total. -/
theorem tendstoUniformlyOn_sum_jacobiOn_mul_jacobiSecondKind_ellipse (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {ρ σ : ℝ} (hρ : ‖r - s‖ / 4 < ρ) (hρσ : ρ < σ) :
    TendstoUniformlyOn
      (fun N (xy : ℂ × ℂ) => ∑ n ∈ Finset.range N,
        (jacobiOn α β r s n).eval xy.1 * jacobiSecondKind α β r s n xy.2)
      (fun xy => (xy.2 - xy.1)⁻¹) atTop
      ({x | jacobiEllipseRadius r s x ≤ ρ} ×ˢ {y | σ ≤ jacobiEllipseRadius r s y}) := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_jacobiOn_mul_jacobiSecondKind_ellipse α β r s hρ hρσ
  have hunif := tendstoUniformlyOn_tsum_nat hM (s := {x | jacobiEllipseRadius r s x ≤ ρ} ×ˢ
    {y | σ ≤ jacobiEllipseRadius r s y})
    (f := fun n (xy : ℂ × ℂ) => (jacobiOn α β r s n).eval xy.1 * jacobiSecondKind α β r s n xy.2)
    (fun n xy hxy => hbound n xy.1 xy.2 hxy.1 hxy.2)
  refine hunif.congr_right (fun xy hxy => ?_)
  -- identify the sum with the Cauchy kernel
  set x := xy.1
  have hx : jacobiEllipseRadius r s x ≤ ρ := hxy.1
  have hlocal : TendstoLocallyUniformlyOn
      (fun N y => ∑ n ∈ Finset.range N, (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y)
      (fun y => ∑' n, (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y) atTop
      {y | ρ < jacobiEllipseRadius r s y} := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
      (isOpen_lt continuous_const (continuous_jacobiEllipseRadius r s))]
    intro K hKsub hK
    rcases K.eq_empty_or_nonempty with he | hne
    · subst he; exact tendstoUniformlyOn_empty
    obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne
      (continuous_jacobiEllipseRadius r s).continuousOn
    obtain ⟨M', hM', hbound'⟩ := exists_summable_jacobiOn_mul_jacobiSecondKind_ellipse α β r s
      hρ (hKsub hy₀)
    exact tendstoUniformlyOn_tsum_nat hM'
      (f := fun n y => (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y)
      (fun n y hy => hbound' n x y hx (hmin hy))
  have heq := eqOn_cauchyKernel_of_tendstoLocallyUniformlyOn α β r s hc hρ hx hlocal
    (show ρ < jacobiEllipseRadius r s xy.2 from hρσ.trans_le hxy.2)
  exact heq

/-- Carlson's Lemma 7.6-1: the Cauchy kernel expansion `1/(y - x) = Σ pₙ(x) qₙ(y)` holds
whenever `μ(x) < μ(y)`, with absolute convergence. -/
theorem hasSum_jacobiOn_mul_jacobiSecondKind (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {x y : ℂ}
    (hxy : jacobiEllipseRadius r s x < jacobiEllipseRadius r s y) :
    HasSum (fun n => (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y) (y - x)⁻¹ := by
  set a := jacobiEllipseRadius r s x
  set b := jacobiEllipseRadius r s y
  have ha := le_jacobiEllipseRadius r s x
  have hρ : ‖r - s‖ / 4 < a + (b - a) / 3 := by linarith
  have hρσ : a + (b - a) / 3 < a + 2 * (b - a) / 3 := by linarith
  have hu := tendstoUniformlyOn_sum_jacobiOn_mul_jacobiSecondKind_ellipse α β r s hc hρ hρσ
  have hmem : (x, y) ∈ {x | jacobiEllipseRadius r s x ≤ a + (b - a) / 3} ×ˢ
      {y | a + 2 * (b - a) / 3 ≤ jacobiEllipseRadius r s y} :=
    ⟨show a ≤ _ by linarith, show _ ≤ b by linarith⟩
  obtain ⟨M, hM, hbound⟩ := exists_summable_jacobiOn_mul_jacobiSecondKind_ellipse α β r s hρ hρσ
  have hs : Summable (fun n => (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n y) :=
    Summable.of_norm_bounded hM (fun n => hbound n x y hmem.1 hmem.2)
  exact hs.hasSum_iff_tendsto_nat.mpr (hu.tendsto_at hmem)

/-- Integrals over a `C¹` cycle commute with uniform limits of continuous functions on the
cycle. -/
theorem tendsto_cycle_integral_of_tendstoUniformlyOn (Γ : Cycle) (hΓ : Γ.IsC1)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ N, ContinuousOn (F N) Γ.range)
    (hlim : TendstoUniformlyOn F f atTop Γ.range) :
    Tendsto (fun N => Γ.integral (fun z => toSpanSingleton ℂ (F N z))) atTop
      (𝓝 (Γ.integral (fun z => toSpanSingleton ℂ (f z)))) := by
  have hf : ContinuousOn f Γ.range := hlim.continuousOn (Frequently.of_forall hF)
  obtain ⟨L, hL, hbound⟩ := Γ.exists_norm_integral_le (F := ℂ) hΓ
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hLδ⟩ := exists_pos_mul_lt hε L
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) δ hδ] with N hN
  have hi := Γ.integrable_toSpanSingleton_of_continuousOn hΓ (hF N) subset_rfl
  have hj := Γ.integrable_toSpanSingleton_of_continuousOn hΓ hf subset_rfl
  have he : (fun z => toSpanSingleton ℂ (F N z - f z)) =
      (fun z => toSpanSingleton ℂ (F N z)) - (fun z => toSpanSingleton ℂ (f z)) := by
    funext z; ext; simp
  rw [dist_eq_norm, ← Γ.integral_sub hi hj, ← he]
  refine (hbound _ δ (fun z hz => ?_)).trans_lt hLδ
  exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hN z hz)

/-- Carlson's Theorem 7.6-2 for a general contour: if `f` is holomorphic on an open set `U`
and `Γ` is a `C¹` cycle in `U`, homologous to zero there, lying in a closed elliptic exterior
`μ ≥ σ`, then at every point `x ∈ U` with `μ(x) ≤ ρ < σ` the Jacobi series with contour
coefficients converges absolutely to the index of `Γ` about `x` times `f x`. -/
theorem hasSum_jacobiContourCoefficient_of_cycle (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (Γ : Cycle) (hΓ : Γ.IsC1) (hΓU : Γ.range ⊆ U)
    (hind : ∀ w, w ∉ U → Γ.index w = 0) {ρ σ : ℝ} (hρ : ‖r - s‖ / 4 < ρ) (hρσ : ρ < σ)
    (hΓσ : ∀ y ∈ Γ.range, σ ≤ jacobiEllipseRadius r s y) {x : ℂ} (hxU : x ∈ U)
    (hx : jacobiEllipseRadius r s x ≤ ρ) :
    HasSum (fun n => jacobiContourCoefficient α β r s n Γ f * (jacobiOn α β r s n).eval x)
      (Γ.index x * f x) := by
  have havoid : Γ.range ⊆ (segment ℝ r s)ᶜ := fun y hy =>
    not_mem_segment_of_lt_jacobiEllipseRadius ((hρ.trans hρσ).trans_le (hΓσ y hy))
  have hxΓ : x ∉ Γ.range := fun h => by linarith [hΓσ x h]
  have hfc : ContinuousOn f Γ.range := hf.continuousOn.mono hΓU
  obtain ⟨B, hB⟩ := Γ.isCompact_range.exists_bound_of_continuousOn hfc
  set F := max B 0
  have hF0 : 0 ≤ F := le_max_right _ _
  have hfF : ∀ z ∈ Γ.range, ‖f z‖ ≤ F := fun z hz => (hB z hz).trans (le_max_left _ _)
  have hq (n : ℕ) : ContinuousOn (jacobiSecondKind α β r s n) Γ.range :=
    (analyticOnNhd_jacobiSecondKind α β r s n).continuousOn.mono havoid
  -- absolute summability
  obtain ⟨M, hM, hbound⟩ := exists_summable_jacobiOn_mul_jacobiSecondKind_ellipse α β r s hρ hρσ
  obtain ⟨L, hL, hLbound⟩ := Γ.exists_norm_integral_le (F := ℂ) hΓ
  have hcoef (n : ℕ) : ‖jacobiContourCoefficient α β r s n Γ f * (jacobiOn α β r s n).eval x‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * L * F * M n := by
    unfold jacobiContourCoefficient
    have h := hLbound (fun z => jacobiSecondKind α β r s n z * f z * (jacobiOn α β r s n).eval x)
      (M n * F) (fun z hz => by
        rw [norm_mul, norm_mul]
        calc
          _ = ‖(jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n z‖ * ‖f z‖ := by
            rw [norm_mul]; ring
          _ ≤ M n * F := mul_le_mul (hbound n x z hx (hΓσ z hz)) (hfF z hz) (norm_nonneg _)
            ((norm_nonneg _).trans (hbound n x z hx (hΓσ z hz))))
    have hsmul : Γ.integral (fun z => toSpanSingleton ℂ
        (jacobiSecondKind α β r s n z * f z * (jacobiOn α β r s n).eval x)) =
        (jacobiOn α β r s n).eval x •
          Γ.integral (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * f z)) := by
      rw [← Γ.integral_smul]
      congr 1; funext z; ext; simp [mul_comm]
    rw [hsmul, smul_eq_mul] at h
    calc
      _ = ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * ‖(jacobiOn α β r s n).eval x *
          Γ.integral (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * f z))‖ := by
        rw [norm_mul, norm_mul, norm_mul]; ring
      _ ≤ ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (L * (M n * F)) := by gcongr
      _ = _ := by ring
  have hsum : Summable (fun n =>
      jacobiContourCoefficient α β r s n Γ f * (jacobiOn α β r s n).eval x) :=
    Summable.of_norm_bounded (hM.mul_left _) hcoef
  -- partial sums as contour integrals
  set T : ℕ → ℂ → ℂ := fun N z => ∑ n ∈ Finset.range N,
    (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n z * f z
  have hTc (N : ℕ) : ContinuousOn (T N) Γ.range :=
    continuousOn_finsetSum _ (fun n _ => (continuousOn_const.mul (hq n)).mul hfc)
  have hpartial (N : ℕ) : ∑ n ∈ Finset.range N,
      jacobiContourCoefficient α β r s n Γ f * (jacobiOn α β r s n).eval x =
      (2 * (Real.pi : ℂ) * I)⁻¹ * Γ.integral (fun z => toSpanSingleton ℂ (T N z)) := by
    induction N with
    | zero => simp [T, Cycle.integral]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 := Γ.integrable_toSpanSingleton_of_continuousOn hΓ (hTc N) subset_rfl
      have h2 := Γ.integrable_toSpanSingleton_of_continuousOn hΓ
        (f := fun z => (jacobiOn α β r s N).eval x * jacobiSecondKind α β r s N z * f z)
        ((continuousOn_const.mul (hq N)).mul hfc) subset_rfl
      have he : (fun z => toSpanSingleton ℂ (T (N + 1) z)) =
          (fun z => toSpanSingleton ℂ (T N z)) + (fun z => toSpanSingleton ℂ
            ((jacobiOn α β r s N).eval x * jacobiSecondKind α β r s N z * f z)) := by
        funext z; ext; simp [T, Finset.sum_range_succ]
      rw [he, Γ.integral_add h1 h2]
      have hsmul : Γ.integral (fun z => toSpanSingleton ℂ
          ((jacobiOn α β r s N).eval x * jacobiSecondKind α β r s N z * f z)) =
          (jacobiOn α β r s N).eval x •
            Γ.integral (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s N z * f z)) := by
        rw [← Γ.integral_smul]
        congr 1; funext z; ext; simp [mul_assoc]
      rw [hsmul, smul_eq_mul]
      unfold jacobiContourCoefficient
      ring
  -- uniform convergence of the partial integrands
  have hker := tendstoUniformlyOn_sum_jacobiOn_mul_jacobiSecondKind_ellipse α β r s hc hρ hρσ
  have hTlim : TendstoUniformlyOn T (fun z => (z - x)⁻¹ * f z) atTop Γ.range := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨δ, hδ, hFδ⟩ := exists_pos_mul_lt hε F
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hker) δ hδ] with N hN
    intro z hz
    have h := hN (x, z) ⟨hx, hΓσ z hz⟩
    simp only at h
    rw [dist_eq_norm] at h ⊢
    have he : (z - x)⁻¹ * f z - T N z = ((z - x)⁻¹ - ∑ n ∈ Finset.range N,
        (jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n z) * f z := by
      simp only [T, Finset.sum_mul, sub_mul]
    rw [he, norm_mul]
    calc
      _ ≤ δ * F := mul_le_mul h.le (hfF z hz) (norm_nonneg _) hδ.le
      _ < ε := by linarith
  have hlim := tendsto_cycle_integral_of_tendstoUniformlyOn Γ hΓ hTc hTlim
  have hcauchy := Complex.Cycle.integral_sub_inv_smul_eq_index_smul (Γ := Γ) hU hΓ hΓU hind hf
    hxU hxΓ
  simp only [smul_eq_mul] at hcauchy
  have htend : Tendsto (fun N => ∑ n ∈ Finset.range N,
      jacobiContourCoefficient α β r s n Γ f * (jacobiOn α β r s n).eval x) atTop
      (𝓝 (Γ.index x * f x)) := by
    simp only [hpartial]
    convert hlim.const_mul (2 * (Real.pi : ℂ) * I)⁻¹ using 2
    rw [hcauchy]
    have : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    field_simp
  exact hsum.hasSum_iff_tendsto_nat.mpr htend

/-- Jacobi coefficients of a function holomorphic on an open elliptic disk do not depend on
the confocal ellipse inside the disk used to compute them. -/
theorem jacobiContourCoefficient_jacobiEllipseCycle_eq (α β r s : ℂ) (n : ℕ) {τ : ℝ}
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (jacobiEllipseDisk r s τ)) {σ₁ σ₂ : ℝ}
    (h₁0 : 0 < σ₁) (h₂0 : 0 < σ₂) (h₁ : ‖r - s‖ / 4 < σ₁) (h₂ : ‖r - s‖ / 4 < σ₂)
    (h₁τ : σ₁ < τ) (h₂τ : σ₂ < τ) :
    jacobiContourCoefficient α β r s n (jacobiEllipseCycle r s h₁0) f =
      jacobiContourCoefficient α β r s n (jacobiEllipseCycle r s h₂0) f := by
  have hsub (σ : ℝ) (h0 : 0 < σ) (h : ‖r - s‖ / 4 < σ) (hτ : σ < τ) :
      (jacobiEllipseCycle r s h0).range ⊆ jacobiEllipseDisk r s τ := fun z hz => by
    change jacobiEllipseRadius r s z < τ
    rw [jacobiEllipseRadius_of_mem_range_jacobiEllipseCycle r s h0 h.le hz]; exact hτ
  have havoid (σ : ℝ) (h0 : 0 < σ) (h : ‖r - s‖ / 4 < σ) :
      (jacobiEllipseCycle r s h0).range ⊆ (segment ℝ r s)ᶜ := fun z hz =>
    not_mem_segment_of_lt_jacobiEllipseRadius (by
      rw [jacobiEllipseRadius_of_mem_range_jacobiEllipseCycle r s h0 h.le hz]; exact h)
  have hrμ : jacobiEllipseRadius r s r = ‖r - s‖ / 4 := jacobiEllipseRadius_left r s
  unfold jacobiContourCoefficient
  congr 1
  apply cycleIntegral_jacobiSecondKind_mul_eq_of_index_eq α β r s n
    (isOpen_lt (continuous_jacobiEllipseRadius r s) continuous_const) hf
    _ _ (jacobiEllipseCycle_isC1 r s h₁0) (jacobiEllipseCycle_isC1 r s h₂0)
    (hsub σ₁ h₁0 h₁ h₁τ) (hsub σ₂ h₂0 h₂ h₂τ) (havoid σ₁ h₁0 h₁) (havoid σ₂ h₂0 h₂)
  · intro z hz
    have hz' : τ ≤ jacobiEllipseRadius r s z := le_of_not_gt hz
    rw [index_jacobiEllipseCycle_of_gt r s h₁0 h₁ (h₁τ.trans_le hz'),
      index_jacobiEllipseCycle_of_gt r s h₂0 h₂ (h₂τ.trans_le hz')]
  · rw [index_jacobiEllipseCycle_of_lt r s h₁0 h₁ (hrμ ▸ h₁),
      index_jacobiEllipseCycle_of_lt r s h₂0 h₂ (hrμ ▸ h₂)]

/-- Carlson's Theorem 7.6-2: a function holomorphic on an open elliptic disk with foci `r, s`
is the sum of its Jacobi series at every point of the disk. The coefficients are computed on
any confocal ellipse enclosing the point inside the disk, and the series converges
absolutely. -/
theorem hasSum_jacobiContourCoefficient_jacobiEllipseCycle (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {τ : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (jacobiEllipseDisk r s τ)) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ‖r - s‖ / 4 < σ) (hστ : σ < τ) {x : ℂ} (hx : jacobiEllipseRadius r s x < σ) :
    HasSum (fun n => jacobiContourCoefficient α β r s n (jacobiEllipseCycle r s hσ0) f *
      (jacobiOn α β r s n).eval x) (f x) := by
  have hμx := le_jacobiEllipseRadius r s x
  have h := hasSum_jacobiContourCoefficient_of_cycle α β r s hc
    (isOpen_lt (continuous_jacobiEllipseRadius r s) continuous_const) hf
    (jacobiEllipseCycle r s hσ0) (jacobiEllipseCycle_isC1 r s hσ0)
    (fun z hz => show jacobiEllipseRadius r s z < τ by
      rw [jacobiEllipseRadius_of_mem_range_jacobiEllipseCycle r s hσ0 hσ.le hz]; exact hστ)
    (fun w hw => index_jacobiEllipseCycle_of_gt r s hσ0 hσ
      (hστ.trans_le (le_of_not_gt hw)))
    (ρ := (jacobiEllipseRadius r s x + σ) / 2) (by linarith) (by linarith)
    (fun y hy => (jacobiEllipseRadius_of_mem_range_jacobiEllipseCycle r s hσ0 hσ.le hy).ge)
    (show jacobiEllipseRadius r s x < τ by linarith) (by linarith)
  rwa [index_jacobiEllipseCycle_of_lt r s hσ0 hσ hx, one_mul] at h

/-- On a closed elliptic disk inside the disk of holomorphy, the Jacobi series of Theorem 7.6-2
converges uniformly, with a summable majorant. -/
theorem tendstoUniformlyOn_sum_jacobiContourCoefficient_jacobiEllipseCycle (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {τ : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (jacobiEllipseDisk r s τ)) {ρ σ : ℝ} (hσ0 : 0 < σ)
    (hρ : ‖r - s‖ / 4 < ρ) (hρσ : ρ < σ) (hστ : σ < τ) :
    TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N,
      jacobiContourCoefficient α β r s n (jacobiEllipseCycle r s hσ0) f *
        (jacobiOn α β r s n).eval x) f atTop {x | jacobiEllipseRadius r s x ≤ ρ} := by
  set Γ := jacobiEllipseCycle r s hσ0
  have hΓ := jacobiEllipseCycle_isC1 r s hσ0
  have hσ : ‖r - s‖ / 4 < σ := hρ.trans hρσ
  have hΓσ : ∀ y ∈ Γ.range, jacobiEllipseRadius r s y = σ := fun y hy =>
    jacobiEllipseRadius_of_mem_range_jacobiEllipseCycle r s hσ0 hσ.le hy
  have hΓU : Γ.range ⊆ jacobiEllipseDisk r s τ := fun y hy => show _ < τ by rw [hΓσ y hy]; exact hστ
  obtain ⟨B, hB⟩ := Γ.isCompact_range.exists_bound_of_continuousOn (hf.continuousOn.mono hΓU)
  set F := max B 0
  have hfF : ∀ z ∈ Γ.range, ‖f z‖ ≤ F := fun z hz => (hB z hz).trans (le_max_left _ _)
  obtain ⟨M, hM, hbound⟩ := exists_summable_jacobiOn_mul_jacobiSecondKind_ellipse α β r s hρ hρσ
  obtain ⟨L, hL, hLbound⟩ := Γ.exists_norm_integral_le (F := ℂ) hΓ
  have hcoef (n : ℕ) (x : ℂ) (hx : jacobiEllipseRadius r s x ≤ ρ) :
      ‖jacobiContourCoefficient α β r s n Γ f * (jacobiOn α β r s n).eval x‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * L * F * M n := by
    unfold jacobiContourCoefficient
    have h := hLbound (fun z => jacobiSecondKind α β r s n z * f z * (jacobiOn α β r s n).eval x)
      (M n * F) (fun z hz => by
        rw [norm_mul, norm_mul]
        calc
          _ = ‖(jacobiOn α β r s n).eval x * jacobiSecondKind α β r s n z‖ * ‖f z‖ := by
            rw [norm_mul]; ring
          _ ≤ M n * F := mul_le_mul (hbound n x z hx (hΓσ z hz).ge) (hfF z hz) (norm_nonneg _)
            ((norm_nonneg _).trans (hbound n x z hx (hΓσ z hz).ge)))
    have hsmul : Γ.integral (fun z => toSpanSingleton ℂ
        (jacobiSecondKind α β r s n z * f z * (jacobiOn α β r s n).eval x)) =
        (jacobiOn α β r s n).eval x •
          Γ.integral (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * f z)) := by
      rw [← Γ.integral_smul]
      congr 1; funext z; ext; simp [mul_comm]
    rw [hsmul, smul_eq_mul] at h
    calc
      _ = ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * ‖(jacobiOn α β r s n).eval x *
          Γ.integral (fun z => toSpanSingleton ℂ (jacobiSecondKind α β r s n z * f z))‖ := by
        rw [norm_mul, norm_mul, norm_mul]; ring
      _ ≤ ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (L * (M n * F)) := by gcongr
      _ = _ := by ring
  have hu := tendstoUniformlyOn_tsum_nat (hM.mul_left (‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * L * F))
    (f := fun n x => jacobiContourCoefficient α β r s n Γ f * (jacobiOn α β r s n).eval x)
    (s := {x | jacobiEllipseRadius r s x ≤ ρ}) (fun n x hx => hcoef n x hx)
  refine hu.congr_right (fun x hx => ?_)
  exact (hasSum_jacobiContourCoefficient_jacobiEllipseCycle α β r s hc hf hσ0 hσ hστ
    (lt_of_le_of_lt hx hρσ)).tsum_eq

/-- Uniqueness in Theorem 7.6-2: a Jacobi series converging uniformly on a confocal ellipse
has the contour coefficients of its sum on that ellipse. -/
theorem jacobiContourCoefficient_jacobiEllipseCycle_eq_of_tendstoUniformlyOn (α β r s : ℂ)
    (hc : IsGammaRegular (α + β + 2)) {σ : ℝ} (hσ0 : 0 < σ) (hσ : ‖r - s‖ / 4 < σ)
    (b : ℕ → ℂ) {f : ℂ → ℂ}
    (hlim : TendstoUniformlyOn
      (fun N z => ∑ m ∈ Finset.range N, b m * (jacobiOn α β r s m).eval z)
      f atTop (jacobiEllipseCycle r s hσ0).range) (n : ℕ) :
    jacobiContourCoefficient α β r s n (jacobiEllipseCycle r s hσ0) f = b n := by
  have havoid : (jacobiEllipseCycle r s hσ0).range ⊆ (segment ℝ r s)ᶜ := fun z hz =>
    not_mem_segment_of_lt_jacobiEllipseRadius (by
      rw [jacobiEllipseRadius_of_mem_range_jacobiEllipseCycle r s hσ0 hσ.le hz]; exact hσ)
  rw [jacobiContourCoefficient_eq_of_tendstoUniformlyOn α β r s hc b _
    (jacobiEllipseCycle_isC1 r s hσ0) havoid hlim n,
    index_jacobiEllipseCycle_of_lt r s hσ0 hσ (by rw [jacobiEllipseRadius_left]; exact hσ),
    one_mul]

end Carlson.TwoVariable
