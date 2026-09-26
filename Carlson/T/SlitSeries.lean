/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SlitDeriv
public import Carlson.R.SlitIntegral
public import SeveralComplexVariables.LocallyUniform
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# The reciprocal-exponential series on slit-plane nodes

The translated R-resolvent controls the negative integral powers by Cauchy's derivative
estimate. Factorial decay then gives the series defining the principal branch of T.

## Main results

* `Carlson.iteratedDeriv_regCarlsonR_neg_one_translate`: derivatives of the translated
  resolvent are factorial multiples of negative integral R-functions.
* `Carlson.norm_regCarlsonR_neg_nat_succ_le`: Cauchy's estimate bounds those R-functions.
* `Carlson.hasSumLocallyUniformlyOn_regCarlsonTSlit`: normal convergence of the T-series.
* `Carlson.analyticOnNhd_regCarlsonTSlit_joint`: joint holomorphy on the product slit plane.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.12.
-/

open Complex Dirichlet Set Metric Filter
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- Derivatives of the translated R-resolvent are factorial multiples of negative
integral R-functions on the principal branch. -/
theorem iteratedDeriv_regCarlsonR_neg_one_translate (n : ℕ) (b z : ι → ℂ) {x : ℂ}
    (hx : (fun i => x + z i) ∈ carlsonRSlitDomain) :
    iteratedDeriv n (fun w => regCarlsonR (-1) b (fun i => w + z i)) x =
      (-1 : ℂ) ^ n * n.factorial * regCarlsonR (-(n : ℂ) - 1) b (fun i => x + z i) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have he : iteratedDeriv n (fun w => regCarlsonR (-1) b (fun i => w + z i)) =ᶠ[𝓝 x]
        (fun w => (-1 : ℂ) ^ n * n.factorial *
          regCarlsonR (-(n : ℂ) - 1) b (fun i => w + z i)) := by
      have ho : IsOpen {w : ℂ | (fun i => w + z i) ∈ carlsonRSlitDomain} :=
        isOpen_carlsonRSlitDomain.preimage (by fun_prop)
      filter_upwards [ho.mem_nhds hx] with w hw
      exact ih hw
    rw [iteratedDeriv_succ, he.deriv_eq,
      ((hasDerivAt_regCarlsonR_translate (-(n : ℂ) - 1) b z hx).const_mul
        ((-1 : ℂ) ^ n * n.factorial)).deriv]
    simp only [Nat.cast_add, Nat.cast_one, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    rw [show -(↑n + 1 : ℂ) - 1 = -↑n - 1 - 1 by ring]
    ring

/-- A bound for the translated resolvent on a circle gives a geometric bound for
negative integral R-functions, uniformly in the Dirichlet parameters. -/
theorem norm_regCarlsonR_neg_nat_succ_le (n : ℕ) (b z : ι → ℂ)
    {r C : ℝ} (hr : 0 < r)
    (hz : ∀ w ∈ closedBall (0 : ℂ) r, (fun i => w + z i) ∈ carlsonRSlitDomain)
    (hC : ∀ w ∈ sphere (0 : ℂ) r, ‖regCarlsonR (-1) b (fun i => w + z i)‖ ≤ C) :
    ‖regCarlsonR (-(n : ℂ) - 1) b z‖ ≤ C / r ^ n := by
  have ha : AnalyticOnNhd ℂ (fun w => regCarlsonR (-1) b (fun i => w + z i))
      (closedBall 0 r) := by
    intro w hw
    exact analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pi_iff.mpr fun i => analyticAt_id.add analyticAt_const) (hz w hw)
  have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    ⟨ha.differentiableOn.mono ball_subset_closedBall,
      ha.continuousOn.mono (closure_ball_subset_closedBall)⟩ hC
  rw [iteratedDeriv_regCarlsonR_neg_one_translate n b z (hz 0 (mem_closedBall_self hr.le))] at h
  simp only [zero_add, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast] at h
  rw [mul_div_assoc] at h
  exact (mul_le_mul_iff_right₀ (show (0 : ℝ) < n.factorial by positivity)).mp h

/-- Negative integral R-functions have uniform geometric bounds on compact subsets
of the joint parameter and slit-node domain. -/
theorem exists_bound_regCarlsonR_neg_nat_succ
    {K : Set (Sum ι ι → ℂ)}
    (hK : IsCompact K) (hKU : K ⊆ {q | (fun i => q (.inr i)) ∈ carlsonRSlitDomain}) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ q ∈ K, ∀ n : ℕ,
      ‖regCarlsonR (-(n : ℂ) - 1) (fun i => q (.inl i)) (fun i => q (.inr i))‖ ≤ C / r ^ n := by
  let U : Set (Sum ι ι → ℂ) := {q | (fun i => q (.inr i)) ∈ carlsonRSlitDomain}
  have hU : IsOpen U := isOpen_carlsonRSlitDomain.preimage (by fun_prop)
  obtain ⟨r, hr, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  let σ : (Sum ι ι → ℂ) × ℂ → Sum ι ι → ℂ :=
    fun p k => Sum.elim (fun i => p.1 (.inl i)) (fun i => p.2 + p.1 (.inr i)) k
  have hσ : ∀ q ∈ K, ∀ w ∈ closedBall (0 : ℂ) r, σ (q, w) ∈ U := by
    intro q hq w hw
    apply hsub
    apply closedBall_subset_cthickening hq r
    apply (dist_pi_le_iff hr.le).mpr
    intro k
    cases k with
    | inl i => simp [σ, hr.le]
    | inr i => simpa [σ, dist_eq_norm] using hw
  let F : (Sum ι ι → ℂ) × ℂ → ℂ := fun p =>
    regCarlsonR (-1) (fun i => p.1 (.inl i)) (fun i => p.2 + p.1 (.inr i))
  have hF : ContinuousOn (fun p => ‖F p‖) (K ×ˢ closedBall (0 : ℂ) r) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.norm
    apply AnalyticAt.continuousAt (𝕜 := ℂ)
    exact analyticAt_regCarlsonR_comp
      (b := fun p : (Sum ι ι → ℂ) × ℂ => fun i => p.1 (.inl i))
      (z := fun p : (Sum ι ι → ℂ) × ℂ => fun i => p.2 + p.1 (.inr i)) analyticAt_const
      (analyticAt_pi_iff.mpr fun i =>
        ((ContinuousLinearMap.proj (Sum.inl i) : (Sum ι ι → ℂ) →L[ℂ] ℂ).analyticAt p.1).comp_of_eq
          analyticAt_fst rfl)
      (analyticAt_pi_iff.mpr fun i => analyticAt_snd.add
        (((ContinuousLinearMap.proj (Sum.inr i) : (Sum ι ι → ℂ) →L[ℂ] ℂ).analyticAt p.1).comp_of_eq
          analyticAt_fst rfl)) (hσ p.1 hp.1 p.2 hp.2)
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : ℂ) r)).bddAbove_image hF
  refine ⟨r, max C 0, hr, le_max_right _ _, fun q hq n => ?_⟩
  apply norm_regCarlsonR_neg_nat_succ_le n _ _ hr (fun w hw => hσ q hq w hw)
  intro w hw
  exact (hC (mem_image_of_mem (fun p => ‖F p‖) (show (q, w) ∈ K ×ˢ closedBall 0 r from
    ⟨hq, sphere_subset_closedBall hw⟩))).trans (le_max_left _ _)

/-- The principal slit-plane branch of the regularized reciprocal-exponential average.
Its values outside the product slit plane are unspecified. -/
def regCarlsonTSlit (b z : ι → ℂ) : ℂ :=
  ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * regCarlsonR (-(n : ℂ)) b z

/-- The reciprocal-exponential R-series has a summable majorant on each joint compact
set of parameters and slit-plane nodes. -/
theorem exists_summable_bound_regCarlsonTSlit
    {K : Set (Sum ι ι → ℂ)} (hK : IsCompact K)
    (hKU : K ⊆ {q | (fun i => q (.inr i)) ∈ carlsonRSlitDomain}) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ (n : ℕ) (q : Sum ι ι → ℂ), q ∈ K →
      ‖(n.factorial : ℂ)⁻¹ * regCarlsonR (-(n : ℂ))
        (fun i => q (.inl i)) (fun i => q (.inr i))‖ ≤ M n := by
  obtain ⟨r, C, hr, hC, hbound⟩ := exists_bound_regCarlsonR_neg_nat_succ hK hKU
  have hzero : ContinuousOn (fun q : Sum ι ι → ℂ =>
      ‖regCarlsonR 0 (fun i => q (.inl i)) (fun i => q (.inr i))‖) K := by
    intro q hq
    exact (analyticAt_regCarlsonR_comp
      (b := fun q : Sum ι ι → ℂ => fun i => q (.inl i))
      (z := fun q : Sum ι ι → ℂ => fun i => q (.inr i)) analyticAt_const
      (analyticAt_pi_iff.mpr fun i =>
        (ContinuousLinearMap.proj (Sum.inl i) : (Sum ι ι → ℂ) →L[ℂ] ℂ).analyticAt q)
      (analyticAt_pi_iff.mpr fun i =>
        (ContinuousLinearMap.proj (Sum.inr i) : (Sum ι ι → ℂ) →L[ℂ] ℂ).analyticAt q)
      (hKU hq)).continuousAt.norm.continuousWithinAt
  obtain ⟨D, hD⟩ := hK.bddAbove_image hzero
  let M : ℕ → ℝ | 0 => D | n + 1 => C * (r⁻¹ ^ n / n.factorial)
  refine ⟨M, (summable_nat_add_iff 1).mp ((Real.summable_pow_div_factorial r⁻¹).mul_left C), ?_⟩
  intro n q hq
  cases n with
  | zero => simpa [M] using hD (mem_image_of_mem _ hq)
  | succ n =>
    simp only [Nat.cast_add, Nat.cast_one, neg_add, norm_mul, norm_inv,
      Complex.norm_natCast, ← sub_eq_add_neg]
    change ((n + 1).factorial : ℝ)⁻¹ *
      ‖regCarlsonR (-(n : ℂ) - 1) (fun i => q (.inl i)) (fun i => q (.inr i))‖ ≤ _
    calc
      _ ≤ ((n + 1).factorial : ℝ)⁻¹ * (C / r ^ n) :=
        mul_le_mul_of_nonneg_left (hbound q hq n) (by positivity)
      _ ≤ (n.factorial : ℝ)⁻¹ * (C / r ^ n) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.le_succ n))
      _ = M (n + 1) := by simp only [M, inv_pow, div_eq_mul_inv]; ring

/-- The reciprocal-exponential series converges locally uniformly jointly in all
parameters and slit-plane nodes. -/
theorem hasSumLocallyUniformlyOn_regCarlsonTSlit :
    HasSumLocallyUniformlyOn
      (fun (n : ℕ) (q : Sum ι ι → ℂ) => (n.factorial : ℂ)⁻¹ *
        regCarlsonR (-(n : ℂ)) (fun i => q (.inl i)) (fun i => q (.inr i)))
      (fun q => regCarlsonTSlit (fun i => q (.inl i)) (fun i => q (.inr i)))
      {q | (fun i => q (.inr i)) ∈ carlsonRSlitDomain} := by
  apply SummableLocallyUniformlyOn.hasSumLocallyUniformlyOn
  apply SummableLocallyUniformlyOn_of_locally_bounded
    (isOpen_carlsonRSlitDomain.preimage (by fun_prop))
  intro K hKU hK
  exact exists_summable_bound_regCarlsonTSlit hK hKU

/-- The regularized principal T-branch is jointly entire in the parameters and
holomorphic in every node throughout the product slit plane. -/
theorem analyticOnNhd_regCarlsonTSlit_joint :
    AnalyticOnNhd ℂ (fun q : Sum ι ι → ℂ =>
      regCarlsonTSlit (fun i => q (.inl i)) (fun i => q (.inr i)))
      {q | (fun i => q (.inr i)) ∈ carlsonRSlitDomain} := by
  classical
  apply hasSumLocallyUniformlyOn_regCarlsonTSlit.analyticOnNhd_pi _
    (isOpen_carlsonRSlitDomain.preimage (by fun_prop))
  intro n q hq
  apply AnalyticAt.mul analyticAt_const
  exact analyticAt_regCarlsonR_comp
    (b := fun q : Sum ι ι → ℂ => fun i => q (.inl i))
    (z := fun q : Sum ι ι → ℂ => fun i => q (.inr i)) analyticAt_const
    (analyticAt_pi_iff.mpr fun i =>
        (ContinuousLinearMap.proj (Sum.inl i) : (Sum ι ι → ℂ) →L[ℂ] ℂ).analyticAt q)
    (analyticAt_pi_iff.mpr fun i =>
        (ContinuousLinearMap.proj (Sum.inr i) : (Sum ι ι → ℂ) →L[ℂ] ℂ).analyticAt q) hq

/-- Analytic substitutions preserve the joint holomorphy of the principal T-branch. -/
theorem analyticAt_regCarlsonTSlit_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b z : E → ι → ℂ} {p : E} (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hdom : z p ∈ carlsonRSlitDomain) :
    AnalyticAt ℂ (fun q => regCarlsonTSlit (b q) (z q)) p := by
  have hm : AnalyticAt ℂ (fun q => Sum.elim (b q) (z q)) p := by
    apply analyticAt_pi_iff.mpr
    intro i
    cases i with
    | inl i => exact (analyticAt_pi_iff.mp hb) i
    | inr i => exact (analyticAt_pi_iff.mp hz) i
  exact (analyticOnNhd_regCarlsonTSlit_joint (Sum.elim (b p) (z p)) hdom).comp_of_eq hm rfl

/-- At fixed slit-plane nodes the principal regularized T-branch is entire in the parameters. -/
theorem analyticOnNhd_regCarlsonTSlit_parameters {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    AnalyticOnNhd ℂ (fun b => regCarlsonTSlit b z) univ := fun _ _ =>
  analyticAt_regCarlsonTSlit_comp analyticAt_id analyticAt_const hz

/-- At fixed parameters the principal regularized T-branch is holomorphic on the
full product slit plane. -/
theorem analyticOnNhd_regCarlsonTSlit_variables (b : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonTSlit b) carlsonRSlitDomain := fun _ hz =>
  analyticAt_regCarlsonTSlit_comp analyticAt_const analyticAt_id hz

/-- The principal T-series vanishes for an empty node index type. -/
@[simp] theorem regCarlsonTSlit_eq_zero_of_isEmpty [IsEmpty ι] (b z : ι → ℂ) :
    regCarlsonTSlit b z = 0 := by simp [regCarlsonTSlit, regCarlsonR_eq_zero_of_isEmpty]

end Carlson
