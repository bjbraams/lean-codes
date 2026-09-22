/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.S.Basic
public import Dirichlet.Average.Continuation
public import Carlson.RPolynomial.PowerSeries
public import Carlson.RPolynomial.Estimates
public import SeveralComplexVariables.LocallyUniform
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The exponential series and entire parameter continuation of S

Carlson's exponential generating series `∑ n, Rₙ(b, z) / n!` (formula 6.3-5) converges
absolutely for all complex parameters and nodes and defines the entire regularized continuation
of the S-function. This continuation is characterized uniquely by holomorphy in the parameters
and agreement with the native integral.

## Main definitions

* `Carlson.IsRegCarlsonSContinuation`: the continuation predicate.
* `Carlson.regCarlsonSSeries`, `Carlson.regCarlsonSPartialSum`: the series and its partial sums.

## Main results

* `Carlson.hasSum_regCarlsonSSeries`, `Carlson.summable_norm_regCarlsonR_div_factorial`:
  absolute convergence everywhere.
* `Carlson.regCarlsonSSeries_eq_regCarlsonSIntegral`: agreement with the native integral.
* `Carlson.isRegCarlsonSContinuation_series`, `Carlson.IsRegCarlsonSContinuation.eq_series`:
  the series is the unique entire continuation.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- A candidate is an entire regularized continuation of Carlson's `S` if it agrees with the
native regularized integral wherever all Dirichlet parameters have positive real part. -/
def IsRegCarlsonSContinuation (z : ι → ℂ) (G : (ι → ℂ) → ℂ) : Prop :=
  IsRegCarlsonContinuation exp z G

/-- A regularized Carlson `S` continuation is entire in the Dirichlet parameters. -/
theorem IsRegCarlsonSContinuation.analyticOnNhd {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonSContinuation z G) : AnalyticOnNhd ℂ G Set.univ :=
  hG.1

/-- A regularized Carlson `S` continuation agrees with the native integral on its ordinary
domain of absolute convergence. -/
theorem IsRegCarlsonSContinuation.eq_integral {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonSContinuation z G) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    G b = regCarlsonSIntegral b z :=
  hG.2 hb

/-- An entire regularized continuation of Carlson's `S`, if it exists, is unique. -/
theorem IsRegCarlsonSContinuation.eq {z : ι → ℂ} {G H : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonSContinuation z G) (hH : IsRegCarlsonSContinuation z H) : G = H :=
  IsRegCarlsonContinuation.eq hG hH

/-- The series defining the entire regularized Carlson `S` function.  This is the
exponential specialization of Carlson's regularized Taylor construction. -/
def regCarlsonSSeries (z b : ι → ℂ) : ℂ :=
  regCarlsonTaylorSeries 0 (fun n ↦ (Nat.factorial n : ℂ)⁻¹) z b

/-- Carlson's formula (6.3-5), exposing the regularized `S` continuation as the exponential
generating series of the regularized `R` polynomials. -/
theorem regCarlsonSSeries_eq_tsum_regCarlsonRPolynomial (z b : ι → ℂ) :
    regCarlsonSSeries z b =
      ∑' n : ℕ, (Nat.factorial n : ℂ)⁻¹ * regCarlsonRPolynomial n b z := by
  simp [regCarlsonSSeries, regCarlsonTaylorSeries]

/-- Carlson's exponential series is absolutely summable at every complex parameter and
node vector, including parameters outside the native integral's convergence region. -/
theorem summable_norm_regCarlsonR_div_factorial (z b : ι → ℂ) :
    Summable fun n : ℕ ↦ ‖(Nat.factorial n : ℂ)⁻¹ * regCarlsonRPolynomial n b z‖ := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_summable_norm_regCarlsonR_div_factorial_on_compact_parameters z
      (isCompact_singleton (x := b))
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ hbound n b (Set.mem_singleton b)) hM

/-- The exponential generating series sums to the continued `S` function for all complex
parameters and nodes, without an integral-convergence hypothesis. -/
theorem hasSum_regCarlsonSSeries (z b : ι → ℂ) :
    HasSum (fun n : ℕ ↦ (Nat.factorial n : ℂ)⁻¹ * regCarlsonRPolynomial n b z)
      (regCarlsonSSeries z b) := by
  rw [regCarlsonSSeries_eq_tsum_regCarlsonRPolynomial]
  exact (summable_norm_regCarlsonR_div_factorial z b).of_norm.hasSum

/-- The `N`th partial sum in Carlson's exponential-series construction of the regularized
`S` function. -/
def regCarlsonSPartialSum (N : ℕ) (z b : ι → ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (Nat.factorial n : ℂ)⁻¹ * regCarlsonRPolynomial n b z

/-- Every partial sum in Carlson's construction is entire in the Dirichlet parameters. -/
theorem analyticOnNhd_regCarlsonSPartialSum (N : ℕ) (z : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonSPartialSum N z) Set.univ := by
  intro b _
  unfold regCarlsonSPartialSum
  apply Finset.analyticAt_fun_sum
  intro n _
  exact analyticAt_const.mul
    (analyticOnNhd_regCarlsonRPolynomial n z b (Set.mem_univ b))

/-- The partial-sum consequence of summability.  The unconditional version for all complex
parameters and nodes is `tendsto_regCarlsonSPartialSum_all`. -/
theorem tendsto_regCarlsonSPartialSum (z b : ι → ℂ)
    (h : Summable fun n : ℕ ↦ (Nat.factorial n : ℂ)⁻¹ * regCarlsonRPolynomial n b z) :
    Filter.Tendsto (fun N ↦ regCarlsonSPartialSum N z b) Filter.atTop
      (nhds (regCarlsonSSeries z b)) := by
  rw [regCarlsonSSeries_eq_tsum_regCarlsonRPolynomial]
  exact h.hasSum.tendsto_sum_nat

/-- The partial sums converge to the entire regularized `S` function at every complex
parameter and node vector. -/
theorem tendsto_regCarlsonSPartialSum_all (z b : ι → ℂ) :
    Filter.Tendsto (fun N ↦ regCarlsonSPartialSum N z b) Filter.atTop
      (nhds (regCarlsonSSeries z b)) :=
  (hasSum_regCarlsonSSeries z b).tendsto_sum_nat

/-- The exponential series of the Carlson affine form converges pointwise to the exponential
kernel. -/
theorem hasSum_exp_carlsonAffineForm (z : ι → ℂ) (u : ι → ℝ) :
    HasSum (fun n : ℕ ↦ carlsonAffineForm z u ^ n / Nat.factorial n)
      (exp (carlsonAffineForm z u)) :=
  by
    simpa [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp (carlsonAffineForm z u))

/-- On the native convergence region, Carlson's exponential series is summable and its sum
is the regularized `S` integral.  This is the integral form of the power-series construction
in Sections 5.7--5.8. -/
theorem hasSum_regCarlsonR_div_factorial_eq_regCarlsonSIntegral
    (z : ι → ℂ) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    HasSum (fun n : ℕ ↦ (Nat.factorial n : ℂ)⁻¹ * regCarlsonRPolynomial n b z)
      (regCarlsonSIntegral b z) := by
  let μ := (MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict
      (Convexity.StdSimplex.coordinateSet ℝ ι)
  let C : ℝ := ∑ i, ‖z i‖
  let M : ℕ → ℝ := fun n ↦ C ^ n / Nat.factorial n
  let F : ℕ → (ι → ℝ) → ℂ := fun n u ↦
    regDirichletDensity b u * (carlsonAffineForm z u ^ n / Nat.factorial n)
  let g : (ι → ℝ) → ℂ := fun u ↦
    regDirichletDensity b u * exp (carlsonAffineForm z u)
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hM : Summable M := by
    simpa [M] using Real.summable_pow_div_factorial C
  have hdens : Integrable (fun u ↦ regDirichletDensity b u) μ :=
    integrableOn_regDirichletDensity b hb
  have hF_meas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    exact (integrableOn_regDirichletDensity_mul b hb
      ((continuous_carlsonAffineForm z).continuousOn.pow n |>.div_const _)).1
  have hbound (n : ℕ) : ∀ᵐ u ∂μ, ‖F n u‖ ≤ M n * ‖regDirichletDensity b u‖ := by
    filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    simp only [F, M, norm_mul, norm_div, norm_natCast]
    calc
      ‖regDirichletDensity b u‖ * (‖carlsonAffineForm z u ^ n‖ / ↑n.factorial) ≤
          ‖regDirichletDensity b u‖ * (C ^ n / ↑n.factorial) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            rw [norm_pow]
            exact pow_le_pow_left₀ (norm_nonneg _)
              (norm_carlsonAffineForm_le_sum_norm z hu) n
      _ = C ^ n / ↑n.factorial * ‖regDirichletDensity b u‖ := by ring
  have hbound_summable : ∀ᵐ u ∂μ,
      Summable fun n ↦ M n * ‖regDirichletDensity b u‖ := by
    filter_upwards with u
    exact hM.mul_right _
  have hbound_integrable : Integrable
      (fun u ↦ ∑' n, M n * ‖regDirichletDensity b u‖) μ := by
    have heq : (fun u ↦ ∑' n, M n * ‖regDirichletDensity b u‖) =
        fun u ↦ (∑' n, M n) * ‖regDirichletDensity b u‖ := by
      funext u
      rw [tsum_mul_right]
    rw [heq]
    exact hdens.norm.const_mul _
  have hlim : ∀ᵐ u ∂μ, HasSum (fun n ↦ F n u) (g u) := by
    filter_upwards with u
    exact (hasSum_exp_carlsonAffineForm z u).mul_left (regDirichletDensity b u)
  have h := hasSum_integral_of_dominated_convergence
    (fun n u ↦ M n * ‖regDirichletDensity b u‖) hF_meas hbound
      hbound_summable hbound_integrable hlim
  have hterm (n : ℕ) : (∫ u, F n u ∂μ) =
      (Nat.factorial n : ℂ)⁻¹ * regCarlsonRPolynomial n b z := by
    rw [show (fun u ↦ F n u) = fun u ↦ (Nat.factorial n : ℂ)⁻¹ *
        (regDirichletDensity b u * carlsonAffineForm z u ^ n) by
      funext u
      simp [F, div_eq_mul_inv]
      ring]
    rw [integral_const_mul]
    rw [← regCarlsonDirichletAverage_pow n z hb]
    rfl
  simpa [g, μ, regCarlsonSIntegral, regCarlsonDirichletAverage,
    regDirichletIntegral] using h.congr_fun (fun n ↦ (hterm n).symm)

/-- Carlson's exponential series is summable throughout the native Dirichlet convergence
region. -/
theorem summable_regCarlsonR_div_factorial
    (z : ι → ℂ) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    Summable fun n : ℕ ↦ (Nat.factorial n : ℂ)⁻¹ * regCarlsonRPolynomial n b z :=
  (hasSum_regCarlsonR_div_factorial_eq_regCarlsonSIntegral z hb).summable

/-- On the native convergence region, the series construction of the regularized `S`
function agrees with its defining Dirichlet integral. -/
theorem regCarlsonSSeries_eq_regCarlsonSIntegral
    (z : ι → ℂ) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonSSeries z b = regCarlsonSIntegral b z := by
  rw [regCarlsonSSeries_eq_tsum_regCarlsonRPolynomial]
  exact (hasSum_regCarlsonR_div_factorial_eq_regCarlsonSIntegral z hb).tsum_eq

/-- Carlson's series construction is entire in all Dirichlet parameters.  This is the
analytic assertion in Corollary 6.3-3; its proof is the locally uniform version of the
coefficient estimate used above for pointwise summability. -/
theorem analyticOnNhd_regCarlsonSSeries (z : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonSSeries z) Set.univ := by
  classical
  rw [show regCarlsonSSeries z = fun b ↦ ∑' n : ℕ,
      (Nat.factorial n : ℂ)⁻¹ * regCarlsonRPolynomial n b z by
    funext b
    exact regCarlsonSSeries_eq_tsum_regCarlsonRPolynomial z b]
  apply analyticOnNhd_tsum_of_summable_norm_on_compacts isOpen_univ
  · intro n
    exact analyticOnNhd_const.mul (analyticOnNhd_regCarlsonRPolynomial n z)
  · intro K hKuniv hK
    exact exists_summable_norm_regCarlsonR_div_factorial_on_compact_parameters z hK

/-- The exponential series realizes Carlson's entire regularized continuation of `S`. -/
theorem isRegCarlsonSContinuation_series (z : ι → ℂ) :
    IsRegCarlsonSContinuation z (regCarlsonSSeries z) := by
  refine ⟨analyticOnNhd_regCarlsonSSeries z, ?_⟩
  intro b hb
  exact regCarlsonSSeries_eq_regCarlsonSIntegral z hb

/-- Every entire regularized continuation of Carlson's `S` is the exponential series. -/
theorem IsRegCarlsonSContinuation.eq_series {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonSContinuation z G) : G = regCarlsonSSeries z :=
  hG.eq (isRegCarlsonSContinuation_series z)

end Carlson
