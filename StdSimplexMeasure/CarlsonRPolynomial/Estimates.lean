/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import StdSimplexMeasure.CarlsonRPolynomial.Coefficients
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Data.Nat.Choose.Multinomial

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Pochhammer.Estimates

/-! # Estimates for Carlson's R-polynomials

Home for the Section 6.2 bounds used in normally convergent series.
-/

open Complex Finset ProbabilityTheory Set
open scoped Classical
@[expose] public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The power kernel represented by `carlsonPowerPolynomial` is uniformly bounded on the
standard simplex by the corresponding power of the sum of the variable norms. -/
theorem norm_eval_carlsonPowerPolynomial_le (n : ℕ) (z : ι → ℂ) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) :
    ‖(carlsonPowerPolynomial n z).eval (fun i ↦ (u i : ℂ))‖ ≤
      (∑ i, ‖z i‖) ^ n := by
  rw [eval_carlsonPowerPolynomial, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_carlsonAffineForm_le_sum_norm z hu) n

lemma norm_carlsonRPolynomialNumerator_le (n : ℕ) (b z : ι → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ i, ‖b i‖ ≤ B) :
    ‖carlsonRPolynomialNumerator n b z‖ ≤
      (B + n) ^ n * (∑ i, ‖z i‖) ^ n := by
  classical
  rw [carlsonRPolynomialNumerator]
  have hdeg {m : ι →₀ ℕ} (hm : m ∈ (carlsonPowerPolynomial n z).support) :
      m.sum (fun _ e ↦ e) = n := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hm)
      (coeff_carlsonPowerPolynomial_eq_zero_of_sum_ne n z m hne)
  have hpoch {m : ι →₀ ℕ} (hm : m ∈ (carlsonPowerPolynomial n z).support) :
      ‖∏ i, (ascPochhammer ℂ (m i)).eval (b i)‖ ≤ (B + n) ^ n := by
    have hmi : ∀ i, m i ≤ n := fun i => by
      have hle := Finset.single_le_sum (s := univ) (f := fun j : ι => m j)
        (fun _ _ => Nat.zero_le _) (mem_univ i)
      have hsum : ∑ j, m j = m.sum (fun _ e ↦ e) := by
        simpa using
          (Finsupp.sum_of_support_subset m (subset_univ m.support)
            (fun _ e ↦ e) (fun _ _ ↦ rfl)).symm
      simpa [hsum, hdeg hm] using hle
    refine (Complex.norm_prod univ _).trans_le ?_
    have hpt : ∀ i ∈ (univ : Finset ι),
        ‖(ascPochhammer ℂ (m i)).eval (b i)‖ ≤ (B + n) ^ m i :=
      fun i _ => (norm_ascPochhammer_eval_le (b i) (m i) hB (hb i)).trans <|
        pow_le_pow_left₀ (by positivity)
          (by gcongr; exact_mod_cast hmi i) _
    refine (prod_le_prod (fun _ _ => norm_nonneg _) hpt).trans ?_
    rw [prod_pow_eq_pow_sum]
    have hsum : ∑ j, m j = n := by
      have := Finsupp.sum_of_support_subset m (subset_univ m.support)
        (fun _ e ↦ e) (fun _ _ ↦ rfl)
      simpa using this.symm.trans (hdeg hm)
    simp [hsum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m ∈ (carlsonPowerPolynomial n z).support,
      ‖(m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e) *
          ∏ i, (ascPochhammer ℂ (m i)).eval (b i)‖ ≤
        (B + n) ^ n * ((m.multinomial : ℝ) * ∏ i, ‖z i‖ ^ m i) := by
    intro m hm
    have hzprod : ‖m.prod (fun i e ↦ z i ^ e)‖ = ∏ i, ‖z i‖ ^ m i := by
      rw [Finsupp.prod_of_support_subset m (subset_univ _) (fun i e ↦ z i ^ e) (by simp)]
      simp [norm_pow]
    calc
      ‖(m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e) *
            ∏ i, (ascPochhammer ℂ (m i)).eval (b i)‖ =
          (m.multinomial : ℝ) * ‖m.prod (fun i e ↦ z i ^ e)‖ *
            ‖∏ i, (ascPochhammer ℂ (m i)).eval (b i)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_natCast]
      _ = (m.multinomial : ℝ) * (∏ i, ‖z i‖ ^ m i) *
            ‖∏ i, (ascPochhammer ℂ (m i)).eval (b i)‖ := by rw [hzprod]
      _ ≤ (m.multinomial : ℝ) * (∏ i, ‖z i‖ ^ m i) * (B + n) ^ n := by
        gcongr
        exact hpoch hm
      _ = (B + n) ^ n * ((m.multinomial : ℝ) * ∏ i, ‖z i‖ ^ m i) := by ring
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  gcongr
  have hinj : InjOn (fun m : ι →₀ ℕ => (m : ι → ℕ))
      (carlsonPowerPolynomial n z).support := by
    intro x _ y _ hxy
    exact DFunLike.coe_injective hxy
  have himage :
      ((carlsonPowerPolynomial n z).support.image fun m : ι →₀ ℕ => (m : ι → ℕ)) ⊆
        piAntidiag univ n := by
    intro g hg
    rcases mem_image.mp hg with ⟨m, hm, rfl⟩
    refine mem_piAntidiag.mpr ⟨?_, fun _ _ => mem_univ _⟩
    have : univ.sum (m : ι → ℕ) = m.sum (fun _ e ↦ e) := by
      simpa using
        (Finsupp.sum_of_support_subset m (subset_univ m.support)
          (fun _ e ↦ e) (fun _ _ ↦ rfl)).symm
    exact this.trans (hdeg hm)
  have hsum :
      ∑ m ∈ (carlsonPowerPolynomial n z).support,
          (m.multinomial : ℝ) * ∏ i, ‖z i‖ ^ m i =
        ∑ g ∈ (carlsonPowerPolynomial n z).support.image fun m : ι →₀ ℕ => (m : ι → ℕ),
          (Nat.multinomial univ g : ℝ) * ∏ i, ‖z i‖ ^ g i := by
    rw [sum_image hinj]
    refine sum_congr rfl fun m hm => ?_
    congr 1
    exact_mod_cast (Finsupp.multinomial_of_support_subset (subset_univ _)).symm
  rw [hsum]
  refine (sum_le_sum_of_subset_of_nonneg himage fun _ _ _ => by positivity).trans_eq ?_
  exact (sum_pow_eq_sum_piAntidiag univ (fun i => ‖z i‖) n).symm

/-- On every compact set of Dirichlet parameters, the exponential generating terms of the
regularized Carlson R-polynomials admit a common summable majorant.  This is the compact-local
estimate underlying Carlson's entire continuation of the S-function in its parameters. -/
theorem exists_summable_norm_regCarlsonR_div_factorial_on_compact_parameters
    (z : ι → ℂ) {K : Set (ι → ℂ)} (hK : IsCompact K) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ n b, b ∈ K →
      ‖(Nat.factorial n : ℂ)⁻¹ * regCarlsonR n z b‖ ≤ M n := by
  /- The numerator bound is `norm_carlsonRPolynomialNumerator_le`.  The remaining input is a
  compact-uniform bound `‖Gamma (s + n)⁻¹‖ ≤ C * 2 ^ n / (n-1)!` for `s` in the compact
  image of `∑ i, b i`, obtained from the Gamma recurrence and a strip away from the
  nonpositive integers, after which `∑ n, (n+B)^n (C')^n / (n!)^2` is summable by the ratio
  test. -/
  sorry

end DirichletTransform
end CarlsonRPolynomial
