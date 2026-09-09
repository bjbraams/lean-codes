/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonRPolynomial.Estimates
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Generating functions of Carlson's R-polynomials

This file develops [Carl77, Section 6.6].  The scalar geometric kernel is recorded separately
from the subsequent coefficient and convergence argument.
-/

open Complex Filter Finset
open scoped Classical Topology Nat
public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The scalar kernels used in Carlson's generating relation converge to the exponential
kernel under confluence. -/
theorem tendsto_carlsonGeneratingKernel (w : ℂ) :
    Tendsto (fun n : ℕ ↦ (1 + w / n) ^ n) atTop (𝓝 (exp w)) :=
  Complex.tendsto_one_add_div_pow_exp w

/-- The scalar binomial series used in each factor of Carlson's generating relation 6.6-1,
written with ascending Pochhammer coefficients. -/
theorem hasSum_ascPochhammer_mul_pow_div_factorial (a t : ℂ) (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ ↦
      (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * t ^ n)
      (1 / (1 - t) ^ a) := by
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).hasSum
    (show t ∈ Metric.eball (0 : ℂ) 1 by
      simp only [Metric.mem_eball, edist_zero_right]
      rw [enorm_eq_nnnorm]
      exact_mod_cast ht)
  have hmulti : HasSum (fun n : ℕ ↦ Ring.multichoose a n * t ^ n)
      (1 / (1 - t) ^ a) := by
    simpa [FormalMultilinearSeries.ofScalars, Ring.multichoose_eq] using h
  convert hmulti using 1 with n
  funext n
  congr 1
  symm
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).2
  rw [mul_comm]
  simpa [Polynomial.ascPochhammer_smeval_cast,
    Polynomial.ascPochhammer_smeval_eq_eval] using
      (Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n)

/-- Ascending Pochhammer symbols divided by factorials are the binomial-ring multichoose
coefficients. -/
theorem ascPochhammer_eval_div_factorial (a : ℂ) (n : ℕ) :
    (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) = Ring.multichoose a n := by
  refine Eq.symm ?_
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).2
  rw [mul_comm]
  simpa [Polynomial.ascPochhammer_smeval_cast,
    Polynomial.ascPochhammer_smeval_eq_eval] using
      (Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n)

/-- The scalar binomial series of Carlson's generating relation is absolutely summable
inside the unit disk. -/
theorem summable_norm_ascPochhammer_mul_pow_div_factorial (a t : ℂ) (ht : ‖t‖ < 1) :
    Summable fun n : ℕ =>
      ‖(ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * t ^ n‖ := by
  have hp := Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a
  have htball : t ∈ Metric.eball (0 : ℂ) 1 := by
    simp only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    exact_mod_cast ht
  have hx : t ∈ Metric.eball (0 : ℂ)
      (FormalMultilinearSeries.ofScalars ℂ
        fun n ↦ Ring.choose (a + n - 1) n).radius :=
    (Metric.eball_subset_eball hp.r_le) htball
  have hnorm :=
    (FormalMultilinearSeries.ofScalars ℂ
      fun n ↦ Ring.choose (a + n - 1) n).summable_norm_apply hx
  refine hnorm.congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [← Ring.multichoose_eq, ← ascPochhammer_eval_div_factorial]

/-- The Pochhammer-weighted multinomial coefficient of total degree `n` on a finite
index set. -/
def carlsonGeneratingCoeff (s : Finset ι) (b z : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ m ∈ piAntidiag s n,
    (Nat.multinomial s m : ℂ) *
      (∏ i ∈ s, z i ^ m i) *
      (∏ i ∈ s, (ascPochhammer ℂ (m i)).eval (b i))

/-- Reindexing the degree-`n` Finsupp antidiagonal along `Finsupp.equivFunOnFinite`. -/
theorem map_equivFunOnFinite_piAntidiag_univ (n : ℕ) :
    (piAntidiag (univ : Finset ι) n).map
      ⟨Finsupp.equivFunOnFinite.symm, Equiv.injective _⟩ =
      finsuppAntidiag (univ : Finset ι) n := by
  apply Finset.ext
  intro m
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_piAntidiag,
    mem_finsuppAntidiag]
  constructor
  · rintro ⟨f, ⟨hfsum, _⟩, rfl⟩
    refine ⟨?_, subset_univ _⟩
    simpa [Finsupp.equivFunOnFinite] using hfsum
  · intro ⟨hsum, _⟩
    refine ⟨(m : ι → ℕ), ⟨hsum, fun _ _ => mem_univ _⟩, ?_⟩
    exact Finsupp.equivFunOnFinite.symm_apply_apply m

/-- The Pochhammer numerator is the complete degree-`n` multinomial expansion. -/
theorem carlsonRPolynomialNumerator_eq_sum_piAntidiag (n : ℕ) (b z : ι → ℂ) :
    carlsonRPolynomialNumerator n b z =
      carlsonGeneratingCoeff (univ : Finset ι) b z n := by
  unfold carlsonRPolynomialNumerator carlsonGeneratingCoeff
  have hsub : (carlsonPowerPolynomial n z).support ⊆
      finsuppAntidiag (univ : Finset ι) n := by
    intro m hm
    have hdeg : m.sum (fun _ e ↦ e) = n := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hm)
        (coeff_carlsonPowerPolynomial_eq_zero_of_sum_ne n z m hne)
    refine (mem_finsuppAntidiag (s := univ) (n := n) (f := m)).2 ⟨?_, subset_univ _⟩
    have : univ.sum (m : ι → ℕ) = m.sum (fun _ e ↦ e) := by
      simpa using
        (Finsupp.sum_of_support_subset m (subset_univ m.support)
          (fun _ e ↦ e) (fun _ _ ↦ rfl)).symm
    exact this.trans hdeg
  have hsum :
      ∑ m ∈ (carlsonPowerPolynomial n z).support,
          (m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e) *
            ∏ i, (ascPochhammer ℂ (m i)).eval (b i) =
        ∑ m ∈ finsuppAntidiag (univ : Finset ι) n,
          (m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e) *
            ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
    apply Finset.sum_subset hsub
    intro m hm hn
    have hdeg : univ.sum (m : ι → ℕ) = n :=
      (mem_finsuppAntidiag.mp hm).1
    have hcoeff := coeff_carlsonPowerPolynomial n z m
    have hz : (carlsonPowerPolynomial n z).coeff m = 0 :=
      MvPolynomial.notMem_support_iff.mp hn
    have hsum' : m.sum (fun _ e ↦ e) = n := by
      have : univ.sum (m : ι → ℕ) = m.sum (fun _ e ↦ e) := by
        simpa using
          (Finsupp.sum_of_support_subset m (subset_univ m.support)
            (fun _ e ↦ e) (fun _ _ ↦ rfl)).symm
      exact this.symm.trans hdeg
    simp only [hsum', ↓reduceIte] at hcoeff
    have : (m.multinomial : ℂ) * m.prod (fun i e ↦ z i ^ e) = 0 :=
      hcoeff ▸ hz
    rw [this, zero_mul]
  rw [hsum, ← map_equivFunOnFinite_piAntidiag_univ, sum_map]
  apply sum_congr rfl
  intro f hf
  simp only [Function.Embedding.coeFn_mk]
  have hsupp : (Finsupp.equivFunOnFinite.symm f).support ⊆ univ := subset_univ _
  rw [Finsupp.multinomial_eq_of_support_subset hsupp]
  have hprod :
      (Finsupp.equivFunOnFinite.symm f).prod (fun i e ↦ z i ^ e) =
        ∏ i, z i ^ f i := by
    rw [Finsupp.prod_of_support_subset _ hsupp (fun i e ↦ z i ^ e) (by simp)]
    simp
  simp [hprod]

/-- The finite product on the left side of Carlson's generating relation 6.6-1. -/
def carlsonRGeneratingKernel (b z : ι → ℂ) (t : ℂ) : ℂ :=
  ∏ i, 1 / (1 - t * z i) ^ (b i)

/-- One antidiagonal slice of the Cauchy product for a `cons` generating coefficient. -/
theorem carlsonGeneratingCoeff_cons_antidiag {s : Finset ι} {i : ι} (hi : i ∉ s)
    (b z : ι → ℂ) (t : ℂ) {k l n : ℕ} (hkl : k + l = n) :
    ∑ m ∈ piAntidiag s l,
        (Nat.multinomial (cons i s hi) (m + fun j => if j = i then k else 0) : ℂ) *
          (∏ j ∈ cons i s hi, z j ^ (m j + if j = i then k else 0)) *
          (∏ j ∈ cons i s hi,
            (ascPochhammer ℂ (m j + if j = i then k else 0)).eval (b j)) /
        (n.factorial : ℂ) * t ^ n =
      ((ascPochhammer ℂ k).eval (b i) / (k.factorial : ℂ) * (t * z i) ^ k) *
        (carlsonGeneratingCoeff s b z l / (l.factorial : ℂ) * t ^ l) := by
  have hklen : k ≤ n := Nat.le.intro hkl
  have hpoint : ∀ m ∈ piAntidiag s l,
      (Nat.multinomial (cons i s hi) (m + fun j => if j = i then k else 0) : ℂ) *
          (∏ j ∈ cons i s hi, z j ^ (m j + if j = i then k else 0)) *
          (∏ j ∈ cons i s hi,
            (ascPochhammer ℂ (m j + if j = i then k else 0)).eval (b j)) /
        (n.factorial : ℂ) * t ^ n =
        ((ascPochhammer ℂ k).eval (b i) / (k.factorial : ℂ) * (t * z i) ^ k) *
          ((Nat.multinomial s m : ℂ) * (∏ j ∈ s, z j ^ m j) *
            (∏ j ∈ s, (ascPochhammer ℂ (m j)).eval (b j)) /
            (l.factorial : ℂ) * t ^ l) := by
    intro m hm
    have hmi : m i = 0 := (not_imp_comm.1 ((mem_piAntidiag.mp hm).2 i)) hi
    have hsumg : s.sum m = l := (mem_piAntidiag.mp hm).1
    have hx : ∀ x ∈ s, (m + fun j => if j = i then k else 0) x = m x := by
      intro x hx
      simp [Pi.add_apply, ne_of_mem_of_not_mem hx hi]
    have hmn :
        Nat.multinomial (cons i s hi) (m + fun j => if j = i then k else 0) =
          n.choose k * Nat.multinomial s m := by
      rw [Nat.multinomial_cons hi]
      simp only [Pi.add_apply, ↓reduceIte, hmi, zero_add]
      have hsum' : ∑ x ∈ s, (m x + if x = i then k else 0) = l := by
        trans ∑ x ∈ s, m x
        · exact sum_congr rfl fun x hx' => by simp [ne_of_mem_of_not_mem hx' hi]
        · exact hsumg
      rw [hsum', hkl, Nat.multinomial_congr hx]
    have hpow :
        (∏ j ∈ cons i s hi, z j ^ (m j + if j = i then k else 0)) =
          z i ^ k * ∏ j ∈ s, z j ^ m j := by
      rw [prod_cons]
      simp only [↓reduceIte, hmi, zero_add]
      congr 1
      exact prod_congr rfl fun j hj => by simp [ne_of_mem_of_not_mem hj hi]
    have hpoch :
        (∏ j ∈ cons i s hi,
            (ascPochhammer ℂ (m j + if j = i then k else 0)).eval (b j)) =
          (ascPochhammer ℂ k).eval (b i) *
            ∏ j ∈ s, (ascPochhammer ℂ (m j)).eval (b j) := by
      rw [prod_cons]
      simp only [↓reduceIte, hmi, zero_add]
      congr 1
      exact prod_congr rfl fun j hj => by simp [ne_of_mem_of_not_mem hj hi]
    have htpow : t ^ n = t ^ k * t ^ l := by
      rw [← pow_add, hkl]
    have hN : n.choose k * k.factorial * l.factorial = n.factorial := by
      have := Nat.choose_mul_factorial_mul_factorial hklen
      simpa [show n - k = l by omega] using this
    rw [hmn, hpow, hpoch, Nat.cast_mul, htpow]
    have hk0 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hl0 : (l.factorial : ℂ) ≠ 0 := by exact_mod_cast l.factorial_ne_zero
    have hn0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hNℂ : (n.choose k : ℂ) * (k.factorial : ℂ) * (l.factorial : ℂ) =
        n.factorial := by exact_mod_cast hN
    field_simp
    rw [← hNℂ]
    ring
  rw [sum_congr rfl hpoint]
  trans ∑ m ∈ piAntidiag s l,
      ((ascPochhammer ℂ k).eval (b i) / (k.factorial : ℂ) * (t * z i) ^ k) *
        ((Nat.multinomial s m : ℂ) * (∏ j ∈ s, z j ^ m j) *
          (∏ j ∈ s, (ascPochhammer ℂ (m j)).eval (b j)) /
          (l.factorial : ℂ) * t ^ l)
  · apply sum_congr rfl
    intro m hm
    ring
  rw [← mul_sum]
  unfold carlsonGeneratingCoeff
  simp_rw [div_eq_mul_inv]
  congr 1
  have hsmul := sum_mul (s := piAntidiag s l)
    (fun x =>
      ((Nat.multinomial s x : ℂ) * (∏ j ∈ s, z j ^ x j) *
          ∏ j ∈ s, (ascPochhammer ℂ (x j)).eval (b j)) *
        (l.factorial : ℂ)⁻¹)
    (t ^ l)
  refine Eq.trans ?_ (hsmul.symm.trans ?_)
  · apply sum_congr rfl
    intro x hx
    ring
  · simp [sum_mul]

/-- Adjoining one Carlson coordinate corresponds to the Cauchy product of generating
series. -/
theorem carlsonGeneratingCoeff_cons {s : Finset ι} {i : ι} (hi : i ∉ s)
    (b z : ι → ℂ) (t : ℂ) (n : ℕ) :
    carlsonGeneratingCoeff (cons i s hi) b z n / (n.factorial : ℂ) * t ^ n =
      ∑ k ∈ range (n + 1),
        ((ascPochhammer ℂ k).eval (b i) / (k.factorial : ℂ) * (t * z i) ^ k) *
          (carlsonGeneratingCoeff s b z (n - k) / ((n - k).factorial : ℂ) *
            t ^ (n - k)) := by
  unfold carlsonGeneratingCoeff
  rw [piAntidiag_cons hi, sum_disjiUnion]
  simp only [sum_map, addRightEmbedding_apply, Pi.add_apply]
  simp_rw [div_mul_eq_mul_div]
  rw [sum_mul, sum_div]
  simp_rw [← div_mul_eq_mul_div]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l =>
      (∑ m ∈ piAntidiag s l,
          (Nat.multinomial (cons i s hi) (m + fun j => if j = i then k else 0) : ℂ) *
            (∏ j ∈ cons i s hi, z j ^ (m j + if j = i then k else 0)) *
            (∏ j ∈ cons i s hi,
              (ascPochhammer ℂ (m j + if j = i then k else 0)).eval (b j))) /
        (n.factorial : ℂ) * t ^ n)]
  apply sum_congr rfl
  intro k hk
  have hklen : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hkl : k + (n - k) = n := Nat.add_sub_of_le hklen
  convert (carlsonGeneratingCoeff_cons_antidiag (s := s) (i := i) hi b z t hkl) using 1
  · rw [sum_div, mul_comm _ (t ^ n), ← sum_mul, mul_comm]
  · simp [carlsonGeneratingCoeff]

/-- The empty generating series is the constant series `1`. -/
theorem carlsonGeneratingCoeff_empty (b z : ι → ℂ) (n : ℕ) :
    carlsonGeneratingCoeff (∅ : Finset ι) b z n = if n = 0 then 1 else 0 := by
  unfold carlsonGeneratingCoeff
  cases n with
  | zero => simp [Nat.multinomial_empty]
  | succ n => simp [piAntidiag_empty_of_ne_zero (Nat.succ_ne_zero n)]

/-- The generating series attached to a subset of the Carlson coordinates. -/
theorem hasSum_carlsonGeneratingCoeff (s : Finset ι) (b z : ι → ℂ) (t : ℂ)
    (ht : ∀ i ∈ s, ‖t * z i‖ < 1) :
    HasSum (fun n : ℕ =>
      carlsonGeneratingCoeff s b z n / (n.factorial : ℂ) * t ^ n)
      (∏ i ∈ s, 1 / (1 - t * z i) ^ (b i)) ∧
    Summable (fun n : ℕ =>
      ‖carlsonGeneratingCoeff s b z n / (n.factorial : ℂ) * t ^ n‖) := by
  induction s using Finset.cons_induction with
  | empty =>
      have hterm : ∀ n : ℕ,
          carlsonGeneratingCoeff (∅ : Finset ι) b z n / (n.factorial : ℂ) * t ^ n =
            if n = 0 then 1 else 0 := by
        intro n
        rw [carlsonGeneratingCoeff_empty]
        split_ifs with hn
        · subst n; simp
        · simp
      constructor
      · convert hasSum_ite_eq (0 : ℕ) (1 : ℂ)
        · exact hterm _
        · simp
      · have hnorm : ∀ n : ℕ,
            ‖carlsonGeneratingCoeff (∅ : Finset ι) b z n / (n.factorial : ℂ) * t ^ n‖ =
              if n = 0 then (1 : ℝ) else 0 := by
          intro n
          rw [hterm]
          split_ifs <;> simp
        convert (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable
        exact hnorm _
  | cons i s hi ih =>
      have ih' := ih (fun j hj => ht j (mem_cons.mpr (Or.inr hj)))
      have hti : ‖t * z i‖ < 1 := ht i (by simp)
      have hf := hasSum_ascPochhammer_mul_pow_div_factorial (b i) (t * z i) hti
      have hfnorm :=
        summable_norm_ascPochhammer_mul_pow_div_factorial (b i) (t * z i) hti
      let f : ℕ → ℂ := fun k =>
        (ascPochhammer ℂ k).eval (b i) / (k.factorial : ℂ) * (t * z i) ^ k
      let g : ℕ → ℂ := fun l =>
        carlsonGeneratingCoeff s b z l / (l.factorial : ℂ) * t ^ l
      have hCauchy :=
        hasSum_sum_range_mul_of_summable_norm (R := ℂ) (f := f) (g := g)
          hfnorm ih'.2
      have hident := carlsonGeneratingCoeff_cons (s := s) (i := i) hi b z t
      have hfun :
          (fun n : ℕ => ∑ k ∈ range (n + 1), f k * g (n - k)) =
            fun n =>
              carlsonGeneratingCoeff (cons i s hi) b z n / (n.factorial : ℂ) * t ^ n := by
        funext n
        exact (hident n).symm
      constructor
      · rw [hfun] at hCauchy
        rw [hf.tsum_eq, ih'.1.tsum_eq] at hCauchy
        simp only [one_div, prod_cons] at hCauchy ⊢
        simpa [mul_inv] using hCauchy
      · have hnormCauchy :=
          summable_norm_sum_mul_range_of_summable_norm (R := ℂ) hfnorm ih'.2
        have hfun' :
            (fun n : ℕ => ‖∑ k ∈ range (n + 1), f k * g (n - k)‖) =
              fun n =>
                ‖carlsonGeneratingCoeff (cons i s hi) b z n / (n.factorial : ℂ) *
                  t ^ n‖ := by
          funext n
          rw [hident n]
        rwa [hfun'] at hnormCauchy

/-- Carlson's generating relation 6.6-1 in the division-free Pochhammer-numerator
normalization.

The hypothesis puts every scalar binomial series inside its disk of convergence.  The
coefficient of `t ^ n` is the Pochhammer numerator divided by `n!`; consequently this
statement continues to make sense at exceptional values of the total parameter. -/
theorem hasSum_carlsonRPolynomialNumerator_div_factorial (b z : ι → ℂ) (t : ℂ)
    (ht : ∀ i, ‖t * z i‖ < 1) :
    HasSum (fun n : ℕ =>
      carlsonRPolynomialNumerator n b z / (n.factorial : ℂ) * t ^ n)
      (carlsonRGeneratingKernel b z t) := by
  have h := hasSum_carlsonGeneratingCoeff (univ : Finset ι) b z t (fun i _ => ht i)
  simpa [carlsonRGeneratingKernel, carlsonRPolynomialNumerator_eq_sum_piAntidiag]
    using h.1

/-- Within the common disk `‖t * z i‖ < 1`, the series of Carlson numerator
coefficients is summable. -/
theorem summable_carlsonRPolynomialNumerator_div_factorial (b z : ι → ℂ) (t : ℂ)
    (ht : ∀ i, ‖t * z i‖ < 1) :
    Summable (fun n : ℕ =>
      carlsonRPolynomialNumerator n b z / (n.factorial : ℂ) * t ^ n) :=
  (hasSum_carlsonRPolynomialNumerator_div_factorial b z t ht).summable

/- Generating Relation 6.6-1 in Carlson's usual normalization is

  `∏ i, (1 - t * z i) ^ (-b i) =
    ∑' n, (ascPochhammer ℂ n).eval (∑ i, b i) / n! * Rₙ(b,z) * t^n`.

The theorem above records its parameter-robust numerator form. -/

end DirichletTransform
end CarlsonRPolynomial
