/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Algebra.LinearDependence
public import Carlson.Associated.Shift
public import Carlson.R.AssociatedRecurrence
public import Carlson.R.Relations
public import Pochhammer.Gamma

/-!
# Reduction of integral exponent shifts to a finite polynomial span

Carlson's reduction lemma 8.4-2: the R-functions obtained by shifting the exponent by arbitrary
integers, with fixed Dirichlet parameters, all lie in the span of finitely many of them over
the rational functions in the nodes. The proof uses the division-free homogeneity recurrence
of `Carlson.R.AssociatedRecurrence` and the denominator-clearing algebra of
`Algebra.LinearDependence`.

## Main results

* `Carlson.exists_polynomial_carlsonAssociated_exponent_reduction`: reduction with polynomial
  coefficients, valid on the whole node domain.
* `Carlson.exists_rational_carlsonAssociated_exponent_reduction`: reduction with rational
  coefficients, Carlson's Lemma 8.4-2.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The last polynomial recurrence coefficient can be used to lower the exponent at
every downward step. Unlike the quotient presentation, this statement includes `a = 0`. -/
theorem carlsonAssociatedRecurrencePolynomial_lower_ne_zero [Nonempty ι]
    {t : ℂ} (ht : IsCarlsonGammaRegular (1 - t)) (b z : ι → ℂ)
    (hz : z ∈ carlsonRVariableDomain) (m : ℕ) :
    (carlsonAssociatedRecurrencePolynomial (Fintype.card ι) (-t + m)
      ((∑ i, b i) + t - m) b).eval z ≠ 0 := by
  simp only [carlsonAssociatedRecurrencePolynomial, ite_eq_right Fintype.card_ne_zero,
    ↓reduceIte, map_mul, MvPolynomial.eval_C]
  change -(ascPochhammer ℂ (Fintype.card ι - 1)).eval (-t + m + 1) *
    carlsonElementarySymmetric (Fintype.card ι) z ≠ 0
  rw [show -t + (m : ℂ) + 1 = (1 - t) + m by ring, carlsonElementarySymmetric_card]
  exact mul_ne_zero (neg_ne_zero.mpr ((ht.add_nat m).ascPochhammer_ne_zero _))
    (Finset.prod_ne_zero_iff.mpr (fun i _ ↦
      slitPlane_ne_zero (carlsonRightHalfPlane_subset_slitPlane (hz i))))

/-- The first polynomial recurrence coefficient can be used to raise the exponent at
every upward step. The second regularity hypothesis of Carlson's reduction lemma is
exactly the one needed here. -/
theorem carlsonAssociatedRecurrencePolynomial_raise_ne_zero
    {t : ℂ} (b z : ι → ℂ)
    (ht : IsCarlsonGammaRegular ((∑ i, b i) + t - Fintype.card ι + 2)) (m : ℕ) :
    (carlsonAssociatedRecurrencePolynomial 0 (-(t + m + 1))
      ((∑ i, b i) + t + m + 1) b).eval z ≠ 0 := by
  simp only [carlsonAssociatedRecurrencePolynomial, ↓reduceIte, MvPolynomial.eval_C]
  rw [show (∑ i, b i) + t + m + 1 - Fintype.card ι + 1 =
    ((∑ i, b i) + t - Fintype.card ι + 2) + m by ring]
  exact (ht.add_nat m).ascPochhammer_ne_zero _

/-- The R-integral with fixed parameters, restricted to the variable domain, as a function of
the exponent. -/
private def rIntegralOnDomain (b : ι → ℂ) (u : ℂ) :
    {z : ι → ℂ // z ∈ carlsonRVariableDomain} → ℂ :=
  fun z => carlsonRIntegral u b z.1

/-- Polynomials act on functions on the variable domain by pointwise evaluation. -/
@[instance_reducible] private def moduleOfEval :
    Module (MvPolynomial ι ℂ) ({z : ι → ℂ // z ∈ carlsonRVariableDomain} → ℂ) :=
  Module.compHom _
    (RingHom.pi (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} => MvPolynomial.eval z.1))

attribute [local instance] moduleOfEval

/-- The denominator closure of the polynomial span of `card ι` consecutive downward exponent
shifts. -/
private def exponentReductionClosure (t : ℂ) (b : ι → ℂ) :
    Submodule (MvPolynomial ι ℂ) ({z : ι → ℂ // z ∈ carlsonRVariableDomain} → ℂ) :=
  Submodule.denominatorClosure (Submodule.span (MvPolynomial ι ℂ)
    (Set.range (fun j : Fin (Fintype.card ι) => rIntegralOnDomain b (t - (j : ℕ)))))

/-- One application of the homogeneity recurrence inside the denominator closure: among
`card ι + 1` consecutive exponent shifts, a shift with nonzero recurrence coefficient lies in
the closure as soon as all the others do. -/
private lemma rIntegralOnDomain_mem_of_forall_ne [Nonempty ι] (t : ℂ) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (a : ℂ) {i : ℕ} (hi : i ≤ Fintype.card ι)
    (hci : carlsonAssociatedRecurrencePolynomial i a ((∑ j, b j) - a) b ≠ 0)
    (hrest : ∀ j ∈ Finset.range (Fintype.card ι + 1), j ≠ i →
      rIntegralOnDomain b (-a - j) ∈ exponentReductionClosure t b) :
    rIntegralOnDomain b (-a - i) ∈ exponentReductionClosure t b := by
  apply Submodule.mem_denominatorClosure_of_sum_smul_eq_zero _
    (C := fun j => carlsonAssociatedRecurrencePolynomial j a ((∑ l, b l) - a) b)
    (F := fun j => rIntegralOnDomain b (-a - j)) (s := Finset.range (Fintype.card ι + 1)) _
    (Finset.mem_range.mpr (by omega)) hci hrest
  ext z
  simp only [Finset.sum_apply, Pi.zero_apply]
  exact sum_carlsonAssociatedRecurrencePolynomial_mul_rIntegral a hb z.2

/-- Every downward integer shift of the exponent lies in the closure. -/
private lemma rIntegralOnDomain_sub_natCast_mem [Nonempty ι] (t : ℂ) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (ht : IsCarlsonGammaRegular (1 - t)) (m : ℕ) :
    rIntegralOnDomain b (t - m) ∈ exponentReductionClosure t b := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m < Fintype.card ι
    · exact Submodule.mem_denominatorClosure _ (Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩)
    have he : t - (m : ℂ) = -(-t + (m - Fintype.card ι : ℕ)) - Fintype.card ι := by
      rw [Nat.cast_sub (by omega : Fintype.card ι ≤ m)]
      ring
    rw [he]
    apply rIntegralOnDomain_mem_of_forall_ne t hb _ le_rfl
    · have hc := carlsonAssociatedRecurrencePolynomial_lower_ne_zero ht b
        (fun _ => 1) (by intro i; norm_num [carlsonRVariableDomain, carlsonRightHalfPlane])
        (m - Fintype.card ι)
      intro h
      apply hc
      rw [show (∑ i, b i) + t - (m - Fintype.card ι : ℕ) =
        (∑ i, b i) - (-t + (m - Fintype.card ι : ℕ)) by ring, h, map_zero]
    · intro j hj hji
      have hj' := Finset.mem_range.mp hj
      have heq : -(-t + (m - Fintype.card ι : ℕ)) - j =
          t - (m - Fintype.card ι + j : ℕ) := by push_cast; ring
      rw [heq]
      exact ih _ (by omega)

/-- Every upward integer shift of the exponent lies in the closure. -/
private lemma rIntegralOnDomain_add_natCast_mem [Nonempty ι] (t : ℂ) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (ht : IsCarlsonGammaRegular (1 - t))
    (hct : IsCarlsonGammaRegular ((∑ i, b i) + t - Fintype.card ι + 2)) (m : ℕ) :
    rIntegralOnDomain b (t + m) ∈ exponentReductionClosure t b := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simpa using rIntegralOnDomain_sub_natCast_mem t hb ht 0
    | succ m =>
      have he : t + (m + 1 : ℕ) = -(-(t + m + 1)) - (0 : ℕ) := by push_cast; ring
      rw [he]
      apply rIntegralOnDomain_mem_of_forall_ne t hb _ (Nat.zero_le _)
      · have hc := carlsonAssociatedRecurrencePolynomial_raise_ne_zero b (fun _ => 1) hct m
        intro h
        apply hc
        rw [show (∑ i, b i) + t + m + 1 = (∑ i, b i) - (-(t + m + 1)) by ring,
          h, map_zero]
      · intro j hj hj0
        by_cases hjm : j ≤ m + 1
        · have heq : -(-(t + m + 1)) - j = t + (m + 1 - j : ℕ) := by
            rw [Nat.cast_sub hjm]; push_cast; ring
          rw [heq]
          exact ih _ (by omega)
        · have heq : -(-(t + m + 1)) - j = t - (j - (m + 1) : ℕ) := by
            rw [Nat.cast_sub (by omega : m + 1 ≤ j)]; push_cast; ring
          rw [heq]
          exact rIntegralOnDomain_sub_natCast_mem t hb ht _

/-- Denominator-cleared exponent reduction. The identity holds on the whole variable
domain, including the zero set of the denominator polynomial. -/
theorem exists_polynomial_carlsonAssociated_exponent_reduction
    (t : ℂ) (b : ι → ℂ) (n : ℤ)
    (hb : b ∈ mvBetaConvergent)
    (ht : IsCarlsonGammaRegular (1 - t))
    (hct : IsCarlsonGammaRegular ((∑ i, b i) + t - Fintype.card ι + 2)) :
    ∃ d : MvPolynomial ι ℂ, d ≠ 0 ∧
      ∃ p : Fin (Fintype.card ι) → MvPolynomial ι ℂ,
        ∀ z ∈ carlsonRVariableDomain,
          d.eval z * carlsonRIntegral (t + n) b z =
            ∑ j, (p j).eval z * carlsonRIntegral (t - (j : ℕ)) b z := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let _ := hι
    refine ⟨1, one_ne_zero, 0, ?_⟩
    simp [carlsonRIntegral]
  | inr hι =>
    let _ := hι
    have hn : rIntegralOnDomain b (t + n) ∈ exponentReductionClosure t b := by
      cases n with
      | ofNat m => exact rIntegralOnDomain_add_natCast_mem t hb ht hct m
      | negSucc m =>
        simpa [Int.cast_negSucc, sub_eq_add_neg] using
          rIntegralOnDomain_sub_natCast_mem t hb ht (m + 1)
    obtain ⟨d, hd, hspan⟩ := hn
    obtain ⟨p, hp⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial ι ℂ)).mp hspan
    refine ⟨d, hd, p, ?_⟩
    intro z hz
    have heq := congrFun hp (⟨z, hz⟩ : {z : ι → ℂ // z ∈ carlsonRVariableDomain})
    simp only [Finset.sum_apply] at heq
    change (∑ j, (p j).eval z * carlsonRIntegral (t - (j : ℕ)) b z) =
      d.eval z * carlsonRIntegral (t + n) b z at heq
    exact heq.symm

/-- Carlson's reduction lemma 8.4-2: all integral exponent shifts with fixed parameters lie
in the rational-function span of `card ι` consecutive R-functions. -/
theorem exists_rational_carlsonAssociated_exponent_reduction
    (t : ℂ) (b : ι → ℂ) (n : ℤ)
    (hb : b ∈ mvBetaConvergent)
    (ht : IsCarlsonGammaRegular (1 - t))
    (hct : IsCarlsonGammaRegular ((∑ i, b i) + t - Fintype.card ι + 2)) :
    ∃ q : Fin (Fintype.card ι) → CarlsonRRationalCoefficient ι,
      ∀ z ∈ carlsonRVariableDomain,
        (∀ j, (q j).denominator.eval z ≠ 0) →
        carlsonRIntegral (t + n) b z =
          ∑ j, (q j).eval z * carlsonRIntegral (t - (j : ℕ)) b z := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let _ := hι
    refine ⟨fun j => False.elim (by simpa using j.isLt), ?_⟩
    simp [carlsonRIntegral]
  | inr hι =>
    let _ := hι
    obtain ⟨d, hd, p, hp⟩ :=
      exists_polynomial_carlsonAssociated_exponent_reduction t b n hb ht hct
    refine ⟨fun j => ⟨p j, d, hd⟩, ?_⟩
    intro z hz hden
    have hd_eval : d.eval z ≠ 0 := hden ⟨0, Fintype.card_pos⟩
    change _ = ∑ j, ((p j).eval z / d.eval z) * _
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← hp z hz]
    exact (mul_div_cancel_left₀ _ hd_eval).symm

end Carlson
