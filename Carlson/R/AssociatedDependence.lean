/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import Carlson.R.AssociatedRecurrence
public import Carlson.R.Relations
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Polynomial dependence of associated Carlson R-functions

This file proves [Carl77, Lemma 8.4-2 and Theorem 8.4-3]. The algebraic exponent reduction
uses the recurrence from `Carlson.R.AssociatedRecurrence`, retaining a denominator-cleared
identity valid throughout the variable domain. Repeated parameter raising then reduces
associated functions to a common parameter vector. Finite-dimensional linear algebra over
the polynomial ring gives a nontrivial polynomial relation between any `card ι + 1` of them.

`exists_polynomial_relation_associatedRContinued` extends this conclusion to arbitrary
complex exponents and Dirichlet parameters for the regularized continued functions.
The nodes remain in `carlsonRVariableDomain` (the product of right half-planes).

The choice of common parameters also ensures Gamma regularity at both ends of the exponent
recurrence, including the exceptional integral cases discussed by Carlson. The empty index
type is handled separately. There are no admitted proofs in this file.
-/

open Complex ProbabilityTheory
open scoped Classical
@[expose] public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Clearing a nonzero scalar denominator in a submodule. -/
private def denominatorClosure {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] (P : Submodule A M) : Submodule A M where
  carrier := {v | ∃ d : A, d ≠ 0 ∧ d • v ∈ P}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro v w ⟨d, hd, hv⟩ ⟨e, he, hw⟩
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    have h := P.add_mem (P.smul_mem e hv) (P.smul_mem d hw)
    rw [smul_comm e d v] at h
    simpa only [smul_add, mul_smul] using h
  smul_mem' := by
    rintro c v ⟨d, hd, hv⟩
    refine ⟨d, hd, ?_⟩
    rw [smul_comm d c v]
    exact P.smul_mem c hv

private theorem mem_denominatorClosure {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] (P : Submodule A M) {v : M} (hv : v ∈ P) :
    v ∈ denominatorClosure P :=
  ⟨1, one_ne_zero, by simpa using hv⟩

private theorem denominatorClosure_cancel {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] (P : Submodule A M) {c : A} {v : M}
    (hc : c ≠ 0) (hv : c • v ∈ denominatorClosure P) :
    v ∈ denominatorClosure P := by
  obtain ⟨d, hd, hv⟩ := hv
  exact ⟨d * c, mul_ne_zero hd hc, by simpa [mul_smul] using hv⟩

/-- Clearing denominators reduces dependence in a saturated finite span to dependence
of coefficient vectors over the original integral domain. -/
private theorem exists_relation_of_mem_denominatorClosure
    {A M J K : Type*} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M]
    [Fintype J] [Fintype K] (v : K → M) (w : J → M)
    (hcard : Fintype.card K < Fintype.card J)
    (hw : ∀ j, w j ∈ denominatorClosure (Submodule.span A (Set.range v))) :
    ∃ a : J → A, (∃ j, a j ≠ 0) ∧ ∑ j, a j • w j = 0 := by
  choose d hd hmem using hw
  choose p hp using fun j => (Submodule.mem_span_range_iff_exists_fun A).mp (hmem j)
  have hdep : ¬ LinearIndependent A p := by
    intro h
    have hc := h.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at hc
    omega
  obtain ⟨a, ha, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨fun j => a j * d j, ⟨j, mul_ne_zero hj (hd j)⟩, ?_⟩
  simp_rw [mul_smul, ← hp, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hcoeff (k : K) : ∑ j, a j * p j k = 0 := by
    simpa using congrFun ha k
  simp_rw [← Finset.sum_smul, hcoeff, zero_smul, Finset.sum_const_zero]

/-- Integral shifts specifying a Carlson R-function associated to a fixed exponent and
Dirichlet parameter vector. -/
structure CarlsonRAssociatedShift (ι : Type*) where
  /-- Integral shift of the homogeneity parameter. -/
  exponent : ℤ
  /-- Integral shifts of the Dirichlet parameters. -/
  parameter : ι → ℤ

/-- Apply an associated shift to an R-function's exponent. -/
def CarlsonRAssociatedShift.exponentValue
    (s : CarlsonRAssociatedShift ι) (t : ℂ) : ℂ :=
  t + s.exponent

/-- Apply an associated shift to an R-function's Dirichlet parameters. -/
def CarlsonRAssociatedShift.parameterValue
    (s : CarlsonRAssociatedShift ι) (b : ι → ℂ) : ι → ℂ :=
  fun i => b i + s.parameter i

/-- A rational function in the Carlson variables, represented by a numerator and a nonzero
denominator polynomial. -/
structure CarlsonRRationalCoefficient (ι : Type*) where
  /-- Numerator polynomial. -/
  numerator : MvPolynomial ι ℂ
  /-- Denominator polynomial. -/
  denominator : MvPolynomial ι ℂ
  /-- The denominator is not the zero polynomial. -/
  denominator_ne_zero : denominator ≠ 0

/-- Evaluate a rational Carlson coefficient away from the zero set of its denominator. -/
def CarlsonRRationalCoefficient.eval
    (q : CarlsonRRationalCoefficient ι) (z : ι → ℂ) : ℂ :=
  q.numerator.eval z / q.denominator.eval z

/-- Carlson's set `U`: complex numbers that are not nonpositive integers, equivalently the
finite points at which the Gamma function has no pole. -/
def IsCarlsonGammaRegular (w : ℂ) : Prop :=
  ∀ n : ℕ, w ≠ -(n : ℂ)

/-- Positive integral shifts preserve Gamma regularity. -/
theorem IsCarlsonGammaRegular.add_nat {w : ℂ} (hw : IsCarlsonGammaRegular w) (m : ℕ) :
    IsCarlsonGammaRegular (w + m) := by
  intro n h
  apply hw (n + m)
  push_cast
  linear_combination h

/-- No ascending Pochhammer factor vanishes at a Gamma-regular argument. -/
theorem IsCarlsonGammaRegular.ascPochhammer_ne_zero {w : ℂ}
    (hw : IsCarlsonGammaRegular w) (n : ℕ) :
    (ascPochhammer ℂ n).eval w ≠ 0 := by
  rw [Ne, ascPochhammer_eval_eq_zero_iff]
  rintro ⟨m, _, hm⟩
  apply hw m
  linear_combination hm

/-- The last polynomial recurrence coefficient can be used to lower the exponent at
every downward step. Unlike the quotient presentation, this statement includes `a = 0`. -/
theorem carlsonAssociatedRecurrencePolynomial_lower_ne_zero [Nonempty ι]
    {t : ℂ} (ht : IsCarlsonGammaRegular (1 - t)) (b z : ι → ℂ)
    (hz : z ∈ carlsonRVariableDomain) (m : ℕ) :
    (carlsonAssociatedRecurrencePolynomial (Fintype.card ι) (-t + m)
      ((∑ i, b i) + t - m) b).eval z ≠ 0 := by
  simp only [carlsonAssociatedRecurrencePolynomial, if_neg Fintype.card_ne_zero,
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
    let D := {z : ι → ℂ // z ∈ carlsonRVariableDomain}
    let A := MvPolynomial ι ℂ
    let : Module A (D → ℂ) := Module.compHom _
      (RingHom.pi (fun z : D => MvPolynomial.eval z.1))
    let F : ℂ → D → ℂ := fun u z => carlsonRIntegral u b z.1
    let P : Submodule A (D → ℂ) :=
      Submodule.span A (Set.range (fun j : Fin (Fintype.card ι) => F (t - (j : ℕ))))
    let Q := denominatorClosure P
    have hbase (j : ℕ) (hj : j < Fintype.card ι) : F (t - j) ∈ Q :=
      mem_denominatorClosure P (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    have hstep (a : ℂ) (i : ℕ) (hi : i ≤ Fintype.card ι)
        (hci : carlsonAssociatedRecurrencePolynomial i a ((∑ j, b j) - a) b ≠ 0)
        (hrest : ∀ j ∈ Finset.range (Fintype.card ι + 1), j ≠ i → F (-a - j) ∈ Q) :
        F (-a - i) ∈ Q := by
      let C := fun j => carlsonAssociatedRecurrencePolynomial j a ((∑ l, b l) - a) b
      have hsum : ∑ j ∈ Finset.range (Fintype.card ι + 1), C j • F (-a - j) = 0 := by
        ext z
        simp only [Finset.sum_apply, Pi.zero_apply]
        exact sum_carlsonAssociatedRecurrencePolynomial_mul_rIntegral a hb z.2
      have hmem : ∑ j ∈ (Finset.range (Fintype.card ι + 1)).erase i,
          C j • F (-a - j) ∈ Q := by
        apply Q.sum_mem
        intro j hj
        exact Q.smul_mem _ (hrest j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1)
      have heq := Finset.sum_erase_add (Finset.range (Fintype.card ι + 1))
        (fun j => C j • F (-a - j)) (Finset.mem_range.mpr (by omega : i < Fintype.card ι + 1))
      rw [hsum] at heq
      apply denominatorClosure_cancel P hci
      exact (eq_neg_of_add_eq_zero_right heq) ▸ Q.neg_mem hmem
    have hdown (m : ℕ) : F (t - m) ∈ Q := by
      induction m using Nat.strong_induction_on with
      | h m ih =>
        by_cases hm : m < Fintype.card ι
        · exact hbase m hm
        have he : t - (m : ℂ) = -(-t + (m - Fintype.card ι : ℕ)) - Fintype.card ι := by
          rw [Nat.cast_sub (by omega : Fintype.card ι ≤ m)]
          ring
        rw [he]
        apply hstep _ _ le_rfl
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
    have hup (m : ℕ) : F (t + m) ∈ Q := by
      induction m using Nat.strong_induction_on with
      | h m ih =>
        cases m with
        | zero => simpa using hdown 0
        | succ m =>
          have he : t + (m + 1 : ℕ) = -(-(t + m + 1)) - (0 : ℕ) := by push_cast; ring
          rw [he]
          apply hstep _ _ (Nat.zero_le _)
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
              exact hdown _
    have hn : F (t + n) ∈ Q := by
      cases n with
      | ofNat m => exact hup m
      | negSucc m => simpa [Int.cast_negSucc, sub_eq_add_neg] using hdown (m + 1)
    obtain ⟨d, hd, hspan⟩ := hn
    obtain ⟨p, hp⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hspan
    refine ⟨d, hd, p, ?_⟩
    intro z hz
    have heq := congrFun hp (⟨z, hz⟩ : D)
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

private abbrev CarlsonVariableFunctions (ι : Type*) [Fintype ι] :=
  {z : ι → ℂ // z ∈ carlsonRVariableDomain} → ℂ

-- Polynomial scalars act by evaluation on the variable domain.
local instance : Module (MvPolynomial ι ℂ)
    ({z : ι → ℂ // z ∈ carlsonRVariableDomain} → ℂ) :=
  Module.compHom _ (RingHom.pi
    (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} => MvPolynomial.eval z.1))

private theorem polynomial_smul_apply (p : MvPolynomial ι ℂ)
    (f : CarlsonVariableFunctions ι) (z : {z : ι → ℂ // z ∈ carlsonRVariableDomain}) :
    (p • f) z = p.eval z.1 * f z := rfl

/-- The parameter-raising identity with Gamma normalization cleared. -/
private theorem sum_mul_carlsonRIntegral_eq_update_add_one
    (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    (∑ j, b j) * carlsonRIntegral t b z =
      ((∑ j, b j) + t) * carlsonRIntegral t (addDirichletUnit b i) z -
        t * z i * carlsonRIntegral (t - 1) (addDirichletUnit b i) z := by
  let : Nonempty ι := ⟨i⟩
  have hc := ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hb)
  simp only [carlsonRIntegral, sum_addDirichletUnit, Gamma_add_one _ hc]
  rw [regCarlsonRIntegral_eq_update_add_one t hb hz i]
  ring

/-- Repeatedly raising individual parameters puts the original function in the same
denominator-closed span as all exponent shifts at the raised parameter vector. -/
private theorem carlsonRIntegral_mem_of_nat_shift
    (P : Submodule (MvPolynomial ι ℂ) (CarlsonVariableFunctions ι))
    (n : ι → ℕ) (b : ι → ℂ) (hb : b ∈ mvBetaConvergent) (t : ℂ)
    (hupper : ∀ m : ℤ, (fun z => carlsonRIntegral (t + m)
      (fun i => b i + n i) z.1) ∈ denominatorClosure P) :
    (fun z => carlsonRIntegral t b z.1) ∈ denominatorClosure P := by
  induction n using (measure (fun n : ι → ℕ => ∑ i, n i)).wf.induction generalizing b t with
  | h n ih =>
    by_cases hn : n = 0
    · simpa [hn] using hupper 0
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      simpa only [funext_iff, Pi.zero_apply, not_forall] using hn
    let n' := Function.update n i (n i - 1)
    have hlt : (∑ j, n' j) < ∑ j, n j := by
      apply Finset.sum_lt_sum
      · intro j _
        by_cases hji : j = i <;> simp [n', hji]
      · exact ⟨i, Finset.mem_univ _, by simp [n']; omega⟩
    have hB : (fun j => addDirichletUnit b i j + (n' j : ℂ)) =
        (fun j => b j + (n j : ℂ)) := by
      ext j
      by_cases hji : j = i
      · subst j
        simp only [addDirichletUnit, n', Function.update_self]
        rw [Nat.cast_sub (by omega : 1 ≤ n i)]
        push_cast
        ring
      · simp [addDirichletUnit, n', hji]
    have hb' := addDirichletUnit_mem_mvBetaConvergent hb i
    have h₀ := ih n' hlt (addDirichletUnit b i) hb' t
      (fun m => by simpa only [hB] using hupper m)
    have h₁ := ih n' hlt (addDirichletUnit b i) hb' (t - 1) (fun m => by
      rw [hB, show t - 1 + (m : ℂ) = t + (m - 1 : ℤ) by push_cast; ring]
      exact hupper (m - 1))
    let : Nonempty ι := ⟨i⟩
    have hc := ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hb)
    apply denominatorClosure_cancel P (c := MvPolynomial.C (∑ j, b j))
      (by simpa only [ne_eq, MvPolynomial.C_eq_zero] using hc)
    have heq : MvPolynomial.C (σ := ι) (∑ j, b j) •
        (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} => carlsonRIntegral t b z.1) =
        MvPolynomial.C (σ := ι) ((∑ j, b j) + t) •
          (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} =>
            carlsonRIntegral t (addDirichletUnit b i) z.1) -
        (MvPolynomial.C t * MvPolynomial.X i) •
          (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} =>
            carlsonRIntegral (t - 1) (addDirichletUnit b i) z.1) := by
      ext z
      simp only [Pi.sub_apply, polynomial_smul_apply, map_mul,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
      exact sum_mul_carlsonRIntegral_eq_update_add_one t hb z.2 i
    rw [heq]
    exact (denominatorClosure P).sub_mem
      ((denominatorClosure P).smul_mem _ h₀) ((denominatorClosure P).smul_mem _ h₁)

private theorem isCarlsonGammaRegular_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    IsCarlsonGammaRegular w := by
  intro n hn
  have he := congrArg Complex.re hn
  simp only [neg_re, natCast_re] at he
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Choose common raised parameters and a shifted exponent with both recurrence endpoints
Gamma-regular. Positive real parts avoid all exceptional integral cases at once. -/
private theorem exists_common_carlsonAssociated_parameters [Nonempty ι]
    (t : ℂ) (b : ι → ℂ)
    (s : Fin (Fintype.card ι + 1) → CarlsonRAssociatedShift ι) :
    ∃ N : ℕ, ∃ B : ι → ℂ, B ∈ mvBetaConvergent ∧
      IsCarlsonGammaRegular (1 - (t - N)) ∧
      IsCarlsonGammaRegular ((∑ i, B i) + (t - N) - Fintype.card ι + 2) ∧
      ∀ j, ∃ n : ι → ℕ, B = fun i => (s j).parameterValue b i + n i := by
  obtain ⟨N, hN⟩ := exists_nat_gt t.re
  obtain ⟨L, hL⟩ := exists_nat_gt ((N : ℝ) + Fintype.card ι - t.re)
  choose n hn using fun i => exists_nat_gt (-(b i).re)
  let k : ι → ℕ := fun i => Finset.univ.sup (fun j => ((s j).parameter i).toNat) + n i
  have hk (j) (i) : (s j).parameter i ≤ (k i : ℤ) := by
    have h := Finset.le_sup (f := fun j => ((s j).parameter i).toNat) (Finset.mem_univ j)
    dsimp [k]
    omega
  let c : ι → ℂ := fun i => b i + k i
  have hc : c ∈ mvBetaConvergent := by
    intro i
    have hi := hn i
    have hki : (n i : ℝ) ≤ (k i : ℝ) := by
      exact_mod_cast (Nat.le_add_left (n i) (Finset.univ.sup (fun j => ((s j).parameter i).toNat)))
    change 0 < (b i + (k i : ℂ)).re
    simp only [add_re, natCast_re]
    linarith
  let B : ι → ℂ := fun i => c i + L
  have hB : B ∈ mvBetaConvergent := by
    intro i
    change 0 < (c i + (L : ℂ)).re
    simp only [add_re, natCast_re]
    exact add_pos_of_pos_of_nonneg (hc i) (Nat.cast_nonneg L)
  refine ⟨N, B, hB, isCarlsonGammaRegular_of_re_pos ?_,
    isCarlsonGammaRegular_of_re_pos ?_, ?_⟩
  · simp only [sub_re, one_re, natCast_re]
    linarith
  · have hcpos := sum_re_pos_of_mem_mvBetaConvergent hc
    have hkpos : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
    have hsum : (∑ i, B i).re = (∑ i, c i).re + Fintype.card ι * L := by
      simp [B, Finset.sum_add_distrib]
    simp only [add_re, sub_re, natCast_re, re_ofNat, hsum]
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  · intro j
    refine ⟨fun i => ((k i : ℤ) + L - (s j).parameter i).toNat, ?_⟩
    ext i
    have hnonneg : 0 ≤ (k i : ℤ) + L - (s j).parameter i := by
      have := hk j i
      omega
    have he : (((((k i : ℤ) + L - (s j).parameter i).toNat : ℕ) : ℤ) : ℂ) =
        ((k i : ℤ) + L - (s j).parameter i : ℤ) :=
      congrArg (Int.cast : ℤ → ℂ) (Int.toNat_of_nonneg hnonneg)
    simp only [Int.cast_natCast, Int.cast_sub, Int.cast_add] at he
    dsimp [B, c, CarlsonRAssociatedShift.parameterValue]
    rw [he]
    ring

/-- Carlson's existence theorem 8.4-3: any `card ι + 1` associated R-functions satisfy a
nontrivial homogeneous relation with polynomial coefficients. -/
theorem exists_polynomial_relation_associatedR
    (t : ℂ) (b : ι → ℂ)
    (s : Fin (Fintype.card ι + 1) → CarlsonRAssociatedShift ι)
    (hconv : ∀ j, (s j).parameterValue b ∈ mvBetaConvergent) :
    ∃ A : Fin (Fintype.card ι + 1) → MvPolynomial ι ℂ,
      (∃ j, A j ≠ 0) ∧
      ∀ z ∈ carlsonRVariableDomain,
        ∑ j, (A j).eval z *
          carlsonRIntegral ((s j).exponentValue t) ((s j).parameterValue b) z = 0 := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let _ := hι
    refine ⟨fun _ => 1, ⟨0, one_ne_zero⟩, ?_⟩
    simp [carlsonRIntegral]
  | inr hι =>
    let _ := hι
    obtain ⟨N, B, hB, hT, hBT, hshift⟩ :=
      exists_common_carlsonAssociated_parameters t b s
    let v : Fin (Fintype.card ι) → CarlsonVariableFunctions ι :=
      fun j z => carlsonRIntegral ((t - N) - (j : ℕ)) B z.1
    let P := Submodule.span (MvPolynomial ι ℂ) (Set.range v)
    have hfixed (m : ℤ) : (fun z => carlsonRIntegral ((t - N) + m) B z.1) ∈
        denominatorClosure P := by
      obtain ⟨d, hd, p, hp⟩ :=
        exists_polynomial_carlsonAssociated_exponent_reduction (t - N) B m hB hT hBT
      refine ⟨d, hd, ?_⟩
      have heq : d • (fun z => carlsonRIntegral ((t - N) + m) B z.1) =
          ∑ j, p j • v j := by
        ext z
        simp only [Finset.sum_apply]
        exact hp z.1 z.2
      rw [heq]
      exact P.sum_mem fun j _ => P.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
    let w : Fin (Fintype.card ι + 1) → CarlsonVariableFunctions ι :=
      fun j z => carlsonRIntegral ((s j).exponentValue t) ((s j).parameterValue b) z.1
    have hw (j) : w j ∈ denominatorClosure P := by
      obtain ⟨n, hn⟩ := hshift j
      apply carlsonRIntegral_mem_of_nat_shift P n _ (hconv j)
      intro m
      rw [← hn, show (s j).exponentValue t + (m : ℂ) =
        (t - N) + ((N : ℤ) + (s j).exponent + m : ℤ) by
          dsimp [CarlsonRAssociatedShift.exponentValue]; push_cast; ring]
      exact hfixed _
    obtain ⟨a, ha, hrel⟩ := exists_relation_of_mem_denominatorClosure v w (by simp) hw
    refine ⟨a, ha, ?_⟩
    intro z hz
    have heq := congrFun hrel ⟨z, hz⟩
    simp only [Finset.sum_apply, Pi.zero_apply] at heq
    exact heq

/-- In the regularized normalization, raising parameters preserves any polynomial
submodule containing the raised functions. No scalar denominator is cancelled. -/
private theorem regCarlsonRContinued_mem_of_nat_shift
    (P : Submodule (MvPolynomial ι ℂ) (CarlsonVariableFunctions ι))
    (n : ι → ℕ) (b : ι → ℂ) (t : ℂ)
    (hupper : ∀ m : ℤ, (fun z => regCarlsonRContinued (t + m) z.1 z.2
      (fun i => b i + n i)) ∈ P) :
    (fun z => regCarlsonRContinued t z.1 z.2 b) ∈ P := by
  induction n using (measure (fun n : ι → ℕ => ∑ i, n i)).wf.induction generalizing b t with
  | h n ih =>
    by_cases hn : n = 0
    · simpa [hn] using hupper 0
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      simpa only [funext_iff, Pi.zero_apply, not_forall] using hn
    let n' := Function.update n i (n i - 1)
    have hlt : (∑ j, n' j) < ∑ j, n j := by
      apply Finset.sum_lt_sum
      · intro j _
        by_cases hji : j = i <;> simp [n', hji]
      · exact ⟨i, Finset.mem_univ _, by simp [n']; omega⟩
    have hB : (fun j => addDirichletUnit b i j + (n' j : ℂ)) =
        (fun j => b j + (n j : ℂ)) := by
      ext j
      by_cases hji : j = i
      · subst j
        simp only [addDirichletUnit, n', Function.update_self]
        rw [Nat.cast_sub (by omega : 1 ≤ n i)]
        push_cast
        ring
      · simp [addDirichletUnit, n', hji]
    have h₀ := ih n' hlt (addDirichletUnit b i) t
      (fun m => by simpa only [hB] using hupper m)
    have h₁ := ih n' hlt (addDirichletUnit b i) (t - 1) (fun m => by
      rw [hB, show t - 1 + (m : ℂ) = t + (m - 1 : ℤ) by push_cast; ring]
      exact hupper (m - 1))
    have heq : (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} =>
        regCarlsonRContinued t z.1 z.2 b) =
        MvPolynomial.C (σ := ι) ((∑ j, b j) + t) •
          (fun z => regCarlsonRContinued t z.1 z.2 (addDirichletUnit b i)) -
        (MvPolynomial.C t * MvPolynomial.X i) •
          (fun z => regCarlsonRContinued (t - 1) z.1 z.2 (addDirichletUnit b i)) := by
      ext z
      simp only [Pi.sub_apply, polynomial_smul_apply, map_mul,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
      exact regCarlsonRContinued_eq_addDirichletUnit t b z.2 i
    rw [heq]
    exact P.sub_mem (P.smul_mem _ h₀) (P.smul_mem _ h₁)

/-- Carlson's Theorem 8.4-3 on the entire Dirichlet-parameter space. The relation
is nontrivial as a polynomial identity, not merely a pointwise scalar dependence.
Gamma regularization includes all exceptional total parameters. -/
theorem exists_polynomial_relation_associatedRContinued
    (t : ℂ) (b : ι → ℂ)
    (s : Fin (Fintype.card ι + 1) → CarlsonRAssociatedShift ι) :
    ∃ A : Fin (Fintype.card ι + 1) → MvPolynomial ι ℂ,
      (∃ j, A j ≠ 0) ∧
      ∀ (z : ι → ℂ) (hz : z ∈ carlsonRVariableDomain),
        ∑ j, (A j).eval z *
          regCarlsonRContinued ((s j).exponentValue t) z hz ((s j).parameterValue b) = 0 := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have hzero (u : ℂ) (z c : ι → ℂ) (hz : z ∈ carlsonRVariableDomain) :
        regCarlsonRContinued u z hz c = 0 := by
      rw [regCarlsonRContinued_eq_integral u hz (by intro i; exact isEmptyElim i)]
      simp [regCarlsonRIntegral, regCarlsonDirichletAverage, regDirichletIntegral]
    exact ⟨fun _ => 1, ⟨0, one_ne_zero⟩, fun z hz => by simp [hzero]⟩
  | inr hι =>
    obtain ⟨N, B, hB, hT, hBT, hshift⟩ := exists_common_carlsonAssociated_parameters t b s
    let v : Fin (Fintype.card ι) → CarlsonVariableFunctions ι :=
      fun j z => carlsonRIntegral ((t - N) - (j : ℕ)) B z.1
    let P := Submodule.span (MvPolynomial ι ℂ) (Set.range v)
    have hfixed (m : ℤ) : (fun z => carlsonRIntegral ((t - N) + m) B z.1) ∈
        denominatorClosure P := by
      obtain ⟨d, hd, p, hp⟩ :=
        exists_polynomial_carlsonAssociated_exponent_reduction (t - N) B m hB hT hBT
      refine ⟨d, hd, ?_⟩
      have heq : d • (fun z => carlsonRIntegral ((t - N) + m) B z.1) =
          ∑ j, p j • v j := by
        ext z
        simp only [Finset.sum_apply]
        exact hp z.1 z.2
      rw [heq]
      exact P.sum_mem fun j _ => P.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
    have hfixedReg (m : ℤ) :
        (fun z => regCarlsonRContinued ((t - N) + m) z.1 z.2 B) ∈ denominatorClosure P := by
      have hGamma := Gamma_ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hB)
      have heq : (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} =>
          regCarlsonRContinued ((t - N) + m) z.1 z.2 B) =
          MvPolynomial.C (σ := ι) (Gamma (∑ i, B i))⁻¹ •
            (fun z => carlsonRIntegral ((t - N) + m) B z.1) := by
        ext z
        simp only [polynomial_smul_apply, MvPolynomial.eval_C, carlsonRIntegral,
          regCarlsonRContinued_eq_integral _ z.2 hB]
        rw [← mul_assoc, inv_mul_cancel₀ hGamma, one_mul]
      rw [heq]
      exact (denominatorClosure P).smul_mem _ (hfixed m)
    let w : Fin (Fintype.card ι + 1) → CarlsonVariableFunctions ι :=
      fun j z => regCarlsonRContinued ((s j).exponentValue t) z.1 z.2 ((s j).parameterValue b)
    have hw (j) : w j ∈ denominatorClosure P := by
      obtain ⟨n, hn⟩ := hshift j
      apply regCarlsonRContinued_mem_of_nat_shift (denominatorClosure P) n _ _
      intro m
      rw [← hn, show (s j).exponentValue t + (m : ℂ) =
        (t - N) + ((N : ℤ) + (s j).exponent + m : ℤ) by
          dsimp [CarlsonRAssociatedShift.exponentValue]; push_cast; ring]
      exact hfixedReg _
    obtain ⟨a, ha, hrel⟩ := exists_relation_of_mem_denominatorClosure v w (by simp) hw
    refine ⟨a, ha, ?_⟩
    intro z hz
    have heq := congrFun hrel ⟨z, hz⟩
    simp only [Finset.sum_apply, Pi.zero_apply] at heq
    exact heq

end DirichletTransform
end CarlsonR
