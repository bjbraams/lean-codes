/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import Carlson.R.RayKernel
public import Carlson.R.Exponent
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Fixed-parameter recurrence for associated Carlson R-functions

This file contains the coefficient polynomials and recurrence of [Carl77, Relation 8.4-1].
The native-strip proof follows Carlson's pp. 245–246: the single-integral representation
from Exercise 6.8-8, integration by parts with justified convergence and endpoint limits,
the elementary-symmetric expansion, and beta/Gamma normalization. Analytic continuation
then removes the strip restriction. There are no admitted proofs in this file.
-/

open Complex ProbabilityTheory
open scoped Classical Topology
@[expose] public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The `n`th elementary symmetric polynomial evaluated at the Carlson variables. -/
def carlsonElementarySymmetric (n : ℕ) (z : ι → ℂ) : ℂ :=
  (MvPolynomial.esymm ι ℂ n).eval z

/-- The finite generating polynomial for the elementary symmetric coefficients. -/
theorem carlsonElementarySymmetric_generating_polynomial (w : ℂ) :
    (∏ i : ι, (1 + MvPolynomial.C w * MvPolynomial.X i)) =
      ∑ n ∈ Finset.range (Fintype.card ι + 1),
        MvPolynomial.C (w ^ n) * MvPolynomial.esymm ι ℂ n := by
  rw [Finset.prod_one_add, Finset.sum_powerset]
  simp only [Finset.card_univ]
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.esymm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hs).2, map_pow]

/-- Euler's identity for an elementary symmetric polynomial. -/
theorem carlsonElementarySymmetric_euler (n : ℕ) (z : ι → ℂ) :
    ∑ i, z i * (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z =
      n * carlsonElementarySymmetric n z := by
  have hhom : (MvPolynomial.esymm ι ℂ n).IsHomogeneous n := by
    unfold MvPolynomial.esymm
    apply MvPolynomial.IsHomogeneous.sum
    intro s hs
    have H := MvPolynomial.IsHomogeneous.prod s (fun i => MvPolynomial.X i) (fun _ => 1)
      (fun i _ => MvPolynomial.isHomogeneous_X ℂ i)
    simpa [(Finset.mem_powersetCard.mp hs).2] using H
  have H := congrArg (MvPolynomial.eval z) hhom.sum_X_mul_pderiv
  simpa [carlsonElementarySymmetric, nsmul_eq_mul] using H

/-- Differentiating the generating polynomial with respect to one Carlson variable. -/
theorem carlsonElementarySymmetric_generating_pderiv (w : ℂ) (z : ι → ℂ) (i : ι) :
    w * (∏ j ∈ Finset.univ.erase i, (1 + w * z j)) =
      ∑ n ∈ Finset.range (Fintype.card ι + 1),
        w ^ n * (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z := by
  have hz (s : Finset ι) (hi : i ∉ s) :
      MvPolynomial.pderiv i (∏ j ∈ s, (1 + MvPolynomial.C w * MvPolynomial.X j)) = 0 := by
    induction s using Finset.induction with
    | empty => simp
    | @insert j s hj ih =>
      simp only [Finset.mem_insert, not_or] at hi
      simp [hj, Derivation.leibniz, ih hi.2, hi.1, smul_eq_mul]
  have H := congrArg (MvPolynomial.pderiv i)
    (carlsonElementarySymmetric_generating_polynomial (ι := ι) w)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Derivation.leibniz] at H
  simp only [hz _ (Finset.notMem_erase _ _), smul_zero, zero_add] at H
  have H' := congrArg (MvPolynomial.eval z) H
  simpa [Derivation.leibniz, smul_eq_mul, mul_comm] using H'

/-- The polynomial factor in the differentiated ray kernel, expanded as in (8.4-6). -/
theorem carlsonAssociatedRecurrenceKernel_polynomial (a w : ℂ) (b z : ι → ℂ) :
    a * (∏ i, (1 + w * z i)) + w *
        ∑ i, (1 - b i) * z i * ∏ j ∈ Finset.univ.erase i, (1 + w * z j) =
      ∑ n ∈ Finset.range (Fintype.card ι + 1), w ^ n *
        ((a + n) * carlsonElementarySymmetric n z -
          ∑ i, b i * z i * (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z) := by
  have hg : (∏ i, (1 + w * z i)) =
      ∑ n ∈ Finset.range (Fintype.card ι + 1), w ^ n * carlsonElementarySymmetric n z := by
    simpa [carlsonElementarySymmetric] using
      congrArg (MvPolynomial.eval z) (carlsonElementarySymmetric_generating_polynomial (ι := ι) w)
  have hd (i : ι) : w * ((1 - b i) * z i *
      ∏ j ∈ Finset.univ.erase i, (1 + w * z j)) =
      ∑ n ∈ Finset.range (Fintype.card ι + 1), w ^ n * ((1 - b i) * z i *
        (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z) := by
    rw [show w * ((1 - b i) * z i * ∏ j ∈ Finset.univ.erase i, (1 + w * z j)) =
      ((1 - b i) * z i) * (w * ∏ j ∈ Finset.univ.erase i, (1 + w * z j)) by ring,
      carlsonElementarySymmetric_generating_pderiv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hg, Finset.mul_sum, Finset.mul_sum]
  simp_rw [hd]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.mul_sum]
  have he : (∑ i, (1 - b i) * z i *
      (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z) =
      n * carlsonElementarySymmetric n z -
        ∑ i, b i * z i * (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z := by
    simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
    rw [carlsonElementarySymmetric_euler]
  rw [he]
  ring

/-- Carlson's coefficient `Aₙ` from Relation 8.4-1 in its displayed quotient form.
`eval_carlsonAssociatedRecurrencePolynomial` identifies its polynomial form away from
the two displayed denominators. -/
def carlsonAssociatedRecurrenceCoeff
    (n : ℕ) (a a' : ℂ) (b z : ι → ℂ) : ℂ :=
  (ascPochhammer ℂ n).eval a *
    (ascPochhammer ℂ (Fintype.card ι - n)).eval (a' - Fintype.card ι) /
      (a * (a' - Fintype.card ι)) *
    ((a + n) * carlsonElementarySymmetric n z -
      ∑ i, b i * z i * (MvPolynomial.pderiv i
        (MvPolynomial.esymm ι ℂ n)).eval z)

/-- The top elementary symmetric polynomial is the product of all variables. -/
theorem carlsonElementarySymmetric_card (z : ι → ℂ) :
    carlsonElementarySymmetric (Fintype.card ι) z = ∏ i, z i := by
  simp [carlsonElementarySymmetric, MvPolynomial.esymm,
    ← Finset.card_univ, Finset.powersetCard_self]

private lemma X_mul_pderiv_esymm_card (i : ι) :
    MvPolynomial.X i * MvPolynomial.pderiv i
      (MvPolynomial.esymm ι ℂ (Fintype.card ι)) =
        MvPolynomial.esymm ι ℂ (Fintype.card ι) := by
  have he : MvPolynomial.esymm ι ℂ (Fintype.card ι) =
      MvPolynomial.monomial (∑ j : ι, Finsupp.single j 1) (1 : ℂ) := by
    simp [MvPolynomial.esymm, ← Finset.card_univ, Finset.powersetCard_self,
      MvPolynomial.monomial_sum_one, MvPolynomial.X]
  rw [he, MvPolynomial.X_mul_pderiv_monomial]
  simp

/-- Carlson's last coefficient has a removable singularity at `a' = card ι`. -/
theorem carlsonAssociatedRecurrenceCoeff_card [Nonempty ι]
    {a a' : ℂ} {b z : ι → ℂ}
    (hsum : a + a' = ∑ i, b i) (ha : a ≠ 0)
    (ha' : a' ≠ Fintype.card ι) :
    carlsonAssociatedRecurrenceCoeff (Fintype.card ι) a a' b z =
      -(ascPochhammer ℂ (Fintype.card ι - 1)).eval (a + 1) * ∏ i, z i := by
  have hcard : Fintype.card ι = (Fintype.card ι - 1) + 1 :=
    (Nat.sub_add_cancel Fintype.card_pos).symm
  have hp : (ascPochhammer ℂ (Fintype.card ι)).eval a =
      a * (ascPochhammer ℂ (Fintype.card ι - 1)).eval (a + 1) := by
    conv_lhs => rw [hcard, ascPochhammer_succ_left]
    simp
  have hd (i : ι) : z i * (MvPolynomial.pderiv i
      (MvPolynomial.esymm ι ℂ (Fintype.card ι))).eval z = ∏ j, z j := by
    have h := congrArg (MvPolynomial.eval z) (X_mul_pderiv_esymm_card (ι := ι) i)
    simp only [map_mul, MvPolynomial.eval_X] at h
    exact h.trans (carlsonElementarySymmetric_card z)
  have hs : (∑ i, b i * z i * (MvPolynomial.pderiv i
      (MvPolynomial.esymm ι ℂ (Fintype.card ι))).eval z) =
      (a + a') * ∏ j, z j := by
    simp_rw [mul_assoc, hd]
    rw [← Finset.sum_mul, hsum]
  simp only [carlsonAssociatedRecurrenceCoeff, Nat.sub_self, ascPochhammer_zero,
    Polynomial.eval_one, mul_one, hp, carlsonElementarySymmetric_card, hs]
  field_simp
  ring

/-- Carlson's first coefficient has a removable singularity at `a = 0`. -/
theorem carlsonAssociatedRecurrenceCoeff_zero [Nonempty ι]
    {a a' : ℂ} (b z : ι → ℂ) (ha : a ≠ 0) (ha' : a' ≠ Fintype.card ι) :
    carlsonAssociatedRecurrenceCoeff 0 a a' b z =
      (ascPochhammer ℂ (Fintype.card ι - 1)).eval (a' - Fintype.card ι + 1) := by
  have hcard : Fintype.card ι = (Fintype.card ι - 1) + 1 :=
    (Nat.sub_add_cancel Fintype.card_pos).symm
  have hp : (ascPochhammer ℂ (Fintype.card ι)).eval (a' - Fintype.card ι) =
      (a' - Fintype.card ι) *
        (ascPochhammer ℂ (Fintype.card ι - 1)).eval (a' - Fintype.card ι + 1) := by
    have h := congrArg (Polynomial.eval (a' - Fintype.card ι))
      (ascPochhammer_succ_left ℂ (Fintype.card ι - 1))
    simpa only [← hcard, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one] using h
  simp only [carlsonAssociatedRecurrenceCoeff, Nat.sub_zero, ascPochhammer_zero,
    Polynomial.eval_one, one_mul, Nat.cast_zero, add_zero, carlsonElementarySymmetric,
    MvPolynomial.esymm_zero, MvPolynomial.pderiv_one, map_zero, mul_zero,
    Finset.sum_const_zero, sub_zero, hp]
  simp only [map_one, mul_one]
  field_simp

/-- The division-free polynomial coefficient in Carlson's recurrence for a nonempty index
type, including its removable-singularity values. The endpoint formulas are used separately because the
corresponding factors cancel against the expression involving the symmetric polynomial. -/
def carlsonAssociatedRecurrencePolynomial
    (n : ℕ) (a a' : ℂ) (b : ι → ℂ) : MvPolynomial ι ℂ :=
  if n = 0 then
    MvPolynomial.C ((ascPochhammer ℂ (Fintype.card ι - 1)).eval
      (a' - Fintype.card ι + 1))
  else if n = Fintype.card ι then
    MvPolynomial.C (-(ascPochhammer ℂ (Fintype.card ι - 1)).eval (a + 1)) *
      MvPolynomial.esymm ι ℂ n
  else
    MvPolynomial.C ((ascPochhammer ℂ (n - 1)).eval (a + 1) *
      (ascPochhammer ℂ (Fintype.card ι - n - 1)).eval
        (a' - Fintype.card ι + 1)) *
      (MvPolynomial.C (a + n) * MvPolynomial.esymm ι ℂ n -
        ∑ i, MvPolynomial.C (b i) * MvPolynomial.X i *
          MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n))

/-- Away from the two displayed denominators, the polynomial coefficients agree with
Carlson's quotient formula. No parameter-dependent denominator remains in the polynomial. -/
theorem eval_carlsonAssociatedRecurrencePolynomial [Nonempty ι]
    {n : ℕ} (hn : n ≤ Fintype.card ι) {a a' : ℂ} {b z : ι → ℂ}
    (hsum : a + a' = ∑ i, b i) (ha : a ≠ 0) (ha' : a' ≠ Fintype.card ι) :
    (carlsonAssociatedRecurrencePolynomial n a a' b).eval z =
      carlsonAssociatedRecurrenceCoeff n a a' b z := by
  by_cases hn0 : n = 0
  · subst n
    simp [carlsonAssociatedRecurrencePolynomial,
      carlsonAssociatedRecurrenceCoeff_zero b z ha ha']
  by_cases hnk : n = Fintype.card ι
  · subst n
    simp [carlsonAssociatedRecurrencePolynomial, Fintype.card_ne_zero,
      carlsonAssociatedRecurrenceCoeff_card hsum ha ha',
      ← carlsonElementarySymmetric_card z, carlsonElementarySymmetric]
  have hp (m : ℕ) (hm : 0 < m) (w : ℂ) :
      (ascPochhammer ℂ m).eval w =
        w * (ascPochhammer ℂ (m - 1)).eval (w + 1) := by
    have h := congrArg (Polynomial.eval w) (ascPochhammer_succ_left ℂ (m - 1))
    simpa only [Nat.sub_add_cancel hm, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one] using h
  simp only [carlsonAssociatedRecurrencePolynomial, if_neg hn0, if_neg hnk,
    map_mul, MvPolynomial.eval_C, map_sub, map_sum, MvPolynomial.eval_X,
    carlsonAssociatedRecurrenceCoeff, carlsonElementarySymmetric,
    hp n (Nat.pos_of_ne_zero hn0), hp (Fintype.card ι - n) (by omega)]
  field_simp

/-- Polynomial recurrence coefficients depend analytically on analytic parameters. -/
theorem analyticAt_carlsonAssociatedRecurrencePolynomial_eval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x : E} {a a' : E → ℂ} {b : E → ι → ℂ}
    (ha : AnalyticAt ℂ a x) (ha' : AnalyticAt ℂ a' x)
    (hb : ∀ i, AnalyticAt ℂ (fun y ↦ b y i) x) (n : ℕ) (z : ι → ℂ) :
    AnalyticAt ℂ (fun y ↦ (carlsonAssociatedRecurrencePolynomial n
      (a y) (a' y) (b y)).eval z) x := by
  have hp (m : ℕ) {f : E → ℂ} (hf : AnalyticAt ℂ f x) :
      AnalyticAt ℂ (fun y ↦ (ascPochhammer ℂ m).eval (f y)) x :=
    ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (ascPochhammer ℂ m))
      (f x) (Set.mem_univ _)).comp_of_eq hf rfl
  simp only [carlsonAssociatedRecurrencePolynomial]
  split_ifs
  · simp only [MvPolynomial.eval_C]
    exact hp _ ((ha'.sub analyticAt_const).add analyticAt_const)
  · simp only [map_mul, MvPolynomial.eval_C]
    exact (hp _ (ha.add analyticAt_const)).neg.mul analyticAt_const
  · simp only [map_mul, map_sub, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X]
    refine ((hp _ (ha.add analyticAt_const)).mul
      (hp _ ((ha'.sub analyticAt_const).add analyticAt_const))).mul ?_
    refine ((ha.add analyticAt_const).mul analyticAt_const).sub ?_
    exact Finset.analyticAt_fun_sum _ (fun i _ ↦
      ((hb i).mul analyticAt_const).mul analyticAt_const)

/-- The division-free, regularized residual of Carlson's fixed-parameter recurrence.
The constraint on the total parameter is built into this definition. -/
def carlsonAssociatedRecurrenceResidual (a : ℂ) (b z : ι → ℂ) : ℂ :=
  ∑ n ∈ Finset.range (Fintype.card ι + 1),
    (carlsonAssociatedRecurrencePolynomial n a ((∑ i, b i) - a) b).eval z *
      regCarlsonRIntegral (-a - n) b z

/-- The division-free recurrence residual is entire in its exponent parameter. -/
theorem analyticOnNhd_carlsonAssociatedRecurrenceResidual_exponent
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (fun a ↦ carlsonAssociatedRecurrenceResidual a b z) Set.univ := by
  intro a _
  unfold carlsonAssociatedRecurrenceResidual
  apply Finset.analyticAt_fun_sum
  intro n _
  have hc := analyticAt_carlsonAssociatedRecurrencePolynomial_eval
    (a := fun w : ℂ ↦ w) (a' := fun w : ℂ ↦ (∑ i, b i) - w)
    (b := fun _ : ℂ ↦ b) (x := a) analyticAt_id
    (analyticAt_const.sub analyticAt_id) (fun _ ↦ analyticAt_const) n z
  have hr : AnalyticAt ℂ (fun w ↦ regCarlsonRIntegral w b z) (-a - n) :=
    analyticOnNhd_regCarlsonRIntegral_exponent hb hz _ (Set.mem_univ _)
  have hs : AnalyticAt ℂ (fun w : ℂ ↦ -w - n) a :=
    analyticAt_id.neg.sub analyticAt_const
  exact hc.mul (hr.comp_of_eq hs rfl)

/-- The same residual is analytic in the Dirichlet parameters on their native domain. -/
theorem analyticOnNhd_carlsonAssociatedRecurrenceResidual_parameters (a : ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (fun b ↦ carlsonAssociatedRecurrenceResidual a b z) mvBetaConvergent := by
  intro b hb
  unfold carlsonAssociatedRecurrenceResidual
  apply Finset.analyticAt_fun_sum
  intro n _
  have hsum : AnalyticAt ℂ (fun c : ι → ℂ ↦ ∑ i, c i) b :=
    Finset.analyticAt_fun_sum _ (fun i _ ↦
      (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b)
  refine (analyticAt_carlsonAssociatedRecurrencePolynomial_eval analyticAt_const
    (hsum.sub analyticAt_const)
    (fun i ↦ (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b) n z).mul ?_
  have hpow : ContinuousOn (fun u ↦ carlsonAffineForm z u ^ (-a - n)) (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    (continuous_carlsonAffineForm z).continuousOn.cpow_const
      (fun _ hu ↦ carlsonAffineForm_mem_slitPlane hz hu)
  exact (isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp
    (regDirichletIntegral_analyticOn hpow)) b hb

/-- A proof of the recurrence in the absolutely convergent single-integral strip suffices
for all native Dirichlet parameters and all exponents. Analytic continuation is performed
first in the exponent, then in the Dirichlet parameters, using division-free coefficients.
This lemma does not assume the recurrence outside the strip. -/
theorem carlsonAssociatedRecurrenceResidual_eq_zero_of_strip [Nonempty ι]
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    (hstrip : ∀ (a : ℂ) (b : ι → ℂ), b ∈ mvBetaConvergent →
      0 < a.re → (Fintype.card ι : ℝ) < ((∑ i, b i) - a).re →
      carlsonAssociatedRecurrenceResidual a b z = 0)
    (a : ℂ) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    carlsonAssociatedRecurrenceResidual a b z = 0 := by
  have hlarge (c : ι → ℂ) (hc : c ∈ mvBetaConvergent)
      (hct : (Fintype.card ι : ℝ) < (∑ i, c i).re) :
      ∀ w, carlsonAssociatedRecurrenceResidual w c z = 0 := by
    let w₀ : ℂ := (((∑ i, c i).re - Fintype.card ι) / 2 : ℝ)
    have hw₀ : 0 < w₀.re := by dsimp [w₀]; linarith
    have hc₀ : (Fintype.card ι : ℝ) < ((∑ i, c i) - w₀).re := by
      simp only [sub_re, w₀, ofReal_re]; linarith
    have hlocal : (fun w ↦ carlsonAssociatedRecurrenceResidual w c z) =ᶠ[nhds w₀]
        (fun _ ↦ 0) := by
      have hpos := (isOpen_lt continuous_const Complex.continuous_re).eventually_mem hw₀
      have hsum := (isOpen_lt continuous_const
        (Complex.continuous_re.comp (continuous_const.sub continuous_id))).eventually_mem hc₀
      filter_upwards [hpos, hsum] with w hw hcw
      exact hstrip w c hc hw hcw
    have heq := (analyticOnNhd_carlsonAssociatedRecurrenceResidual_exponent hc hz).eq_of_eventuallyEq
      analyticOnNhd_const hlocal
    intro w
    exact congrFun heq w
  have hlocal : (fun c ↦ carlsonAssociatedRecurrenceResidual a c z) =ᶠ[nhds (fun _ ↦ (2 : ℂ))]
      (fun _ ↦ 0) := by
    have hev : ∀ᶠ c : ι → ℂ in nhds (fun _ ↦ 2), ∀ i, 1 < (c i).re := by
      apply Filter.eventually_all.mpr
      intro i
      exact (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply i))).eventually_mem
        (by norm_num)
    filter_upwards [hev] with c hc
    apply hlarge c (fun i ↦ lt_trans zero_lt_one (hc i)) _ a
    have hsum := Finset.sum_lt_sum (s := Finset.univ)
      (f := fun _ : ι ↦ (1 : ℝ)) (g := fun i ↦ (c i).re)
      (fun i _ ↦ (hc i).le) (by obtain ⟨i⟩ := ‹Nonempty ι›; exact ⟨i, Finset.mem_univ i, hc i⟩)
    simpa using hsum
  exact (analyticOnNhd_carlsonAssociatedRecurrenceResidual_parameters a hz).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const
    (by simpa using isPreconnected_dirichletConvergenceRegion (ι := ι) 0)
    (z₀ := fun _ ↦ 2) (by intro i; norm_num) hlocal hb

/-- The primitive whose endpoint values give the associated-function recurrence. -/
def carlsonAssociatedRecurrenceKernel (a : ℂ) (b z : ι → ℂ) (w : ℂ) : ℂ :=
  w ^ a * ∏ i, (1 + w * z i) ^ (1 - b i)

/-- The derivative of the ray primitive, with all complex powers factored out.
The remaining factor is a polynomial in `w`; expanding it gives the elementary
symmetric coefficients of Carlson's recurrence. -/
theorem hasDerivAt_carlsonAssociatedRecurrenceKernel
    (a : ℂ) (b z : ι → ℂ) {w : ℂ} (hw : w ∈ slitPlane)
    (hz : ∀ i, 1 + w * z i ∈ slitPlane) :
    HasDerivAt (carlsonAssociatedRecurrenceKernel a b z)
      (w ^ (a - 1) * (∏ i, (1 + w * z i) ^ (-b i)) *
        (a * (∏ i, (1 + w * z i)) + w *
          ∑ i, (1 - b i) * z i * ∏ j ∈ Finset.univ.erase i, (1 + w * z j))) w := by
  let L := fun i => 1 + w * z i
  let G := fun i => L i ^ (-b i)
  have hpow (v c : ℂ) (hv : v ≠ 0) : v ^ c = v * v ^ (c - 1) := by
    calc
      v ^ c = v ^ (1 + (c - 1)) := by congr 1; ring
      _ = v ^ (1 : ℂ) * v ^ (c - 1) := cpow_add _ _ hv
      _ = v * v ^ (c - 1) := by rw [cpow_one]
  have hfactor (i : ι) : L i ^ (1 - b i) = L i * G i := by
    rw [hpow _ _ (slitPlane_ne_zero (hz i))]
    congr 1
    congr 1
    ring
  have hd (i : ι) : HasDerivAt (fun v : ℂ => (1 + v * z i) ^ (1 - b i))
      ((1 - b i) * G i * z i) w := by
    simpa only [G, L, id_eq, one_mul, sub_sub_cancel_left] using
      (((hasDerivAt_id w).mul_const (z i)).const_add 1).cpow_const
        (c := 1 - b i) (hz i)
  have H := ((Complex.hasStrictDerivAt_cpow_const (c := a) hw).hasDerivAt).mul
    (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hd i))
  have hterm (i : ι) :
      (∏ j ∈ Finset.univ.erase i, L j * G j) * ((1 - b i) * G i * z i) =
        (∏ j, G j) * ((1 - b i) * z i * ∏ j ∈ Finset.univ.erase i, L j) := by
    rw [Finset.prod_mul_distrib, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    ring
  convert H using 1
  all_goals try rfl
  simp only [L, G] at hfactor hterm
  simp only [hfactor, smul_eq_mul, G, L]
  simp only [hterm]
  simp only [← Finset.mul_sum, Finset.prod_mul_distrib]
  rw [hpow w a (slitPlane_ne_zero hw)]
  ring

/-- The left endpoint of the ray primitive vanishes whenever the first Mellin
exponent has positive real part. No condition on the other parameters is needed here. -/
theorem tendsto_carlsonAssociatedRecurrenceKernel_zero
    {a : ℂ} (ha : 0 < a.re) (b z : ι → ℂ) :
    Filter.Tendsto (carlsonAssociatedRecurrenceKernel a b z) (nhds 0) (nhds 0) := by
  have hp : ContinuousAt (fun w : ℂ => w ^ a) 0 :=
    (Complex.continuousAt_cpow_zero_of_re_pos ha).comp (f := fun w : ℂ => (w, a))
      (continuousAt_id.prodMk continuousAt_const)
  have hg : ContinuousAt (fun w : ℂ => ∏ i, (1 + w * z i) ^ (1 - b i)) 0 := by
    apply tendsto_finsetProd
    intro i _
    exact (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).cpow
      continuousAt_const (by simp)
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  unfold carlsonAssociatedRecurrenceKernel
  simpa [ha0] using (hp.fun_mul hg).tendsto

/-- On the positive ray, the right-half-plane hypothesis supplies all branch
conditions required by the factored derivative formula. -/
theorem hasDerivAt_carlsonAssociatedRecurrenceKernel_ofReal
    (a : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun r : ℝ => carlsonAssociatedRecurrenceKernel a b z r)
      ((x : ℂ) ^ (a - 1) * (∏ i, (1 + (x : ℂ) * z i) ^ (-b i)) *
        (a * (∏ i, (1 + (x : ℂ) * z i)) + (x : ℂ) *
          ∑ i, (1 - b i) * z i * ∏ j ∈ Finset.univ.erase i, (1 + (x : ℂ) * z j))) x := by
  apply HasDerivAt.comp_ofReal
  apply hasDerivAt_carlsonAssociatedRecurrenceKernel
  · exact carlsonRightHalfPlane_subset_slitPlane hx
  · intro i
    apply carlsonRightHalfPlane_subset_slitPlane
    change 0 < (1 + (x : ℂ) * z i).re
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    have hi : 0 < (z i).re := hz i
    positivity

/-- The recurrence primitive vanishes at infinity under Carlson's upper strip bound.
Unlike the eventual R-function application, this needs no positivity assumption on `b`. -/
theorem tendsto_carlsonAssociatedRecurrenceKernel_atTop
    {a : ℂ} {b z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    (ha' : (Fintype.card ι : ℝ) < ((∑ i, b i) - a).re) :
    Filter.Tendsto (fun x : ℝ => carlsonAssociatedRecurrenceKernel a b z x)
      Filter.atTop (nhds 0) := by
  apply tendsto_cpow_mul_carlsonRayProduct_atTop a (fun i => 1 - b i) hz
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, sub_re, natCast_re] at *
  linarith

/-- Carlson's integration-by-parts calculation in the proof of Relation 8.4-1
(pp. 245–246), with absolute integrability and endpoint limits justified.

This is the factored integral identity before expanding the finite products by elementary
symmetric polynomials and applying the single-integral representation from Section 6.8. -/
theorem integral_carlsonAssociatedRecurrenceKernel_derivative_eq_zero
    {a : ℂ} {b z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    (ha : 0 < a.re)
    (ha' : (Fintype.card ι : ℝ) < ((∑ i, b i) - a).re) :
    ∫ x : ℝ in Set.Ioi 0,
      (x : ℂ) ^ (a - 1) * (∏ i, (1 + (x : ℂ) * z i) ^ (-b i)) *
        (a * (∏ i, (1 + (x : ℂ) * z i)) + (x : ℂ) *
          ∑ i, (1 - b i) * z i * ∏ j ∈ Finset.univ.erase i, (1 + (x : ℂ) * z j)) = 0 := by
  have hstrip : a.re + (∑ i, (1 - b i)).re < 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, sub_re, natCast_re] at *
    linarith
  calc
    _ = ∫ x : ℝ in Set.Ioi 0, carlsonRayDerivative a (fun i => 1 - b i) z x := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (hasDerivAt_carlsonAssociatedRecurrenceKernel_ofReal a b hz hx).unique
        (hasDerivAt_cpow_mul_carlsonRayProduct a (fun i => 1 - b i) hz hx)
    _ = 0 := integral_carlsonRayDerivative_eq_zero (fun i => 1 - b i) hz ha hstrip

private theorem carlsonAssociatedRecurrenceCoeff_eq_Gamma
    {n : ℕ} (hn : n ≤ Fintype.card ι) {a a' : ℂ} (b z : ι → ℂ)
    (ha : 0 < a.re) (ha' : (Fintype.card ι : ℝ) < a'.re) :
    carlsonAssociatedRecurrenceCoeff n a a' b z =
      (Gamma (a + n) * Gamma (a' - n) /
        (Gamma (a + 1) * Gamma (a' - Fintype.card ι + 1))) *
        ((a + n) * carlsonElementarySymmetric n z -
          ∑ i, b i * z i * (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z) := by
  have hd : 0 < (a' - Fintype.card ι).re := by simpa using sub_pos.mpr ha'
  have hreg (w : ℂ) (hw : 0 < w.re) (k : ℕ) : w ≠ -(k : ℂ) := by
    intro h
    have H := congrArg Complex.re h
    simp only [neg_re, natCast_re] at H
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have ha0 : a ≠ 0 := by simpa using hreg a ha 0
  have hd0 : a' - Fintype.card ι ≠ 0 := by simpa using hreg _ hd 0
  have hGa := Gamma_ne_zero_of_re_pos ha
  have hGd := Gamma_ne_zero_of_re_pos hd
  rw [carlsonAssociatedRecurrenceCoeff,
    ← Gamma_add_nat_div_Gamma_eq a (hreg a ha),
    ← Gamma_add_nat_div_Gamma_eq (a' - Fintype.card ι) (hreg _ hd),
    show a' - (Fintype.card ι : ℂ) + (Fintype.card ι - n : ℕ) = a' - n by
      rw [Nat.cast_sub hn]; ring,
    Gamma_add_one a ha0, Gamma_add_one _ hd0]
  field_simp

private theorem carlsonAssociatedRecurrence_term_eq_mellin [Nonempty ι]
    {n : ℕ} (hn : n ≤ Fintype.card ι) {a : ℂ} {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain)
    (ha : 0 < a.re) (ha' : (Fintype.card ι : ℝ) < ((∑ i, b i) - a).re) :
    (carlsonAssociatedRecurrencePolynomial n a ((∑ i, b i) - a) b).eval z *
      regCarlsonRIntegral (-a - n) b z =
      (1 / (Gamma (a + 1) * Gamma ((∑ i, b i) - a - Fintype.card ι + 1))) *
        (((a + n) * carlsonElementarySymmetric n z -
          ∑ i, b i * z i * (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z) *
            mellin (carlsonRayProduct (fun i => -b i) z) (a + n)) := by
  have han : 0 < (a + n).re := by simp only [add_re, natCast_re]; positivity
  have hbn : 0 < ((∑ i, b i) - a - n).re := by
    have hn' : (n : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
    simp only [sub_re, natCast_re] at *
    linarith
  have hsum : (a + n) + ((∑ i, b i) - a - n) = ∑ i, b i := by ring
  have hG : Gamma (∑ i, b i) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    rw [← hsum, add_re]; exact add_pos han hbn)
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hd0 : (∑ i, b i) - a ≠ Fintype.card ι := by
    intro h
    simp [h] at ha'
  rw [eval_carlsonAssociatedRecurrencePolynomial hn (by ring) ha0 hd0,
    carlsonAssociatedRecurrenceCoeff_eq_Gamma hn b z ha ha',
    mellin_carlsonRayProduct_eq_rIntegral han hbn hsum hb hz,
    betaIntegral_eq_Gamma_mul_div _ _ han hbn, hsum, carlsonRIntegral,
    show -(a + (n : ℂ)) = -a - n by ring]
  field_simp

/-- The recurrence residual vanishes in the absolutely convergent single-integral strip.
Combine the ray integration-by-parts identity with the elementary-symmetric expansion
in Carlson's (8.4-5)–(8.4-7), Exercise 6.8-8, and beta/Gamma normalization. -/
theorem carlsonAssociatedRecurrenceResidual_eq_zero_in_strip [Nonempty ι]
    {a : ℂ} {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain)
    (ha : 0 < a.re)
    (ha' : (Fintype.card ι : ℝ) < ((∑ i, b i) - a).re) :
    carlsonAssociatedRecurrenceResidual a b z = 0 := by
  let D : ℕ → ℂ := fun n => (a + n) * carlsonElementarySymmetric n z -
    ∑ i, b i * z i * (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)).eval z
  let f : ℕ → ℝ → ℂ := fun n x => D n *
    ((x : ℂ) ^ (a + n - 1) * carlsonRayProduct (fun i => -b i) z x)
  have hint (n : ℕ) (hn : n ∈ Finset.range (Fintype.card ι + 1)) :
      MeasureTheory.IntegrableOn (f n) (Set.Ioi 0) := by
    apply MeasureTheory.Integrable.const_mul
    apply mellinConvergent_carlsonRayProduct _ hz
    · simp only [add_re, natCast_re]; positivity
    · have hn' : (n : ℝ) ≤ Fintype.card ι := by
        exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
      simp only [Finset.sum_neg_distrib, neg_re, add_re, natCast_re, sub_re] at *
      linarith
  have hpoint (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
      (∑ n ∈ Finset.range (Fintype.card ι + 1), f n x) =
        (x : ℂ) ^ (a - 1) * (∏ i, (1 + (x : ℂ) * z i) ^ (-b i)) *
          (a * (∏ i, (1 + (x : ℂ) * z i)) + (x : ℂ) *
            ∑ i, (1 - b i) * z i * ∏ j ∈ Finset.univ.erase i, (1 + (x : ℂ) * z j)) := by
    rw [carlsonAssociatedRecurrenceKernel_polynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [f, D, carlsonRayProduct]
    rw [show a + (n : ℂ) - 1 = (a - 1) + n by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx)), cpow_natCast]
    ring
  have hzero : (∑ n ∈ Finset.range (Fintype.card ι + 1),
      D n * mellin (carlsonRayProduct (fun i => -b i) z) (a + n)) = 0 := by
    simp_rw [mellin, smul_eq_mul, ← MeasureTheory.integral_const_mul]
    rw [← MeasureTheory.integral_finsetSum _ hint]
    exact (MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpoint).trans
      (integral_carlsonAssociatedRecurrenceKernel_derivative_eq_zero hz ha ha')
  unfold carlsonAssociatedRecurrenceResidual
  simp_rw [Finset.sum_congr rfl (fun n hn =>
    carlsonAssociatedRecurrence_term_eq_mellin (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) hb hz ha ha')]
  rw [← Finset.mul_sum]
  change _ * (∑ n ∈ Finset.range (Fintype.card ι + 1),
    D n * mellin (carlsonRayProduct (fun i => -b i) z) (a + n)) = 0
  rw [hzero, mul_zero]

/-- The division-free residual vanishes for all native Dirichlet parameters and all exponents. -/
theorem carlsonAssociatedRecurrenceResidual_eq_zero [Nonempty ι]
    (a : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    carlsonAssociatedRecurrenceResidual a b z = 0 :=
  carlsonAssociatedRecurrenceResidual_eq_zero_of_strip hz
    (fun _ c hc hw hc' =>
      carlsonAssociatedRecurrenceResidual_eq_zero_in_strip hc hz hw hc') a hb

/-- Polynomial form of Relation 8.4-1, including the removable-singularity values
`a = 0` and `a' = card ι`. -/
theorem sum_carlsonAssociatedRecurrencePolynomial_mul_rIntegral [Nonempty ι]
    (a : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    ∑ n ∈ Finset.range (Fintype.card ι + 1),
      (carlsonAssociatedRecurrencePolynomial n a ((∑ i, b i) - a) b).eval z *
        carlsonRIntegral (-a - n) b z = 0 := by
  have hzero := carlsonAssociatedRecurrenceResidual_eq_zero a hb hz
  unfold carlsonRIntegral
  calc
    ∑ n ∈ Finset.range (Fintype.card ι + 1),
          (carlsonAssociatedRecurrencePolynomial n a ((∑ i, b i) - a) b).eval z *
            (Gamma (∑ i, b i) * regCarlsonRIntegral (-a - n) b z) =
        Gamma (∑ i, b i) * ∑ n ∈ Finset.range (Fintype.card ι + 1),
          (carlsonAssociatedRecurrencePolynomial n a ((∑ i, b i) - a) b).eval z *
            regCarlsonRIntegral (-a - n) b z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = Gamma (∑ i, b i) * carlsonAssociatedRecurrenceResidual a b z := rfl
    _ = 0 := by rw [hzero, mul_zero]

/-- Carlson's fixed-parameter recurrence, Relation 8.4-1, on the native domain. -/
theorem sum_carlsonAssociatedRecurrenceCoeff_mul_rIntegral
    {a a' : ℂ} {b z : ι → ℂ}
    (hsum : a + a' = ∑ i, b i)
    (ha : a ≠ 0) (ha' : a' ≠ Fintype.card ι)
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    ∑ n ∈ Finset.range (Fintype.card ι + 1),
      carlsonAssociatedRecurrenceCoeff n a a' b z *
        carlsonRIntegral (-a - n) b z = 0 := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [carlsonRIntegral]
  | inr hι =>
      let _ := hι
      have ha'eq : (∑ i, b i) - a = a' := by linear_combination -hsum
      have hzero := sum_carlsonAssociatedRecurrencePolynomial_mul_rIntegral a hb hz
      convert hzero using 1
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : n ≤ Fintype.card ι := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      rw [ha'eq, eval_carlsonAssociatedRecurrencePolynomial hn' hsum ha ha']

end DirichletTransform
end CarlsonR
