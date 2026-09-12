/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import Carlson.R.Relations
public import Carlson.R.Exponent
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Fixed-parameter recurrence for associated Carlson R-functions

This file contains the coefficient polynomials and recurrence of [Carl77, Relation 8.4-1].
-/

open Complex ProbabilityTheory
open scoped Classical Topology
@[expose] public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The `n`th elementary symmetric polynomial evaluated at the Carlson variables. -/
def carlsonElementarySymmetric (n : ℕ) (z : ι → ℂ) : ℂ :=
  (MvPolynomial.esymm ι ℂ n).eval z

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
  have hpow : ContinuousOn (fun u ↦ carlsonAffineForm z u ^ (-a - n)) (stdSimplex ℝ ι) :=
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
      have hzero : carlsonAssociatedRecurrenceResidual a b z = 0 := by
        apply carlsonAssociatedRecurrenceResidual_eq_zero_of_strip hz ?_ a hb
        intro w c hc hw hc'
        -- Remaining analytic calculation: integrate the derivative of
        -- u^w (1-u)^(sum c - w - card ι) * ∏ i, (1-u+u*z i)^(1-c i)
        -- on [0,1]. Both endpoint values vanish in this strip. Expanding the
        -- product by elementary symmetric polynomials gives the residual.
        sorry
      have ha'eq : (∑ i, b i) - a = a' := by linear_combination -hsum
      calc
        ∑ n ∈ Finset.range (Fintype.card ι + 1),
            carlsonAssociatedRecurrenceCoeff n a a' b z * carlsonRIntegral (-a - n) b z =
            Gamma (∑ i, b i) * carlsonAssociatedRecurrenceResidual a b z := by
          unfold carlsonAssociatedRecurrenceResidual
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          have hn' : n ≤ Fintype.card ι := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
          rw [ha'eq, eval_carlsonAssociatedRecurrencePolynomial hn' hsum ha ha', carlsonRIntegral]
          ring
        _ = 0 := by rw [hzero, mul_zero]

end DirichletTransform
end CarlsonR
