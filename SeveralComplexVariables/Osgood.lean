/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.MeasureTheory.Integral.TorusIntegral

/-!
# Osgood's theorem in finite products

This file proves a finite-product form of Osgood's theorem. Its immediate application is to
functions on `ι → ℂ`: analyticity of every one-coordinate update, together with joint continuity,
implies joint analyticity on an open domain.

This is a temporary project home for material ultimately intended for a Mathlib location such as
`Mathlib.Analysis.Complex.SeveralVariables.Osgood`.

## Main result

`analyticOnNhd_pi_of_analyticOnNhd_update` is presently Osgood's theorem: separate holomorphy
together with joint continuity implies joint analyticity on an open set in `ι → ℂ`.  The
classically stronger Hartogs theorem, which drops continuity and recovers local boundedness from
separate holomorphy, is not proved here.

The converse direction, extracting separate analyticity from joint analyticity, is already
largely supplied by composition with continuous linear coordinate maps.

The proof also exposes `polydiscCauchyCoeff` and `polydiscCauchySeries`, the multi-index Cauchy
coefficients and their packaging as a `FormalMultilinearSeries`.
-/

public section

open Complex Filter Function MeasureTheory Metric Set
open scoped Classical ENNReal NNReal Real Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-! ### Closed polydiscs -/

/-- The closed polydisc of equal radii.  For `0 ≤ R` this coincides with the closed ball for the
sup-norm. -/
def closedPolydisc {n : ℕ} (c : Fin n → ℂ) (R : ℝ) : Set (Fin n → ℂ) :=
  Set.pi univ fun i => closedBall (c i) R

/-- Membership in an equal-radius closed polydisc is coordinatewise membership in the
corresponding closed balls. -/
lemma mem_closedPolydisc {n : ℕ} {c z : Fin n → ℂ} {R : ℝ} :
    z ∈ closedPolydisc c R ↔ ∀ i, z i ∈ closedBall (c i) R := by
  simp [closedPolydisc]

/-- An equal-radius closed polydisc is the closed ball for the supremum norm. -/
lemma closedPolydisc_eq_closedBall {n : ℕ} {c : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    closedPolydisc c R = closedBall c R :=
  (closedBall_pi c hR).symm

/-- The standard torus with nonnegative radius lies in its associated closed polydisc. -/
lemma torusMap_mem_closedPolydisc {n : ℕ} {c : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (θ : Fin n → ℝ) : torusMap c (fun _ => R) θ ∈ closedPolydisc c R := by
  intro i _
  simp [torusMap, mem_closedBall, dist_eq_norm, abs_of_nonneg hR]

/-- Adjoining a point in the first coordinate ball to a point in the tail polydisc produces a
point in the full polydisc. -/
lemma cons_mem_closedPolydisc {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} {x : ℂ}
    {y : Fin n → ℂ} (hx : x ∈ closedBall (c 0) R)
    (hy : y ∈ closedPolydisc (c ∘ Fin.succ) R) :
    Fin.cons x y ∈ closedPolydisc c R := by
  intro i _
  refine Fin.cases ?_ ?_ i
  · simpa [Fin.cons_zero] using hx
  · intro j
    simpa [Fin.cons_succ] using hy j (mem_univ _)

/-- The standard equal-radius torus parametrization is continuous. -/
lemma continuous_torusMap {n : ℕ} (c : Fin n → ℂ) (R : ℝ) :
    Continuous (torusMap c (fun _ => R)) :=
  continuous_pi fun i => by
    simp only [torusMap]
    fun_prop

/-- No natural-number power of `2 * π * I` vanishes. -/
lemma two_pi_I_pow_ne_zero (n : ℕ) : ((2 * π * I : ℂ) ^ n) ≠ 0 :=
  pow_ne_zero _ two_pi_I_ne_zero

/-- Every coordinate of the standard equal-radius torus has the prescribed distance from its
center. -/
lemma torusMap_coord_norm {n : ℕ} {c : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (θ : Fin n → ℝ) (i : Fin n) :
    ‖torusMap c (fun _ => R) θ i - c i‖ = R := by
  simp [torusMap, abs_of_nonneg hR]

/-- A point strictly inside a coordinate disc does not meet the corresponding coordinate circle,
so its Cauchy kernel has no pole on the torus. -/
lemma cauchyKernel_ne_zero_on_torus {n : ℕ} {c w : Fin n → ℂ} {R : ℝ} {θ : Fin n → ℝ}
    {i : Fin n} (hR : 0 < R) (hw : ‖w i - c i‖ < R) :
    torusMap c (fun _ => R) θ i ≠ w i := by
  intro h
  have : ‖torusMap c (fun _ => R) θ i - c i‖ = R := torusMap_coord_norm hR.le θ i
  rw [h] at this
  exact hw.not_ge this.ge

/-! ### Cauchy's formula on a polydisc -/

omit [CompleteSpace E] in
/-- The vector-valued Cauchy kernel of a continuous function is integrable on a torus whenever
the evaluation point lies in the interior polydisc. -/
lemma torusIntegrable_cauchyKernel {n : ℕ} {f : (Fin n → ℂ) → E} {c w : Fin n → ℂ} {R : ℝ}
    (hR : 0 < R) (hw : ∀ i, ‖w i - c i‖ < R)
    (hfc : ContinuousOn f (closedPolydisc c R)) :
    TorusIntegrable (fun z => (∏ i, (z i - w i)⁻¹) • f z) c (fun _ => R) := by
  have hmaps : MapsTo (torusMap c (fun _ => R))
      (Icc (0 : Fin n → ℝ) fun _ => 2 * π) (closedPolydisc c R) :=
    fun θ _ => torusMap_mem_closedPolydisc hR.le θ
  have hfθ : ContinuousOn (fun θ => f (torusMap c (fun _ => R) θ))
      (Icc (0 : Fin n → ℝ) fun _ => 2 * π) :=
    hfc.comp (continuous_torusMap c R).continuousOn hmaps
  have hker : ContinuousOn
      (fun θ : Fin n → ℝ => (∏ i, (torusMap c (fun _ => R) θ i - w i)⁻¹))
      (Icc (0 : Fin n → ℝ) fun _ => 2 * π) := by
    refine continuousOn_finsetProd _ fun i _ => ?_
    refine ((((continuous_apply i).comp (continuous_torusMap c R)).continuousOn).sub
      continuousOn_const).inv₀ ?_
    intro θ _
    exact sub_ne_zero.2 (cauchyKernel_ne_zero_on_torus hR (hw i))
  exact (hker.smul hfθ).integrableOn_compact isCompact_Icc

/-- Splitting off the first coordinate factors the finite-product Cauchy kernel. -/
lemma cauchyKernel_cons {n : ℕ} (x : ℂ) (y : Fin n → ℂ) (w : Fin (n + 1) → ℂ) :
    (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - w i)⁻¹) =
      (x - w 0)⁻¹ * ∏ i, (y i - w i.succ)⁻¹ := by
  simp [Fin.prod_univ_succ, mul_comm]

/-- Iterated Cauchy integral formula on a closed polydisc. -/
theorem polydisc_cauchy {n : ℕ} {f : (Fin n → ℂ) → E} {c w : Fin n → ℂ} {R : ℝ}
    (hR : 0 < R) (hw : ∀ i, ‖w i - c i‖ < R)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i)) :
    ((2 * π * I : ℂ) ^ n)⁻¹ •
      torusIntegral (fun z => (∏ i, (z i - w i)⁻¹) • f z) c (fun _ => R) = f w := by
  induction n with
  | zero =>
    have : w = c := Subsingleton.elim _ _
    subst this
    simp [torusIntegral_dim0]
  | succ n ih =>
    set F : (Fin (n + 1) → ℂ) → E :=
      fun z => (∏ i, (z i - w i)⁻¹) • f z
    have hFint : TorusIntegrable F c (fun _ => R) :=
      torusIntegrable_cauchyKernel hR hw hfc
    have hx_sphere : ∀ x, x ∈ sphere (c 0) R →
        x ∈ closedBall (c 0) R ∧ x ≠ w 0 ∧ ‖x - c 0‖ = R := by
      intro x hx
      have hxR : ‖x - c 0‖ = R := by
        rw [← dist_eq_norm]
        exact mem_sphere.1 hx
      refine ⟨mem_closedBall.2 (by rw [dist_eq_norm, hxR]), ?_, hxR⟩
      intro h
      rw [h] at hxR
      exact (hw 0).not_ge hxR.ge
    have hinter : ∀ x ∈ sphere (c 0) R,
        torusIntegral (fun y => F (Fin.cons x y)) (c ∘ Fin.succ) (fun _ => R) =
          (x - w 0)⁻¹ • ((2 * π * I : ℂ) ^ n •
            f (Fin.cons x (w ∘ Fin.succ))) := by
      intro x hx
      obtain ⟨hxcl, hxw, hxR⟩ := hx_sphere x hx
      have hgcont : ContinuousOn (fun y => f (Fin.cons x y))
          (closedPolydisc (c ∘ Fin.succ) R) :=
        hfc.comp (continuousOn_const.finCons continuousOn_id)
          (fun y hy => cons_mem_closedPolydisc hxcl hy)
      have hga : ∀ y ∈ closedPolydisc (c ∘ Fin.succ) R, ∀ j,
          AnalyticAt ℂ (fun t => f (Fin.cons x (update y j t))) (y j) := by
        intro y hy j
        have hz := cons_mem_closedPolydisc hxcl hy
        simpa [Fin.cons_update] using hfa (Fin.cons x y) hz j.succ
      have hw' : ∀ i : Fin n, ‖w i.succ - c i.succ‖ < R := fun i => hw i.succ
      have ih' :=
        ih (f := fun y => f (Fin.cons x y)) (c := c ∘ Fin.succ) (w := w ∘ Fin.succ)
          hw' hgcont hga
      have ih_int :
          torusIntegral (fun y => (∏ i, (y i - w i.succ)⁻¹) • f (Fin.cons x y))
            (c ∘ Fin.succ) (fun _ => R) =
            (2 * π * I : ℂ) ^ n • f (Fin.cons x (w ∘ Fin.succ)) :=
        ((eq_inv_smul_iff₀ (two_pi_I_pow_ne_zero n)).mp ih'.symm).symm
      have hsmul := torusIntegral_smul (x - w 0)⁻¹
        (fun y => (∏ i, (y i - w i.succ)⁻¹) • f (Fin.cons x y))
        (c ∘ Fin.succ) (fun _ => R)
      calc
        torusIntegral (fun y => F (Fin.cons x y)) (c ∘ Fin.succ) (fun _ => R)
            = torusIntegral (fun y => (x - w 0)⁻¹ •
                (∏ i, (y i - w i.succ)⁻¹) • f (Fin.cons x y))
                (c ∘ Fin.succ) (fun _ => R) := by
              congr 1
              funext y
              simp only [F]
              rw [cauchyKernel_cons x y w, mul_smul]
        _ = (x - w 0)⁻¹ • torusIntegral
              (fun y => (∏ i, (y i - w i.succ)⁻¹) • f (Fin.cons x y))
              (c ∘ Fin.succ) (fun _ => R) := hsmul
        _ = (x - w 0)⁻¹ • ((2 * π * I : ℂ) ^ n •
              f (Fin.cons x (w ∘ Fin.succ))) := by rw [ih_int]
    have hcons : Continuous (fun x : ℂ => (Fin.cons x (w ∘ Fin.succ) : Fin (n + 1) → ℂ)) :=
      Continuous.finCons (A := fun _ : Fin (n + 1) => ℂ) continuous_id continuous_const
    have hψcont : ContinuousOn (fun x => f (Fin.cons x (w ∘ Fin.succ)))
        (closedBall (c 0) R) :=
      hfc.comp hcons.continuousOn fun x hx =>
        cons_mem_closedPolydisc hx (fun i _ =>
          mem_closedBall.2 (le_of_lt (by simpa [dist_eq_norm] using hw i.succ)))
    have hψdiff : ∀ x ∈ ball (c 0) R,
        DifferentiableAt ℂ (fun t => f (Fin.cons t (w ∘ Fin.succ))) x := by
      intro x hx
      have hz : Fin.cons x (w ∘ Fin.succ) ∈ closedPolydisc c R :=
        cons_mem_closedPolydisc (ball_subset_closedBall hx) fun i _ =>
          mem_closedBall.2 (le_of_lt (by simpa [dist_eq_norm] using hw i.succ))
      simpa [Fin.update_cons_zero] using (hfa _ hz 0).differentiableAt
    have hcircle :
        ((2 * π * I : ℂ)⁻¹ •
          ∮ x in C(c 0, R), (x - w 0)⁻¹ • f (Fin.cons x (w ∘ Fin.succ))) =
          f (Fin.cons (w 0) (w ∘ Fin.succ)) := by
      have hw0 : w 0 ∈ ball (c 0) R := by simpa [dist_eq_norm] using hw 0
      simpa using
        two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
          (s := (∅ : Set ℂ)) countable_empty hw0 hψcont fun x hx => hψdiff x hx.1
    have houter :
        torusIntegral F c (fun _ => R) =
          (2 * π * I : ℂ) ^ n •
            ∮ x in C(c 0, R), (x - w 0)⁻¹ • f (Fin.cons x (w ∘ Fin.succ)) := by
      rw [torusIntegral_succ hFint]
      refine (circleIntegral.integral_congr hR.le fun x hx => hinter x hx).trans ?_
      rw [show (fun x => (x - w 0)⁻¹ • ((2 * π * I : ℂ) ^ n •
            f (Fin.cons x (w ∘ Fin.succ)))) =
          fun x => ((2 * π * I : ℂ) ^ n) • ((x - w 0)⁻¹ •
            f (Fin.cons x (w ∘ Fin.succ))) by
        funext x; simp [smul_smul, mul_comm]]
      rw [circleIntegral.integral_smul]
    have hw_eq : Fin.cons (w 0) (w ∘ Fin.succ) = w := Fin.cons_self_tail w
    rw [← hw_eq, houter, smul_smul]
    convert hcircle using 2
    simp [pow_succ, two_pi_I_pow_ne_zero n]


/-! ### Multi-index Cauchy series -/

/-- The continuous multilinear monomial associated to a multi-index of total degree `n`. -/
noncomputable def multiIndexMonomial {d n : ℕ} (m : Fin d → ℕ)
    (hm : ∑ i, m i = n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => (Fin d → ℂ)) ℂ := by
  let e : (Σ i, Fin (m i)) ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hm)
  exact ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Σ i, Fin (m i)) ℂ).compContinuousLinearMap
    (fun q => ContinuousLinearMap.proj q.1)).domDomCongr e

/-- On the diagonal, `multiIndexMonomial` evaluates to the usual multi-index monomial. -/
lemma multiIndexMonomial_apply {d n : ℕ} (m : Fin d → ℕ)
    (hm : ∑ i, m i = n) (w : Fin d → ℂ) :
    multiIndexMonomial m hm (fun _ => w) = ∏ i, w i ^ m i := by
  simp [multiIndexMonomial, Fintype.prod_sigma]

/-- The operator norm of `multiIndexMonomial` is at most one for the sup norm. -/
lemma norm_multiIndexMonomial_le {d n : ℕ} (m : Fin d → ℕ)
    (hm : ∑ i, m i = n) : ‖multiIndexMonomial m hm‖ ≤ 1 := by
  rw [multiIndexMonomial, ContinuousMultilinearMap.norm_domDomCongr]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [ContinuousMultilinearMap.norm_mkPiAlgebra]
  simp only [one_mul]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun q _ => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  simpa using norm_le_pi_norm w q.1

private lemma summable_norm_pi_geometric {K : Type*} [NormedCommRing K]
    {d : ℕ} (x : Fin d → K) (hx : ∀ i, ‖x i‖ < 1) :
    Summable fun m : Fin d → ℕ => ‖∏ i, x i ^ m i‖ := by
  induction d with
  | zero =>
      exact (hasSum_single (0 : Fin 0 → ℕ) fun m hm =>
        (hm (Subsingleton.elim _ _)).elim).summable
  | succ d ih =>
      let e := Fin.consEquiv (fun _ : Fin (d + 1) => ℕ)
      have hhead : Summable (fun n : ℕ => ‖x 0 ^ n‖) :=
        summable_norm_geometric_of_norm_lt_one (hx 0)
      have htail := ih (fun i => x i.succ) (fun i => hx i.succ)
      have hprod := hhead.mul_of_nonneg htail (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      rw [← e.summable_iff]
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hprod
      intro p
      simpa only [Function.comp_apply, e, Fin.consEquiv_apply, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ] using
        norm_mul_le (x 0 ^ p.1) (∏ i, x i.succ ^ p.2 i)

private lemma hasSum_pi_geometric {K : Type*} [NormedField K] [CompleteSpace K]
    {d : ℕ} (x : Fin d → K) (hx : ∀ i, ‖x i‖ < 1) :
    HasSum (fun m : Fin d → ℕ => ∏ i, x i ^ m i) (∏ i, (1 - x i)⁻¹) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      let e := Fin.consEquiv (fun _ : Fin (d + 1) => ℕ)
      have hhead : HasSum (fun n : ℕ => x 0 ^ n) (1 - x 0)⁻¹ :=
        hasSum_geometric_of_norm_lt_one (hx 0)
      have htail : HasSum (fun m : Fin d → ℕ => ∏ i, x i.succ ^ m i)
          (∏ i : Fin d, (1 - x i.succ)⁻¹) :=
        ih (fun i => x i.succ) (fun i => hx i.succ)
      have hnormHead : Summable (fun n : ℕ => ‖x 0 ^ n‖) :=
        summable_norm_geometric_of_norm_lt_one (hx 0)
      have hnormTail : Summable (fun m : Fin d → ℕ => ‖∏ i, x i.succ ^ m i‖) :=
        summable_norm_pi_geometric _ (fun i => hx i.succ)
      have hsummul : Summable
          (fun p : ℕ × (Fin d → ℕ) => x 0 ^ p.1 * ∏ i, x i.succ ^ p.2 i) :=
        (hnormHead.mul_norm hnormTail).of_norm
      have hprod : HasSum
          (fun p : ℕ × (Fin d → ℕ) => x 0 ^ p.1 * ∏ i, x i.succ ^ p.2 i)
          ((1 - x 0)⁻¹ * ∏ i : Fin d, (1 - x i.succ)⁻¹) := by
        rw [← hhead.tsum_eq, ← htail.tsum_eq,
          tsum_mul_tsum_of_summable_norm hnormHead hnormTail]
        exact hsummul.hasSum
      rw [← e.hasSum_iff]
      convert hprod using 1
      · ext p
        simp [e, Fin.prod_univ_succ]
      · simp [Fin.prod_univ_succ, mul_comm]

private lemma hasSum_antidiagonalTuple_geometric {K : Type*} [NormedField K] [CompleteSpace K]
    {d : ℕ} (x : Fin d → K)
    (hx : ∀ i, ‖x i‖ < 1) :
    HasSum (fun n : ℕ => ∑ m ∈ Finset.Nat.antidiagonalTuple d n, ∏ i, x i ^ m i)
      (∏ i, (1 - x i)⁻¹) := by
  have h := hasSum_pi_geometric x hx
  let e := Finset.Nat.sigmaAntidiagonalTupleEquivTuple d
  have he0 : HasSum
      ((fun m : Fin d → ℕ => ∏ i, x i ^ m i) ∘ e)
      (∏ i, (1 - x i)⁻¹) := e.hasSum_iff.mpr h
  have he : HasSum
      (fun p : Σ n, Finset.Nat.antidiagonalTuple d n =>
        ∏ i, x i ^ (p.2 : Fin d → ℕ) i)
      (∏ i, (1 - x i)⁻¹) := by
    convert he0 using 1
    · ext p
      rfl
  have hfin : ∀ n, HasSum
      (fun m : Finset.Nat.antidiagonalTuple d n => ∏ i, x i ^ (m : Fin d → ℕ) i)
      (∑ m ∈ Finset.Nat.antidiagonalTuple d n, ∏ i, x i ^ m i) := by
    intro n
    rw [← Finset.sum_finset_coe]
    exact hasSum_fintype (f := fun m : Finset.Nat.antidiagonalTuple d n =>
      ∏ i, x i ^ (m : Fin d → ℕ) i)
  exact he.sigma hfin

/-- The multi-index Cauchy coefficient of a vector-valued function on a polydisc. -/
noncomputable def polydiscCauchyCoeff {d : ℕ} (f : (Fin d → ℂ) → E)
    (c : Fin d → ℂ) (R : ℝ) (m : Fin d → ℕ) : E :=
  ((2 * π * I : ℂ) ^ d)⁻¹ • torusIntegral
    (fun z => (∏ i, (z i - c i)⁻¹ ^ (m i + 1)) • f z) c (fun _ => R)

/-- The formal multilinear series obtained by grouping the polydisc Cauchy coefficients by total
degree. -/
noncomputable def polydiscCauchySeries {d : ℕ} (f : (Fin d → ℂ) → E)
    (c : Fin d → ℂ) (R : ℝ) : FormalMultilinearSeries ℂ (Fin d → ℂ) E := fun n =>
  ∑ m : Finset.Nat.antidiagonalTuple d n,
    (multiIndexMonomial (m : Fin d → ℕ)
      (Finset.Nat.mem_antidiagonalTuple.mp m.property)).smulRight
        (polydiscCauchyCoeff f c R m)

omit [CompleteSpace E] in
/-- Evaluation of the homogeneous terms of `polydiscCauchySeries` on the diagonal. -/
lemma polydiscCauchySeries_apply {d n : ℕ} (f : (Fin d → ℂ) → E)
    (c h : Fin d → ℂ) (R : ℝ) :
    polydiscCauchySeries f c R n (fun _ => h) =
      ∑ m : Finset.Nat.antidiagonalTuple d n,
        (∏ i, h i ^ (m : Fin d → ℕ) i) • polydiscCauchyCoeff f c R m := by
  simp [polydiscCauchySeries, multiIndexMonomial_apply]

omit [CompleteSpace E] in
/-- Cauchy's coefficient estimate for the multi-index coefficients of a bounded function on a
closed polydisc. -/
lemma norm_polydiscCauchyCoeff_le {d : ℕ} {f : (Fin d → ℂ) → E}
    {c : Fin d → ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) (m : Fin d → ℕ) :
    ‖polydiscCauchyCoeff f c R m‖ ≤ M * R⁻¹ ^ (∑ i, m i) := by
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans (hM c (by
    intro i _
    simp [mem_closedBall, dist_self, hR.le]))
  rw [polydiscCauchyCoeff, norm_smul]
  refine (mul_le_mul_of_nonneg_left (norm_torusIntegral_le_of_norm_le_const
    (C := M * R⁻¹ ^ (∑ i, (m i + 1))) ?_)
    (norm_nonneg _)).trans_eq ?_
  · intro θ
    rw [norm_smul]
    calc
      ‖∏ i, (torusMap c (fun _ => R) θ i - c i)⁻¹ ^ (m i + 1)‖ *
          ‖f (torusMap c (fun _ => R) θ)‖
          ≤ ‖∏ i, (torusMap c (fun _ => R) θ i - c i)⁻¹ ^ (m i + 1)‖ * M :=
        mul_le_mul_of_nonneg_left (hM _ (torusMap_mem_closedPolydisc hR.le θ))
          (norm_nonneg _)
      _ = M * R⁻¹ ^ (∑ i, (m i + 1)) := by
        simp only [norm_prod, norm_pow, norm_inv, torusMap_coord_norm hR.le]
        rw [Finset.prod_pow_eq_pow_sum]
        ring
  · simp only [norm_inv, norm_pow, norm_mul, norm_ofNat, norm_real, norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hR, abs_of_pos Real.pi_pos, Fin.prod_const]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    field_simp
    simp only [one_div, pow_add]
    calc
      R ^ d * M * (R⁻¹ ^ (∑ x, m x) * R⁻¹ ^ d) =
          M * R⁻¹ ^ (∑ x, m x) * (R ^ d * R⁻¹ ^ d) := by ring
      _ = M * R⁻¹ ^ ∑ x, m x := by
        rw [← mul_pow, mul_inv_cancel₀ hR.ne', one_pow, mul_one]

omit [CompleteSpace E] in
private lemma norm_polydiscCauchySeries_mul_pow_le {d : ℕ} {f : (Fin d → ℂ) → E}
    {c : Fin d → ℂ} {R M r : ℝ} (hR : 0 < R) (hr : 0 ≤ r)
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖polydiscCauchySeries f c R n‖ * r ^ n ≤
      M * ∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, (r * R⁻¹) ^ (m : Fin d → ℕ) i := by
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans (hM c (by
    intro i _
    simp [mem_closedBall, dist_self, hR.le]))
  rw [polydiscCauchySeries]
  calc
    ‖∑ m : Finset.Nat.antidiagonalTuple d n,
        (multiIndexMonomial (m : Fin d → ℕ)
          (Finset.Nat.mem_antidiagonalTuple.mp m.property)).smulRight
            (polydiscCauchyCoeff f c R m)‖ * r ^ n
        ≤ (∑ m : Finset.Nat.antidiagonalTuple d n,
            ‖(multiIndexMonomial (m : Fin d → ℕ)
              (Finset.Nat.mem_antidiagonalTuple.mp m.property)).smulRight
                (polydiscCauchyCoeff f c R m)‖) * r ^ n := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ (∑ _m : Finset.Nat.antidiagonalTuple d n, M * R⁻¹ ^ n) * r ^ n := by
          gcongr with m
          rw [ContinuousMultilinearMap.norm_smulRight]
          calc
            ‖multiIndexMonomial (m : Fin d → ℕ)
                (Finset.Nat.mem_antidiagonalTuple.mp m.property)‖ *
                  ‖polydiscCauchyCoeff f c R m‖
                ≤ 1 * (M * R⁻¹ ^ (∑ i, (m : Fin d → ℕ) i)) := by
                  gcongr
                  · exact norm_multiIndexMonomial_le _ _
                  · exact norm_polydiscCauchyCoeff_le hR hM _
            _ = M * R⁻¹ ^ n := by
                  rw [Finset.Nat.mem_antidiagonalTuple.mp m.property]
                  ring
      _ = M * ∑ m : Finset.Nat.antidiagonalTuple d n,
          ∏ i, (r * R⁻¹) ^ (m : Fin d → ℕ) i := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
          Finset.prod_pow_eq_pow_sum,
          Finset.Nat.mem_antidiagonalTuple.mp m.property]
        ring

omit [CompleteSpace E] in
private lemma summable_norm_polydiscCauchySeries_mul_pow {d : ℕ}
    {f : (Fin d → ℂ) → E} {c : Fin d → ℂ} {R M r : ℝ} (hR : 0 < R)
    (hr : 0 ≤ r) (hrR : r < R)
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) :
    Summable fun n => ‖polydiscCauchySeries f c R n‖ * r ^ n := by
  have hq0 : 0 ≤ r * R⁻¹ := mul_nonneg hr (inv_nonneg.mpr hR.le)
  have hq1 : r * R⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hR]
    exact hrR
  have hq1norm : ∀ _i : Fin d, ‖(r * R⁻¹ : ℝ)‖ < 1 := fun _ => by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hseries : HasSum (fun n : ℕ =>
      ∑ m ∈ Finset.Nat.antidiagonalTuple d n,
        ∏ i, (r * R⁻¹) ^ (m : Fin d → ℕ) i)
      (∏ _i : Fin d, (1 - r * R⁻¹)⁻¹) :=
    hasSum_antidiagonalTuple_geometric (K := ℝ) (fun _ => r * R⁻¹) hq1norm
  have hgeom : Summable fun n : ℕ =>
      ∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, (r * R⁻¹) ^ (m : Fin d → ℕ) i := by
    exact hseries.summable.congr fun n =>
      (Finset.sum_finset_coe
        (fun m : Fin d → ℕ => ∏ i, (r * R⁻¹) ^ m i)
        (Finset.Nat.antidiagonalTuple d n)).symm
  have hmajor : Summable fun n => M *
      ∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, (r * R⁻¹) ^ (m : Fin d → ℕ) i := hgeom.mul_left M
  refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (pow_nonneg hr _))
    (norm_polydiscCauchySeries_mul_pow_le hR hr hM) ?_
  exact hmajor

private lemma hasSum_polydiscCauchyKernel {d : ℕ} {z c h : Fin d → ℂ}
    (hz : ∀ i, z i ≠ c i) (hh : ∀ i, ‖h i‖ < ‖z i - c i‖) :
    HasSum (fun n : ℕ => ∑ m : Finset.Nat.antidiagonalTuple d n,
        (∏ i, h i ^ (m : Fin d → ℕ) i) *
          ∏ i, (z i - c i)⁻¹ ^ ((m : Fin d → ℕ) i + 1))
      (∏ i, (z i - (c + h) i)⁻¹) := by
  have hx : ∀ i, ‖h i / (z i - c i)‖ < 1 := by
    intro i
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (sub_ne_zero.mpr (hz i)))]
    exact hh i
  have hs := (hasSum_antidiagonalTuple_geometric
    (fun i => h i / (z i - c i)) hx).mul_right (∏ i, (z i - c i)⁻¹)
  have hterm : (fun n : ℕ => ∑ m : Finset.Nat.antidiagonalTuple d n,
        (∏ i, h i ^ (m : Fin d → ℕ) i) *
          ∏ i, (z i - c i)⁻¹ ^ ((m : Fin d → ℕ) i + 1)) =
      fun n => (∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, (h i / (z i - c i)) ^ (m : Fin d → ℕ) i) *
          ∏ i, (z i - c i)⁻¹ := by
    funext n
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [pow_succ, div_pow, inv_pow]
    field_simp [sub_ne_zero.mpr (hz i)]
  have hconst : (∏ i, (z i - (c + h) i)⁻¹) =
      (∏ i, (1 - h i / (z i - c i))⁻¹) * ∏ i, (z i - c i)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hzi : z i - c i ≠ 0 := sub_ne_zero.mpr (hz i)
    have hzih : z i - (c + h) i ≠ 0 := by
      intro heq
      have : z i - c i = h i := by
        calc
          z i - c i = (c + h) i - c i := by rw [sub_eq_zero.mp heq]
          _ = h i := by simp [Pi.add_apply]
      have hi := hh i
      rw [this] at hi
      exact (lt_irrefl _ hi)
    simp only [Pi.add_apply]
    field_simp [hzi, hzih]
    ring
  have hsource : (fun n => (∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, (h i / (z i - c i)) ^ (m : Fin d → ℕ) i) *
          ∏ i, (z i - c i)⁻¹) =
      fun n => (∑ m ∈ Finset.Nat.antidiagonalTuple d n,
        ∏ i, (h i / (z i - c i)) ^ m i) * ∏ i, (z i - c i)⁻¹ := by
    funext n
    exact congrArg (fun v => v * ∏ i, (z i - c i)⁻¹)
      (Finset.sum_finset_coe
        (fun m : Fin d → ℕ => ∏ i, (h i / (z i - c i)) ^ m i)
        (Finset.Nat.antidiagonalTuple d n))
  rw [hterm, hsource, hconst]
  exact hs

omit [CompleteSpace E] in
private lemma hasSum_torusIntegral_of_uniform {d : ℕ} {F : ℕ → (Fin d → ℂ) → E}
    {g : (Fin d → ℂ) → E} {c : Fin d → ℂ} {R : Fin d → ℝ} {a : ℕ → ℝ}
    (ha : Summable a)
    (hFint : ∀ n, TorusIntegrable (F n) c R)
    (hbound : ∀ n θ, ‖F n (torusMap c R θ)‖ ≤ a n)
    (hsum : ∀ θ, HasSum (fun n => F n (torusMap c R θ)) (g (torusMap c R θ))) :
    HasSum (fun n => torusIntegral (F n) c R) (torusIntegral g c R) := by
  let J : (Fin d → ℝ) → ℂ := fun θ => ∏ i, R i * exp (θ i * I) * I
  have h := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (0 : Fin d → ℝ) fun _ => 2 * π))
    (F := fun n θ => J θ • F n (torusMap c R θ))
    (f := fun θ => J θ • g (torusMap c R θ))
    (fun n _ => (∏ i, |R i|) * a n)
    (fun n => (hFint n).function_integrable.1)
    (fun n => ae_of_all _ fun θ => by
      rw [norm_smul]
      have hJ : ‖J θ‖ = ∏ i, |R i| := by simp [J]
      rw [hJ]
      exact mul_le_mul_of_nonneg_left (hbound n θ) (by positivity))
    (ae_of_all _ fun _ => (ha.mul_left (∏ i, |R i|)))
    (by
      simp only [tsum_mul_left]
      exact integrableOn_const (hs := measure_Icc_lt_top.ne))
    (ae_of_all _ fun θ => (hsum θ).const_smul (J θ))
  simpa [torusIntegral, J] using h

private noncomputable def polydiscCauchyTerm {d : ℕ} (f : (Fin d → ℂ) → E)
    (c h : Fin d → ℂ) (n : ℕ) (z : Fin d → ℂ) : E :=
  (∑ m : Finset.Nat.antidiagonalTuple d n,
    (∏ i, h i ^ (m : Fin d → ℕ) i) *
      ∏ i, (z i - c i)⁻¹ ^ ((m : Fin d → ℕ) i + 1)) • f z

omit [CompleteSpace E] in
private lemma torusIntegral_fintype_sum {d : ℕ} {α : Type*} [Fintype α]
    {F : α → (Fin d → ℂ) → E} {c : Fin d → ℂ} {R : Fin d → ℝ}
    (hF : ∀ a, TorusIntegrable (F a) c R) :
    torusIntegral (fun z => ∑ a, F a z) c R = ∑ a, torusIntegral (F a) c R := by
  simp only [torusIntegral, Finset.smul_sum]
  exact integral_finsetSum _ fun a _ => (hF a).function_integrable

omit [CompleteSpace E] in
private lemma torusIntegrable_polydiscCauchySummand {d : ℕ}
    {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ} {R : ℝ} (hR : 0 < R)
    (hfc : ContinuousOn f (closedPolydisc c R)) (m : Fin d → ℕ) :
    TorusIntegrable (fun z => ((∏ i, h i ^ m i) *
      ∏ i, (z i - c i)⁻¹ ^ (m i + 1)) • f z) c (fun _ => R) := by
  have hfθ : ContinuousOn (fun θ => f (torusMap c (fun _ => R) θ))
      (Icc (0 : Fin d → ℝ) fun _ => 2 * π) :=
    hfc.comp (continuous_torusMap c R).continuousOn
      (fun θ _ => torusMap_mem_closedPolydisc hR.le θ)
  have hscalar : ContinuousOn (fun θ : Fin d → ℝ =>
      (∏ i, h i ^ m i) *
        ∏ i, (torusMap c (fun _ => R) θ i - c i)⁻¹ ^ (m i + 1))
      (Icc (0 : Fin d → ℝ) fun _ => 2 * π) := by
    refine continuousOn_const.mul (continuousOn_finsetProd _ fun i _ => ?_)
    refine (((((continuous_apply i).comp (continuous_torusMap c R)).continuousOn).sub
      continuousOn_const).inv₀ ?_).pow _
    intro θ _
    apply sub_ne_zero.mpr
    intro heq
    have := torusMap_coord_norm (c := c) hR.le θ i
    have heq' : torusMap c (fun _ => R) θ i = c i := by
      simpa only [Function.comp_apply] using heq
    rw [heq', sub_self, norm_zero] at this
    exact hR.ne' this.symm
  exact (hscalar.smul hfθ).integrableOn_compact isCompact_Icc

omit [CompleteSpace E] in
private lemma torusIntegrable_polydiscCauchyTerm {d n : ℕ}
    {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ} {R : ℝ} (hR : 0 < R)
    (hfc : ContinuousOn f (closedPolydisc c R)) :
    TorusIntegrable (polydiscCauchyTerm f c h n) c (fun _ => R) := by
  have hfθ : ContinuousOn (fun θ => f (torusMap c (fun _ => R) θ))
      (Icc (0 : Fin d → ℝ) fun _ => 2 * π) :=
    hfc.comp (continuous_torusMap c R).continuousOn
      (fun θ _ => torusMap_mem_closedPolydisc hR.le θ)
  have hscalar : ContinuousOn (fun θ : Fin d → ℝ =>
      ∑ m : Finset.Nat.antidiagonalTuple d n,
        (∏ i, h i ^ (m : Fin d → ℕ) i) *
          ∏ i, (torusMap c (fun _ => R) θ i - c i)⁻¹ ^
            ((m : Fin d → ℕ) i + 1))
      (Icc (0 : Fin d → ℝ) fun _ => 2 * π) := by
    refine continuousOn_finsetSum _ fun m _ =>
      continuousOn_const.mul (continuousOn_finsetProd _ fun i _ => ?_)
    refine (((((continuous_apply i).comp (continuous_torusMap c R)).continuousOn).sub
      continuousOn_const).inv₀ ?_).pow _
    intro θ _
    apply sub_ne_zero.mpr
    intro heq
    have := torusMap_coord_norm (c := c) hR.le θ i
    have heq' : torusMap c (fun _ => R) θ i = c i := by
      simpa only [Function.comp_apply] using heq
    rw [heq', sub_self, norm_zero] at this
    exact hR.ne' this.symm
  exact (hscalar.smul hfθ).integrableOn_compact isCompact_Icc

omit [CompleteSpace E] in
private lemma norm_polydiscCauchyTerm_le {d n : ℕ} {f : (Fin d → ℂ) → E}
    {c h : Fin d → ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) (θ : Fin d → ℝ) :
    ‖polydiscCauchyTerm f c h n (torusMap c (fun _ => R) θ)‖ ≤
      (M * R⁻¹ ^ d) * ∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, (‖h i‖ * R⁻¹) ^ (m : Fin d → ℕ) i := by
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans (hM c (by
    intro i _
    simp [mem_closedBall, dist_self, hR.le]))
  rw [polydiscCauchyTerm, norm_smul]
  calc
    ‖∑ m : Finset.Nat.antidiagonalTuple d n,
        (∏ i, h i ^ (m : Fin d → ℕ) i) *
          ∏ i, (torusMap c (fun _ => R) θ i - c i)⁻¹ ^
            ((m : Fin d → ℕ) i + 1)‖ *
          ‖f (torusMap c (fun _ => R) θ)‖
        ≤ (∑ m : Finset.Nat.antidiagonalTuple d n,
            ‖(∏ i, h i ^ (m : Fin d → ℕ) i) *
              ∏ i, (torusMap c (fun _ => R) θ i - c i)⁻¹ ^
                ((m : Fin d → ℕ) i + 1)‖) * M := by
          gcongr
          · exact norm_sum_le _ _
          · exact hM _ (torusMap_mem_closedPolydisc hR.le θ)
    _ = (M * R⁻¹ ^ d) * ∑ m : Finset.Nat.antidiagonalTuple d n,
          ∏ i, (‖h i‖ * R⁻¹) ^ (m : Fin d → ℕ) i := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _
        simp only [norm_mul, norm_prod, norm_pow, norm_inv,
          torusMap_coord_norm hR.le]
        simp_rw [pow_succ, mul_pow]
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        ring

omit [CompleteSpace E] in
private lemma polydiscCauchySeries_apply_eq_torusIntegral {d n : ℕ}
    {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ} {R : ℝ} (hR : 0 < R)
    (hfc : ContinuousOn f (closedPolydisc c R)) :
    polydiscCauchySeries f c R n (fun _ => h) =
      ((2 * π * I : ℂ) ^ d)⁻¹ •
        torusIntegral (polydiscCauchyTerm f c h n) c (fun _ => R) := by
  let A : ℂ := ((2 * π * I : ℂ) ^ d)⁻¹
  let a : Finset.Nat.antidiagonalTuple d n → ℂ :=
    fun m => ∏ i, h i ^ (m : Fin d → ℕ) i
  let K : Finset.Nat.antidiagonalTuple d n → (Fin d → ℂ) → E :=
    fun m z => (∏ i, (z i - c i)⁻¹ ^ ((m : Fin d → ℕ) i + 1)) • f z
  rw [polydiscCauchySeries_apply]
  simp only [polydiscCauchyCoeff]
  change (∑ m, a m • (A • torusIntegral (K m) c (fun _ => R))) =
    A • torusIntegral (polydiscCauchyTerm f c h n) c (fun _ => R)
  have hInt : ∀ m, TorusIntegrable (fun z => a m • K m z) c (fun _ => R) := by
    intro m
    simpa only [a, K, smul_smul] using
      (torusIntegrable_polydiscCauchySummand (f := f) (c := c) (h := h) hR hfc
        (m : Fin d → ℕ))
  calc
    (∑ m, a m • (A • torusIntegral (K m) c (fun _ => R))) =
        A • ∑ m, a m • torusIntegral (K m) c (fun _ => R) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro m _
      simp only [smul_smul]
      rw [mul_comm]
    _ = A • ∑ m, torusIntegral (fun z => a m • K m z) c (fun _ => R) := by
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      exact (torusIntegral_smul (a m) (K m) c (fun _ => R)).symm
    _ = A • torusIntegral (fun z => ∑ m, a m • K m z) c (fun _ => R) := by
      rw [torusIntegral_fintype_sum hInt]
    _ = A • torusIntegral (polydiscCauchyTerm f c h n) c (fun _ => R) := by
      congr 2
      funext z
      rw [polydiscCauchyTerm, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro m _
      simp only [a, K, smul_smul]

omit [CompleteSpace E] in
private lemma hasSum_polydiscCauchySeries_integral {d : ℕ}
    {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ} {R M : ℝ} (hR : 0 < R)
    (hh : ∀ i, ‖h i‖ < R) (hfc : ContinuousOn f (closedPolydisc c R))
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) :
    HasSum (fun n => polydiscCauchySeries f c R n (fun _ => h))
      (((2 * π * I : ℂ) ^ d)⁻¹ • torusIntegral
        (fun z => (∏ i, (z i - (c + h) i)⁻¹) • f z) c (fun _ => R)) := by
  let q : Fin d → ℝ := fun i => ‖h i‖ * R⁻¹
  let a : ℕ → ℝ := fun n => (M * R⁻¹ ^ d) *
    ∑ m : Finset.Nat.antidiagonalTuple d n,
      ∏ i, q i ^ (m : Fin d → ℕ) i
  have hq0 : ∀ i, 0 ≤ q i := fun i => mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hR.le)
  have hq1 : ∀ i, ‖q i‖ < 1 := by
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hq0 i)]
    simp only [q]
    rw [← div_eq_mul_inv, div_lt_one hR]
    exact hh i
  have hgeom : Summable fun n =>
      ∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, q i ^ (m : Fin d → ℕ) i := by
    exact (hasSum_antidiagonalTuple_geometric q hq1).summable.congr fun n =>
      (Finset.sum_finset_coe
        (fun m : Fin d → ℕ => ∏ i, q i ^ m i)
        (Finset.Nat.antidiagonalTuple d n)).symm
  have ha : Summable a := by
    change Summable fun n => (M * R⁻¹ ^ d) *
      ∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, q i ^ (m : Fin d → ℕ) i
    exact hgeom.mul_left (M * R⁻¹ ^ d)
  have ht := hasSum_torusIntegral_of_uniform (E := E)
    (g := fun z => (∏ i, (z i - (c + h) i)⁻¹) • f z) ha
    (fun n => torusIntegrable_polydiscCauchyTerm hR hfc)
    (fun n θ => by
      simpa [a, q] using norm_polydiscCauchyTerm_le hR hM θ)
    (fun θ => by
      have hz : ∀ i, torusMap c (fun _ => R) θ i ≠ c i := by
        intro i heq
        have := torusMap_coord_norm (c := c) hR.le θ i
        rw [heq, sub_self, norm_zero] at this
        exact hR.ne' this.symm
      have hk := hasSum_polydiscCauchyKernel
        (z := torusMap c (fun _ => R) θ) (c := c) (h := h) hz (fun i => by
          rw [torusMap_coord_norm (c := c) hR.le θ i]
          exact hh i)
      simpa [polydiscCauchyTerm] using
        hk.smul_const (f (torusMap c (fun _ => R) θ)))
  have hs := ht.const_smul (((2 * π * I : ℂ) ^ d)⁻¹)
  simpa only [polydiscCauchySeries_apply_eq_torusIntegral hR hfc] using hs

/-- A continuous, separately analytic function on a closed polydisc is represented on the
concentric polydisc of half the radius by its multivariable Cauchy series. -/
theorem hasFPowerSeriesOnBall_polydiscCauchy {d : ℕ}
    {f : (Fin d → ℂ) → E} {c : Fin d → ℂ} {R M : ℝ} (hR : 0 < R)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i))
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) :
    HasFPowerSeriesOnBall f (polydiscCauchySeries f c R) c
      (ENNReal.ofReal (R / 2)) := by
  let r : ℝ≥0 := ⟨R / 2, div_nonneg hR.le zero_le_two⟩
  have hrENN : (r : ℝ≥0∞) = ENNReal.ofReal (R / 2) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  have hr0 : 0 < (r : ℝ) := by
    change 0 < R / 2
    positivity
  have hrR : (r : ℝ) < R := by
    change R / 2 < R
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [← hrENN]
    exact polydiscCauchySeries f c R |>.le_radius_of_summable_norm
      (summable_norm_polydiscCauchySeries_mul_pow hR hr0.le hrR hM)
  · exact ENNReal.ofReal_pos.mpr hr0
  intro h hh
  rw [← hrENN] at hh
  rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_lt_coe] at hh
  have hhreal : ‖h‖ < (r : ℝ) := by exact_mod_cast hh
  have hhi : ∀ i, ‖h i‖ < R := fun i =>
    (norm_le_pi_norm h i).trans_lt (hhreal.trans hrR)
  have hs := hasSum_polydiscCauchySeries_integral hR hhi hfc hM
  have hcauchy := polydisc_cauchy (f := f) (c := c) (w := c + h) (R := R) hR (fun i => by
    simpa [Pi.add_apply] using hhi i) hfc hfa
  rw [← hcauchy]
  exact hs

private theorem analyticOnNhd_fin_of_analyticOnNhd_update {d : ℕ}
    {U : Set (Fin d → ℂ)} {f : (Fin d → ℂ) → E}
    (hU : IsOpen U) (hfc : ContinuousOn f U)
    (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  intro c hc
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hc)
  have hP : closedPolydisc c R ⊆ U := by
    rw [closedPolydisc_eq_closedBall hR.le]
    exact hRU
  have hfcP : ContinuousOn f (closedPolydisc c R) := hfc.mono hP
  have hfaP : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i) := fun z hz => hf z (hP hz)
  have hPcpt : IsCompact (closedPolydisc c R) := by
    rw [closedPolydisc_eq_closedBall hR.le]
    exact isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hPcpt.bddAbove_image hfcP.norm
  exact (hasFPowerSeriesOnBall_polydiscCauchy hR hfcP hfaP
    (fun z hz => hM (mem_image_of_mem _ hz))).analyticAt

/-- **Osgood's theorem, finite-product form.** A jointly continuous function on an open subset of
a finite product of copies of `ℂ` is jointly analytic when all of its one-coordinate restrictions
are analytic.

This is weaker than Hartogs' theorem, which drops the continuity hypothesis. Continuity is
present in every current application in this library. -/
theorem analyticOnNhd_pi_of_analyticOnNhd_update
    {ι : Type*} [Fintype ι] {U : Set (ι → ℂ)} {f : (ι → ℂ) → E}
    (hU : IsOpen U) (hfc : ContinuousOn f U)
    (hf : ∀ z ∈ U, ∀ i,
      AnalyticAt ℂ (fun w => f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let L : (Fin (Fintype.card ι) → ℂ) ≃L[ℂ] (ι → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : ι => ℂ) e
  let V : Set (Fin (Fintype.card ι) → ℂ) := L ⁻¹' U
  let g : (Fin (Fintype.card ι) → ℂ) → E := f ∘ L
  have hV : IsOpen V := hU.preimage L.continuous
  have hgc : ContinuousOn g V :=
    hfc.comp L.continuous.continuousOn (fun _ hz => hz)
  have hL_apply (z : Fin (Fintype.card ι) → ℂ)
      (j : Fin (Fintype.card ι)) : L z (e j) = z j := by
    change (Equiv.piCongrLeft (fun _ : ι => ℂ) e) z (e j) = z j
    exact Equiv.piCongrLeft_apply_apply (fun _ : ι => ℂ) e z j
  have hL_update (z : Fin (Fintype.card ι) → ℂ)
      (j : Fin (Fintype.card ι)) (w : ℂ) :
      L (update z j w) = update (L z) (e j) w := by
    funext i
    obtain ⟨k, rfl⟩ := e.surjective i
    by_cases hkj : k = j
    · subst k
      simp [hL_apply]
    · have hek : e k ≠ e j := fun he => hkj (e.injective he)
      simp [hkj, hek, hL_apply]
  have hga : ∀ z ∈ V, ∀ j,
      AnalyticAt ℂ (fun w => g (update z j w)) (z j) := by
    intro z hz j
    have h := hf (L z) hz (e j)
    convert h using 1
    · funext w
      simp only [g, Function.comp_apply]
      rw [hL_update]
    · exact (hL_apply z j).symm
  have hg := analyticOnNhd_fin_of_analyticOnNhd_update hV hgc hga
  intro z hz
  have hzV : L.symm z ∈ V := by
    change L (L.symm z) ∈ U
    simpa
  have hcomp : AnalyticAt ℂ (g ∘ ⇑L.symm.toContinuousLinearMap) z :=
    AnalyticAt.compContinuousLinearMap (u := L.symm.toContinuousLinearMap)
      (hg (L.symm z) hzV)
  simpa [g, Function.comp_def] using hcomp


end SeveralComplexVariables

end
