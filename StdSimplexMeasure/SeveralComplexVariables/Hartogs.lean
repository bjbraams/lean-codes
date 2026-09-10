/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.MeasureTheory.Integral.TorusIntegral

/-!
# Separate and joint analyticity in finite products

This file is the proposed home for a finite-product form of Hartogs' theorem.  Its immediate
application is to functions on `ι → ℂ`: analyticity of every one-coordinate update should imply
joint analyticity on an open product domain.  More general binary-product and finite-product
forms can be added as the proof architecture becomes clear.

This is a temporary project home for material ultimately intended for a Mathlib location such as
`Mathlib.Analysis.Complex.SeveralVariables.Hartogs`.

## Main result

`analyticOnNhd_pi_of_analyticOnNhd_update` is presently Osgood's theorem: separate holomorphy
together with joint continuity implies joint analyticity on an open set in `ι → ℂ`.  The
classically stronger Hartogs theorem, which drops continuity and recovers local boundedness from
separate holomorphy, is not proved here.

The converse direction, extracting separate analyticity from joint analyticity, is already
largely supplied by composition with continuous linear coordinate maps.
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

lemma mem_closedPolydisc {n : ℕ} {c z : Fin n → ℂ} {R : ℝ} :
    z ∈ closedPolydisc c R ↔ ∀ i, z i ∈ closedBall (c i) R := by
  simp [closedPolydisc]

lemma closedPolydisc_eq_closedBall {n : ℕ} {c : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    closedPolydisc c R = closedBall c R :=
  (closedBall_pi c hR).symm

lemma torusMap_mem_closedPolydisc {n : ℕ} {c : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (θ : Fin n → ℝ) : torusMap c (fun _ => R) θ ∈ closedPolydisc c R := by
  intro i _
  simp [torusMap, mem_closedBall, dist_eq_norm, abs_of_nonneg hR]

lemma cons_mem_closedPolydisc {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} {x : ℂ}
    {y : Fin n → ℂ} (hx : x ∈ closedBall (c 0) R)
    (hy : y ∈ closedPolydisc (c ∘ Fin.succ) R) :
    Fin.cons x y ∈ closedPolydisc c R := by
  intro i _
  refine Fin.cases ?_ ?_ i
  · simpa [Fin.cons_zero] using hx
  · intro j
    simpa [Fin.cons_succ] using hy j (mem_univ _)

lemma continuous_torusMap {n : ℕ} (c : Fin n → ℂ) (R : ℝ) :
    Continuous (torusMap c (fun _ => R)) :=
  continuous_pi fun i => by
    simp only [torusMap]
    fun_prop

lemma two_pi_I_pow_ne_zero (n : ℕ) : ((2 * π * I : ℂ) ^ n) ≠ 0 :=
  pow_ne_zero _ two_pi_I_ne_zero

lemma torusMap_coord_norm {n : ℕ} {c : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (θ : Fin n → ℝ) (i : Fin n) :
    ‖torusMap c (fun _ => R) θ i - c i‖ = R := by
  simp [torusMap, abs_of_nonneg hR]

lemma cauchyKernel_ne_zero_on_torus {n : ℕ} {c w : Fin n → ℂ} {R : ℝ} {θ : Fin n → ℝ}
    {i : Fin n} (hR : 0 < R) (hw : ‖w i - c i‖ < R) :
    torusMap c (fun _ => R) θ i ≠ w i := by
  intro h
  have : ‖torusMap c (fun _ => R) θ i - c i‖ = R := torusMap_coord_norm hR.le θ i
  rw [h] at this
  exact hw.not_ge this.ge

/-! ### Cauchy's formula on a polydisc -/

omit [CompleteSpace E] in
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

/-- **Osgood's theorem, finite-product form.** A jointly continuous function on an open subset of
a finite product of copies of `ℂ` is jointly analytic when all of its one-coordinate restrictions
are analytic.

This is weaker than Hartogs' theorem, which drops the continuity hypothesis.  Continuity is
present in every current application in this library. -/
theorem analyticOnNhd_pi_of_analyticOnNhd_update
    {ι : Type*} [Fintype ι] {U : Set (ι → ℂ)} {f : (ι → ℂ) → E}
    (hU : IsOpen U) (hfc : ContinuousOn f U)
    (hf : ∀ z ∈ U, ∀ i,
      AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  /- `polydisc_cauchy` supplies the iterated Cauchy integral on a small closed polydisc.
  The remaining step is to expand the Cauchy kernel as a product of geometric series
  and package the result as a `FormalMultilinearSeries` on `ι → ℂ`. -/
  sorry

end SeveralComplexVariables

end
