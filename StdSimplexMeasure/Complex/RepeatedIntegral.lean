/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.Complex.Integral
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Repeated integration along complex segments

Segment integration is identified with Mathlib's curve integral. Its iterates are expressed
as simplex integrals with coalesced base nodes, for kernels continuous on a convex domain.
-/

open MeasureTheory

@[expose] public noncomputable section

namespace Complex

/-- Integration of a complex-valued function along the oriented segment from `a` to `x`. -/
def segmentIntegral (a x : ℂ) (f : ℂ → ℂ) : ℂ :=
  (x - a) * ∫ t in (0 : ℝ)..1, f (a + (t : ℂ) * (x - a))

/-- The repeated integration operator based at `a`, defined recursively by segment
integration. -/
def repeatedIntegral : ℕ → ℂ → (ℂ → ℂ) → ℂ → ℂ
  | 0, _, f, x => f x
  | n + 1, a, f, x => segmentIntegral a x (repeatedIntegral n a f)

/-- The zeroth repeated integral is the original function. -/
@[simp] theorem repeatedIntegral_zero (a : ℂ) (f : ℂ → ℂ) (x : ℂ) :
    repeatedIntegral 0 a f x = f x := rfl

/-- The successor step for the repeated integration operator. -/
@[simp] theorem repeatedIntegral_succ (n : ℕ) (a : ℂ) (f : ℂ → ℂ) (x : ℂ) :
    repeatedIntegral (n + 1) a f x =
      segmentIntegral a x (repeatedIntegral n a f) := rfl

/-- Segment integration agrees with Mathlib's curve integral of the associated one-form. -/
theorem segmentIntegral_eq_curveIntegral (a x : ℂ) (f : ℂ → ℂ) :
    segmentIntegral a x f =
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) (Path.segment a x) := by
  rw [curveIntegral_segment, segmentIntegral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simp [AffineMap.lineMap_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Complex.real_smul, add_comm]

/-- The unnormalized simplex integral with all base nodes coalesced at `a`. -/
private def coalescedSimplexIntegral (n : ℕ) (a x : ℂ) (f : ℂ → ℂ) : ℂ :=
  ∫ v in posSimplexFin n 1, f (a + ((1 - ∑ k, v k : ℝ) : ℂ) * (x - a))

/-- The coalesced coordinate integral is the simplex kernel integral at repeated base nodes. -/
private lemma simplexIntegral_coalesced (n : ℕ) (a x : ℂ) (f : ℂ → ℂ) :
    simplexIntegral (Fin.snoc (fun _ : Fin n => a) x) f = coalescedSimplexIntegral n a x f := by
  rw [simplexIntegral_eq_integral]
  congr 1
  funext v
  congr 1
  simp only [finSimplexPoint, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    ← Finset.sum_mul, ← ofReal_sum, ofReal_sub, ofReal_one]
  ring

/-- Slicing and dilating the simplex gives the recursion for coalesced integrals. -/
private lemma coalescedSimplexIntegral_succ
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : ContinuousOn f Ω)
    {a x : ℂ} (ha : a ∈ Ω) (hx : x ∈ Ω) (n : ℕ) :
    coalescedSimplexIntegral (n + 1) a x f =
      ∫ t in (0 : ℝ)..1, (t : ℂ) ^ n * coalescedSimplexIntegral n a (a + (t : ℂ) * (x - a)) f := by
  have hc : ContinuousOn
      (fun v : Fin (n + 1) → ℝ => f (a + ((1 - ∑ k, v k : ℝ) : ℂ) * (x - a)))
      (posSimplexFin (n + 1) 1) := by
    apply hf.comp (by fun_prop)
    intro v hv
    have hs : 0 ≤ ∑ k, v k := Finset.sum_nonneg (fun k _ => hv.1 k)
    have H := hΩconv ha hx hs (sub_nonneg.mpr hv.2)
      (by ring : (∑ k, v k) + (1 - ∑ k, v k) = 1)
    convert H using 1
    simp only [Complex.real_smul, ofReal_sub, ofReal_one]
    ring
  have hi := hc.integrableOn_compact (μ := volume) (isCompact_posSimplexFin_one (n + 1))
  unfold coalescedSimplexIntegral at ⊢
  rw [integral_posSimplexFin_snoc_outer _ hi]
  have hs : (∫ t in Set.Icc (0 : ℝ) 1,
      ∫ v in posSimplexFin n (1 - t),
        f (a + ((1 - ∑ k, Fin.snoc v t k : ℝ) : ℂ) * (x - a))) =
      ∫ t in Set.Icc (0 : ℝ) 1, ((1 - t : ℝ) : ℂ) ^ n *
        ∫ v in posSimplexFin n 1,
          f (a + ((1 - ∑ k, v k : ℝ) : ℂ) * ((a + ((1 - t : ℝ) : ℂ) * (x - a)) - a)) := by
    rw [integral_Icc_eq_integral_Ico, integral_Icc_eq_integral_Ico]
    apply setIntegral_congr_fun measurableSet_Ico
    intro t ht
    dsimp only
    rw [integral_posSimplexFin_scale _ (sub_pos.mpr ht.2)]
    simp only [Complex.real_smul, ofReal_pow]
    congr 1
    apply setIntegral_congr_fun (measurableSet_posSimplexFin _ _)
    intro v _
    dsimp only
    congr 1
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Pi.smul_apply,
      smul_eq_mul, ← Finset.mul_sum, ofReal_sub, ofReal_one, ofReal_add, ofReal_mul]
    ring
  rw [hs, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have H := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => (t : ℂ) ^ n * ∫ v in posSimplexFin n 1,
      f (a + ((1 - ∑ k, v k : ℝ) : ℂ) * ((a + (t : ℂ) * (x - a)) - a))) 1
    (a := (0 : ℝ)) (b := 1)
  simpa using H

/-- Repeated segment integration equals the coalesced simplex integral times the endpoint power. -/
private lemma repeatedIntegral_eq_coalesced
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : ContinuousOn f Ω)
    {a x : ℂ} (ha : a ∈ Ω) (hx : x ∈ Ω) (n : ℕ) :
    repeatedIntegral n a f x = (x - a) ^ n * coalescedSimplexIntegral n a x f := by
  induction n generalizing x with
  | zero =>
      simp only [repeatedIntegral_zero, pow_zero, one_mul, coalescedSimplexIntegral]
      rw [Measure.volume_pi_eq_dirac]
      simp [posSimplexFin]
  | succ n ih =>
      rw [repeatedIntegral_succ, segmentIntegral, coalescedSimplexIntegral_succ hΩconv hf ha hx]
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
      have hy : a + (t : ℂ) * (x - a) ∈ Ω := by
        have H := hΩconv ha hx (sub_nonneg.mpr ht'.2) ht'.1 (by ring : 1 - t + t = 1)
        convert H using 1
        simp only [Complex.real_smul, ofReal_sub, ofReal_one]
        ring
      rw [ih hy]
      simp only [add_sub_cancel_left, mul_pow, pow_succ]
      ring

/-- Repeated segment integration as a simplex integral with the base nodes coalesced.
Continuity on a convex domain suffices; analyticity is not required. -/
theorem repeatedIntegral_eq_simplexIntegral
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : ContinuousOn f Ω)
    {a x : ℂ} (ha : a ∈ Ω) (hx : x ∈ Ω) (n : ℕ) :
    repeatedIntegral n a f x =
      (x - a) ^ n * simplexIntegral (Fin.snoc (fun _ : Fin n => a) x) f := by
  rw [repeatedIntegral_eq_coalesced hΩconv hf ha hx, simplexIntegral_coalesced]

end Complex
