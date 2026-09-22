/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Basic
public import Carlson.S
public import Analysis.SpecialFunctions.Gamma
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Laplace representation of Carlson's R-function

This file develops the inverse confluence formula of [Carl77, Theorem 5.10-2], which expresses
`R` as a one-dimensional Laplace--Mellin transform of `S`.
The scalar complex-rate Gamma integral is supplied by `Analysis.SpecialFunctions.Gamma`.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.10,
  Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
@[expose] public noncomputable section CarlsonR
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The regularized Laplace--Mellin expression in Carlson's inverse confluence formula. -/
def regCarlsonRLaplaceIntegral (a : ℂ) (b z : ι → ℂ) : ℂ :=
  1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
    (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)

/-- The unregularized Laplace--Mellin expression in Carlson's inverse confluence formula. -/
def carlsonRLaplaceIntegral (a : ℂ) (b z : ι → ℂ) : ℂ :=
  1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
    (y : ℂ) ^ (a - 1) * carlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)

/-- Regularization in the Dirichlet parameters commutes with Carlson's one-dimensional
Laplace--Mellin construction. -/
theorem carlsonRLaplaceIntegral_eq_Gamma_mul_reg (a : ℂ) (b z : ι → ℂ) :
    carlsonRLaplaceIntegral a b z =
      Gamma (∑ i, b i) * regCarlsonRLaplaceIntegral a b z := by
  simp only [carlsonRLaplaceIntegral, regCarlsonRLaplaceIntegral, carlsonSIntegral]
  calc
    1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
        (y : ℂ) ^ (a - 1) *
          (Gamma (∑ i, b i) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) =
      1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
        Gamma (∑ i, b i) *
          ((y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) := by
        congr 2
        funext y
        ring
    _ = 1 / Gamma a * (Gamma (∑ i, b i) * ∫ y : ℝ in Set.Ioi 0,
        (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) := by
          rw [integral_const_mul]
    _ = Gamma (∑ i, b i) * (1 / Gamma a * ∫ y : ℝ in Set.Ioi 0,
        (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) := by
          ring

/-- A positive lower bound for the real part of the affine kernel over the closed simplex, for
nodes in the right-half-plane domain. -/
theorem exists_pos_le_re_carlsonAffineForm [Nonempty ι] {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    ∃ r : ℝ, 0 < r ∧ ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      r ≤ (carlsonAffineForm z u).re := by
  classical
  let s : Finset ℝ := Finset.univ.image (fun i => (z i).re)
  have hs : s.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  refine ⟨s.min' hs, ?_, fun u hu => ?_⟩
  · rcases Finset.mem_image.mp (Finset.min'_mem s hs) with ⟨i, -, hi⟩
    rw [← hi]
    exact hz i
  · have hre : (carlsonAffineForm z u).re = ∑ i, u i * (z i).re := by
      simp [carlsonAffineForm, mul_re]
    rw [hre]
    calc
      s.min' hs = ∑ i, u i * s.min' hs := by rw [← Finset.sum_mul, hu.2, one_mul]
      _ ≤ ∑ i, u i * (z i).re := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left
          (Finset.min'_le s _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)) (hu.1 i)

/-- The product kernel of Carlson's Laplace--Mellin representation: the Mellin weight in the
radial variable times the Dirichlet density and the exponential of the affine form. -/
private def laplaceKernel (a : ℂ) (b z : ι → ℂ) (p : ℝ × (ι → ℝ)) : ℂ :=
  (p.1 : ℂ) ^ (a - 1) *
    (regDirichletDensity b p.2 * exp (-(p.1 : ℂ) * carlsonAffineForm z p.2))

/-- The product of Lebesgue measure on the positive half-line and the simplex measure. -/
private abbrev laplaceMeasure (ι : Type*) [Fintype ι] : Measure (ℝ × (ι → ℝ)) :=
  (volume.restrict (Set.Ioi (0 : ℝ))).prod
    (MeasureTheory.Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι))

/-- The Laplace kernel is strongly measurable on the product of the half-line and the simplex. -/
private theorem aestronglyMeasurable_laplaceKernel (a : ℂ) (b z : ι → ℂ) :
    AEStronglyMeasurable (laplaceKernel a b z) (laplaceMeasure ι) := by
  have hk : ContinuousOn (fun p : ℝ × (ι → ℝ) =>
      (p.1 : ℂ) ^ (a - 1) * exp (-(p.1 : ℂ) * carlsonAffineForm z p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    have hy : ContinuousAt (fun q : ℝ × (ι → ℝ) => (q.1 : ℂ)) p := by
      simpa only [Function.comp_def] using
        (continuous_ofReal.comp continuous_fst).continuousAt
    have hW : ContinuousAt (fun q : ℝ × (ι → ℝ) => carlsonAffineForm z q.2) p := by
      simpa only [Function.comp_def] using
        ((continuous_carlsonAffineForm z).comp continuous_snd).continuousAt
    apply ContinuousAt.mul
    · exact (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hp.1)).comp_of_eq hy rfl
    · exact continuous_exp.continuousAt.comp (hy.neg.mul hW)
  unfold laplaceMeasure
  rw [Measure.prod_restrict]
  have hmeas : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι) :=
    measurableSet_Ioi.prod (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  convert (hk.aestronglyMeasurable hmeas).mul
    ((measurable_regDirichletDensity b).comp measurable_snd).aestronglyMeasurable using 1
  ext p
  simp only [laplaceKernel, Pi.mul_apply, Function.comp_apply]
  ring

/-- Pointwise domination of the Laplace kernel by a product kernel with a constant decay rate,
almost everywhere on the product of the half-line and the simplex. -/
private theorem norm_laplaceKernel_le {a : ℂ} {b z : ι → ℂ} {r : ℝ}
    (hr : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, r ≤ (carlsonAffineForm z u).re) :
    ∀ᵐ p ∂(laplaceMeasure ι), ‖laplaceKernel a b z p‖ ≤
      ‖((p.1 : ℂ) ^ (a - 1) * exp (-(r * p.1))) * regDirichletDensity b p.2‖ := by
  have hp_mem : ∀ᵐ p ∂(laplaceMeasure ι),
      p.1 ∈ Set.Ioi (0 : ℝ) ∧ p.2 ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
    unfold laplaceMeasure
    rw [Measure.prod_restrict]
    exact ae_restrict_mem
      (measurableSet_Ioi.prod (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet)
  filter_upwards [hp_mem] with p hp
  rw [show ‖laplaceKernel a b z p‖ = ‖regDirichletDensity b p.2‖ *
      (Real.exp (-(carlsonAffineForm z p.2).re * p.1) * p.1 ^ (a.re - 1)) by
    rw [show laplaceKernel a b z p = regDirichletDensity b p.2 *
        ((p.1 : ℂ) ^ (a - 1) * exp (-(p.1 : ℂ) * carlsonAffineForm z p.2)) by
          unfold laplaceKernel; ring,
      norm_mul, norm_cpow_mul_exp_neg_mul hp.1]]
  rw [show ‖((p.1 : ℂ) ^ (a - 1) * exp (-(r * p.1))) * regDirichletDensity b p.2‖ =
      ‖regDirichletDensity b p.2‖ * (Real.exp (-r * p.1) * p.1 ^ (a.re - 1)) by
    rw [show ((p.1 : ℂ) ^ (a - 1) * exp (-(r * p.1))) * regDirichletDensity b p.2 =
        regDirichletDensity b p.2 * ((p.1 : ℂ) ^ (a - 1) * exp (-(p.1 : ℂ) * (r : ℂ))) by
          have he : (-(r * p.1) : ℂ) = -(p.1 : ℂ) * (r : ℂ) := by
            simp [mul_comm]
          rw [he]
          ring,
      norm_mul, norm_cpow_mul_exp_neg_mul hp.1]
    simp [mul_comm]]
  have hyp : 0 < p.1 := hp.1
  refine mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hyp.le _)) (norm_nonneg _)
  exact Real.exp_le_exp.mpr (by nlinarith [hr p.2 hp.2])

/-- The Laplace kernel is integrable on the product of the half-line and the simplex. -/
private theorem integrable_laplaceKernel [Nonempty ι] {a : ℂ} (ha : 0 < a.re) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    Integrable (laplaceKernel a b z) (laplaceMeasure ι) := by
  obtain ⟨r, hr, hr_le⟩ := exists_pos_le_re_carlsonAffineForm hz
  have hG : Integrable (fun p : ℝ × (ι → ℝ) =>
      ((p.1 : ℂ) ^ (a - 1) * exp (-(r * p.1))) * regDirichletDensity b p.2)
      (laplaceMeasure ι) := by
    have hy := integrableOn_cpow_mul_exp_neg_mul_Ioi_ofReal (a := a) (r := r) ha hr
    have hu : Integrable (regDirichletDensity b)
        (MeasureTheory.Measure.stdSimplexMeasure.restrict
          (Convexity.StdSimplex.coordinateSet ℝ ι)) :=
      integrableOn_regDirichletDensity b hb
    unfold laplaceMeasure
    simpa using hy.mul_prod hu
  exact Integrable.mono' hG.norm (aestronglyMeasurable_laplaceKernel a b z)
    (norm_laplaceKernel_le hr_le)

/-- The simplex integral of the Laplace kernel at fixed radial variable is the Mellin weight
times the regularized `S`-integral at the scaled nodes. -/
private theorem integral_laplaceKernel_snd (a : ℂ) (b z : ι → ℂ) (y : ℝ) :
    (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i) =
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, laplaceKernel a b z (y, u)
        ∂MeasureTheory.Measure.stdSimplexMeasure := by
  have hS : regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i) =
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, regDirichletDensity b u *
        exp (-(y : ℂ) * carlsonAffineForm z u) ∂MeasureTheory.Measure.stdSimplexMeasure := by
    unfold regCarlsonSIntegral regCarlsonDirichletAverage regDirichletIntegral
    apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    intro u hu
    have haff : carlsonAffineForm (fun i ↦ -(y : ℂ) * z i) u =
        -(y : ℂ) * carlsonAffineForm z u := by
      simpa using carlsonAffineForm_affine hu (-(y : ℂ)) 0 z
    change regDirichletDensity b u * exp (carlsonAffineForm (fun i ↦ -(y : ℂ) * z i) u) =
      regDirichletDensity b u * exp (-(y : ℂ) * carlsonAffineForm z u)
    rw [haff]
  rw [hS, ← integral_const_mul]
  rfl

/-- The radial integral of the Laplace kernel at a fixed simplex point is evaluated by the
complex-rate Gamma integral. -/
private theorem integral_laplaceKernel_fst {a : ℂ} (ha : 0 < a.re) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    (∫ y in Set.Ioi (0 : ℝ), laplaceKernel a b z (y, u)) =
      regDirichletDensity b u * (carlsonAffineForm z u ^ (-a) * Gamma a) := by
  calc
    (∫ y in Set.Ioi (0 : ℝ), laplaceKernel a b z (y, u)) = regDirichletDensity b u *
        ∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * carlsonAffineForm z u) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      unfold laplaceKernel
      ring
    _ = regDirichletDensity b u * (carlsonAffineForm z u ^ (-a) * Gamma a) := by
      rw [integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos ha
        (carlsonAffineForm_mem_rightHalfPlane hz hu)]

/-- Carlson's inverse confluence formula, Theorem 5.10-2, in regularized form. The proof
exchanges the order of integration in the Laplace kernel and evaluates the radial integral by
the complex-rate Gamma integral. -/
theorem regCarlsonRIntegral_eq_regCarlsonRLaplaceIntegral
    {a : ℂ} (ha : 0 < a.re) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral (-a) b z = regCarlsonRLaplaceIntegral a b z := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [regCarlsonRIntegral, regCarlsonDirichletAverage, regDirichletIntegral,
        regCarlsonRLaplaceIntegral, regCarlsonSIntegral,
        MeasureTheory.Measure.stdSimplexMeasure_empty]
  | inr hι =>
    let _ := hι
    have hswap :
        (∫ y, ∫ u, laplaceKernel a b z (y, u)
            ∂(MeasureTheory.Measure.stdSimplexMeasure.restrict
              (Convexity.StdSimplex.coordinateSet ℝ ι))
          ∂(volume.restrict (Set.Ioi (0 : ℝ)))) =
          ∫ u, ∫ y, laplaceKernel a b z (y, u) ∂(volume.restrict (Set.Ioi (0 : ℝ)))
            ∂(MeasureTheory.Measure.stdSimplexMeasure.restrict
              (Convexity.StdSimplex.coordinateSet ℝ ι)) :=
      integral_integral_swap (f := fun y u => laplaceKernel a b z (y, u))
        (integrable_laplaceKernel ha hb hz)
    have hout : (∫ y : ℝ in Set.Ioi 0,
          (y : ℂ) ^ (a - 1) * regCarlsonSIntegral b (fun i ↦ -(y : ℂ) * z i)) =
        Gamma a * regCarlsonRIntegral (-a) b z := by
      simp_rw [integral_laplaceKernel_snd a b z]
      rw [hswap]
      unfold regCarlsonRIntegral regCarlsonDirichletAverage regDirichletIntegral
      rw [← integral_const_mul]
      apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
      intro u hu
      dsimp only
      rw [integral_laplaceKernel_fst ha b hz hu]
      ring
    rw [regCarlsonRLaplaceIntegral, hout]
    field_simp [Gamma_ne_zero_of_re_pos ha]

/-- Carlson's inverse confluence formula in the native unregularized normalization. -/
theorem carlsonRIntegral_eq_carlsonRLaplaceIntegral
    {a : ℂ} (ha : 0 < a.re) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    carlsonRIntegral (-a) b z = carlsonRLaplaceIntegral a b z := by
  rw [carlsonRIntegral_eq_Gamma_mul_reg,
    carlsonRLaplaceIntegral_eq_Gamma_mul_reg,
    regCarlsonRIntegral_eq_regCarlsonRLaplaceIntegral ha hb hz]

end Carlson
end CarlsonR
