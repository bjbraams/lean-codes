/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.Face
public import SimplexMellin.Lattice
public import SimplexMellin.Uniqueness
public import Dirichlet.GammaPoles

/-!
# Boundary traces and poles of the simplex Mellin transform

The unnormalized transform of a smooth simplex kernel continues as the product of its
entire regularized transform and the coordinate Gamma factors. It is analytic away from
the nonpositive integral coordinate hyperplanes. Near their intersections, it has a
jointly analytic numerator divided by the product of the simple coordinate denominators.

The one-variable pole and removability results specialize `Dirichlet.GammaPoles`.
The face formulas identify transverse residues with tangential boundary jets. At a zero
parameter, removability for all positive complementary parameters is equivalent to the
vanishing of the kernel's trace on that face, by moment determination.

All pole statements concern punctured germs. Gamma's totalized values at its poles are
not analytic extension values. At intersections, the joint numerator describes the pole
structure; a slice lying in a different pole hyperplane can have totalized zero values.
The face-trace criterion therefore assumes regular complementary parameters.

## Main results

* `simplexMomentContinuation_eq_native` and `simplexMomentContinuation_eq_sum`.
* `simplexMomentContinuation_eq_poleNumerator_div` and
  `analyticAt_simplexMomentPoleNumerator`: joint normal-crossing pole form.
* `tendsto_mul_simplexMomentContinuation_update_eq_sum_face`: boundary-jet residues.
* `exists_analyticAt_simplexMomentContinuation_update_iff`: transverse removability.
* `removable_zero_hyperplane_iff_face_eq_zero`: the boundary-trace criterion.
* `tendsto_mul_simplexMoment_update_nhdsGT_zero`: the native positive-parameter boundary limit.
-/

open Complex MeasureTheory Set Filter Function
open scoped Topology
@[expose] public noncomputable section
namespace Dirichlet
variable {ι : Type*} [Fintype ι]
open scoped Classical

/-- The Gamma-normalized entire transform, agreeing with the native simplex moment integral
on the convergence region. At poles this definition uses the totalized Gamma values. -/
def simplexMomentContinuation (g : (ι → ℝ) → ℂ) (hg : SmoothNearStdSimplex g)
    (b : ι → ℂ) : ℂ := (∏ i, Gamma (b i)) * regDirichletTransform g hg b

/-- The continued moment transform agrees with the convergent integral. -/
theorem simplexMomentContinuation_eq_native {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    simplexMomentContinuation g hg b = simplexMoment b g := by
  rw [simplexMomentContinuation, regDirichletTransform_eq_integral hg hb]
  have he := simplexMoment_eq_prod_Gamma_mul g 0 b (fun i => by
    simpa using Gamma_ne_zero_of_re_pos (hb i))
  have hdiv : divMonomial 0 g = g := funext fun u => by simp [divMonomial]
  simpa only [Nat.cast_zero, add_zero, hdiv] using he.symm

/-- Coordinate slices of the continued moment transform are one-variable meromorphic. -/
theorem meromorphic_simplexMomentContinuation_update {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (b : ι → ℂ) (i : ι) :
    Meromorphic (fun z : ℂ => simplexMomentContinuation g hg (update b i z)) := by
  intro z
  unfold simplexMomentContinuation
  apply MeromorphicAt.mul
  · apply MeromorphicAt.fun_prod
    intro j _
    exact (Meromorphic.Gamma _).comp_analyticAt
      (analyticAt_pi_iff.mp (analyticAt_update_apply b i z) j)
  · exact ((analyticOnNhd_regDirichletTransform hg) _ (mem_univ _)).comp
      (analyticAt_update_apply b i z) |>.meromorphicAt

/-- A coordinate slice separates its only varying Gamma factor. -/
theorem simplexMomentContinuation_update {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g)
    (b : ι → ℂ) (i : ι) (z : ℂ) :
    simplexMomentContinuation g hg (update b i z) = Gamma z *
      ((∏ j ∈ Finset.univ.erase i, Gamma (b j)) *
        regDirichletTransform g hg (update b i z)) := by
  unfold simplexMomentContinuation
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), update_self]
  rw [mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro j hj
  rw [update_of_ne (Finset.mem_erase.mp hj).1]

/-- The regularized numerator of a coordinate slice is analytic at every point. -/
theorem analyticAt_simplexMoment_slice_numerator {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (b : ι → ℂ) (i : ι) (z : ℂ) :
    AnalyticAt ℂ (fun z => (∏ j ∈ Finset.univ.erase i, Gamma (b j)) *
      regDirichletTransform g hg (update b i z)) z :=
  analyticAt_const.mul (((analyticOnNhd_regDirichletTransform hg) _ (mem_univ _)).comp
    (analyticAt_update_apply b i z))

/-- Multiplication by `z + m` extracts the transverse residue at `b i = -m`. -/
theorem tendsto_mul_simplexMomentContinuation_update {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (b : ι → ℂ) (i : ι) (m : ℕ) :
    Tendsto (fun z : ℂ => (z + m) * simplexMomentContinuation g hg (update b i z))
      (𝓝[≠] (-(m : ℂ)))
      (𝓝 (((-1 : ℂ) ^ m / m.factorial) *
        ((∏ j ∈ Finset.univ.erase i, Gamma (b j)) *
          regDirichletTransform g hg (update b i (-m))))) := by
  simpa only [simplexMomentContinuation_update] using
    tendsto_mul_Gamma_mul m (analyticAt_simplexMoment_slice_numerator hg b i (-m)).continuousAt

/-- A transverse Gamma pole is removable exactly when the regularized slice vanishes there,
provided no complementary Gamma factor is a pole. -/
theorem exists_analyticAt_simplexMomentContinuation_update_iff {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (b : ι → ℂ) (i : ι) (m : ℕ)
    (hreg : ∀ j, j ≠ i → IsGammaRegular (b j)) :
    (∃ H : ℂ → ℂ, AnalyticAt ℂ H (-m) ∧
      (fun z => simplexMomentContinuation g hg (update b i z)) =ᶠ[𝓝[≠] (-m : ℂ)] H) ↔
      regDirichletTransform g hg (update b i (-m)) = 0 := by
  have hprod : (∏ j ∈ Finset.univ.erase i, Gamma (b j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => Gamma_ne_zero (hreg j (Finset.mem_erase.mp hj).1)
  simpa only [simplexMomentContinuation_update, mul_eq_zero, hprod, false_or] using
    exists_analyticAt_Gamma_mul_iff m (analyticAt_simplexMoment_slice_numerator hg b i (-m))
/-- Analyticity away from the coordinate hyperplanes of nonpositive integral parameters. -/
theorem analyticAt_simplexMomentContinuation {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (b : ι → ℂ) (hreg : ∀ i, IsGammaRegular (b i)) :
    AnalyticAt ℂ (simplexMomentContinuation g hg) b := by
  apply AnalyticAt.mul
  · apply Finset.analyticAt_fun_prod
    intro i _
    simpa only [mul_one] using
      (analyticAt_Gamma_mul_comp (c := fun q : ι → ℂ => q i) (F := fun _ => 1)
        ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b)
        analyticAt_const (hreg i))
  · exact analyticOnNhd_regDirichletTransform hg b (mem_univ _)

/-- An analytic numerator for simultaneous coordinate poles of the moment transform. -/
def simplexMomentPoleNumerator (g : (ι → ℝ) → ℂ) (hg : SmoothNearStdSimplex g)
    (s : Finset ι) (m : ι → ℕ) (b : ι → ℂ) : ℂ :=
    (∏ i ∈ s, GammaPoleFactor (m i) (b i)) *
      (∏ i ∈ sᶜ, Gamma (b i)) * regDirichletTransform g hg b

/-- The continued transform has at most simple coordinate poles, including their intersections.
The identity uses totalized values at the zero denominators; analytic germs use punctured values. -/
theorem simplexMomentContinuation_eq_poleNumerator_div {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (s : Finset ι) (m : ι → ℕ) (b : ι → ℂ) :
    simplexMomentContinuation g hg b = simplexMomentPoleNumerator g hg s m b /
      (∏ i ∈ s, (b i + m i)) := by
  unfold simplexMomentContinuation simplexMomentPoleNumerator
  rw [← Finset.prod_mul_prod_compl s (fun i => Gamma (b i))]
  have hΓ : (∏ i ∈ s, Gamma (b i)) =
      (∏ i ∈ s, GammaPoleFactor (m i) (b i)) / (∏ i ∈ s, (b i + m i)) := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun i _ => Gamma_eq_GammaPoleFactor_div (m i) (b i)
  rw [hΓ]
  ring

/-- The pole numerator is jointly analytic near a crossing when all remaining parameters
avoid Gamma poles. -/
theorem analyticAt_simplexMomentPoleNumerator {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (s : Finset ι) (m : ι → ℕ) (b : ι → ℂ)
    (hp : ∀ i ∈ s, b i = -m i) (hreg : ∀ i ∉ s, IsGammaRegular (b i)) :
    AnalyticAt ℂ (simplexMomentPoleNumerator g hg s m) b := by
  apply AnalyticAt.mul
  · apply AnalyticAt.mul
    · apply Finset.analyticAt_fun_prod
      intro i hi
      exact (analyticAt_GammaPoleFactor (m i)).comp_of_eq
        ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b) (hp i hi)
    · apply Finset.analyticAt_fun_prod
      intro i hi
      simpa only [mul_one] using
        (analyticAt_Gamma_mul_comp (c := fun q : ι → ℂ => q i) (F := fun _ => 1)
          ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b)
          analyticAt_const (hreg i (Finset.mem_compl.mp hi)))
  · exact analyticOnNhd_regDirichletTransform hg b (mem_univ _)

/-- The numerator at a pole crossing is the product of Gamma residues and the regularized
transform there; the face formulas express the latter through boundary jets. -/
theorem simplexMomentPoleNumerator_apply {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (s : Finset ι) (m : ι → ℕ) (b : ι → ℂ)
    (hp : ∀ i ∈ s, b i = -m i) :
    simplexMomentPoleNumerator g hg s m b =
      (∏ i ∈ s, (-1 : ℂ) ^ m i / (m i).factorial) *
        (∏ i ∈ sᶜ, Gamma (b i)) * regDirichletTransform g hg b := by
  unfold simplexMomentPoleNumerator
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  rw [hp i hi, GammaPoleFactor_neg_nat]

/-- At `b i = -m`, the transverse residue is explicitly determined by the tangential
boundary jets of the kernel on the face `u i = 0`. -/
theorem tendsto_mul_simplexMomentContinuation_update_eq_sum_face
    {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g) (b : ι → ℂ)
    (i : ι) (j : {j : ι // j ≠ i}) (m : ℕ) :
    Tendsto (fun z : ℂ => (z + m) * simplexMomentContinuation g hg (update b i z))
      (𝓝[≠] (-(m : ℂ)))
      (𝓝 (((-1 : ℂ) ^ m / m.factorial) * ((∏ k ∈ Finset.univ.erase i, Gamma (b k)) *
        ∑ p ∈ Finset.antidiagonal m, (m.choose p.1 : ℂ) *
          regDirichletTransform
            (stdSimplexFaceRestriction i ((stdSimplexTangentDeriv (j : ι) i)^[p.1] g))
            ((hg.iterate_tangentDeriv j i p.1).faceRestriction i)
            (fun q => b q - (Pi.single j (p.2 : ℂ) : {k : ι // k ≠ i} → ℂ) q)))) := by
  have hupdate (z : ℂ) (q : {k : ι // k ≠ i}) : update b i z q = b q := by
    rw [update_of_ne q.property]
  have hface := regDirichletTransform_eq_sum_face hg i j m
    (b := update b i (-m)) (by simp)
  have hlim := tendsto_mul_simplexMomentContinuation_update hg b i m
  rw [hface] at hlim
  simpa only [hupdate] using hlim

/-- The residue at a zero parameter is the complementary Gamma product times the continued
transform of the boundary trace. -/
theorem tendsto_mul_simplexMomentContinuation_update_zero [Nontrivial ι]
    {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g) (b : ι → ℂ) (i : ι) :
    Tendsto (fun z : ℂ => z * simplexMomentContinuation g hg (update b i z))
      (𝓝[≠] 0) (𝓝 ((∏ j ∈ Finset.univ.erase i, Gamma (b j)) *
        regDirichletTransform (stdSimplexFaceRestriction i g) (hg.faceRestriction i)
          (fun q => b q))) := by
  have hupdate (z : ℂ) (q : {k : ι // k ≠ i}) : update b i z q = b q := by
    rw [update_of_ne q.property]
  have hface := (isRegDirichletContinuation_transform hg).face_zero i
    (isRegDirichletContinuation_transform (hg.faceRestriction i)) hg.continuousOn
    (b := update b i 0) (by simp)
  have hlim := tendsto_mul_simplexMomentContinuation_update hg b i 0
  simpa only [Nat.cast_zero, neg_zero, add_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul, hface, hupdate] using hlim

/-- At a zero parameter with regular complementary parameters, removability is equivalent
to vanishing of the corresponding continued face transform. -/
theorem exists_analyticAt_simplexMomentContinuation_update_zero_iff [Nontrivial ι]
    {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g) (b : ι → ℂ) (i : ι)
    (hreg : ∀ j, j ≠ i → IsGammaRegular (b j)) :
    (∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      (fun z => simplexMomentContinuation g hg (update b i z)) =ᶠ[𝓝[≠] 0] H) ↔
      regDirichletTransform (stdSimplexFaceRestriction i g) (hg.faceRestriction i)
        (fun q => b q) = 0 := by
  have hupdate (z : ℂ) (q : {k : ι // k ≠ i}) : update b i z q = b q := by
    rw [update_of_ne q.property]
  have hface := (isRegDirichletContinuation_transform hg).face_zero i
    (isRegDirichletContinuation_transform (hg.faceRestriction i)) hg.continuousOn
    (b := update b i 0) (by simp)
  simpa only [Nat.cast_zero, neg_zero, hface, hupdate] using
    exists_analyticAt_simplexMomentContinuation_update_iff hg b i 0 hreg

/-- The zero-parameter poles are removable for all positive complementary parameters exactly
when the boundary trace of the kernel vanishes on that face. -/
theorem removable_zero_hyperplane_iff_face_eq_zero [Nontrivial ι]
    {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g) (i : ι) :
    (∀ b : ι → ℂ, (∀ j, j ≠ i → 0 < (b j).re) →
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
        (fun z => simplexMomentContinuation g hg (update b i z)) =ᶠ[𝓝[≠] 0] H) ↔
      EqOn (stdSimplexFaceRestriction i g) 0
        (Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i}) := by
  constructor
  · intro hrem
    apply (isRegDirichletContinuation_transform (hg.faceRestriction i)).eqOn_of_eq_natCast_add_one
      isRegDirichletContinuation_zero (hg.faceRestriction i).continuousOn continuousOn_const
    intro n
    let b : ι → ℂ := fun j => if h : j = i then 0 else (n ⟨j, h⟩ : ℂ) + 1
    have hb : ∀ j, j ≠ i → 0 < (b j).re := by
      intro j hj
      simp only [b, dite_eq_right hj, add_re, natCast_re, one_re]
      positivity
    have hz := (exists_analyticAt_simplexMomentContinuation_update_zero_iff hg b i
      (fun j hj => IsGammaRegular.of_re_pos (hb j hj))).mp (hrem b hb)
    have hparam : (fun q : {j : ι // j ≠ i} => b q) = fun q => (n q : ℂ) + 1 := by
      funext q
      simp only [b, dite_eq_right q.property]
    simpa only [hparam] using hz
  · intro htrace b hb
    apply (exists_analyticAt_simplexMomentContinuation_update_zero_iff hg b i
      (fun j hj => IsGammaRegular.of_re_pos (hb j hj))).mpr
    have hz : IsRegDirichletContinuation (stdSimplexFaceRestriction i g) (fun _ => 0) :=
      isRegDirichletContinuation_zero.congr htrace.symm
    exact congrFun ((isRegDirichletContinuation_transform (hg.faceRestriction i)).eq hz) _

/-- The continued transform satisfies the simplex sum-shift equation away from Gamma poles.
At exceptional parameters the equation is an identity of germs rather than totalized values. -/
theorem simplexMomentContinuation_eq_sum {g : (ι → ℝ) → ℂ}
    (hg : SmoothNearStdSimplex g) (b : ι → ℂ) (hreg : ∀ i, IsGammaRegular (b i)) :
    simplexMomentContinuation g hg b =
      ∑ i, simplexMomentContinuation g hg (addDirichletUnit b i) := by
  have hshift := (isRegDirichletContinuation_transform hg).sum_shift hg.continuousOn b
  unfold simplexMomentContinuation
  rw [hshift, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hΓ : (∏ j, Gamma (addDirichletUnit b i j)) = (∏ j, Gamma (b j)) * b i := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun j => Gamma (b j)) (Finset.mem_univ i)]
    have hi0 : b i ≠ 0 := by simpa using hreg i 0
    have hp : (∏ j ∈ Finset.univ.erase i, Gamma (addDirichletUnit b i j)) =
        ∏ j ∈ Finset.univ.erase i, Gamma (b j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [addDirichletUnit, update_of_ne (Finset.mem_erase.mp hj).1]
    rw [hp]
    simp only [addDirichletUnit, update_self, Gamma_add_one _ hi0]
    ring
  rw [hΓ]
  ring

/-- From the native positive convergence region, multiplying by the parameter tending to zero
recovers the unnormalized transform of the boundary trace. -/
theorem tendsto_mul_simplexMoment_update_nhdsGT_zero [Nontrivial ι]
    {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g) (b : ι → ℂ) (i : ι)
    (hb : ∀ j, j ≠ i → 0 < (b j).re) :
    Tendsto (fun t : ℝ => (t : ℂ) * simplexMoment (update b i (t : ℂ)) g)
      (𝓝[>] 0) (𝓝 (simplexMoment (fun q : {j : ι // j ≠ i} => b q)
        (stdSimplexFaceRestriction i g))) := by
  have hreal : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · exact continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact ofReal_ne_zero.mpr (ne_of_gt ht)
  have hlim := (tendsto_mul_simplexMomentContinuation_update_zero hg b i).comp hreal
  have hprod : (∏ j ∈ Finset.univ.erase i, Gamma (b j)) =
      ∏ j : {j : ι // j ≠ i}, Gamma (b j) :=
    Finset.prod_subtype _ (by simp) _
  rw [hprod, ← simplexMomentContinuation,
    simplexMomentContinuation_eq_native (hg.faceRestriction i) (fun q => hb q q.property)] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htB : update b i (t : ℂ) ∈ mvBetaConvergent := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [update_self, ofReal_re, mem_Ioi] using ht
    · rw [update_of_ne hji]
      exact hb j hji
  simp only [Function.comp_apply, simplexMomentContinuation_eq_native hg htB]

end Dirichlet

end
