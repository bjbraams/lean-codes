/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.SimplexFTC
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Complex kernels integrated over simplices

Unnormalized simplex integrals, node symmetry, coalescence, and a simplex fundamental
theorem of calculus on convex complex domains. Only the general simplex foundation of
`StdSimplexMeasure` and Mathlib's complex analysis are used; there is no dependence on the
`ComplexAnalysis` library, on Dirichlet measures or on Carlson functions.
-/

open MeasureTheory

@[expose] public noncomputable section

namespace Complex

/-- The integral of a complex kernel over the simplex spanned by its nodes.
The coordinate measure has mass `1 / n!`; this is not a probability average. -/
def simplexIntegral (z : Fin (n + 1) → ℂ) (f : ℂ → ℂ) : ℂ :=
  ∫ u in Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)),
    f (∑ k, (u k : ℂ) * z k) ∂Measure.stdSimplexMeasure

/-- Compute a simplex kernel integral using its first `n` barycentric coordinates. -/
theorem simplexIntegral_eq_integral (z : Fin (n + 1) → ℂ) (f : ℂ → ℂ) :
    simplexIntegral z f =
      ∫ v in posSimplexFin n 1, f (∑ k, (finSimplexPoint v k : ℂ) * z k) :=
  integral_stdSimplex_fin _

/-- A simplex kernel integral is invariant under permutation of its nodes. -/
theorem simplexIntegral_perm (z : Fin (n + 1) → ℂ) (f : ℂ → ℂ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    simplexIntegral (z ∘ σ) f = simplexIntegral z f := by
  unfold simplexIntegral
  simp only [Function.comp_apply]
  rw [← integral_stdSimplex_comp_perm σ
    (fun u : Fin (n + 1) → ℝ => f (∑ k, (u k : ℂ) * z (σ k)))]
  congr 1
  funext u
  congr 1
  exact Equiv.sum_comp σ (fun k => (u k : ℂ) * z k)

/-- Coalescing all nodes evaluates the kernel, with the simplex volume factor. -/
theorem simplexIntegral_const (n : ℕ) (f : ℂ → ℂ) (w : ℂ) :
    simplexIntegral (fun _ : Fin (n + 1) => w) f = f w / (n.factorial : ℂ) := by
  unfold simplexIntegral
  have h : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)),
      f (∑ k, (u k : ℂ) * w) = f w := by
    intro u hu
    rw [← Finset.sum_mul, ← ofReal_sum, hu.2, ofReal_one, one_mul]
  rw [integral_stdSimplex_congr h, setIntegral_const]
  simp [Measure.real, Complex.real_smul,
    div_eq_mul_inv, mul_comm]

/-- Elementary barycentric sum used only in the simplex FTC proof. -/
private def nodeSum (z : Fin m → ℂ) (u : Fin m → ℝ) : ℂ :=
  ∑ k, (u k : ℂ) * z k

/-- Barycentric sums are continuous in their weights. -/
private lemma continuous_nodeSum (z : Fin m → ℂ) : Continuous (nodeSum z) := by
  unfold nodeSum
  fun_prop

/-- Barycentric sums belong to the convex hull of their nodes. -/
private lemma nodeSum_mem_convexHull (z : Fin m → ℂ) {u : Fin m → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin m)) :
    nodeSum z u ∈ convexHull ℝ (Set.range z) := by
  have h := affineCombination_mem_convexHull (s := Finset.univ) (v := z) (w := u)
    (fun i _ ↦ hu.1 i) hu.2
  rw [affineCombination_eq_centerMass hu.2] at h
  simpa [Finset.centerMass, hu.2, nodeSum, Complex.real_smul, mul_comm] using h

/-- Separate the last node of a barycentric sum. -/
private lemma nodeSum_finSimplexPoint_snoc (z : Fin n → ℂ) (x : ℂ) (v : Fin n → ℝ) :
    nodeSum (Fin.snoc z x) (finSimplexPoint v) =
      (∑ k, (v k : ℂ) * z k) + ((1 - ∑ k, v k : ℝ) : ℂ) * x := by
  simp [nodeSum, finSimplexPoint, Fin.sum_univ_castSucc]

/-- Changing the last node gives a segment parametrization. -/
private lemma nodeSum_finSimplexPoint_snoc_snoc
    (z : Fin n → ℂ) (x y : ℂ) (v : Fin n → ℝ) (t : ℝ) :
    nodeSum (Fin.snoc (Fin.snoc z x) y) (finSimplexPoint (Fin.snoc v t)) =
      nodeSum (Fin.snoc z y) (finSimplexPoint v) + (t : ℂ) * (x - y) := by
  simp [nodeSum_finSimplexPoint_snoc, Fin.sum_univ_castSucc]
  ring

/-- A continuous kernel stays continuous in simplex coordinates. -/
private lemma continuousOn_comp_finSimplex
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : ContinuousOn f Ω)
    {z : Fin (n + 1) → ℂ} (hz : Set.range z ⊆ Ω) :
    ContinuousOn (fun v => f (nodeSum z (finSimplexPoint v))) (posSimplexFin n 1) :=
  hf.comp ((continuous_nodeSum z).comp continuous_finSimplexPoint).continuousOn
    (fun _ hv => convexHull_min hz hΩconv
      (nodeSum_mem_convexHull z (finSimplexPoint_mem hv)))

/-- Appending a node preserves membership in the domain. -/
private lemma range_snoc_subset {Ω : Set ℂ} {z : Fin n → ℂ}
    (hz : Set.range z ⊆ Ω) {x : ℂ} (hx : x ∈ Ω) : Set.range (Fin.snoc z x) ⊆ Ω := by
  rintro _ ⟨k, rfl⟩
  refine Fin.lastCases ?_ (fun l => ?_) k
  · simpa using hx
  · simpa using hz ⟨l, rfl⟩

/-- The simplex fundamental theorem of calculus for a holomorphic kernel. -/
theorem simplexIntegral_sub
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (z : Fin n → ℂ) (hz : Set.range z ⊆ Ω) {x y : ℂ} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    simplexIntegral (Fin.snoc z x) f - simplexIntegral (Fin.snoc z y) f =
      (x - y) * simplexIntegral (Fin.snoc (Fin.snoc z x) y) (deriv f) := by
  simp only [simplexIntegral_eq_integral]
  change (∫ v in posSimplexFin n 1, f (nodeSum (Fin.snoc z x) (finSimplexPoint v))) -
    (∫ v in posSimplexFin n 1, f (nodeSum (Fin.snoc z y) (finSimplexPoint v))) =
    (x - y) * ∫ v in posSimplexFin (n + 1) 1,
      deriv f (nodeSum (Fin.snoc (Fin.snoc z x) y) (finSimplexPoint v))
  have hzx := range_snoc_subset hz hx
  have hzy := range_snoc_subset hz hy
  have hzxy := range_snoc_subset hzx hy
  have hcx := continuousOn_comp_finSimplex hΩconv hf.continuousOn hzx
  have hcy := continuousOn_comp_finSimplex hΩconv hf.continuousOn hzy
  have hcd := continuousOn_comp_finSimplex hΩconv hf.deriv.continuousOn hzxy
  have hix := hcx.integrableOn_compact (μ := volume) (isCompact_posSimplexFin_one n)
  have hiy := hcy.integrableOn_compact (μ := volume) (isCompact_posSimplexFin_one n)
  have hid : IntegrableOn (fun v => (x - y) *
      deriv f (nodeSum (Fin.snoc (Fin.snoc z x) y) (finSimplexPoint v)))
      (posSimplexFin (n + 1) 1) :=
    (continuousOn_const (c := x - y) |>.mul hcd).integrableOn_compact
      (isCompact_posSimplexFin_one (n + 1))
  rw [← integral_sub hix hiy, ← integral_const_mul,
    integral_posSimplexFin_snoc _ hid]
  apply setIntegral_congr_fun (measurableSet_posSimplexFin _ _)
  intro v hv
  dsimp only
  let r : ℝ := 1 - ∑ k, v k
  have hr : 0 ≤ r := sub_nonneg.mpr hv.2
  let A : ℂ := nodeSum (Fin.snoc z y) (finSimplexPoint v)
  have hmem {t : ℝ} (ht : t ∈ Set.Icc 0 r) : A + (t : ℂ) * (x - y) ∈ Ω := by
    rw [← nodeSum_finSimplexPoint_snoc_snoc]
    apply convexHull_min hzxy hΩconv
    apply nodeSum_mem_convexHull _ (finSimplexPoint_mem ?_)
    constructor
    · intro k
      refine Fin.lastCases ?_ (fun l => ?_) k <;> simp [hv.1, ht.1]
    · simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      dsimp [r] at ht
      linarith [ht.2]
  have hd (t : ℝ) (ht : t ∈ Set.Icc 0 r) :
      HasDerivAt (fun t : ℝ => f (A + (t : ℂ) * (x - y)))
        ((x - y) * deriv f (A + (t : ℂ) * (x - y))) t := by
    have hline : HasDerivAt (fun t : ℝ => A + (t : ℂ) * (x - y)) (x - y) t := by
      simpa using! ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (x - y)).const_add A
    simpa [mul_comm] using! ((hf _ (hmem ht)).differentiableAt.hasDerivAt.comp t hline)
  have hint : IntervalIntegrable (fun t : ℝ => (x - y) * deriv f (A + (t : ℂ) * (x - y)))
      volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hr]
    exact continuousOn_const.mul (hf.deriv.continuousOn.comp (by fun_prop) (fun t ht => hmem ht))
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa [Set.uIcc_of_le hr] using ht)) hint
  rw [intervalIntegral.integral_of_le hr, ← integral_Icc_eq_integral_Ioc] at H
  simp only [nodeSum_finSimplexPoint_snoc_snoc]
  change f (nodeSum (Fin.snoc z x) (finSimplexPoint v)) - f A = _
  rw [H]
  simp only [ofReal_zero, zero_mul, add_zero]
  congr 2
  simp only [A, r, nodeSum_finSimplexPoint_snoc]
  ring


end Complex
